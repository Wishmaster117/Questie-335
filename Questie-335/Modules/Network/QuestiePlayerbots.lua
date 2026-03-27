---@class QuestiePlayerbots
local QuestiePlayerbots = QuestieLoader:CreateModule("QuestiePlayerbots")

---@type QuestieDB
local QuestieDB = QuestieLoader:ImportModule("QuestieDB")
---@type QuestieMap
local QuestieMap = QuestieLoader:ImportModule("QuestieMap")
---@type QuestiePlayer
local QuestiePlayer = QuestieLoader:ImportModule("QuestiePlayer")
---@type QuestieLib
local QuestieLib = QuestieLoader:ImportModule("QuestieLib")
---@type ZoneDB
local ZoneDB = QuestieLoader:ImportModule("ZoneDB")

--- COMPATIBILITY ---
local C_Timer = QuestieCompat.C_Timer

-- Constants
local AVAILABLE_NOTE_TYPE = "playerbots_available"
local COMPLETE_NOTE_TYPE  = "playerbots_complete"
local BOT_ICON_COLOR      = { 1.00, 0.00, 1.00 }
local DEBUG_PLAYERBOTS    = false
local BOT_SCAN_TIMEOUT    = 1.0
local QUEST_LIST_SYNC_TIMEOUT = 1.25

-- State
local pendingScan
local scanGeneration = 0
local pendingQuestListSync
local questListSyncGeneration = 0
local questNameIndex
local questObjectiveCache
local questLootObjectiveCache
local lootMessageParsers

-- Forward declarations
local _EnsureUnifiedCache
local _NormalizeUnifiedCache
local _InferRequiredItemCount
local _StartQuestListSync
local _HandleQuestListSyncWhisper

-- Upvalues
local ipairs   = ipairs
local pairs    = pairs
local next     = next
local select   = select
local tconcat  = table.concat
local tsort    = table.sort
local tonumber = tonumber
local strsplit = strsplit
local strlower = string.lower
local format   = string.format
local tostring = tostring
local time     = time
local UnitExists = UnitExists
local UnitIsConnected = UnitIsConnected

local eventFrame = CreateFrame("Frame")

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

local function _Dbg(msg, ...)
    if not DEBUG_PLAYERBOTS then
        return
    end

    local text
    if select("#", ...) > 0 then
        text = format(msg, ...)
    else
        text = tostring(msg)
    end

    print("|cff00ff00[QuestiePB]|r " .. text)
end

local function _SafeName(value)
    if value == nil then
        return "nil"
    end
    return tostring(value)
end

local function _GetQuestName(questId)
    local quest = QuestieDB.GetQuest(questId)
    if quest and quest.name then
        return quest.name
    end
    return "Quest " .. tostring(questId)
end

local function _ExtractNpcIdFromGuid(guid)
    if not guid then return nil end
    local unitType, _, _, _, _, npcId = strsplit("-", guid)
    if unitType ~= "Creature" and unitType ~= "Vehicle" then return nil end
    return tonumber(npcId)
end

local function _GetGroupMemberNames()
    local names      = {}
    local playerName = UnitName("player")

    local function _AddUnitIfGroupedAndOnline(unit)
        if not unit or (UnitExists and not UnitExists(unit)) then
            return
        end

        if UnitIsConnected and not UnitIsConnected(unit) then
            return
        end

        local name = UnitName(unit)
        if name and name ~= playerName then
            names[#names + 1] = name
        end
    end

    if IsInRaid() then
        for i = 1, (GetNumRaidMembers() or 0) do
            _AddUnitIfGroupedAndOnline("raid" .. i)
        end
    elseif GetNumPartyMembers and GetNumPartyMembers() > 0 then
        for i = 1, GetNumPartyMembers() do
            _AddUnitIfGroupedAndOnline("party" .. i)
        end
    end

    return names
end

local function _GetCurrentGroupSignature()
    local groupMembers = _GetGroupMemberNames()
    if #groupMembers == 0 then return nil end
    tsort(groupMembers)
    return tconcat(groupMembers, "|")
end

local function _IsGroupMemberOnline(name)
    if not name or name == "" then
        return false
    end

    for _, memberName in ipairs(_GetGroupMemberNames()) do
        if memberName == name then
            return true
        end
    end

    return false
end

local function _StripWoWFormatting(text)
    if not text then
        return nil
    end

    text = text:gsub("|c%x%x%x%x%x%x%x%x", "")
    text = text:gsub("|r", "")
    text = text:gsub("|H.-|h(.-)|h", "%1")
    return text
end

local function _EscapeLuaPattern(text)
    return (tostring(text):gsub("([%(%)%.%%%+%-%*%?%[%]%^%$])", "%%%1"))
end

local function _Trim(text)
    if not text then
        return nil
    end

    return (tostring(text):gsub("^%s+", ""):gsub("%s+$", ""))
end

local function _NormalizeQuestName(text)
    text = _StripWoWFormatting(text)
    text = _Trim(text)
    if not text or text == "" then
        return nil
    end

    text = strlower(text)
    text = text:gsub("%s+", " ")
    text = _Trim(text)

    return text ~= "" and text or nil
end

local function _ExtractQuestLinkName(message)
    if not message then
        return nil
    end
    return _Trim(_StripWoWFormatting(message:match("|Hquest:%d+.-|h%[(.-)%]|h")))
end

local function _NormalizeObjectiveLabel(text)
    text = _StripWoWFormatting(text)
    text = _Trim(text)
    if not text or text == "" then
        return nil
    end

    text = strlower(text)
    text = text:gsub("[%.,:;!?]+$", "")
    text = text:gsub("^[-%*%s]+", "")
    text = text:gsub("%s+", " ")
    text = _Trim(text)

    if text == "" then
        return nil
    end

    return text
end

local function _ParseBotObjectiveProgressMessage(message)
    local cleanMessage = _StripWoWFormatting(message)
    cleanMessage = _Trim(cleanMessage)
    if not cleanMessage or cleanMessage == "" then
        return nil, nil, nil, nil
    end

    local objectiveText, currentCount, neededCount, questName = cleanMessage:match("^(.+)%s+(%d+)%s*/%s*(%d+)%s+%[(.+)%]$")
    if not objectiveText then
        objectiveText, currentCount, neededCount, questName = cleanMessage:match("^(.+)%s*:%s*(%d+)%s*/%s*(%d+)%s+%[(.+)%]$")
    end

    objectiveText = _Trim(objectiveText)
    questName = _Trim(questName)
    currentCount = tonumber(currentCount)
    neededCount = tonumber(neededCount)

    return objectiveText, currentCount, neededCount, questName
end

local function _BuildObjectiveDisplayName(objective, objectiveName)
    local displayName = objectiveName

    if (not displayName or displayName == "") and objective and objective.Text then
        local text = _StripWoWFormatting(objective.Text)
        text = _Trim(text)

        if text and text ~= "" then
            text = text:gsub("%s*:%s*%d+%s*/%s*%d+$", "")
            text = text:gsub("%s+%d+%s*/%s*%d+$", "")
            displayName = _Trim(text)
        end
    end

    return displayName
end

local function _BuildChatMessagePattern(formatString)
    if type(formatString) ~= "string" or formatString == "" then
        return nil
    end

    local parts = {"^"}
    local index = 1
    local length = formatString:len()

    while index <= length do
        local char = formatString:sub(index, index)
        if char == "%" then
            local cursor = index + 1
            while cursor <= length and formatString:sub(cursor, cursor):match("[%d%$]") do
                cursor = cursor + 1
            end

            local specifier = formatString:sub(cursor, cursor)
            if specifier == "s" then
                parts[#parts + 1] = "(.+)"
            elseif specifier == "d" then
                parts[#parts + 1] = "(%d+)"
            elseif specifier == "%" then
                parts[#parts + 1] = "%%"
            else
                parts[#parts + 1] = _EscapeLuaPattern(formatString:sub(index, cursor))
            end

            index = cursor + 1
        else
            parts[#parts + 1] = _EscapeLuaPattern(char)
            index = index + 1
        end
    end

    parts[#parts + 1] = "$"
    return tconcat(parts)
end

local function _GetPlayerQuestLogIndexByQuestId(questId)
    if not questId or not QuestiePlayer.currentQuestlog or not QuestiePlayer.currentQuestlog[questId] then
        return nil
    end

    if not GetNumQuestLogEntries or not GetQuestLink then
        return nil
    end

    for questLogIndex = 1, (GetNumQuestLogEntries() or 0) do
        local questLink = GetQuestLink(questLogIndex)
        local currentQuestId = questLink and tonumber(questLink:match("|Hquest:(%d+)")) or nil
        if currentQuestId == questId then
            return questLogIndex
        end
    end

    return nil
end

local function _GetPlayerQuestObjectiveTemplate(questId)
    local questLogIndex = _GetPlayerQuestLogIndexByQuestId(questId)
    if not questLogIndex or not GetQuestLogLeaderBoard or not GetNumQuestLeaderBoards then
        return nil
    end

    local previousSelection = GetQuestLogSelection and GetQuestLogSelection() or nil
    if SelectQuestLogEntry then
        SelectQuestLogEntry(questLogIndex)
    end

    local objectiveCount = GetNumQuestLeaderBoards(questLogIndex)
    if not objectiveCount then
        objectiveCount = GetNumQuestLeaderBoards()
    end

    local template = {}

    for objectiveIndex = 1, (objectiveCount or 0) do
        local objectiveText = GetQuestLogLeaderBoard(objectiveIndex, questLogIndex)
        if not objectiveText then
            objectiveText = GetQuestLogLeaderBoard(objectiveIndex)
        end

        objectiveText = _StripWoWFormatting(objectiveText)
        objectiveText = _Trim(objectiveText)

        if objectiveText and objectiveText ~= "" then
            local currentCount, neededCount = objectiveText:match("(%d+)%s*/%s*(%d+)$")
            local displayName = objectiveText
                :gsub("%s*:%s*%d+%s*/%s*%d+$", "")
                :gsub("%s+%d+%s*/%s*%d+$", "")
            displayName = _Trim(displayName)

            template[#template + 1] = {
                displayName = (displayName and displayName ~= "") and displayName or objectiveText,
                needed      = tonumber(neededCount),
                current     = tonumber(currentCount),
            }
        end
    end

    if SelectQuestLogEntry and previousSelection and previousSelection > 0 then
        SelectQuestLogEntry(previousSelection)
    end

    if #template == 0 then
        return nil
    end

    return template
end

local function _GetQuestObjectiveRequirements(questId)
    if questObjectiveCache and questObjectiveCache[questId] then
        return questObjectiveCache[questId]
    end

    questObjectiveCache = questObjectiveCache or {}

    local result = {
        questId          = questId,
        objectiveCount   = 0,
        isFullyInferable = true,
        objectives       = {},
        orderedKeys      = {},
        aliasToKey       = {},
    }

    local quest = QuestieDB.GetQuest(questId)
    if not quest or not quest.ObjectiveData or #quest.ObjectiveData == 0 then
        result.isFullyInferable = false
        questObjectiveCache[questId] = result
        return result
    end


    local itemObjectiveCount = 0
    for _, objective in ipairs(quest.ObjectiveData) do
        if objective and objective.Type == "item" and objective.Id then
            itemObjectiveCount = itemObjectiveCount + 1
        end
    end

    local function _AddAlias(objectiveEntry, alias)
        alias = _NormalizeObjectiveLabel(alias)
        if not alias or alias == "" or objectiveEntry.aliasLookup[alias] then
            return
        end

        objectiveEntry.aliasLookup[alias] = true
        objectiveEntry.aliases[#objectiveEntry.aliases + 1] = alias
        result.aliasToKey[alias] = result.aliasToKey[alias] or objectiveEntry.key
    end

    for index, objective in ipairs(quest.ObjectiveData) do
        local objectiveType = objective and objective.Type or nil
        local objectiveKey
        local objectiveName
        local neededCount

        if objectiveType == "monster" and objective.Id then
            objectiveKey = "monster:" .. tostring(objective.Id)
            objectiveName = QuestieDB.QueryNPCSingle(objective.Id, "name")
        elseif objectiveType == "object" and objective.Id then
            objectiveKey = "object:" .. tostring(objective.Id)
            objectiveName = QuestieDB.QueryObjectSingle and QuestieDB.QueryObjectSingle(objective.Id, "name") or nil
        elseif objectiveType == "item" and objective.Id then
            objectiveKey = "item:" .. tostring(objective.Id)
            objectiveName = QuestieDB.QueryItemSingle(objective.Id, "name")
            neededCount = _InferRequiredItemCount(quest, objective, itemObjectiveCount)
            if not neededCount or neededCount <= 0 then
                result.isFullyInferable = false
            end
        elseif objectiveType == "killcredit" then
            objectiveKey = "killcredit:" .. tostring(objective.RootId or index)
            objectiveName = objective.RootId and QuestieDB.QueryNPCSingle(objective.RootId, "name") or nil
        elseif objectiveType == "event" or objectiveType == "reputation" or objectiveType == "spell" then
            result.isFullyInferable = false
        elseif objectiveType then
            result.isFullyInferable = false
        end

        if objectiveKey then
            local objectiveEntry = {
                key         = objectiveKey,
                type        = objectiveType,
                aliases     = {},
                aliasLookup = {},
                needed      = neededCount,
                displayName = _BuildObjectiveDisplayName(objective, objectiveName),
            }

            _AddAlias(objectiveEntry, objective.Text)
            _AddAlias(objectiveEntry, objectiveName)

            result.objectives[objectiveKey] = objectiveEntry
            result.orderedKeys[#result.orderedKeys + 1] = objectiveKey
            result.objectiveCount = result.objectiveCount + 1
        end
    end

    if result.objectiveCount == 0 then
        result.isFullyInferable = false
    end

    for _, objectiveEntry in pairs(result.objectives) do
        objectiveEntry.aliasLookup = nil
    end

    questObjectiveCache[questId] = result
    return result
end

local function _CountObjectiveWords(text)
    text = _NormalizeObjectiveLabel(text)
    if not text or text == "" then
        return 0
    end

    local count = 0
    for _ in text:gmatch("%S+") do
        count = count + 1
    end

    return count
end

local function _GetObjectiveCandidateWordCounts(objectiveEntry)
    local counts = {}
    local seen = {}

    local function _AddCount(text)
        local count = _CountObjectiveWords(text)
        if count > 0 and not seen[count] then
            seen[count] = true
            counts[#counts + 1] = count
        end
    end

    if objectiveEntry then
        _AddCount(objectiveEntry.displayName)
        for _, alias in ipairs(objectiveEntry.aliases or {}) do
            _AddCount(alias)
        end
    end

    return counts
end

local function _SelectBestObjectiveKeyByWordCount(requirements, objectiveKeys, objectiveText)
    local objectiveTextWordCount = _CountObjectiveWords(objectiveText)
    if objectiveTextWordCount <= 0 or not objectiveKeys or #objectiveKeys <= 1 then
        return nil
    end

    local bestObjectiveKey = nil
    local bestScore = nil
    local hasTie = false

    for _, objectiveKey in ipairs(objectiveKeys) do
        local objectiveEntry = requirements.objectives[objectiveKey]
        local localBestScore = nil

        for _, candidateWordCount in ipairs(_GetObjectiveCandidateWordCounts(objectiveEntry)) do
            local score = math.abs(candidateWordCount - objectiveTextWordCount)
            if localBestScore == nil or score < localBestScore then
                localBestScore = score
            end
        end

        if localBestScore ~= nil then
            if bestScore == nil or localBestScore < bestScore then
                bestObjectiveKey = objectiveKey
                bestScore = localBestScore
                hasTie = false
            elseif localBestScore == bestScore then
                hasTie = true
            end
        end
    end

    if hasTie then
        return nil
    end

    return bestObjectiveKey
end

local function _FindObjectiveKeyForQuestMessage(questId, objectiveText, botName, neededCount)
    local requirements = _GetQuestObjectiveRequirements(questId)
    local normalizedObjective = _NormalizeObjectiveLabel(objectiveText)
    if not normalizedObjective then
        return nil
    end

    local entry
    local rememberedObjectiveKey
    if botName and botName ~= "" then
        local cache = _EnsureUnifiedCache()
        local botEntries = cache.bots[botName]
        if botEntries then
            entry = botEntries[questId] or botEntries[tostring(questId)]
        end
    end

    if entry and entry.reportedObjectiveAliases and entry.reportedObjectiveAliases[normalizedObjective] then
        rememberedObjectiveKey = entry.reportedObjectiveAliases[normalizedObjective]
    end

    if requirements.aliasToKey[normalizedObjective] then
        return requirements.aliasToKey[normalizedObjective]
    end

    for _, objectiveKey in ipairs(requirements.orderedKeys or {}) do
        local objectiveEntry = requirements.objectives[objectiveKey]
        for _, alias in ipairs(objectiveEntry.aliases or {}) do
            if normalizedObjective == alias
                or normalizedObjective:find(alias, 1, true)
                or alias:find(normalizedObjective, 1, true)
            then
                return objectiveKey
            end
        end
    end

    if requirements.objectiveCount == 1 and requirements.orderedKeys and requirements.orderedKeys[1] then
        _Dbg(
            "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> sole-objective=%s",
            _SafeName(botName),
            _SafeName(questId),
            _GetQuestName(questId),
            _SafeName(objectiveText),
            _SafeName(requirements.orderedKeys[1])
        )
        return requirements.orderedKeys[1]
    end

    if entry and requirements.orderedKeys then
        local unresolvedObjectiveKeys = {}
        local sameNeededUnresolvedObjectiveKeys = {}

        for _, objectiveKey in ipairs(requirements.orderedKeys) do
            local progress = entry.objectiveProgress and entry.objectiveProgress[objectiveKey] or nil
            local current = tonumber(progress and progress.current or 0) or 0
            local needed = tonumber(progress and progress.needed or requirements.objectives[objectiveKey].needed or 0) or 0
            local completed = progress and progress.completed

            if not completed then
                unresolvedObjectiveKeys[#unresolvedObjectiveKeys + 1] = objectiveKey

                if neededCount and neededCount > 0 then
                    if needed == 0 or needed == neededCount or current < neededCount then
                        sameNeededUnresolvedObjectiveKeys[#sameNeededUnresolvedObjectiveKeys + 1] = objectiveKey
                    end
                end
            end
        end

        if #sameNeededUnresolvedObjectiveKeys > 1 then
            local structuralObjectiveKey = _SelectBestObjectiveKeyByWordCount(
                requirements,
                sameNeededUnresolvedObjectiveKeys,
                objectiveText
            )

            if structuralObjectiveKey then
                if rememberedObjectiveKey and rememberedObjectiveKey ~= structuralObjectiveKey then
                    _Dbg(
                        "OBJ-MATCH-ALIAS-OVERRIDE bot=%s quest=%s (%s) objectiveText=%s remembered=%s structural=%s",
                        _SafeName(botName),
                        _SafeName(questId),
                        _GetQuestName(questId),
                        _SafeName(objectiveText),
                        _SafeName(rememberedObjectiveKey),
                        _SafeName(structuralObjectiveKey)
                    )
                else
                    _Dbg(
                        "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> structural-wordcount=%s",
                        _SafeName(botName),
                        _SafeName(questId),
                        _GetQuestName(questId),
                        _SafeName(objectiveText),
                        _SafeName(structuralObjectiveKey)
                    )
                end

                return structuralObjectiveKey
            end
        end

        if rememberedObjectiveKey then
            for _, candidateObjectiveKey in ipairs(sameNeededUnresolvedObjectiveKeys) do
                if candidateObjectiveKey == rememberedObjectiveKey then
                    _Dbg(
                        "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> remembered-alias=%s",
                        _SafeName(botName),
                        _SafeName(questId),
                        _GetQuestName(questId),
                        _SafeName(objectiveText),
                        _SafeName(rememberedObjectiveKey)
                    )
                    return rememberedObjectiveKey
                end
            end
        end

        if #sameNeededUnresolvedObjectiveKeys == 1 then
            _Dbg(
                "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> first-unresolved-same-needed=%s",
                _SafeName(botName),
                _SafeName(questId),
                _GetQuestName(questId),
                _SafeName(objectiveText),
                _SafeName(sameNeededUnresolvedObjectiveKeys[1])
            )
            return sameNeededUnresolvedObjectiveKeys[1]
        end

        if #unresolvedObjectiveKeys == 1 then
            _Dbg(
                "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> only-unresolved=%s",
                _SafeName(botName),
                _SafeName(questId),
                _GetQuestName(questId),
                _SafeName(objectiveText),
                _SafeName(unresolvedObjectiveKeys[1])
            )
            return unresolvedObjectiveKeys[1]
        end

        if #unresolvedObjectiveKeys > 1 then
            local structuralObjectiveKey = _SelectBestObjectiveKeyByWordCount(
                requirements,
                unresolvedObjectiveKeys,
                objectiveText
            )

            if structuralObjectiveKey then
                _Dbg(
                    "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> structural-unresolved=%s",
                    _SafeName(botName),
                    _SafeName(questId),
                    _GetQuestName(questId),
                    _SafeName(objectiveText),
                    _SafeName(structuralObjectiveKey)
                )
                return structuralObjectiveKey
            end

            _Dbg(
                "OBJ-MATCH-FALLBACK bot=%s quest=%s (%s) objectiveText=%s -> ambiguous",
                _SafeName(botName),
                _SafeName(questId),
                _GetQuestName(questId),
                _SafeName(objectiveText)
            )
            return nil
        end
    end

    if rememberedObjectiveKey then
        return rememberedObjectiveKey
    end

    return nil
end

local function _IsObjectiveProgressCompleteForQuest(questId, objectiveProgress)
    local requirements = _GetQuestObjectiveRequirements(questId)
    if not requirements.isFullyInferable then
        return false
    end

    for objectiveKey, objectiveEntry in pairs(requirements.objectives) do
        local progress = objectiveProgress and objectiveProgress[objectiveKey] or nil
        local currentCount = tonumber(progress and progress.current or 0) or 0
        local objectiveNeededCount = tonumber(progress and progress.needed or objectiveEntry.needed or 0) or 0

        if objectiveNeededCount <= 0 or currentCount < objectiveNeededCount then
            return false
        end
    end

    return true
end

local function _GetLootMessageParsers()
    if lootMessageParsers then
        return lootMessageParsers
    end

    lootMessageParsers = {}

    local function _AddLootPattern(formatString, hasPlayerName, hasCount)
        local pattern = _BuildChatMessagePattern(formatString)
        if pattern then
            lootMessageParsers[#lootMessageParsers + 1] = {
                pattern       = pattern,
                hasPlayerName = hasPlayerName,
                hasCount      = hasCount,
            }
        end
    end

    _AddLootPattern(LOOT_ITEM, true, false)
    _AddLootPattern(LOOT_ITEM_MULTIPLE, true, true)
    _AddLootPattern(LOOT_ITEM_PUSHED, true, false)
    _AddLootPattern(LOOT_ITEM_PUSHED_MULTIPLE, true, true)
    _AddLootPattern(LOOT_ITEM_CREATED, true, false)
    _AddLootPattern(LOOT_ITEM_CREATED_MULTIPLE, true, true)

    return lootMessageParsers
end

local function _ParseBotLootMessage(message, fallbackPlayerName)
    if not message then
        return nil, nil, nil
    end

    local itemId = tonumber(message:match("item:(%d+)"))
    if not itemId then
        return nil, nil, nil
    end

    local looterName
    local itemLink
    local quantity

    for _, parser in ipairs(_GetLootMessageParsers()) do
        local a, b, c = message:match(parser.pattern)
        if a then
            if parser.hasPlayerName and parser.hasCount then
                looterName = a
                itemLink   = b
                quantity   = tonumber(c)
            elseif parser.hasPlayerName then
                looterName = a
                itemLink   = b
            elseif parser.hasCount then
                itemLink   = a
                quantity   = tonumber(b)
            else
                itemLink = a
            end
            break
        end
    end

    looterName = looterName or fallbackPlayerName
    if not looterName then
        return nil, nil, nil
    end

    looterName = looterName:match("^[^-]+") or looterName
    quantity = quantity or tonumber(message:match("[xX](%d+)%p?$")) or 1

    if itemLink and itemId ~= tonumber(itemLink:match("item:(%d+)")) then
        itemId = tonumber(itemLink:match("item:(%d+)")) or itemId
    end

    return looterName, itemId, quantity
end

_InferRequiredItemCount = function(quest, objective, itemObjectiveCount)
    if not quest or not objective or not objective.Id then
        return nil
    end

    local itemName = QuestieDB.QueryItemSingle(objective.Id, "name")
    local escapedItemName = itemName and _EscapeLuaPattern(strlower(itemName)) or nil

    local function _TryLineWithoutItemName(line)
        line = _StripWoWFormatting(line)
        if not line or line == "" then
            return nil
        end

        local lowerLine = strlower(line)

        local _, requiredCount = lowerLine:match("(%d+)%s*/%s*(%d+)")
        if requiredCount then
            return tonumber(requiredCount)
        end

        local firstNumber = lowerLine:match("(%d+)")
        if firstNumber then
            return tonumber(firstNumber)
        end

        return nil
    end

    local function _TryLine(line)
        line = _StripWoWFormatting(line)
        if not line or line == "" then
            return nil
        end

        local lowerLine = strlower(line)
        if escapedItemName and not lowerLine:find(escapedItemName, 1, false) then
            return nil
        end

        if escapedItemName then
            local beforeCount = lowerLine:match("(%d+)[^%d]-" .. escapedItemName)
            if beforeCount then
                return tonumber(beforeCount)
            end

            local afterCount = lowerLine:match(escapedItemName .. "[^%d]-(%d+)")
            if afterCount then
                return tonumber(afterCount)
            end
        end

        local completedCount = lowerLine:match("(%d+)%s*/%s*(%d+)")
        if completedCount then
            return tonumber(select(2, lowerLine:match("(%d+)%s*/%s*(%d+)")))
        end

        local firstNumber = lowerLine:match("(%d+)")
        if firstNumber then
            return tonumber(firstNumber)
        end

        return nil
    end

    if objective.Text then
        local count = _TryLine(objective.Text)
        if count and count > 0 then
            return count
        end
    end

    for _, line in ipairs(quest.Description or {}) do
        local count = _TryLine(line)
        if count and count > 0 then
            return count
        end
    end

    if itemObjectiveCount == 1 then
        local fallbackCount = nil

        if objective.Text then
            local count = _TryLineWithoutItemName(objective.Text)
            if count and count > 0 then
                fallbackCount = count
            end
        end

        for _, line in ipairs(quest.Description or {}) do
            local count = _TryLineWithoutItemName(line)
            if count and count > 0 then
                if not fallbackCount or count > fallbackCount then
                    fallbackCount = count
                end
            end
        end

        if fallbackCount and fallbackCount > 0 then
            _Dbg(
                "ITEM-COUNT-FALLBACK quest=%s (%s) item=%s -> inferred=%s",
                _SafeName(quest.Id or objective.Id),
                _GetQuestName(quest.Id or 0),
                _SafeName(objective.Id),
                _SafeName(fallbackCount)
            )
            return fallbackCount
        end
    end

    if itemObjectiveCount == 1 then
        return 1
    end

    return nil
end

local function _GetQuestLootObjectiveRequirements(questId)
    if questLootObjectiveCache and questLootObjectiveCache[questId] then
        return questLootObjectiveCache[questId]
    end

    questLootObjectiveCache = questLootObjectiveCache or {}

    local requirements = {
        isEligible = false,
        items      = {},
    }

    local quest = QuestieDB.GetQuest(questId)
    if not quest or not quest.ObjectiveData then
        questLootObjectiveCache[questId] = requirements
        return requirements
    end

    local itemObjectives = {}
    local itemObjectiveCount = 0
    local hasNonItemObjective = false

    for _, objective in ipairs(quest.ObjectiveData or {}) do
        if objective and objective.Type == "item" and objective.Id then
            itemObjectiveCount = itemObjectiveCount + 1
            itemObjectives[#itemObjectives + 1] = objective
        elseif objective and objective.Type ~= "event" and objective.Type ~= "reputation" then
            hasNonItemObjective = true
        end
    end

    if itemObjectiveCount == 0 or hasNonItemObjective then
        questLootObjectiveCache[questId] = requirements
        return requirements
    end

    for _, objective in ipairs(itemObjectives) do
        local requiredCount = _InferRequiredItemCount(quest, objective, itemObjectiveCount)
        if not requiredCount or requiredCount <= 0 then
            questLootObjectiveCache[questId] = requirements
            return requirements
        end

        requirements.items[objective.Id] = requiredCount
    end

    requirements.isEligible = next(requirements.items) ~= nil
    questLootObjectiveCache[questId] = requirements
    return requirements
end

local function _IsLootProgressCompleteForQuest(questId, lootProgress)
    local requirements = _GetQuestLootObjectiveRequirements(questId)
    if not requirements.isEligible then
        return false
    end

    for itemId, requiredCount in pairs(requirements.items) do
        local currentCount = tonumber(lootProgress and lootProgress[itemId] or 0) or 0
        if currentCount < requiredCount then
            return false
        end
    end

    return true
end

--------------------------------------------------------------------------------
-- Cache Management
--------------------------------------------------------------------------------

_EnsureUnifiedCache = function()
 local cache = Questie.db.char.playerbotsQuestStateCache

 if not cache or type(cache) ~= "table" then
     cache = {
         version        = 4,
         groupSignature = nil,
         bots           = {},
     }
 else
     cache.version = 4
     cache.bots    = cache.bots or {}
 end

 Questie.db.char.playerbotsQuestStateCache = cache

 if _NormalizeUnifiedCache then
     _NormalizeUnifiedCache(cache)
 end

 return cache
end

local function _RememberQuestNameAlias(botName, questId, reportedQuestName)
    if not botName or not questId or not reportedQuestName or reportedQuestName == "" then
        return
    end

    local normalizedQuestName = _NormalizeQuestName(reportedQuestName)
    if not normalizedQuestName then
        return
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then
        return
    end

    local entry = botEntries[questId] or botEntries[tostring(questId)]
    if not entry then
        return
    end

    entry.reportedQuestNames = entry.reportedQuestNames or {}
    entry.reportedQuestNames[normalizedQuestName] = reportedQuestName
    entry.lastSeen = time()
end

local function _RememberObjectiveAlias(botName, questId, objectiveKey, reportedObjectiveText)
    if not botName or not questId or not objectiveKey or not reportedObjectiveText or reportedObjectiveText == "" then
        return
    end

    local normalizedObjectiveText = _NormalizeObjectiveLabel(reportedObjectiveText)
    if not normalizedObjectiveText then
        return
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then
        return
    end

    local entry = botEntries[questId] or botEntries[tostring(questId)]
    if not entry then
        return
    end

    entry.reportedObjectiveAliases = entry.reportedObjectiveAliases or {}
    entry.reportedObjectiveAliases[normalizedObjectiveText] = objectiveKey
    entry.lastSeen = time()
end

local function _RememberObjectiveAlias(botName, questId, objectiveKey, reportedObjectiveText)
    if not botName or not questId or not objectiveKey or not reportedObjectiveText or reportedObjectiveText == "" then
        return
    end

    local normalizedObjectiveText = _NormalizeObjectiveLabel(reportedObjectiveText)
    if not normalizedObjectiveText then
        return
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then
        return
    end

    local entry = botEntries[questId] or botEntries[tostring(questId)]
    if not entry then
        return
    end

    entry.reportedObjectiveAliases = entry.reportedObjectiveAliases or {}
    entry.reportedObjectiveAliases[normalizedObjectiveText] = objectiveKey
    entry.lastSeen = time()
end

local function _CopyStringList(values)
    local copy = {}
    for _, value in ipairs(values or {}) do
        copy[#copy + 1] = value
    end
    return copy
end

local function _GetCurrentOnlineGroupBotsFromCache()
    local cache            = _EnsureUnifiedCache()
    local currentGroupBots = {}
    local currentNames     = _GetGroupMemberNames()

    if #currentNames == 0 then
        return currentGroupBots, nil
    end

    local allowedNames = {}
    for _, botName in ipairs(currentNames) do
        allowedNames[botName] = true
    end

    for botName, botEntries in pairs(cache.bots or {}) do
        if allowedNames[botName] then
            currentGroupBots[botName] = botEntries
        end
    end

    local currentSignatureParts = {}
    for botName in pairs(currentGroupBots) do
        currentSignatureParts[#currentSignatureParts + 1] = botName
    end

    if #currentSignatureParts == 0 then
        return currentGroupBots, nil
    end

    tsort(currentSignatureParts)
    return currentGroupBots, tconcat(currentSignatureParts, "|")
end

local function _GetArchivedBotsFromCache()
    local cache        = _EnsureUnifiedCache()
    local archivedBots = {}
    local currentNames = _GetGroupMemberNames()
    local currentSet   = {}

    for _, botName in ipairs(currentNames) do
        currentSet[botName] = true
    end

    for botName, botEntries in pairs(cache.bots or {}) do
        if not currentSet[botName] then
            archivedBots[botName] = botEntries
        end
    end

    local archivedSignatureParts = {}
    for botName in pairs(archivedBots) do
        archivedSignatureParts[#archivedSignatureParts + 1] = botName
    end

    if #archivedSignatureParts == 0 then
        return archivedBots, nil
    end

    tsort(archivedSignatureParts)
    return archivedBots, tconcat(archivedSignatureParts, "|")
end

--------------------------------------------------------------------------------
-- Quest Data Helpers
--------------------------------------------------------------------------------

local function _GetQuestStartNpcId(questId)
    local quest = QuestieDB.GetQuest(questId)
    if not quest or not quest.Starts or not quest.Starts.NPC or not quest.Starts.NPC[1] then
        return nil
    end
    return quest.Starts.NPC[1]
end

local function _GetQuestFinisherEntity(finisherType, finisherId)
    if finisherType == "monster" then
        local npc = QuestieDB:GetNPC(finisherId)
        return npc, finisherId
    elseif finisherType == "object" then
        local object = QuestieDB:GetObject(finisherId)
        return object, -finisherId
    end

    return nil, nil
end

local function _GetQuestFinisherData(questId)
    local quest = QuestieDB.GetQuest(questId)
    if not quest or not quest.Finisher or not quest.Finisher.Type or not quest.Finisher.Id then
        return nil, nil, nil, nil
    end

    local finisherType = quest.Finisher.Type
    local finisherId   = quest.Finisher.Id
    local entity, noteId = _GetQuestFinisherEntity(finisherType, finisherId)

    if not entity or not noteId then
        return nil, nil, nil, nil
    end

    return finisherType, finisherId, entity, noteId
end

local function _IsAutoTurnInQuest(questId)
    local quest = QuestieDB.GetQuest(questId)
    if not quest or not quest.Starts or not quest.Starts.NPC or not quest.Starts.NPC[1] then
        return false
    end

    if not quest.Finisher or not quest.Finisher.Type or not quest.Finisher.Id then
        return false
    end

    if quest.Finisher.Id == quest.Starts.NPC[1] then
        return false
    end

    if quest.ObjectiveData and #quest.ObjectiveData > 0 then
        return false
    end

    return true
end

local function _NormalizeBotQuestState(questId, state)
    if state == "active" and _IsAutoTurnInQuest(questId) then
        return "completed"
    end

    return state
end

local function _GetImplicitlyRewardedParentQuestIds(questId)
    local parentQuestIds = {}
    local seen = {}

    local function _AddParentQuestId(parentQuestId)
        if not parentQuestId or parentQuestId <= 0 or seen[parentQuestId] then
            return
        end

        seen[parentQuestId] = true
        parentQuestIds[#parentQuestIds + 1] = parentQuestId
    end

    local preQuestGroup = QuestieDB.QueryQuestSingle(questId, "preQuestGroup")
    if preQuestGroup then
        for _, parentQuestId in ipairs(preQuestGroup) do
            _AddParentQuestId(parentQuestId)
        end
    end

    local preQuestSingle = QuestieDB.QueryQuestSingle(questId, "preQuestSingle")
    if preQuestSingle and #preQuestSingle == 1 then
        _AddParentQuestId(preQuestSingle[1])
    end

    return parentQuestIds
end

local function _RemoveCompletedParentStatesFromBotEntries(botEntries, questId)
    if not botEntries or not questId then
        return
    end

    for _, parentQuestId in ipairs(_GetImplicitlyRewardedParentQuestIds(questId)) do
        local parentEntry = botEntries[parentQuestId] or botEntries[tostring(parentQuestId)]
        if parentEntry and parentEntry.state == "completed" then
            botEntries[parentQuestId] = nil
            botEntries[tostring(parentQuestId)] = nil
        end
    end
end

_NormalizeUnifiedCache = function(cache)
    if not cache or type(cache) ~= "table" then return end

    cache.bots = cache.bots or {}

    for botName, botEntries in pairs(cache.bots) do
        if type(botEntries) ~= "table" then
            cache.bots[botName] = nil
        else
            for storedQuestId, entry in pairs(botEntries) do
                local questId = tonumber(storedQuestId)

                if not questId or type(entry) ~= "table" then
                    botEntries[storedQuestId] = nil
                else
                    local finisherType, finisherId = _GetQuestFinisherData(questId)

                    entry.questId      = questId
                    entry.starterNpcId = _GetQuestStartNpcId(questId)
                    entry.finisherType = finisherType
                    entry.finisherId   = finisherId
                    entry.state        = _NormalizeBotQuestState(questId, entry.state)
                    entry.lastSeen     = entry.lastSeen or time()

                    if type(entry.lootProgress) ~= "table" then
                        entry.lootProgress = nil
                    else
                        for storedItemId, amount in pairs(entry.lootProgress) do
                            local itemId = tonumber(storedItemId)
                            local numericAmount = tonumber(amount)
                            if not itemId or not numericAmount or numericAmount <= 0 then
                                entry.lootProgress[storedItemId] = nil
                            else
                                entry.lootProgress[itemId] = numericAmount
                                if tostring(itemId) ~= storedItemId then
                                    entry.lootProgress[storedItemId] = nil
                                end
                            end
                        end

                        if not next(entry.lootProgress) then
                            entry.lootProgress = nil
                        end
                    end

                    if type(entry.objectiveProgress) ~= "table" then
                        entry.objectiveProgress = nil
                    else
                        for objectiveKey, progress in pairs(entry.objectiveProgress) do
                            if type(objectiveKey) ~= "string" or type(progress) ~= "table" then
                                entry.objectiveProgress[objectiveKey] = nil
                            else
                                local currentCount = tonumber(progress.current or 0) or 0
                                local neededCount = tonumber(progress.needed or 0) or 0

                                if currentCount <= 0 and neededCount <= 0 and not progress.completed then
                                    entry.objectiveProgress[objectiveKey] = nil
                                else
                                    progress.current = currentCount > 0 and currentCount or nil
                                    progress.needed = neededCount > 0 and neededCount or nil
                                    progress.completed = progress.completed
                                        or (progress.current and progress.needed and progress.current >= progress.needed)
                                        or nil
                                end
                            end
                        end

                        if not next(entry.objectiveProgress) then
                            entry.objectiveProgress = nil
                        end
                    end

                    if type(entry.reportedQuestNames) ~= "table" then
                        entry.reportedQuestNames = nil
                    else
                        local normalizedReportedQuestNames = {}
                        for reportedKey, reportedName in pairs(entry.reportedQuestNames) do
                            local normalizedReportedQuestName = _NormalizeQuestName(reportedName) or _NormalizeQuestName(reportedKey)
                            if normalizedReportedQuestName then
                                normalizedReportedQuestNames[normalizedReportedQuestName] = reportedName
                            end
                        end

                        entry.reportedQuestNames = next(normalizedReportedQuestNames) and normalizedReportedQuestNames or nil
                    end

                    if type(entry.reportedObjectiveAliases) ~= "table" then
                        entry.reportedObjectiveAliases = nil
                    else
                        local normalizedReportedObjectiveAliases = {}
                        for reportedKey, objectiveKey in pairs(entry.reportedObjectiveAliases) do
                            local normalizedReportedObjective = _NormalizeObjectiveLabel(reportedKey)
                            if normalizedReportedObjective and type(objectiveKey) == "string" then
                                normalizedReportedObjectiveAliases[normalizedReportedObjective] = objectiveKey
                            end
                        end

                        entry.reportedObjectiveAliases = next(normalizedReportedObjectiveAliases) and normalizedReportedObjectiveAliases or nil
                    end

                    if type(entry.reportedObjectiveAliases) ~= "table" then
                        entry.reportedObjectiveAliases = nil
                    else
                        local normalizedReportedObjectiveAliases = {}
                        for reportedKey, objectiveKey in pairs(entry.reportedObjectiveAliases) do
                            local normalizedReportedObjective = _NormalizeObjectiveLabel(reportedKey)
                            if normalizedReportedObjective and type(objectiveKey) == "string" then
                                normalizedReportedObjectiveAliases[normalizedReportedObjective] = objectiveKey
                            end
                        end

                        entry.reportedObjectiveAliases = next(normalizedReportedObjectiveAliases) and normalizedReportedObjectiveAliases or nil
                    end

                    if entry.state == "active" and _IsObjectiveProgressCompleteForQuest(questId, entry.objectiveProgress) then
                        entry.state = "completed"
                        entry.inferredComplete = true
                    elseif entry.state == "active" and _IsLootProgressCompleteForQuest(questId, entry.lootProgress) then
                        entry.state = "completed"
                        entry.lootInferredComplete = true
                    elseif entry.state ~= "completed" then
                        entry.inferredComplete = nil
                        entry.lootInferredComplete = nil
                    end

                    if entry.state ~= "available"
                        and entry.state ~= "active"
                        and entry.state ~= "completed"
                    then
                        botEntries[storedQuestId] = nil
                    elseif entry.state == "available" and not entry.starterNpcId then
                        botEntries[storedQuestId] = nil
                    elseif entry.state == "completed"
                        and (not entry.finisherType or not entry.finisherId)
                    then
                        botEntries[storedQuestId] = nil
                    end
                end
            end

            for storedQuestId, entry in pairs(botEntries) do
                local questId = tonumber(storedQuestId)
                if questId and entry and (
                    entry.state == "available"
                    or entry.state == "active"
                    or entry.state == "completed"
                ) then
                    _RemoveCompletedParentStatesFromBotEntries(botEntries, questId)
                end
            end

            if not next(botEntries) then
                cache.bots[botName] = nil
            end
        end
    end
end

local function _IsQuestLinkedToNpcByState(questId, state, npcId)
    if not questId or not state or not npcId then
        return false
    end

    if state == "available" then
        return _GetQuestStartNpcId(questId) == npcId
    elseif state == "active" then
        local starterNpcId = _GetQuestStartNpcId(questId)
        local finisherType, finisherId = _GetQuestFinisherData(questId)
        return starterNpcId == npcId
            or (finisherType == "monster" and finisherId == npcId)
    elseif state == "completed" then
        local finisherType, finisherId, entity = _GetQuestFinisherData(questId)
        return finisherType == "monster" and finisherId == npcId
    end

    return true
end

--------------------------------------------------------------------------------
-- Bot Quest State
--------------------------------------------------------------------------------

local function _SetBotQuestState(botName, questId, state)
    if not botName or not questId then return end

    state = _NormalizeBotQuestState(questId, state)

    local cache = _EnsureUnifiedCache()
    cache.groupSignature = _GetCurrentGroupSignature() or cache.groupSignature
    cache.bots[botName] = cache.bots[botName] or {}

    local previousEntry = cache.bots[botName][questId]
    local previousReportedObjectiveAliases = previousEntry and previousEntry.reportedObjectiveAliases or nil
    local previousReportedQuestNames = previousEntry and previousEntry.reportedQuestNames or nil
    local previousReportedObjectiveAliases = previousEntry and previousEntry.reportedObjectiveAliases or nil
    local previousObjectiveProgress = previousEntry and previousEntry.objectiveProgress or nil
    local previousInferredComplete = previousEntry and previousEntry.inferredComplete or nil
    local previousLootProgress = previousEntry and previousEntry.lootProgress or nil
    local previousLootInferredComplete = previousEntry and previousEntry.lootInferredComplete or nil

    if state == nil or state == "rewarded" then
        cache.bots[botName][questId] = nil
        if not next(cache.bots[botName]) then
            cache.bots[botName] = nil
        end
        if state == "rewarded" then
            --[[_Dbg(
                "STATE bot=%s quest=%s (%s) -> rewarded",
                _SafeName(botName), _SafeName(questId), _GetQuestName(questId)
            )]]--
        end
        return
    end

    local effectiveState = state
    local inferredComplete = previousInferredComplete
    local lootInferredComplete = previousLootInferredComplete

    if effectiveState == "active" and _IsObjectiveProgressCompleteForQuest(questId, previousObjectiveProgress) then
        effectiveState = "completed"
        inferredComplete = true
    elseif effectiveState == "active" and _IsLootProgressCompleteForQuest(questId, previousLootProgress) then
        effectiveState = "completed"
        lootInferredComplete = true
    elseif effectiveState ~= "completed" then
        inferredComplete = nil
        lootInferredComplete = nil
    end

    local finisherType, finisherId = _GetQuestFinisherData(questId)
    cache.bots[botName][questId] = {
        questId              = questId,
        state                = effectiveState,
        starterNpcId         = _GetQuestStartNpcId(questId),
        finisherType         = finisherType,
        finisherId           = finisherId,
        lastSeen             = time(),
        reportedQuestNames   = previousReportedQuestNames,
        reportedObjectiveAliases = previousReportedObjectiveAliases,
        objectiveProgress    = previousObjectiveProgress,
        inferredComplete     = inferredComplete,
        lootProgress         = previousLootProgress,
        lootInferredComplete = lootInferredComplete,
    }

    if effectiveState == "available"
        or effectiveState == "active"
        or effectiveState == "completed"
    then
        _RemoveCompletedParentStatesFromBotEntries(cache.bots[botName], questId)
    end

    if not next(cache.bots[botName]) then
        cache.bots[botName] = nil
    end

    if effectiveState == "active" or effectiveState == "completed" then
        --[[_Dbg(
            "STATE bot=%s quest=%s (%s) -> %s starter=%s finisher=%s:%s",
            _SafeName(botName),
            tostring(questId),
            _GetQuestName(questId),
            _SafeName(effectiveState),
            _SafeName(cache.bots[botName][questId].starterNpcId),
            _SafeName(cache.bots[botName][questId].finisherType),
            _SafeName(cache.bots[botName][questId].finisherId)
        )--]]
    end
end

local function _ClearBotStatesForNpc(botName, npcId)
    local cache      = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then return end

    for questId, entry in pairs(botEntries) do
        if entry then
            if entry.state == "available" and entry.starterNpcId == npcId then
                botEntries[questId] = nil
            end
        end
    end

    if not next(botEntries) then
        cache.bots[botName] = nil
    end
end

--------------------------------------------------------------------------------
-- Map Notes
--------------------------------------------------------------------------------

local function _ClearVisibleBotQuestNotes()
    QuestieMap.manualFrames[AVAILABLE_NOTE_TYPE] = QuestieMap.manualFrames[AVAILABLE_NOTE_TYPE] or {}
    QuestieMap:ResetManualFrames(AVAILABLE_NOTE_TYPE)

    QuestieMap.manualFrames[COMPLETE_NOTE_TYPE] = QuestieMap.manualFrames[COMPLETE_NOTE_TYPE] or {}
    QuestieMap:ResetManualFrames(COMPLETE_NOTE_TYPE)
end

--------------------------------------------------------------------------------
-- Quest Availability Checks
--------------------------------------------------------------------------------

local function _IsQuestActuallyAvailableToPlayer(questId)
    if not questId then return false end
    if Questie.db.char.complete[questId] then return false end

    if QuestiePlayer.currentQuestlog[questId] and QuestieDB.IsComplete(questId) ~= -1 then
        return false
    end

    local playerLevel = QuestiePlayer.GetPlayerLevel()
    local _, requiredLevel, requiredMaxLevel = QuestieLib.GetTbcLevel(questId, playerLevel)

    if requiredLevel and playerLevel < requiredLevel then return false end
    if requiredMaxLevel and requiredMaxLevel ~= 0 and playerLevel > requiredMaxLevel then
        return false
    end

    local parentQuestId = QuestieDB.QueryQuestSingle(questId, "parentQuest")
    if parentQuestId and parentQuestId ~= 0 and QuestiePlayer.currentQuestlog[parentQuestId] then
        return true
    end

    if QuestieDB.activeChildQuests and QuestieDB.activeChildQuests[questId] then
        return true
    end

    return QuestieDB.IsDoable(questId, Questie.db.profile.debugEnabled)
end

local function _IsQuestActuallyCompletableToPlayer(questId)
    if not questId then return false end
    if Questie.db.char.complete[questId] then return false end
    if not QuestiePlayer.currentQuestlog[questId] then return false end

    local isComplete = QuestieDB.IsComplete(questId)
    if isComplete == 1 then return true end

    if isComplete == 0 then
        local quest = QuestieDB.GetQuest(questId)
        if quest and quest.isComplete == true then return true end
    end

    return false
end

--------------------------------------------------------------------------------
-- Tooltip Builder
--------------------------------------------------------------------------------

local function _BuildTooltipBody(titleLine, questIds, botNamesByQuestId)
    local body = { titleLine }
    tsort(questIds)

    for _, questId in ipairs(questIds) do
        local quest     = QuestieDB.GetQuest(questId)
        local botNames  = _CopyStringList(botNamesByQuestId[questId] or {})
        tsort(botNames)
        body[#body + 1] = {
            quest and quest.name or ("Quest " .. questId),
            #botNames > 0 and tconcat(botNames, ", ") or "bot",
        }
    end

    return body
end

--------------------------------------------------------------------------------
-- Note Drawing
--------------------------------------------------------------------------------

local function _DrawSpawns(data, entity, noteType)
    for zone, spawns in pairs(entity.spawns or {}) do
        if zone and spawns then
            for _, coords in ipairs(spawns) do
                local dungeonLocation = ZoneDB:GetDungeonLocation(zone)
                if dungeonLocation then
                    for _, value in ipairs(dungeonLocation) do
                        QuestieMap:DrawManualIcon(data, value[1], value[2], value[3], noteType)
                    end
                else
                    QuestieMap:DrawManualIcon(data, zone, coords[1], coords[2], noteType)
                end
            end
        end
    end
end

local function _ShowAvailableNote(npcId, npc, questIds, botNamesByQuestId)
    local data = {
        id                    = npc.id,
        Icon                  = Questie.ICON_TYPE_AVAILABLE,
        IconColor             = BOT_ICON_COLOR,
        ForceColor            = true,
        IconScale             = 1.2,
        DrawPriority          = 7,
        WorldMapTextureOffsetX = 2,
        WorldMapTextureOffsetY = 0,
        MiniMapTextureOffsetX  = 5,
        MiniMapTextureOffsetY  = 0,
        Type                  = "manual",
        spawnType             = "monster",
        npcData               = npc,
        Name                  = npc.name,
        IsObjectiveNote       = false,
        ManualTooltipData     = {
            Title              = npc.name .. " (bot-only quests)",
            Body               = _BuildTooltipBody(
                "Group bots have additional available quests here.",
                questIds,
                botNamesByQuestId
            ),
            disableShiftToRemove = true,
        },
    }
    data.GetIconScale = function() return data.IconScale end
    _DrawSpawns(data, npc, AVAILABLE_NOTE_TYPE)
end

local function _ShowCompleteNote(noteId, entity, finisherType, questIds, botNamesByQuestId)
    local data = {
        id                    = noteId,
        Icon                  = Questie.ICON_TYPE_COMPLETE,
        IconColor             = BOT_ICON_COLOR,
        ForceColor            = true,
        IconScale             = 1.2,
        DrawPriority          = 7,
        WorldMapTextureOffsetX = 12,
        WorldMapTextureOffsetY = 0,
        MiniMapTextureOffsetX  = 8,
        MiniMapTextureOffsetY  = 0,
        Type                  = "manual",
        spawnType             = finisherType,
        Name                  = entity.name,
        IsObjectiveNote       = false,
        ManualTooltipData     = {
            Title              = entity.name .. " (bot turn-ins)",
            Body               = _BuildTooltipBody(
                "Group bots can turn in additional quests here.",
                questIds,
                botNamesByQuestId
            ),
            disableShiftToRemove = true,
        },
    }

    if finisherType == "monster" then
        data.npcData    = entity
    else
        data.objectData = entity
    end

    data.GetIconScale = function() return data.IconScale end
    --[[_Dbg(
        "DRAW-COMPLETE noteId=%s entityId=%s entity=%s finisherType=%s questCount=%s",
        _SafeName(noteId),
        entity and _SafeName(entity.id) or "nil",
        entity and _SafeName(entity.name) or "nil",
        _SafeName(finisherType),
        tostring(questIds and #questIds or 0)
    )--]]
    _DrawSpawns(data, entity, COMPLETE_NOTE_TYPE)
end

--------------------------------------------------------------------------------
-- Note Rebuild
--------------------------------------------------------------------------------

local function _RebuildVisibleNotesFromCache()
    _ClearVisibleBotQuestNotes()

    local bots               = select(1, _GetCurrentOnlineGroupBotsFromCache())
    local availableByNpc     = {}
    local completeByFinisher = {}

    if not next(bots) then
        return
    end

    for botName, botEntries in pairs(bots) do
        for questId, entry in pairs(botEntries or {}) do
            if entry.state == "available"
                and entry.starterNpcId
                and not _IsQuestActuallyAvailableToPlayer(questId)
            then
                local npcId = entry.starterNpcId
                availableByNpc[npcId] = availableByNpc[npcId] or {
                    questIds          = {},
                    seenQuestIds      = {},
                    botNamesByQuestId = {},
                }
                local bucket = availableByNpc[npcId]
                if not bucket.seenQuestIds[questId] then
                    bucket.seenQuestIds[questId]         = true
                    bucket.questIds[#bucket.questIds + 1] = questId
                end
                bucket.botNamesByQuestId[questId] = bucket.botNamesByQuestId[questId] or {}
                bucket.botNamesByQuestId[questId][#bucket.botNamesByQuestId[questId] + 1] = botName

            elseif entry.state == "completed"
                and entry.finisherType
                and entry.finisherId
                and not _IsQuestActuallyCompletableToPlayer(questId)
            then

                local finisherKey = entry.finisherType .. ":" .. entry.finisherId
                completeByFinisher[finisherKey] = completeByFinisher[finisherKey] or {
                    questIds          = {},
                    seenQuestIds      = {},
                    botNamesByQuestId = {},
                    finisherType      = entry.finisherType,
                    finisherId        = entry.finisherId,
                }
                local bucket = completeByFinisher[finisherKey]
                if not bucket.seenQuestIds[questId] then
                    bucket.seenQuestIds[questId]         = true
                    bucket.questIds[#bucket.questIds + 1] = questId
                end
                bucket.botNamesByQuestId[questId] = bucket.botNamesByQuestId[questId] or {}
                bucket.botNamesByQuestId[questId][#bucket.botNamesByQuestId[questId] + 1] = botName
            end

        end
    end

    for npcId, bucket in pairs(availableByNpc) do
        local npc = QuestieDB:GetNPC(npcId)
        if npc and npc.spawns and #bucket.questIds > 0 then
            _ShowAvailableNote(npcId, npc, bucket.questIds, bucket.botNamesByQuestId)
        end
    end

    for _, bucket in pairs(completeByFinisher) do
        --[[_Dbg(
            "REBUILD-COMPLETE finisherType=%s finisherId=%s questCount=%s",
            _SafeName(bucket.finisherType),
            _SafeName(bucket.finisherId),
            tostring(bucket.questIds and #bucket.questIds or 0)
        )--]]

        local entity, noteId = _GetQuestFinisherEntity(bucket.finisherType, bucket.finisherId)
        if bucket.finisherType and bucket.finisherId and entity and noteId and #bucket.questIds > 0 then
            _ShowCompleteNote(noteId, entity, bucket.finisherType, bucket.questIds, bucket.botNamesByQuestId)
        end
    end
end

local function _ScheduleRestore(delay)
    C_Timer.After(delay or 0, function()
        _RebuildVisibleNotesFromCache()

        local QuestieTracker = QuestieLoader:ImportModule("QuestieTracker")
        if QuestieTracker
            and QuestieTracker.started
            and QuestieTracker.Update
        then
            QuestieTracker:Update()
        end
    end)
end

local function _BuildQuestNameIndex()
    if questNameIndex then
        return questNameIndex
    end

    questNameIndex = {}

    for questId = 1, 40000 do
        local quest = QuestieDB.GetQuest(questId)
        if quest and quest.name then
            questNameIndex[quest.name] = questNameIndex[quest.name] or {}
            questNameIndex[quest.name][#questNameIndex[quest.name] + 1] = questId
        end
    end

    return questNameIndex
end

local function _ResolveQuestIdFromName(questName, preferredNpcId, section, botName)
    if not questName or questName == "" then
        return nil
    end
    local normalizedQuestName = _NormalizeQuestName(questName)

    if preferredNpcId then
        if section == "completed" then
            for _, questId in ipairs(QuestieDB.QueryNPCSingle(preferredNpcId, "questEnds") or {}) do
                if questName == QuestieDB.QueryQuestSingle(questId, "name") then
                    return questId
                end
            end
        else
            for _, questId in ipairs(QuestieDB.QueryNPCSingle(preferredNpcId, "questStarts") or {}) do
                if questName == QuestieDB.QueryQuestSingle(questId, "name") then
                    return questId
                end
            end
            for _, questId in ipairs(QuestieDB.QueryNPCSingle(preferredNpcId, "questEnds") or {}) do
                if questName == QuestieDB.QueryQuestSingle(questId, "name") then
                    return questId
                end
            end
        end
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if botEntries then
        for questId in pairs(botEntries) do
            if questName == QuestieDB.QueryQuestSingle(questId, "name") then
                return questId
            end
        end

        if normalizedQuestName then
            for questId, entry in pairs(botEntries) do
                if entry
                    and entry.reportedQuestNames
                    and entry.reportedQuestNames[normalizedQuestName]
                then
                return questId
				end
            end
        end
    end

    local ids = _BuildQuestNameIndex()[questName]
    if ids and ids[1] then
        _Dbg(
            "RESOLVE questName=%s bot=%s section=%s -> questId=%s (global-name-index)",
            _SafeName(questName),
            _SafeName(botName),
            _SafeName(section),
            _SafeName(ids[1])
        )
        return ids[1]
    end

    _Dbg(
        "RESOLVE questName=%s bot=%s section=%s -> nil",
        _SafeName(questName),
        _SafeName(botName),
        _SafeName(section)
    )

    return nil
end

local function _UpdateBotQuestObjectiveProgress(botName, questId, objectiveKey, currentCount, neededCount)
    if not botName or not questId or not objectiveKey then
        _Dbg(
            "OBJ-UPDATE bot=%s quest=%s key=%s current=%s needed=%s -> no-entry",
            _SafeName(botName),
            _SafeName(questId),
            _SafeName(objectiveKey),
            _SafeName(currentCount),
            _SafeName(neededCount)
        )
        return false
    end

    local cache = _EnsureUnifiedCache()
    cache.groupSignature = _GetCurrentGroupSignature() or cache.groupSignature
    cache.bots[botName] = cache.bots[botName] or {}

    if not cache.bots[botName][questId] then
        _SetBotQuestState(botName, questId, "active")
    end

    local entry = cache.bots[botName] and cache.bots[botName][questId] or nil
    if not entry then
        return false
    end

    entry.objectiveProgress = entry.objectiveProgress or {}

    local progress = entry.objectiveProgress[objectiveKey] or {}
    local previousCurrent = tonumber(progress.current or 0) or 0
    local previousNeeded = tonumber(progress.needed or 0) or 0

    currentCount = tonumber(currentCount or 0) or 0
    neededCount = tonumber(neededCount or 0) or 0

    if currentCount > previousCurrent then
        progress.current = currentCount
    else
        progress.current = previousCurrent > 0 and previousCurrent or nil
    end

    if neededCount > previousNeeded then
        progress.needed = neededCount
    else
        progress.needed = previousNeeded > 0 and previousNeeded or nil
    end

    if progress.current and progress.needed and progress.current >= progress.needed then
        progress.completed = true
    end

    entry.objectiveProgress[objectiveKey] = progress
    entry.lastSeen = time()

    _Dbg(
        "OBJ-UPDATE bot=%s quest=%s (%s) key=%s current=%s needed=%s storedCurrent=%s storedNeeded=%s completed=%s",
        _SafeName(botName),
        _SafeName(questId),
        _GetQuestName(questId),
        _SafeName(objectiveKey),
        _SafeName(currentCount),
        _SafeName(neededCount),
        _SafeName(progress.current),
        _SafeName(progress.needed),
        _SafeName(progress.completed)
    )

    if entry.state == "active" and _IsObjectiveProgressCompleteForQuest(questId, entry.objectiveProgress) then
        entry.inferredComplete = true
        _Dbg(
            "OBJ-COMPLETE bot=%s quest=%s (%s) -> inferred completed",
            _SafeName(botName),
            _SafeName(questId),
            _GetQuestName(questId)
        )
        _SetBotQuestState(botName, questId, "completed")
        return true
    end

    return false
end

local function _HandleObjectiveProgressWhisper(sender, message)
    local objectiveText, currentCount, neededCount, questName = _ParseBotObjectiveProgressMessage(message)
    if not objectiveText or not currentCount or not neededCount or not questName then
        return false
    end

    _Dbg(
        "OBJ-WHISPER sender=%s raw=%s objective=%s current=%s needed=%s quest=%s",
        _SafeName(sender),
        _SafeName(message),
        _SafeName(objectiveText),
        _SafeName(currentCount),
        _SafeName(neededCount),
        _SafeName(questName)
    )

    if not _IsGroupMemberOnline(sender) then
        _Dbg("OBJ-WHISPER sender=%s ignored (not online in current group)", _SafeName(sender))
        return false
    end

    local questId = _ResolveQuestIdFromName(questName, nil, "active", sender)
    if questId and questId ~= 0 then
        local objectiveKey = _FindObjectiveKeyForQuestMessage(questId, objectiveText, sender, neededCount)
        _Dbg(
            "OBJ-MATCH sender=%s quest=%s (%s) objectiveText=%s -> key=%s",
            _SafeName(sender),
            _SafeName(questId),
            _GetQuestName(questId),
            _SafeName(objectiveText),
            _SafeName(objectiveKey)
        )
        if objectiveKey then
            _RememberObjectiveAlias(sender, questId, objectiveKey, objectiveText)
            _UpdateBotQuestObjectiveProgress(sender, questId, objectiveKey, currentCount, neededCount)
            _ScheduleRestore(0)
            return true
        end

        if currentCount >= neededCount then
            _Dbg(
                "OBJ-WHISPER sender=%s quest=%s (%s) objective unresolved but %s/%s reached -> start quests all sync",
                _SafeName(sender),
                _SafeName(questId),
                _GetQuestName(questId),
                _SafeName(currentCount),
                _SafeName(neededCount)
            )
            if (not pendingQuestListSync) or (not pendingQuestListSync.expectedSenders[sender]) then
                _StartQuestListSync({sender}, nil)
            end
            return true
        end
    end

    if currentCount >= neededCount then
        _Dbg(
            "OBJ-WHISPER sender=%s quest unresolved for %s [%s] but %s/%s reached -> start quests all sync",
            _SafeName(sender),
            _SafeName(objectiveText),
            _SafeName(questName),
            _SafeName(currentCount),
            _SafeName(neededCount)
        )
        if (not pendingQuestListSync) or (not pendingQuestListSync.expectedSenders[sender]) then
            _StartQuestListSync({sender}, nil)
        end
        return true
    end

    return false
end

local function _CreateQuestListSnapshot()
    return {
        section          = nil,
        started          = false,
        finished         = false,
        activeQuestIds   = {},
        completedQuestIds = {},
    }
end

local function _ApplyQuestListSnapshot(botName, snapshot)
    if not botName or not snapshot then
        return
    end

    local cache = _EnsureUnifiedCache()
    cache.groupSignature = _GetCurrentGroupSignature() or cache.groupSignature
    cache.bots[botName] = cache.bots[botName] or {}

    local preservedEntries = {}

    for questId, entry in pairs(cache.bots[botName]) do
        if entry and (entry.state == "active" or entry.state == "completed") then
            preservedEntries[tonumber(questId) or questId] = entry
            cache.bots[botName][questId] = nil
        end
    end

    for questId in pairs(snapshot.activeQuestIds or {}) do
        if preservedEntries[questId] then
            cache.bots[botName][questId] = preservedEntries[questId]
        end
        _SetBotQuestState(botName, questId, "active")
    end

    for questId in pairs(snapshot.completedQuestIds or {}) do
        if preservedEntries[questId] then
            cache.bots[botName][questId] = preservedEntries[questId]
        end
        _SetBotQuestState(botName, questId, "completed")
    end

    if not next(cache.bots[botName]) then
        cache.bots[botName] = nil
    end
end


local function _FinalizeQuestListSync(generation)
    if (not pendingQuestListSync) or pendingQuestListSync.generation ~= generation then
        return
    end

    for sender in pairs(pendingQuestListSync.expectedSenders or {}) do
        local snapshot = pendingQuestListSync.snapshotsBySender[sender]
        if snapshot and (snapshot.finished or snapshot.started or next(snapshot.activeQuestIds) or next(snapshot.completedQuestIds)) then
            _ApplyQuestListSnapshot(sender, snapshot)
        end
    end

    pendingQuestListSync = nil
    _ScheduleRestore(0)
end

_StartQuestListSync = function(groupMembers, preferredNpcId)
    groupMembers = groupMembers or _GetGroupMemberNames()
    if not groupMembers or #groupMembers == 0 then
        return
    end

    questListSyncGeneration = questListSyncGeneration + 1
    pendingQuestListSync = {
        generation      = questListSyncGeneration,
        preferredNpcId  = preferredNpcId,
        expectedSenders = {},
        snapshotsBySender = {},
    }

    for _, name in ipairs(groupMembers) do
        pendingQuestListSync.expectedSenders[name] = true
        pendingQuestListSync.snapshotsBySender[name] = _CreateQuestListSnapshot()
        SendChatMessage("quests all", "WHISPER", nil, name)
    end

    local generation = questListSyncGeneration
    C_Timer.After(QUEST_LIST_SYNC_TIMEOUT, function()
        _FinalizeQuestListSync(generation)
    end)
end

_HandleQuestListSyncWhisper = function(sender, message)
    if not pendingQuestListSync or not pendingQuestListSync.expectedSenders[sender] then
        return false
    end

    local snapshot = pendingQuestListSync.snapshotsBySender[sender]
    if not snapshot then
        return false
    end

    local lowerMessage = strlower(message or "")

    if lowerMessage == "quests all" then
        return true
    elseif lowerMessage:find("--- incompleted quests ---", 1, true) then
        snapshot.section = "active"
        snapshot.started = true
        return true
    elseif lowerMessage:find("--- completed quests ---", 1, true) then
        snapshot.section = "completed"
        snapshot.started = true
        return true
    elseif lowerMessage:find("--- summary ---", 1, true) then
        snapshot.section = nil
        return true
    elseif lowerMessage:find("total:", 1, true) then
        snapshot.finished = true
        return true
    end

    if not snapshot.section or message:find("|Hquest:") then
        return false
    end

    local questName = message:match("^%[(.-)%]$")
    if not questName then
        return false
    end

    local questId = _ResolveQuestIdFromName(questName, pendingQuestListSync.preferredNpcId, snapshot.section, sender)
    if not questId or questId == 0 then
        return false
    end

    if snapshot.section == "active" then
        snapshot.activeQuestIds[questId] = true
        snapshot.completedQuestIds[questId] = nil
    elseif snapshot.section == "completed" then
        snapshot.completedQuestIds[questId] = true
        snapshot.activeQuestIds[questId] = nil
    end

    return true
end

--------------------------------------------------------------------------------
-- Whisper / Scan Logic
--------------------------------------------------------------------------------

local function _HasAnyStateToken(lowerMessage, tokens)
    for _, token in ipairs(tokens) do
        if lowerMessage:find(token, 1, true) then
            return true
        end
    end
    return false
end

local function _ClassifyQuestMessage(message)
    if not message or not message:find("|Hquest:") then return nil, nil end

    local questId = tonumber(message:match("|Hquest:(%d+)"))
    if not questId then return nil, nil end

    local lowerMessage = strlower(message)

    if _HasAnyStateToken(lowerMessage, {
        "quest incompleted",
        "quest incomplete",
        "incompleted",
        "incomplete",
        "not completed",
        "not complete",
    }) then
        return questId, "active"
    elseif _HasAnyStateToken(lowerMessage, { "rewarded", "turned in", "turned-in" }) then
        return questId, "rewarded"
    elseif _HasAnyStateToken(lowerMessage, {
        "quest reward pending",
        "reward pending",
        "quest complete",
        "quest completed",
        "ready to turn in",
        "ready for turn in",
        "can turn in",
        "turn in",
    }) then
        return questId, "completed"
    elseif _HasAnyStateToken(lowerMessage, { "accepted", "already on", "in progress", "active" }) then
        return questId, "active"
    elseif _HasAnyStateToken(lowerMessage, { "available" }) then
        return questId, "available"
    end
    return questId, nil
end

local function _FinalizePendingScan(generation)
     if (not pendingScan) or pendingScan.generation ~= generation then return end
 
    for sender, responded in pairs(pendingScan.responders or {}) do
        if responded then
            _ClearBotStatesForNpc(sender, pendingScan.npcId)
 
            for questId, _ in pairs(pendingScan.availableBySender[sender] or {}) do
                if _IsQuestLinkedToNpcByState(questId, "available", pendingScan.npcId) then
                    _SetBotQuestState(sender, questId, "available")
                end
            end
        end
    end
	
    _ScheduleRestore(0)
    pendingScan = nil
end

local function _StartNpcScan(unitToken)
    local npcGuid = QuestieCompat.UnitGUID(unitToken)
    local npcId   = _ExtractNpcIdFromGuid(npcGuid)
    if not npcId then return end

    local npcFlags   = QuestieDB.QueryNPCSingle(npcId, "npcFlags") or 0
    local questStarts = QuestieDB.QueryNPCSingle(npcId, "questStarts")
    local questEnds   = QuestieDB.QueryNPCSingle(npcId, "questEnds")

    local isQuestGiver = (npcFlags % (2 * QuestieDB.npcFlags.QUEST_GIVER)) >= QuestieDB.npcFlags.QUEST_GIVER
    local hasQuests    = (questStarts and #questStarts > 0) or (questEnds and #questEnds > 0)
    if not isQuestGiver and not hasQuests then return end

    --[[_Dbg(
        "SCAN-START npcId=%s",
        _SafeName(npcId)
    )--]]

    local groupMembers = _GetGroupMemberNames()
    if #groupMembers == 0 then return end

    scanGeneration = scanGeneration + 1
    pendingScan = {
        generation         = scanGeneration,
        npcId              = npcId,
        expectedSenders    = {},
        responders         = {},
        availableBySender  = {},
    }

    for _, name in ipairs(groupMembers) do
        pendingScan.expectedSenders[name]   = true
        pendingScan.availableBySender[name] = {}
        SendChatMessage("talk", "WHISPER", nil, name)
    end

    local generation = scanGeneration
    C_Timer.After(BOT_SCAN_TIMEOUT, function()
        _FinalizePendingScan(generation)
    end)
end

local function _OnWhisper(_, message, sender)
    if not message or not sender then return end
    sender = sender:match("^[^-]+") or sender

    if _HandleQuestListSyncWhisper(sender, message) then
        return
    end

    if _HandleObjectiveProgressWhisper(sender, message) then
        return
    end

    local questId, state = _ClassifyQuestMessage(message)
    local reportedQuestName = questId and _ExtractQuestLinkName(message) or nil
    local isPendingSender = pendingScan and pendingScan.expectedSenders[sender]
    local pendingNpcId = isPendingSender and pendingScan.npcId or nil
    local isValidForPendingNpc = true

    if questId and state and pendingNpcId and state == "available" then
        isValidForPendingNpc = _IsQuestLinkedToNpcByState(questId, state, pendingNpcId)
    end

    if isPendingSender then
        pendingScan.responders[sender] = true
        if questId and state == "available" and isValidForPendingNpc then
            pendingScan.availableBySender[sender][questId] = true
        end
    end

    if not questId or not state then return end

    if not _IsGroupMemberOnline(sender) then return end

    if pendingNpcId and state == "available" then
        return
    end

    if state == "rewarded" then
        _SetBotQuestState(sender, questId, "rewarded")
        _ScheduleRestore(0)
    elseif state == "active" or state == "completed" then
        _SetBotQuestState(sender, questId, state)
        _RememberQuestNameAlias(sender, questId, reportedQuestName)
        _ScheduleRestore(0)
    end
end

local function _OnLoot(_, message, _, _, _, playerName)
    local botName, itemId, quantity = _ParseBotLootMessage(message, playerName)
    if not botName or not itemId or not quantity or quantity <= 0 then
        return
    end

    _Dbg(
        "LOOT bot=%s raw=%s itemId=%s quantity=%s",
        _SafeName(botName),
        _SafeName(message),
        _SafeName(itemId),
        _SafeName(quantity)
    )

    if not _IsGroupMemberOnline(botName) then
        _Dbg("LOOT bot=%s ignored (not online in current group)", _SafeName(botName))
        return
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then
        _Dbg("LOOT bot=%s ignored (no cached quest entries)", _SafeName(botName))
        return
    end

    local objectiveKey = "item:" .. tostring(itemId)
    local completedQuestIds = {}
    local hasStateChange = false

    for questId, entry in pairs(botEntries) do
        local numericQuestId = tonumber(questId)
        if numericQuestId and entry and entry.state == "active" then
            local requirements = _GetQuestLootObjectiveRequirements(numericQuestId)
            local requiredCount = requirements.isEligible and requirements.items[itemId] or nil
            if requiredCount then
                _Dbg(
                    "LOOT-MATCH bot=%s quest=%s (%s) item=%s required=%s",
                    _SafeName(botName),
                    _SafeName(numericQuestId),
                    _GetQuestName(numericQuestId),
                    _SafeName(itemId),
                    _SafeName(requiredCount)
                )
                entry.lootProgress = entry.lootProgress or {}
                local currentCount = tonumber(entry.lootProgress[itemId] or 0) or 0
                local newCount = currentCount + quantity
                if newCount > requiredCount then
                    newCount = requiredCount
                end

                if newCount > currentCount then
                    entry.lootProgress[itemId] = newCount
                    entry.lastSeen = time()

                    if _IsLootProgressCompleteForQuest(numericQuestId, entry.lootProgress) then
                        entry.lootInferredComplete = true
                        completedQuestIds[#completedQuestIds + 1] = numericQuestId
                    end
                end
            end

            local objectiveRequirements = _GetQuestObjectiveRequirements(numericQuestId)
            local objectiveEntry = objectiveRequirements.objectives[objectiveKey]
            if objectiveEntry and objectiveEntry.needed and objectiveEntry.needed > 0 then
                _Dbg(
                    "LOOT-OBJ-MATCH bot=%s quest=%s (%s) key=%s needed=%s",
                    _SafeName(botName),
                    _SafeName(numericQuestId),
                    _GetQuestName(numericQuestId),
                    _SafeName(objectiveKey),
                    _SafeName(objectiveEntry.needed)
                )
                local currentObjectiveCount = 0
                if entry.objectiveProgress and entry.objectiveProgress[objectiveKey] then
                    currentObjectiveCount = tonumber(entry.objectiveProgress[objectiveKey].current or 0) or 0
                end

                local newObjectiveCount = currentObjectiveCount + quantity
                if newObjectiveCount > objectiveEntry.needed then
                    newObjectiveCount = objectiveEntry.needed
                end

                if _UpdateBotQuestObjectiveProgress(botName, numericQuestId, objectiveKey, newObjectiveCount, objectiveEntry.needed) then
                    hasStateChange = true
                end
            end
        end
    end

    for _, questId in ipairs(completedQuestIds) do
        --[[_Dbg(
            "LOOT-COMPLETE bot=%s quest=%s (%s) item=%s amount=%s",
            _SafeName(botName),
            tostring(questId),
            _GetQuestName(questId),
            tostring(itemId),
            tostring(quantity)
        )--]]
        _SetBotQuestState(botName, questId, "completed")
        hasStateChange = true
    end

    if hasStateChange then
        _ScheduleRestore(0)
    end
end

local function _GetBotQuestEntry(botName, questId)
    if not botName or not questId then
        return nil
    end

    local cache = _EnsureUnifiedCache()
    local botEntries = cache.bots[botName]
    if not botEntries then
        return nil
    end

    return botEntries[questId] or botEntries[tostring(questId)]
end

local function _InferSiblingObjectiveNeededCount(entry, requirements, objectiveKey)
    if not entry or not requirements or not objectiveKey then
        return 0
    end

    local targetObjective = requirements.objectives and requirements.objectives[objectiveKey]
    if not targetObjective then
        return 0
    end

    local inferredNeeded = nil

    for _, siblingObjectiveKey in ipairs(requirements.orderedKeys or {}) do
        if siblingObjectiveKey ~= objectiveKey then
            local siblingObjective = requirements.objectives[siblingObjectiveKey]
            if siblingObjective and siblingObjective.type == targetObjective.type then
                local siblingProgress = entry.objectiveProgress and entry.objectiveProgress[siblingObjectiveKey] or nil
                local siblingNeeded = tonumber(siblingProgress and siblingProgress.needed or siblingObjective.needed or 0) or 0

                if siblingNeeded > 0 then
                    if not inferredNeeded then
                        inferredNeeded = siblingNeeded
                    elseif inferredNeeded ~= siblingNeeded then
                        return 0
                    end
                end
            end
        end
    end

    return inferredNeeded or 0
end

local function _BuildBotQuestProgressLinesFromEntry(entry)
    if not entry or not entry.questId or entry.state == "completed" then
        if entry and entry.questId then
            _Dbg(
                "TRACKER-LINES quest=%s (%s) state=%s -> none",
                _SafeName(entry.questId),
                _GetQuestName(entry.questId),
                _SafeName(entry.state)
            )
        end
        return nil
    end

    local requirements = _GetQuestObjectiveRequirements(entry.questId)
    if not requirements or not requirements.orderedKeys or #requirements.orderedKeys == 0 then
        _Dbg(
            "TRACKER-LINES quest=%s (%s) -> no requirements/orderedKeys",
            _SafeName(entry.questId),
            _GetQuestName(entry.questId)
        )
        return nil
    end

    local playerObjectiveTemplate = _GetPlayerQuestObjectiveTemplate(entry.questId)
    if playerObjectiveTemplate and #playerObjectiveTemplate > 0 then
        local progressLines = {}

        for objectiveIndex, templateEntry in ipairs(playerObjectiveTemplate) do
            local objectiveKey = requirements.orderedKeys and requirements.orderedKeys[objectiveIndex] or nil
            local objectiveEntry = objectiveKey and requirements.objectives[objectiveKey] or nil
            local progress = objectiveKey and entry.objectiveProgress and entry.objectiveProgress[objectiveKey] or nil

            local currentCount = tonumber(progress and progress.current or 0) or 0
            local neededCount = tonumber(
                templateEntry.needed
                or (progress and progress.needed)
                or (objectiveEntry and objectiveEntry.needed)
                or 0
            ) or 0

            if neededCount <= 0 and objectiveKey then
                local inferredNeededCount = _InferSiblingObjectiveNeededCount(entry, requirements, objectiveKey)
                if inferredNeededCount > 0 then
                    neededCount = inferredNeededCount
                end
            end

            if currentCount > 0 or neededCount > 0 then
                local displayName = templateEntry.displayName
                    or (objectiveEntry and objectiveEntry.displayName)
                    or objectiveKey
                    or ("Objective " .. tostring(objectiveIndex))

                progressLines[#progressLines + 1] = displayName .. ": " .. tostring(currentCount) .. "/" .. tostring(neededCount)
            end
        end

        if #progressLines > 0 then
            _Dbg(
                "TRACKER-LINES quest=%s (%s) -> %s line(s) (player-template)",
                _SafeName(entry.questId),
                _GetQuestName(entry.questId),
                _SafeName(#progressLines)
            )
            return progressLines
        end
    end

    local progressLines = {}

    for _, objectiveKey in ipairs(requirements.orderedKeys) do
        local objectiveEntry = requirements.objectives[objectiveKey]
        if objectiveEntry then
            local progress = entry.objectiveProgress and entry.objectiveProgress[objectiveKey] or nil
            local currentCount = tonumber(progress and progress.current or 0) or 0
            local neededCount = tonumber(progress and progress.needed or objectiveEntry.needed or 0) or 0

            if neededCount <= 0 then
                local inferredNeededCount = _InferSiblingObjectiveNeededCount(entry, requirements, objectiveKey)
                if inferredNeededCount > 0 then
                    neededCount = inferredNeededCount
                    _Dbg(
                        "TRACKER-LINE-FALLBACK quest=%s (%s) key=%s inferredNeeded=%s from sibling objective",
                        _SafeName(entry.questId),
                        _GetQuestName(entry.questId),
                        _SafeName(objectiveKey),
                        _SafeName(inferredNeededCount)
                    )
                end
            end

            if currentCount > 0 or neededCount > 0 then
                local displayName = objectiveEntry.displayName or objectiveKey
                _Dbg(
                    "TRACKER-LINE quest=%s (%s) key=%s display=%s current=%s needed=%s",
                    _SafeName(entry.questId),
                    _GetQuestName(entry.questId),
                    _SafeName(objectiveKey),
                    _SafeName(displayName),
                    _SafeName(currentCount),
                    _SafeName(neededCount)
                )
                progressLines[#progressLines + 1] = displayName .. ": " .. tostring(currentCount) .. "/" .. tostring(neededCount)
            end
        end
    end

    if #progressLines == 0 then
        _Dbg(
            "TRACKER-LINES quest=%s (%s) -> built 0 lines",
            _SafeName(entry.questId),
            _GetQuestName(entry.questId)
        )
        return nil
    end

    _Dbg(
        "TRACKER-LINES quest=%s (%s) -> %s line(s)",
        _SafeName(entry.questId),
        _GetQuestName(entry.questId),
        _SafeName(#progressLines)
    )

    return progressLines
end

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

function QuestiePlayerbots:Initialize()
    _EnsureUnifiedCache()

    eventFrame:SetScript("OnEvent", function(_, event, ...)
        if event == "CHAT_MSG_WHISPER" then
            _OnWhisper(event, ...)
        elseif event == "CHAT_MSG_LOOT" then
            _OnLoot(event, ...)
        elseif event == "GOSSIP_SHOW" then
            _StartNpcScan("npc")
        elseif event == "QUEST_GREETING" then
            _StartNpcScan("npc")
        elseif event == "PLAYER_ENTERING_WORLD" then
            _ScheduleRestore(1.0)
        elseif event == "GROUP_ROSTER_UPDATE"
            or event == "PARTY_MEMBERS_CHANGED"
            or event == "RAID_ROSTER_UPDATE"
        then
            _ScheduleRestore(0.2)
        end
    end)

    eventFrame:RegisterEvent("CHAT_MSG_WHISPER")
    eventFrame:RegisterEvent("CHAT_MSG_LOOT")
    eventFrame:RegisterEvent("GOSSIP_SHOW")
    eventFrame:RegisterEvent("QUEST_GREETING")
    eventFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
    eventFrame:RegisterEvent("GROUP_ROSTER_UPDATE")
    eventFrame:RegisterEvent("PARTY_MEMBERS_CHANGED")
    eventFrame:RegisterEvent("RAID_ROSTER_UPDATE")

    _ScheduleRestore(0.5)
end

function QuestiePlayerbots:GetCurrentGroupOnlineQuestStateCache()
    return _GetCurrentOnlineGroupBotsFromCache()
end

function QuestiePlayerbots:GetArchivedQuestStateCache()
    return _GetArchivedBotsFromCache()
end

function QuestiePlayerbots:GetPersistentAvailableCache()
    local cache   = _EnsureUnifiedCache()
    local entries = {}

    for botName, botEntries in pairs(cache.bots or {}) do
        for questId, entry in pairs(botEntries or {}) do
            if entry.state == "available" and entry.starterNpcId then
                local npcId = entry.starterNpcId
                entries[npcId] = entries[npcId] or {
                    npcId             = npcId,
                    npcName           = QuestieDB.QueryNPCSingle(npcId, "name"),
                    botOnlyQuestIds   = {},
                    botNamesByQuestId = {},
                    lastSeen          = entry.lastSeen or time(),
                    seenQuestIds      = {},
                }
                local e = entries[npcId]
                if not e.seenQuestIds[questId] then
                    e.seenQuestIds[questId]               = true
                    e.botOnlyQuestIds[#e.botOnlyQuestIds + 1] = questId
                end
                e.botNamesByQuestId[questId] = e.botNamesByQuestId[questId] or {}
                e.botNamesByQuestId[questId][#e.botNamesByQuestId[questId] + 1] = botName
                e.lastSeen = math.max(e.lastSeen or 0, entry.lastSeen or 0)
            end
        end
    end

    for _, entry in pairs(entries) do
        entry.seenQuestIds = nil
    end

    return entries, cache.groupSignature
end

function QuestiePlayerbots:GetPersistentQuestStateCache()
    local cache = _EnsureUnifiedCache()
    return cache.bots or {}, cache.groupSignature
end


function QuestiePlayerbots:GetBotQuestProgressLines(botName, questId)
    local entry = _GetBotQuestEntry(botName, questId)
    if not entry then
        return nil
    end

    return _BuildBotQuestProgressLinesFromEntry(entry)
end

return QuestiePlayerbots