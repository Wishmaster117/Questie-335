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

-- State
local pendingScan
local scanGeneration = 0
local pendingQuestListSync
local questListSyncGeneration = 0
local questNameIndex

-- Upvalues
local ipairs   = ipairs
local pairs    = pairs
local tconcat  = table.concat
local tsort    = table.sort
local tonumber = tonumber
local strsplit = strsplit
local strlower = string.lower
local format   = string.format
local tostring = tostring
local time     = time

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

    if IsInRaid() then
        for i = 1, (GetNumRaidMembers() or 0) do
            local name = UnitName("raid" .. i)
            if name and name ~= playerName then
                names[#names + 1] = name
            end
        end
    elseif GetNumPartyMembers and GetNumPartyMembers() > 0 then
        for i = 1, GetNumPartyMembers() do
            local name = UnitName("party" .. i)
            if name and name ~= playerName then
                names[#names + 1] = name
            end
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

--------------------------------------------------------------------------------
-- Cache Management
--------------------------------------------------------------------------------

local function _EnsureUnifiedCache()
 local cache = Questie.db.char.playerbotsQuestStateCache

 if not cache or type(cache) ~= "table" then
     cache = {
         version        = 3,
         groupSignature = nil,
         bots           = {},
     }
 else
     cache.version = 3
     cache.bots    = cache.bots or {}
 end

 Questie.db.char.playerbotsQuestStateCache = cache

 if _NormalizeUnifiedCache then
     _NormalizeUnifiedCache(cache)
 end

 return cache
end

local function _CopyStringList(values)
    local copy = {}
    for _, value in ipairs(values or {}) do
        copy[#copy + 1] = value
    end
    return copy
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

    if state == nil or state == "rewarded" then
        cache.bots[botName][questId] = nil
        if not next(cache.bots[botName]) then
            cache.bots[botName] = nil
        end
        if state == "rewarded" then
            _Dbg(
                "STATE bot=%s quest=%s (%s) -> rewarded",
                _SafeName(botName), _SafeName(questId), _GetQuestName(questId)
            )
        end
        return
    end

    local finisherType, finisherId = _GetQuestFinisherData(questId)
    cache.bots[botName][questId] = {
        questId      = questId,
        state        = state,
        starterNpcId = _GetQuestStartNpcId(questId),
        finisherType = finisherType,
        finisherId   = finisherId,
        lastSeen     = time(),
    }

    if state == "available"
        or state == "active"
        or state == "completed"
    then
        _RemoveCompletedParentStatesFromBotEntries(cache.bots[botName], questId)
    end

    if not next(cache.bots[botName]) then
        cache.bots[botName] = nil
    end

    if state == "active" or state == "completed" then
        _Dbg(
            "STATE bot=%s quest=%s (%s) -> %s starter=%s finisher=%s:%s",
            _SafeName(botName),
            tostring(questId),
            _GetQuestName(questId),
            _SafeName(state),
            _SafeName(cache.bots[botName][questId].starterNpcId),
            _SafeName(cache.bots[botName][questId].finisherType),
            _SafeName(cache.bots[botName][questId].finisherId)
        )
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
    _Dbg(
        "DRAW-COMPLETE noteId=%s entityId=%s entity=%s finisherType=%s questCount=%s",
        _SafeName(noteId),
        entity and _SafeName(entity.id) or "nil",
        entity and _SafeName(entity.name) or "nil",
        _SafeName(finisherType),
        tostring(questIds and #questIds or 0)
    )
    _DrawSpawns(data, entity, COMPLETE_NOTE_TYPE)
end

--------------------------------------------------------------------------------
-- Note Rebuild
--------------------------------------------------------------------------------

local function _RebuildVisibleNotesFromCache()
    _ClearVisibleBotQuestNotes()

    local cache             = _EnsureUnifiedCache()
    local availableByNpc    = {}
    local completeByFinisher = {}

    for botName, botEntries in pairs(cache.bots or {}) do
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
        _Dbg(
            "REBUILD-COMPLETE finisherType=%s finisherId=%s questCount=%s",
            _SafeName(bucket.finisherType),
            _SafeName(bucket.finisherId),
            tostring(bucket.questIds and #bucket.questIds or 0)
        )

        local entity, noteId = _GetQuestFinisherEntity(bucket.finisherType, bucket.finisherId)
        if bucket.finisherType and bucket.finisherId and entity and noteId and #bucket.questIds > 0 then
            _ShowCompleteNote(noteId, entity, bucket.finisherType, bucket.questIds, bucket.botNamesByQuestId)
        end
    end
end

local function _ScheduleRestore(delay)
    C_Timer.After(delay or 0, function()
        _RebuildVisibleNotesFromCache()
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
    end

    local ids = _BuildQuestNameIndex()[questName]
    if ids and ids[1] then
        return ids[1]
    end

    return nil
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

    for questId, entry in pairs(cache.bots[botName]) do
        if entry and (entry.state == "active" or entry.state == "completed") then
            cache.bots[botName][questId] = nil
        end
    end

    for questId in pairs(snapshot.activeQuestIds or {}) do
        _SetBotQuestState(botName, questId, "active")
    end

    for questId in pairs(snapshot.completedQuestIds or {}) do
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

local function _StartQuestListSync(groupMembers, preferredNpcId)
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

local function _HandleQuestListSyncWhisper(sender, message)
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

    _Dbg(
        "SCAN-START npcId=%s",
        _SafeName(npcId)
    )

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

    local questId, state = _ClassifyQuestMessage(message)
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

    local isGroupMember = false
    for _, name in ipairs(_GetGroupMemberNames()) do
        if name == sender then
            isGroupMember = true
            break
        end
    end
    if not isGroupMember then return end

    if pendingNpcId and state == "available" then
        return
    end

    if state == "rewarded" then
        _SetBotQuestState(sender, questId, "rewarded")
        _ScheduleRestore(0)
    elseif state == "active" or state == "completed" then
        _SetBotQuestState(sender, questId, state)
        _ScheduleRestore(0)
    end
end

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

function QuestiePlayerbots:Initialize()
    _EnsureUnifiedCache()

    eventFrame:SetScript("OnEvent", function(_, event, ...)
        if event == "CHAT_MSG_WHISPER" then
            _OnWhisper(event, ...)
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
    eventFrame:RegisterEvent("GOSSIP_SHOW")
    eventFrame:RegisterEvent("QUEST_GREETING")
    eventFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
    eventFrame:RegisterEvent("GROUP_ROSTER_UPDATE")
    eventFrame:RegisterEvent("PARTY_MEMBERS_CHANGED")
    eventFrame:RegisterEvent("RAID_ROSTER_UPDATE")

    _ScheduleRestore(0.5)
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

return QuestiePlayerbots