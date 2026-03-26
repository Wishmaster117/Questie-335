---@type QuestieJourney
local QuestieJourney  = QuestieLoader:CreateModule("QuestieJourney")
local _QuestieJourney = QuestieJourney.private

_QuestieJourney.botQuests = _QuestieJourney.botQuests or {}

---@type QuestieJourneyUtils
local QuestieJourneyUtils = QuestieLoader:ImportModule("QuestieJourneyUtils")
---@type QuestieDB
local QuestieDB           = QuestieLoader:ImportModule("QuestieDB")
---@type QuestiePlayerbots
local QuestiePlayerbots   = QuestieLoader:ImportModule("QuestiePlayerbots")
---@type l10n
local l10n                = QuestieLoader:ImportModule("l10n")

local AceGUI = LibStub("AceGUI-3.0")

-- Upvalues
local pairs   = pairs
local ipairs  = ipairs
local tsort   = table.sort
local tconcat = table.concat
local date    = date
local time    = time

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

local function _AddEntryToStateBucket(bucket, entry, botName, questId)
    if not bucket[questId] then
        bucket[questId] = {
            questId      = questId,
            botNames     = {},
            lastSeen     = entry.lastSeen or time(),
            starterNpcId = entry.starterNpcId,
            finisherType = entry.finisherType,
            finisherId   = entry.finisherId,
        }
    end

    local e = bucket[questId]
    e.botNames[#e.botNames + 1] = botName
    e.lastSeen = math.max(e.lastSeen or 0, entry.lastSeen or 0)
end

local function _FlattenBucket(bucket)
    local list = {}

    for _, entry in pairs(bucket) do
        tsort(entry.botNames)
        list[#list + 1] = entry
    end

    tsort(list, function(a, b)
        return (a.lastSeen or 0) > (b.lastSeen or 0)
    end)

    return list
end

--------------------------------------------------------------------------------
-- Tab Drawing
--------------------------------------------------------------------------------

function _QuestieJourney.botQuests:DrawTab(container)

    -- Header
    local header = AceGUI:Create("Heading")
    header:SetText(l10n('Cached Bot Quests'))
    header:SetFullWidth(true)
    container:AddChild(header)

    QuestieJourneyUtils:Spacer(container)

    -- Group signature info
    local bots, groupSignature = QuestiePlayerbots:GetPersistentQuestStateCache()

    local info = AceGUI:Create("Label")
    info:SetFullWidth(true)

    if groupSignature then
        info:SetText(
            Questie:Colorize(l10n('Cached group: '), 'yellow') ..
            Questie:Colorize(groupSignature:gsub('|', ', '), 'gray')
        )
    else
        info:SetText(
            Questie:Colorize(l10n('No persistent bot quest cache for the current group yet.'), 'yellow')
        )
    end

    container:AddChild(info)
    QuestieJourneyUtils:Spacer(container)

    -- Scroll frame
    local scrollFrame = AceGUI:Create("ScrollFrame")
    scrollFrame:SetLayout("Flow")
    scrollFrame:SetFullWidth(true)
    scrollFrame:SetFullHeight(true)
    container:AddChild(scrollFrame)

    -- Sort entries by state
    local availableBucket = {}
    local activeBucket    = {}
    local completedBucket = {}

    for botName, botEntries in pairs(bots or {}) do
        for questId, entry in pairs(botEntries or {}) do
            if entry.state == "available" then
                _AddEntryToStateBucket(availableBucket, entry, botName, questId)
            elseif entry.state == "active" then
                _AddEntryToStateBucket(activeBucket, entry, botName, questId)
            elseif entry.state == "completed" then
                _AddEntryToStateBucket(completedBucket, entry, botName, questId)
            end
        end
    end

    local availableEntries = _FlattenBucket(availableBucket)
    local activeEntries    = _FlattenBucket(activeBucket)
    local completedEntries = _FlattenBucket(completedBucket)

    -- Empty state
    if #availableEntries == 0 and #activeEntries == 0 and #completedEntries == 0 then
        local empty = AceGUI:Create("Label")
        empty:SetFullWidth(true)
        empty:SetText(
            Questie:Colorize(
                l10n('No cached bot quests yet. Scan a quest giver once with your bots in group.'),
                'yellow'
            )
        )
        scrollFrame:AddChild(empty)
        return
    end

    -- Section renderer
    local function DrawSection(titleText, entries, color)
        if #entries == 0 then return end

        local heading = AceGUI:Create("Heading")
        heading:SetText(titleText)
        heading:SetFullWidth(true)
        scrollFrame:AddChild(heading)

        for _, entry in ipairs(entries) do
            local questName = QuestieDB.QueryQuestSingle(entry.questId, "name")
                or ("Quest " .. tostring(entry.questId))

            -- Quest name + bot names
            local line = AceGUI:Create("Label")
            line:SetFullWidth(true)
            line:SetText(
                " • " ..
                Questie:Colorize(questName, color) ..
                " " ..
                Questie:Colorize("(" .. tconcat(entry.botNames, ", ") .. ")", 'gray')
            )
            scrollFrame:AddChild(line)

            -- Meta information
            local metaParts = {}

            if entry.starterNpcId then
                metaParts[#metaParts + 1] =
                    l10n('Starter: ') ..
                    (QuestieDB.QueryNPCSingle(entry.starterNpcId, "name")
                        or ("NPC " .. tostring(entry.starterNpcId)))
            end

            if entry.finisherType == "monster" and entry.finisherId then
                metaParts[#metaParts + 1] =
                    l10n('Finisher: ') ..
                    (QuestieDB.QueryNPCSingle(entry.finisherId, "name")
                        or ("NPC " .. tostring(entry.finisherId)))

            elseif entry.finisherType == "object" and entry.finisherId then
                metaParts[#metaParts + 1] =
                    l10n('Finisher: ') ..
                    (QuestieDB.QueryObjectSingle(entry.finisherId, "name")
                        or ("Object " .. tostring(entry.finisherId)))
            end

            metaParts[#metaParts + 1] =
                l10n('Last seen: ') ..
                date('%Y-%m-%d %H:%M:%S', entry.lastSeen or time())

            local meta = AceGUI:Create("Label")
            meta:SetFullWidth(true)
            meta:SetText(
                "   " .. Questie:Colorize(tconcat(metaParts, "  "), 'gray')
            )
            scrollFrame:AddChild(meta)

            QuestieJourneyUtils:Spacer(scrollFrame)
        end
    end

    -- Draw all three sections
    DrawSection(l10n('Available'),   availableEntries, 'yellow')
    DrawSection(l10n('In Progress'), activeEntries,    'white')
    DrawSection(l10n('Completed'),   completedEntries, 'green')
end