-- ═══════════════════════════════════════════════════════════════════
--  King Legacy Boss Detector + Hydra Hunter v23
--  Sea 2 | Delta Executor (Android)
--
--  UPGRADE dari v20:
--  ✓ Adaptive Cycle (67min realistic, bukan fixed 63min)
--  ✓ Watch List System (simpan server, kembali saat mendekati spawn)
--  ✓ Smart Join Threshold (skip jika TTB > 10min, save ke watch)
--  ✓ Hydra Priority Boost (Hydra server dipromosikan lebih agresif)
--  ✓ Server Full Detection (auto-skip server penuh)
--  ✓ Faster Re-scan (scan lebih sering saat hunting)
--  ✓ Better scoring algorithm
--
--  Flow:
--    1. SCAN: Fetch servers via Network API
--    2. ANALYZE: Calculate adaptive cycle/TTB per server
--    3. QUEUE: Sort & build queue (Hydra priority) + Watch List
--    4. JOIN: Teleport when TTB <= 10min (atau langsung utk Hydra)
--    5. VERIFY: Read in-game timers (SKTimeLabel + HDImage)
--    6. DECIDE: Boss alive → FIGHT | HD cycle + close → WAIT | else → HOP
--    7. FIGHT: Position lock (Heartbeat CFrame) + SkillAction
--    8. CHEST: Auto teleport → chest after boss dies
--    9. STORE: Auto store fruit via VIM
--   10. WATCH: Check watch list, promote servers yang siap
--   11. HOP: Next server in queue, re-scan periodically
--
--  Adaptive Boss Cycle:
--    Timer countdown: 60 min (3600s)
--    Average kill time: ~2 min (120s)
--    Island despawn timer: 5 min (300s)
--    Effective cycle: ~67 min (4020s)
--    Pattern: SK1 → SK2 → SK3 → HYDRA (every 4th = Hydra)
--    SK1 at ~60min, SK2 at ~127min, SK3 at ~194min, HYDRA at ~261min
-- ═══════════════════════════════════════════════════════════════════

local Players = game:GetService("Players")
local TeleportService = game:GetService("TeleportService")
local HttpService = game:GetService("HttpService")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local RunService = game:GetService("RunService")
local lp = Players.LocalPlayer
local PlaceID = game.PlaceId
if PlaceID == 0 then PlaceID = 15325001391 end

-- ─── Adaptive Cycle Constants ───────────────────────────────────
local TIMER_DURATION  = 3600
local KILL_EST        = 120
local DESPAWN_TIME    = 300
local EFFECTIVE_CYCLE = TIMER_DURATION + KILL_EST + DESPAWN_TIME
local FIRST_SPAWN     = TIMER_DURATION

-- ─── Hunting Thresholds ─────────────────────────────────────────
local MIN_JOIN_TTB    = 600
local HYDRA_JOIN_TTB  = 900
local MAX_WAIT_HD     = 360
local MAX_WAIT_SK     = 30
local JOIN_EARLY_SEC  = 300
local RESCAN_INTERVAL = 120
local WATCH_RECHECK   = 45
local MAX_QUEUE       = 10
local MAX_WATCH       = 40
local WATCH_EXPIRY    = 3600
local SAFETY_MARGIN   = 60
local ARRIVAL_GRACE   = 12

-- ─── File Paths ─────────────────────────────────────────────────
local CONFIG_FILE  = "BossDetectorConfig.json"
local VISITED_FILE = "NotSameServers.json"
local MEMORY_FILE  = "HunterMemory.json"
local WATCH_FILE   = "BDWatchList.json"
local STATUS_FILE  = "BDStatusMsgId.json"
local EXECCOUNT_FILE = "BDExecCount.txt"

-- ─── Game Data ──────────────────────────────────────────────────
local BOSS_NAMES   = { "HydraSeaKing", "SeaKing" }
local SWORD_NAMES  = { "Kioru V2", "KioruV2", "Kioru" }
local ISLAND_ANCHORS = { "HydraStand", "ClockTime" }
local CHEST_NAMES  = {
    "ChestSpawner", "Top", "Buttom",
    "SkullRetopo", "EyeRight", "EyeLeft",
    "ChestTop", "ChestBottum", "Dragon", "Wing",
}

local CHEST_SET = {}
for _, nm in ipairs(CHEST_NAMES) do CHEST_SET[nm] = true end
local ANCHOR_SET = {}
for _, an in ipairs(ISLAND_ANCHORS) do ANCHOR_SET[an] = true end

local WEBHOOKS = {
    HydraSeaKing = "",
    SeaKing      = "",
    Chest        = "",
    Status       = "https://discord.com/api/webhooks/1487739256519528498/ucU6Kh6YKXaXryEf1OQPzZSPbyujCczAUOR33b89RZRbeVHncOssPQSCnYiGQXTdYPQX",
}

local COL = {
    bg      = Color3.fromRGB(12, 12, 24),
    bgCard  = Color3.fromRGB(20, 20, 38),
    accent  = Color3.fromRGB(88, 140, 255),
    green   = Color3.fromRGB(50, 205, 120),
    red     = Color3.fromRGB(220, 55, 55),
    orange  = Color3.fromRGB(255, 180, 50),
    gold    = Color3.fromRGB(255, 195, 55),
    purple  = Color3.fromRGB(130, 80, 210),
    hydra   = Color3.fromRGB(200, 100, 255),
    text    = Color3.fromRGB(200, 200, 215),
    textSub = Color3.fromRGB(90, 90, 120),
    white   = Color3.fromRGB(255, 255, 255),
    cyan    = Color3.fromRGB(80, 200, 220),
}

-- ─── State ──────────────────────────────────────────────────────
local isRunning       = false
local isFighting      = false
local isPostFight     = false
local isTeleporting   = false
local isScanning      = false

local autoHunt        = true
local autoFight       = true
local autoStore       = false
local hydraOnly       = true
local guiPanel        = nil

local visitedServers  = {}
local serverMemory    = {}
local serverQueue     = {}
local watchList       = {}
local fightPlatform   = nil
local posLockConn     = nil
local foundCode       = nil
local statusLockUntil = 0
local lastScanTime    = 0
local lastWatchCheck  = 0
local totalHops       = 0
local totalScans      = 0
local totalPromoted   = 0
local logLines        = {}
local notifiedJobs    = {}
local notifiedChestJobs = {}
local serverJoinedAt  = tick()
local hopFailCount    = 0

local statStartTime   = tick()
local statSKKills     = 0
local statHDKills     = 0
local statFruits      = 0
local statChests      = 0
local statusMsgId     = nil

local execCount = 1
pcall(function()
    local raw = readfile(EXECCOUNT_FILE)
    if raw and raw ~= "" then execCount = (tonumber(raw) or 0) + 1 end
end)
pcall(function() writefile(EXECCOUNT_FILE, tostring(execCount)) end)

local executorName = "Unknown"
pcall(function()
    if identifyexecutor then
        local name, ver = identifyexecutor()
        executorName = (name or "?") .. " " .. (ver or "")
    end
end)

local Network = nil
pcall(function()
    Network = require(
        ReplicatedStorage:WaitForChild("Chest", 10)
        :WaitForChild("Assets", 5)
        :WaitForChild("Modules", 5)
        :WaitForChild("Network", 5)
    )
end)

local setStatus, setChestStatus, setQueueInfo, setWatchInfo, addLog

-- ─── Event-Driven Registries ────────────────────────────────────
local bossRegistry   = {}
local chestRegistry  = {}
local anchorRegistry = {}

local function isChestValid(obj)
    local parentPath = ""
    pcall(function() parentPath = obj.Parent and obj.Parent:GetFullName() or "" end)
    if parentPath:find("Monster") or parentPath:find("Boss") then return false end
    return true
end

local function tryRegister(obj)
    if obj:IsA("Model") then
        for _, bn in ipairs(BOSS_NAMES) do
            if obj.Name == bn then bossRegistry[obj] = bn; return end
        end
    end
    if obj:IsA("BasePart") then
        if CHEST_SET[obj.Name] and isChestValid(obj) then chestRegistry[obj] = true end
        if ANCHOR_SET[obj.Name] then anchorRegistry[obj] = obj.Name end
    end
    if obj:IsA("Model") and CHEST_SET[obj.Name] and isChestValid(obj) then
        chestRegistry[obj] = true
    end
end

for _, obj in ipairs(workspace:GetDescendants()) do tryRegister(obj) end
workspace.DescendantAdded:Connect(tryRegister)
workspace.DescendantRemoving:Connect(function(obj)
    bossRegistry[obj] = nil
    chestRegistry[obj] = nil
    anchorRegistry[obj] = nil
end)

-- ─── Helpers ────────────────────────────────────────────────────
local function getHRP()
    local c = lp.Character
    return c and c:FindFirstChild("HumanoidRootPart")
end

local function getHumanoid()
    local c = lp.Character
    return c and c:FindFirstChildOfClass("Humanoid")
end

local function isCharLoaded()
    local c = lp.Character
    return c and c:FindFirstChild("HumanoidRootPart") ~= nil
end

local function fmt(sec)
    if not sec or sec < 0 then return "--:--" end
    sec = math.floor(sec)
    local m = math.floor(sec / 60)
    local s = sec % 60
    return string.format("%02d:%02d", m, s)
end

local function fmtLong(sec)
    if not sec or sec < 0 then return "--:--" end
    sec = math.floor(sec)
    local h = math.floor(sec / 3600)
    local m = math.floor((sec % 3600) / 60)
    local s = sec % 60
    if h > 0 then return string.format("%d:%02d:%02d", h, m, s) end
    return string.format("%02d:%02d", m, s)
end

local function fmtDuration(sec)
    local h = math.floor(sec / 3600)
    local m = math.floor((sec % 3600) / 60)
    if h > 0 then return h .. "h " .. m .. "m" end
    return m .. "m"
end

local function log(msg)
    local line = os.date("%H:%M:%S") .. " " .. msg
    table.insert(logLines, line)
    if #logLines > 200 then table.remove(logLines, 1) end
    print("[v23] " .. line)
    pcall(function() addLog() end)
end

-- ─── Config ─────────────────────────────────────────────────────
local _configLoaded = false

local CONFIG_VERSION = 23

local function loadConfig()
    local ok, err = pcall(function()
        local raw = readfile(CONFIG_FILE)
        if raw and raw ~= "" then
            local d = HttpService:JSONDecode(raw)
            if type(d) == "table" then
                if d.version == CONFIG_VERSION then
                    if d.autoHunt ~= nil then autoHunt = d.autoHunt
                    elseif d.hunt ~= nil then autoHunt = d.hunt end
                    if d.autoFight ~= nil then autoFight = d.autoFight
                    elseif d.fight ~= nil then autoFight = d.fight end
                    if d.autoStore ~= nil then autoStore = d.autoStore
                    elseif d.store ~= nil then autoStore = d.store end
                    if d.hydraOnly ~= nil then hydraOnly = d.hydraOnly
                    elseif d.hd ~= nil then hydraOnly = d.hd end
                    _configLoaded = true
                else
                    print("[v23] Old config version (" .. tostring(d.version) .. "), using v23 defaults")
                    _configLoaded = false
                end
            end
        end
    end)
    if not ok then
        print("[v23] CONFIG LOAD ERROR: " .. tostring(err))
    end
end

local function saveConfig()
    local data = {
        version = CONFIG_VERSION,
        autoHunt = autoHunt, autoFight = autoFight,
        autoStore = autoStore, hydraOnly = hydraOnly,
    }
    local json = HttpService:JSONEncode(data)
    pcall(function() writefile(CONFIG_FILE, json) end)
end

local function loadVisited()
    local ok, err = pcall(function()
        local raw = readfile(VISITED_FILE)
        if raw and raw ~= "" then
            local decoded = HttpService:JSONDecode(raw)
            if type(decoded) == "table" then
                for _, id in ipairs(decoded) do
                    visitedServers[id] = true
                end
            end
        end
    end)
    if not ok then
        print("[v23] VISITED LOAD ERROR: " .. tostring(err))
    end
end

local function saveVisited()
    local list = {}
    for id in pairs(visitedServers) do
        table.insert(list, id)
        if #list > 500 then break end
    end
    local json = HttpService:JSONEncode(list)
    local ok, err = pcall(function() writefile(VISITED_FILE, json) end)
    if not ok then
        print("[v23] VISITED SAVE ERROR: " .. tostring(err))
    end
end

local function loadMemory()
    local ok, err = pcall(function()
        local raw = readfile(MEMORY_FILE)
        if raw and raw ~= "" then
            local d = HttpService:JSONDecode(raw)
            if type(d) == "table" then
                for _, m in ipairs(d) do
                    if m.jobId then serverMemory[m.jobId] = m end
                end
            end
        end
    end)
    if not ok then
        print("[v23] MEMORY LOAD ERROR: " .. tostring(err))
    end
end

local function saveMemory()
    local d = {}
    for _, m in pairs(serverMemory) do table.insert(d, m) end
    local json = HttpService:JSONEncode(d)
    local ok, err = pcall(function() writefile(MEMORY_FILE, json) end)
    if not ok then
        print("[v23] MEMORY SAVE ERROR: " .. tostring(err))
    end
end

local function loadWatchList()
    local ok, err = pcall(function()
        local raw = readfile(WATCH_FILE)
        if raw and raw ~= "" then
            local d = HttpService:JSONDecode(raw)
            if type(d) == "table" then
                watchList = d
            end
        end
    end)
    if not ok then
        print("[v23] WATCH LOAD ERROR: " .. tostring(err))
    end
end

local function saveWatchList()
    local json = HttpService:JSONEncode(watchList)
    local ok, err = pcall(function() writefile(WATCH_FILE, json) end)
    if not ok then
        print("[v23] WATCH SAVE ERROR: " .. tostring(err))
    end
end

-- ─── Adaptive Cycle Analysis ────────────────────────────────────
local function analyzeServer(createdAt)
    local age = os.time() - createdAt
    if age < 0 then age = 0 end

    local bossNum
    local ttb
    local phase

    if age < FIRST_SPAWN then
        bossNum = 1
        ttb = FIRST_SPAWN - age
        phase = "countdown"
    else
        local sinceFirst = age - FIRST_SPAWN
        local cycleIdx = math.floor(sinceFirst / EFFECTIVE_CYCLE)
        local posInInterval = sinceFirst % EFFECTIVE_CYCLE

        if posInInterval < KILL_EST then
            bossNum = cycleIdx + 1
            ttb = 0
            phase = "boss_alive"
        elseif posInInterval < KILL_EST + DESPAWN_TIME then
            bossNum = cycleIdx + 2
            local remainingDespawn = (KILL_EST + DESPAWN_TIME) - posInInterval
            ttb = remainingDespawn + TIMER_DURATION
            phase = "despawn"
        else
            bossNum = cycleIdx + 2
            local countdownElapsed = posInInterval - KILL_EST - DESPAWN_TIME
            ttb = TIMER_DURATION - countdownElapsed
            phase = "countdown"
        end
    end

    local cycleNum = ((bossNum - 1) % 4) + 1
    local isHydra = (cycleNum == 4)
    local cycle = isHydra and "HYDRA" or ("SK" .. cycleNum)

    local nextCycleNum = (cycleNum % 4) + 1
    local nextIsHydra = (nextCycleNum == 4)

    local ttHydra = 0
    if isHydra then
        ttHydra = ttb
    else
        local bossesToHydra = 4 - cycleNum
        if bossesToHydra > 0 then
            ttHydra = ttb + (bossesToHydra - 1) * EFFECTIVE_CYCLE + KILL_EST + DESPAWN_TIME + TIMER_DURATION
        end
    end

    return {
        age = age, ttb = ttb, cycleNum = cycleNum, cycle = cycle,
        isHydra = isHydra, nextIsHydra = nextIsHydra,
        phase = phase, bossNum = bossNum, ttHydra = ttHydra,
    }
end

local function scoreServer(info)
    local s = 0

    if info.isHydra and info.ttb <= MIN_JOIN_TTB then
        s = -500000 + info.ttb
    elseif info.isHydra and info.ttb <= HYDRA_JOIN_TTB then
        s = -300000 + info.ttb
    elseif info.isHydra then
        s = -100000 + info.ttb
    elseif info.nextIsHydra and info.ttb <= MIN_JOIN_TTB then
        s = -50000 + info.ttb
    elseif info.ttb <= MIN_JOIN_TTB then
        s = info.ttb
    else
        s = 100000 + info.ttb
    end

    if info.phase == "boss_alive" then
        s = s - 600000
    end

    return s
end

-- ─── Watch List System ──────────────────────────────────────────
local function addToWatch(jobId, createdAt, info)
    for _, w in ipairs(watchList) do
        if w.jobId == jobId then return end
    end

    if #watchList >= MAX_WATCH then
        local removeIdx = nil
        for i = #watchList, 1, -1 do
            if not watchList[i].isHydra then
                removeIdx = i; break
            end
        end
        if removeIdx then
            table.remove(watchList, removeIdx)
        else
            table.remove(watchList, #watchList)
        end
    end

    table.insert(watchList, {
        jobId = jobId,
        createdAt = createdAt,
        isHydra = info.isHydra,
        nextIsHydra = info.nextIsHydra,
        cycle = info.cycle,
        ttb = info.ttb,
        savedAt = os.time(),
    })
end

local function promoteFromWatch()
    local promoted = {}
    local remaining = {}
    local now = os.time()

    for _, w in ipairs(watchList) do
        if now - w.savedAt > WATCH_EXPIRY then
            -- expired, discard
        elseif visitedServers[w.jobId] then
            -- already visited, discard
        else
            local freshInfo = analyzeServer(w.createdAt)
            local joinThreshold = freshInfo.isHydra and HYDRA_JOIN_TTB or MIN_JOIN_TTB

            if freshInfo.ttb <= joinThreshold or freshInfo.phase == "boss_alive" then
                table.insert(promoted, {
                    jobId = w.jobId,
                    createdAt = w.createdAt,
                    name = w.jobId:sub(1, 8) .. "…",
                    playerCount = 0,
                    region = "?",
                    age = freshInfo.age,
                    ttb = freshInfo.ttb,
                    cycle = freshInfo.cycle,
                    cycleNum = freshInfo.cycleNum,
                    isHydra = freshInfo.isHydra,
                    nextIsHydra = freshInfo.nextIsHydra,
                    score = scoreServer(freshInfo),
                    fromWatch = true,
                })
            else
                w.ttb = freshInfo.ttb
                w.cycle = freshInfo.cycle
                w.isHydra = freshInfo.isHydra
                table.insert(remaining, w)
            end
        end
    end

    watchList = remaining
    saveWatchList()

    if #promoted > 0 then
        table.sort(promoted, function(a, b) return a.score < b.score end)
        for i = #promoted, 1, -1 do
            table.insert(serverQueue, 1, promoted[i])
        end
        totalPromoted = totalPromoted + #promoted
        log("Watch: promoted " .. #promoted .. " server(s) to queue!")
    end

    return #promoted
end

-- ─── In-Game Timer Reading ──────────────────────────────────────
local function readTimers()
    local r = { sk = nil, hd = false, skRaw = "?" }
    pcall(function()
        local sea2 = lp.PlayerGui.MainGui.StarterFrame.LegacyPoseFrame.SecondSea
        local skL = sea2:FindFirstChild("SKTimeLabel")
        local hdI = sea2:FindFirstChild("HDImage")
        if skL then
            r.skRaw = skL.Text or "?"
            if r.skRaw:upper():find("UNLEASHED") then
                r.sk = "UNLEASHED"
            else
                local h, m, s = r.skRaw:match("(%d+):(%d+):(%d+)")
                if h then r.sk = tonumber(h)*3600 + tonumber(m)*60 + tonumber(s)
                else
                    local m2, s2 = r.skRaw:match("(%d+):(%d+)")
                    if m2 then r.sk = tonumber(m2)*60 + tonumber(s2) end
                end
            end
        end
        if hdI then r.hd = hdI.Visible == true end
    end)
    return r
end

-- ─── Boss Detection ─────────────────────────────────────────────
local function findBossModel()
    for model, bossName in pairs(bossRegistry) do
        if model.Parent then
            local h = model:FindFirstChildOfClass("Humanoid")
            if h and h.Health > 0 then return model, bossName end
        else
            bossRegistry[model] = nil
        end
    end
    return nil, nil
end

-- ─── Island Anchor ──────────────────────────────────────────────
local function findIslandAnchor()
    for part, anchorName in pairs(anchorRegistry) do
        if part.Parent then return part.Position, anchorName
        else anchorRegistry[part] = nil end
    end
    return nil, nil
end

-- ─── Chest Detection ────────────────────────────────────────────
local function detectTier(nameSet)
    if nameSet["Dragon"] or nameSet["Wing"] then return "T3 Dragon" end
    if (nameSet["ChestTop"] or nameSet["ChestBottum"]) and nameSet["SkullRetopo"] then return "T2" end
    if nameSet["ChestTop"] or nameSet["ChestBottum"] then return "T4?" end
    if nameSet["Top"] or nameSet["Buttom"] then return "T1" end
    return "?"
end

local function scanChestNear(center, radius)
    local nameSet, nameList = {}, {}
    local nearPart, bestDist = nil, math.huge
    for obj in pairs(chestRegistry) do
        if obj.Parent then
            local part = obj:IsA("BasePart") and obj or obj:FindFirstChildOfClass("BasePart")
            if part then
                local d = (part.Position - center).Magnitude
                if d <= radius then
                    local nm = obj.Name
                    if not nameSet[nm] then nameSet[nm] = true; table.insert(nameList, nm) end
                    if d < bestDist then bestDist = d; nearPart = part end
                end
            end
        else chestRegistry[obj] = nil end
    end
    if #nameList == 0 then return nil, {}, "?" end
    return nearPart and nearPart.Position or nil, nameList, detectTier(nameSet)
end

-- ─── Sword / Remotes ────────────────────────────────────────────
local function isSwordTool(tool)
    for _, sn in ipairs(SWORD_NAMES) do
        if tool.Name == sn or tool.Name:find(sn, 1, true) then return true end
    end
    return false
end

local function isSwordEquipped()
    local c = lp.Character; if not c then return false end
    for _, t in ipairs(c:GetChildren()) do
        if t:IsA("Tool") and isSwordTool(t) then return true end
    end
    return false
end

local function getEquippedSwordName()
    local c = lp.Character; if not c then return nil end
    for _, t in ipairs(c:GetChildren()) do
        if t:IsA("Tool") and isSwordTool(t) then return t.Name end
    end
    return nil
end

local function equipSword()
    local hum = getHumanoid(); if not hum then return false end
    local bp = lp:FindFirstChild("Backpack"); if not bp then return false end
    local sword = nil
    for _, sn in ipairs(SWORD_NAMES) do
        sword = bp:FindFirstChild(sn); if sword then break end
    end
    if not sword then
        local tools = {}
        for _, c in ipairs(bp:GetChildren()) do
            if c:IsA("Tool") then table.insert(tools, c) end
        end
        sword = tools[2] or tools[1]
    end
    if sword then
        pcall(function() hum:EquipTool(sword) end)
        task.wait(0.3)
        return true
    end
    return false
end

local function getSkillRemote()
    local rs = game:GetService("ReplicatedStorage")
    return rs:FindFirstChild("Chest") and
           rs.Chest:FindFirstChild("Remotes") and
           rs.Chest.Remotes:FindFirstChild("Functions") and
           rs.Chest.Remotes.Functions:FindFirstChild("SkillAction") or nil
end

local function getPhysicsRemote()
    local rs = game:GetService("ReplicatedStorage")
    return rs:FindFirstChild("Chest") and
           rs.Chest:FindFirstChild("Remotes") and
           rs.Chest.Remotes:FindFirstChild("Events") and
           rs.Chest.Remotes.Events:FindFirstChild("PhysicReplication") or nil
end

-- ─── Anti-Fall Platform ─────────────────────────────────────────
local function createFightPlatform(pos)
    if fightPlatform and fightPlatform.Parent then
        fightPlatform.CFrame = CFrame.new(pos - Vector3.new(0, 3, 0))
        return
    end
    if fightPlatform then pcall(function() fightPlatform:Destroy() end) end
    local p = Instance.new("Part")
    p.Size = Vector3.new(30, 1, 30)
    p.CFrame = CFrame.new(pos - Vector3.new(0, 3, 0))
    p.Anchored = true; p.CanCollide = true; p.Transparency = 1
    p.CanQuery = false; p.CanTouch = false; p.CastShadow = false
    p.Name = "_FightPlatform"; p.Parent = workspace
    fightPlatform = p
end

local function removeFightPlatform()
    if fightPlatform then pcall(function() fightPlatform:Destroy() end); fightPlatform = nil end
end

-- ─── Position Lock ──────────────────────────────────────────────
local function stopPosLock()
    if posLockConn then pcall(function() posLockConn:Disconnect() end); posLockConn = nil end
end

local function startPosLock(getBossHRP)
    stopPosLock()
    local offset = Vector3.new(3, 0, 0)
    posLockConn = RunService.Heartbeat:Connect(function()
        if not isFighting then stopPosLock(); return end
        local hrp = getHRP()
        local bhrp = getBossHRP()
        if hrp and bhrp and bhrp.Parent then
            hrp.CFrame = CFrame.new(bhrp.Position + offset, bhrp.Position)
            hrp.Velocity = Vector3.new(0, 0, 0)
            pcall(function() hrp.AssemblyLinearVelocity = Vector3.new(0, 0, 0) end)
        end
    end)
end

local function restoreMovement()
    stopPosLock()
    removeFightPlatform()
    local hum = getHumanoid()
    if hum then
        pcall(function() hum.WalkSpeed = 16 end)
        pcall(function() hum.JumpPower = 50 end)
        pcall(function() hum.JumpHeight = 7.2 end)
    end
end

-- ─── Discord (simple text) ──────────────────────────────────────
local function sendBossDiscord(bossName, jobId)
    local url = WEBHOOKS[bossName]; if not url or url == "" then return end
    local key = jobId .. "_" .. bossName; if notifiedJobs[key] then return end
    notifiedJobs[key] = true
    task.spawn(function()
        local ok, err = pcall(function()
            local tag = bossName == "HydraSeaKing" and "HYDRA" or "SK"
            local msg = tag .. " | " .. os.date("%H:%M") .. "\n```\n" .. jobId .. "\n```"
            local resp = request({
                Url = url, Method = "POST",
                Headers = { ["Content-Type"] = "application/json" },
                Body = HttpService:JSONEncode({ content = msg })
            })
            if resp and resp.StatusCode ~= 200 and resp.StatusCode ~= 204 then
                print("[v23] DISCORD BOSS SEND FAIL: HTTP " .. tostring(resp.StatusCode))
            end
        end)
        if not ok then print("[v23] DISCORD BOSS ERROR: " .. tostring(err)) end
    end)
end

local function sendChestDiscord(jobId, tier, nameList)
    local url = WEBHOOKS.Chest; if not url or url == "" then return end
    if notifiedChestJobs[jobId] then return end
    notifiedChestJobs[jobId] = true
    task.spawn(function()
        local ok, err = pcall(function()
            local msg = "CHEST " .. tier .. " | " .. os.date("%H:%M") .. "\n```\n" .. jobId .. "\n```"
            local resp = request({
                Url = url, Method = "POST",
                Headers = { ["Content-Type"] = "application/json" },
                Body = HttpService:JSONEncode({ content = msg })
            })
            if resp and resp.StatusCode ~= 200 and resp.StatusCode ~= 204 then
                print("[v23] DISCORD CHEST SEND FAIL: HTTP " .. tostring(resp.StatusCode))
            end
        end)
        if not ok then print("[v23] DISCORD CHEST ERROR: " .. tostring(err)) end
    end)
end

-- ─── Discord Status (edit same message, per-player) ─────────────
local _statusMap = {}
do
    local ok, raw = pcall(readfile, STATUS_FILE)
    if ok and raw and raw ~= "" then
        local decOk, decoded = pcall(function() return HttpService:JSONDecode(raw) end)
        if decOk and type(decoded) == "table" then
            _statusMap = decoded
        end
    end
    if type(raw) == "string" and raw ~= "" and not raw:find("{") then
        _statusMap["_legacy"] = raw:match("^%s*(.-)%s*$")
    end
    local playerKey = tostring(lp.UserId)
    statusMsgId = _statusMap[playerKey] or nil
end

local function saveStatusMsgId()
    local playerKey = tostring(lp.UserId)
    _statusMap[playerKey] = statusMsgId
    local ok, err = pcall(function()
        writefile(STATUS_FILE, HttpService:JSONEncode(_statusMap))
    end)
    if not ok then print("[v23] STATUS MSG SAVE ERROR: " .. tostring(err)) end
end

local function updateDiscordStatus()
    local url = WEBHOOKS.Status
    if not url or url == "" then return end
    task.spawn(function()
        local dsOk, dsErr = pcall(function()
            local playtime = fmtDuration(tick() - statStartTime)
            local pName = lp.Name or "?"
            local uid = tostring(lp.UserId or "?")
            local displayName = "?"
            pcall(function() displayName = lp.DisplayName or pName end)
            local lines = {
                "BOSS DETECTOR v23 (Adaptive)",
                "━━━━━━━━━━━━━━━━━━━━━━",
                "Player: " .. displayName .. " (@" .. pName .. ")",
                "UserID: " .. uid,
                "Executor: " .. executorName,
                "Executes: " .. execCount,
                "",
                "Playtime: " .. playtime,
                "SK Kills: " .. statSKKills,
                "HD Kills: " .. statHDKills,
                "Fruits: " .. statFruits,
                "Chests: " .. statChests,
                "Hops: " .. totalHops,
                "Scans: " .. totalScans,
                "Queue: " .. #serverQueue,
                "Watch: " .. #watchList,
                "Promoted: " .. totalPromoted,
            }
            local msg = "```\n" .. table.concat(lines, "\n") .. "\n```"

            if statusMsgId then
                local editUrl = url:gsub("%?wait=true$", "")
                editUrl = editUrl .. "/messages/" .. statusMsgId
                local resp = request({
                    Url = editUrl, Method = "PATCH",
                    Headers = { ["Content-Type"] = "application/json" },
                    Body = HttpService:JSONEncode({ content = msg })
                })
                if resp and resp.StatusCode == 200 then return end
                statusMsgId = nil
            end

            local postUrl = url
            if not postUrl:find("wait=true") then
                postUrl = postUrl .. (postUrl:find("?") and "&" or "?") .. "wait=true"
            end
            local resp = request({
                Url = postUrl, Method = "POST",
                Headers = { ["Content-Type"] = "application/json" },
                Body = HttpService:JSONEncode({ content = msg })
            })
            if resp and resp.StatusCode == 200 and resp.Body then
                local data = HttpService:JSONDecode(resp.Body)
                if data and data.id then
                    statusMsgId = data.id
                    saveStatusMsgId()
                end
            end
        end)
        if not dsOk then print("[v23] DISCORD STATUS ERROR: " .. tostring(dsErr)) end
    end)
end

task.spawn(function()
    task.wait(10)
    while true do
        if isRunning then updateDiscordStatus() end
        task.wait(60)
    end
end)

-- ─── Auto Store Fruit ───────────────────────────────────────────
local isStoring = false

local function getStoreCount()
    local cnt = -1
    pcall(function()
        local ps = lp:FindFirstChild("PlayerStats")
        if ps then
            local fs = ps:FindFirstChild("FruitStore")
            if fs and fs:IsA("StringValue") then
                if fs.Value == "" then cnt = 0
                else
                    local d = HttpService:JSONDecode(fs.Value)
                    if type(d) == "table" then local c = 0; for _ in pairs(d) do c = c + 1 end; cnt = c end
                end
            end
        end
    end)
    return cnt
end

local function isGuiOpen()
    if guiPanel and guiPanel.Visible == true then return true end
    local pg = lp:FindFirstChild("PlayerGui")
    if pg then
        local ok, result = pcall(function()
            local mg = pg:FindFirstChild("MainGui")
            if mg then
                local inv = mg:FindFirstChild("InventoryFrame")
                if inv and inv:IsA("GuiObject") and inv.Visible then return true end
                local sf = mg:FindFirstChild("StarterFrame")
                if sf and sf:IsA("GuiObject") and sf.Visible == false then return false end
            end
            local ff = pg:FindFirstChild("FruitFrame")
            if ff and ff:IsA("GuiObject") and ff.Visible then return true end
            return false
        end)
        if ok and result then return true end
    end
    return false
end

local storeQueue = {}

local function storeSingleFruit(fruit)
    if not fruit or not fruit.Parent then return false end
    local hum = lp.Character and lp.Character:FindFirstChildOfClass("Humanoid")
    if not hum then log("Store fail: no humanoid"); return false end
    local VIM_S = nil
    pcall(function() VIM_S = game:GetService("VirtualInputManager") end)
    if not VIM_S then log("Store fail: no VIM"); return false end
    local gi = Vector2.new(0, 0)
    pcall(function() gi = game:GetService("GuiService"):GetGuiInset() end)
    local countBefore = getStoreCount()
    log("Store: " .. fruit.Name .. " (count=" .. countBefore .. ")")

    pcall(function() hum:EquipTool(fruit) end)
    local equipped = false
    for _ = 1, 15 do
        local ch = lp.Character
        if ch and ch:FindFirstChild(fruit.Name) then equipped = true; break end
        task.wait(0.1)
    end
    if not equipped then
        log("Store: equip wait extra")
        task.wait(0.5)
        local ch = lp.Character
        if ch and ch:FindFirstChild(fruit.Name) then equipped = true end
    end
    log("Store: equipped=" .. tostring(equipped))

    local eb = nil

    pcall(function()
        if typeof(getconnections) == "function" then
            local conns = getconnections(fruit.Activated)
            log("Store: getconnections found " .. #conns .. " conn(s)")
            for _, c in ipairs(conns) do
                pcall(function() c:Fire() end)
            end
        elseif typeof(firesignal) == "function" then
            log("Store: using firesignal")
            firesignal(fruit.Activated)
        end
    end)
    for _ = 1, 20 do
        eb = lp.PlayerGui:FindFirstChild("EatFruitBecky")
        if eb then break end
        task.wait(0.05)
    end

    if not eb then
        log("Store: getconnections failed, trying VIM touch")
        local panelWasVisible = guiPanel and guiPanel.Visible
        if panelWasVisible then guiPanel.Visible = false; task.wait(0.15) end

        local scx = workspace.CurrentCamera.ViewportSize.X / 2
        local scy = workspace.CurrentCamera.ViewportSize.Y / 2
        pcall(function()
            VIM_S:SendTouchEvent("1", 0, scx, scy, game)
            task.wait(0.03)
            VIM_S:SendTouchEvent("1", 2, scx, scy, game)
        end)

        for _ = 1, 20 do
            eb = lp.PlayerGui:FindFirstChild("EatFruitBecky")
            if eb then break end
            task.wait(0.05)
        end

        if not eb then
            local vp = workspace.CurrentCamera.ViewportSize
            local rx = vp.X * 0.75
            local ry = vp.Y * 0.5
            pcall(function()
                VIM_S:SendTouchEvent("2", 0, rx, ry, game)
                task.wait(0.03)
                VIM_S:SendTouchEvent("2", 2, rx, ry, game)
            end)
            for _ = 1, 15 do
                eb = lp.PlayerGui:FindFirstChild("EatFruitBecky")
                if eb then break end
                task.wait(0.05)
            end
        end

        if panelWasVisible and guiPanel then guiPanel.Visible = true end
    end

    if not eb then log("Store FAIL: EatFruitBecky never appeared"); return false end
    log("Store: EatFruitBecky found! IGI=" .. tostring(eb.IgnoreGuiInset))

    local nc = eb:FindFirstChild("NoClick")
    if nc then nc.Value = false end
    task.wait(0.1)

    local collectBtn = nil
    local bestBtn = nil
    local bestArea = 0
    pcall(function()
        for _, desc in ipairs(eb:GetDescendants()) do
            if (desc:IsA("TextButton") or desc:IsA("ImageButton")) and desc.Visible then
                local nm = desc.Name:lower()
                local txt = ""
                pcall(function() txt = desc.Text:lower() end)
                if nm == "collect" or txt == "collect" then
                    local sz = desc.AbsoluteSize
                    local area = sz.X * sz.Y
                    log("Store: found '" .. desc.Name .. "' AbsPos=" .. tostring(desc.AbsolutePosition) .. " Size=" .. tostring(sz) .. " area=" .. math.floor(area))
                    if area > bestArea then bestArea = area; bestBtn = desc end
                end
            end
        end
    end)
    collectBtn = bestBtn

    if not collectBtn then
        local dlg = eb:FindFirstChild("Dialogue")
        collectBtn = dlg and dlg:FindFirstChild("Collect")
    end
    if not collectBtn then log("Store FAIL: no Collect button"); return false end

    local panelWas2 = guiPanel and guiPanel.Visible
    if panelWas2 then guiPanel.Visible = false; task.wait(0.15) end

    local ap = collectBtn.AbsolutePosition
    local as = collectBtn.AbsoluteSize
    local cx = ap.X + as.X / 2
    local baseY = ap.Y + as.Y / 2

    local offsets = {-gi.Y, 0, gi.Y, -gi.Y / 2, gi.Y / 2}
    local stored = false
    for i, off in ipairs(offsets) do
        local ty = baseY + off
        log("Store: try #" .. i .. " tap " .. math.floor(cx) .. "," .. math.floor(ty) .. " (off=" .. math.floor(off) .. ")")
        pcall(function()
            VIM_S:SendTouchEvent(tostring(i), 0, cx, ty, game)
            task.wait(0.05)
            VIM_S:SendTouchEvent(tostring(i), 2, cx, ty, game)
        end)
        task.wait(0.4)
        if getStoreCount() > countBefore then
            log("Store: SUCCESS at offset=" .. math.floor(off))
            stored = true
            break
        end
    end

    if panelWas2 and guiPanel then task.wait(0.2); guiPanel.Visible = true end

    for _ = 1, 20 do
        if getStoreCount() > countBefore then
            log("Store OK! " .. fruit.Name .. " count=" .. getStoreCount())
            statFruits = statFruits + 1
            return true
        end
        task.wait(0.05)
    end
    if getStoreCount() > countBefore then
        log("Store OK (late)! count=" .. getStoreCount())
        statFruits = statFruits + 1
        return true
    end
    log("Store FAIL: count unchanged (" .. countBefore .. ")")
    return false
end

local function processStoreQueue()
    if isStoring then return end
    isStoring = true
    task.spawn(function()
        while #storeQueue > 0 do
            local fruit = table.remove(storeQueue, 1)
            if fruit and fruit.Parent and fruit:IsA("Tool") and fruit.Name:find("Fruit") then
                lastStoreAttempt = tick()
                log("Storing " .. fruit.Name .. "...")
                local ok = storeSingleFruit(fruit)
                if ok then
                    setStatus("Stored " .. fruit.Name .. "!", COL.green, 3)
                    storeFailedSet[fruit] = nil
                else
                    setStatus("Store failed: " .. fruit.Name, COL.orange, 3)
                    storeFailedSet[fruit] = true
                end
                task.wait(0.5)
            end
        end
        pcall(function()
            local hum2 = lp.Character and lp.Character:FindFirstChildOfClass("Humanoid")
            if hum2 then
                local bp2 = lp:FindFirstChild("Backpack")
                if bp2 then for _, t in ipairs(bp2:GetChildren()) do
                    if t:IsA("Tool") and isSwordTool(t) then hum2:EquipTool(t); break end
                end end
            end
        end)
        isStoring = false
    end)
end

local storeFailedSet = {}
local lastStoreAttempt = 0

local function queueFruit(fruit)
    if not fruit:IsA("Tool") then return end
    if not fruit.Name:find("Fruit") then return end
    if storeFailedSet[fruit] then return end
    if tick() - lastStoreAttempt < 3 then return end
    for _, q in ipairs(storeQueue) do
        if q == fruit then return end
    end
    table.insert(storeQueue, fruit)
    processStoreQueue()
end

local function autoStoreFruits()
    if not autoStore then return end
    local bp = lp:FindFirstChild("Backpack")
    if bp then
        for _, t in ipairs(bp:GetChildren()) do
            if t:IsA("Tool") and t.Name:find("Fruit") then
                queueFruit(t)
            end
        end
    end
    local ch = lp.Character
    if ch then
        for _, t in ipairs(ch:GetChildren()) do
            if t:IsA("Tool") and t.Name:find("Fruit") then
                queueFruit(t)
            end
        end
    end
end

local function startFruitWatcher()
    local function watchBp(bp)
        bp.ChildAdded:Connect(function(child)
            if not autoStore then return end
            if child:IsA("Tool") and child.Name:find("Fruit") then
                task.wait(0.3)
                queueFruit(child)
            end
        end)
    end
    local function watchChar(ch)
        if not ch then return end
        ch.ChildAdded:Connect(function(child)
            if not autoStore then return end
            if child:IsA("Tool") and child.Name:find("Fruit") then
                task.wait(0.3)
                queueFruit(child)
            end
        end)
    end
    local bp = lp:FindFirstChild("Backpack"); if bp then watchBp(bp) end
    if lp.Character then watchChar(lp.Character) end
    lp.CharacterAdded:Connect(function(ch)
        watchChar(ch)
        task.wait(1)
        local newBp = lp:FindFirstChild("Backpack"); if newBp then watchBp(newBp) end
    end)
end

-- ─── Chest Teleport ─────────────────────────────────────────────
local function goToNearbyChest(bossPos)
    setStatus("Searching chest...", COL.gold, 3)
    setChestStatus("Waiting for chest...")
    local islandPos, anchorName = findIslandAnchor()
    local scanCenter = islandPos or bossPos
    local chestPos, nameList, tier = nil, {}, "?"
    for attempt = 1, 25 do
        chestPos, nameList, tier = scanChestNear(scanCenter, 1500)
        if chestPos then break end
        setChestStatus("Waiting... (" .. attempt .. "s)")
        task.wait(1)
    end
    if not chestPos then setChestStatus("No chest found"); log("No chest within 1500 of " .. (anchorName or "bossPos")); return end
    local hrp = getHRP()
    if hrp then hrp.CFrame = CFrame.new(chestPos + Vector3.new(0, 4, 0)) end
    setChestStatus("Chest [" .. tier .. "]: " .. table.concat(nameList, ", "))
    statChests = statChests + 1
    sendChestDiscord(game.JobId, tier, nameList)
    log("Chest [" .. tier .. "] near " .. (anchorName or "boss") .. "!")
    task.wait(3)
    autoStoreFruits()
end

-- ─── Auto Fight (Position Lock) ─────────────────────────────────
local function startFight(boss)
    if isFighting then return end
    isFighting = true; isPostFight = false

    task.spawn(function()
        local bossHRP = boss:FindFirstChild("HumanoidRootPart")
        local savedBossPos = bossHRP and bossHRP.Position or nil
        local bossName = bossRegistry[boss] or "Boss"
        log("Fight: " .. bossName)

        task.spawn(function()
            while isFighting and isRunning do
                if not isSwordEquipped() then equipSword() end
                task.wait(0.5)
            end
        end)

        if bossHRP then createFightPlatform(bossHRP.Position) end

        local hum = getHumanoid()
        if hum then
            pcall(function() hum.WalkSpeed = 0 end)
            pcall(function() hum.JumpPower = 0 end)
            pcall(function() hum.JumpHeight = 0 end)
        end

        if bossHRP then
            local hrp = getHRP()
            if hrp then hrp.CFrame = CFrame.new(bossHRP.Position + Vector3.new(3, 0, 0), bossHRP.Position) end
        end

        startPosLock(function() return boss:FindFirstChild("HumanoidRootPart") end)
        setStatus("Fighting " .. bossName .. "!", COL.orange, 2)

        local VIM = nil; pcall(function() VIM = game:GetService("VirtualInputManager") end)
        local timerZ, timerX, physAccum = 0, 1, 0
        local cx = workspace.CurrentCamera.ViewportSize.X / 2
        local cy = workspace.CurrentCamera.ViewportSize.Y / 2
        local skillRemote = getSkillRemote()
        local physRemote = getPhysicsRemote()

        while isFighting and isRunning do
            local dt = task.wait(0.1)

            if bossHRP and bossHRP.Parent then
                savedBossPos = bossHRP.Position
                createFightPlatform(bossHRP.Position)
            end

            local bossHum = boss:FindFirstChildOfClass("Humanoid")
            if not bossHum or bossHum.Health <= 0 then
                isFighting = false; isPostFight = true
                restoreMovement()
                if bossName == "HydraSeaKing" then statHDKills = statHDKills + 1
                else statSKKills = statSKKills + 1 end
                setStatus("Boss defeated!", COL.green, 3)
                log(bossName .. " defeated!")

                if savedBossPos then goToNearbyChest(savedBossPos) end

                task.wait(5)
                local bossAgain, _ = findBossModel()
                if bossAgain and isRunning then
                    log("Boss alive again — resuming")
                    isPostFight = false
                    startFight(bossAgain)
                    return
                end

                isPostFight = false

                if autoHunt and isRunning then
                    task.wait(2)
                    return
                end
                return
            end

            local swordName = getEquippedSwordName()
            if skillRemote and swordName and bossHRP and bossHRP.Parent then
                pcall(function()
                    skillRemote:InvokeServer("SW_" .. swordName .. "_M1",
                        { MouseHit = CFrame.new(bossHRP.Position) })
                end)
            elseif VIM then
                pcall(function()
                    VIM:SendMouseButtonEvent(cx, cy, 0, true, game, 1)
                    task.wait(0.05)
                    VIM:SendMouseButtonEvent(cx, cy, 0, false, game, 1)
                end)
            end

            timerZ = timerZ + dt
            if timerZ >= 2 then
                timerZ = 0
                if skillRemote and swordName and bossHRP and bossHRP.Parent then
                    pcall(function()
                        local a = { Type = "Down", MouseHit = CFrame.new(bossHRP.Position) }
                        skillRemote:InvokeServer("SW_" .. swordName .. "_Z", a)
                        task.wait(0.1); a.Type = "Up"
                        skillRemote:InvokeServer("SW_" .. swordName .. "_Z", a)
                    end)
                end
            end

            timerX = timerX + dt
            if timerX >= 2 then
                timerX = 0
                if skillRemote and swordName and bossHRP and bossHRP.Parent then
                    pcall(function()
                        local a = { Type = "Down", MouseHit = CFrame.new(bossHRP.Position) }
                        skillRemote:InvokeServer("SW_" .. swordName .. "_X", a)
                        task.wait(0.1); a.Type = "Up"
                        skillRemote:InvokeServer("SW_" .. swordName .. "_X", a)
                    end)
                end
            end

            physAccum = physAccum + dt
            if physAccum >= 0.2 then
                physAccum = 0
                local hrp = getHRP()
                if physRemote and hrp then
                    pcall(function() physRemote:FireServer(hrp.CFrame) end)
                end
            end
        end

        isFighting = false; isPostFight = false
        restoreMovement()
    end)
end

-- ─── Server Scanning + Queue + Watch List ───────────────────────
local function fetchServers()
    local best = {}
    if Network then
        for i = 1, 3 do
            local ok, data = pcall(function()
                return Network:InvokeServer("GetServerLists")
            end)
            if ok and type(data) == "table" and #data > #best then
                best = data
                if #best > 200 then break end
            elseif not ok then
                print("[v23] FETCH SERVERS ERROR (try " .. i .. "): " .. tostring(data))
            end
            if i < 3 and #best == 0 then task.wait(1.5) end
        end
    end
    if #best <= 1 then
        pcall(function()
            local rf = ReplicatedStorage.Chest.Remotes.Functions:FindFirstChild("GetServers")
            if rf and rf:IsA("RemoteFunction") then
                local data2 = rf:InvokeServer()
                if type(data2) == "table" and #data2 > #best then
                    best = data2
                end
            end
        end)
    end
    if #best == 0 then
        print("[v23] NETWORK: no servers returned from any source")
    end
    return best
end

local function buildQueue()
    if isScanning then return end
    isScanning = true
    setStatus("Scanning servers...", COL.accent, 2)

    local rawServers = fetchServers()
    if #rawServers == 0 then
        isScanning = false
        log("Scan: 0 servers (Network fail?)")
        return
    end

    totalScans = totalScans + 1
    lastScanTime = tick()
    local now = os.time()

    local immediatePool = {}
    local watchCount = 0

    for _, s in ipairs(rawServers) do
        local createdAt = tonumber(s.CreatedAt)
        if s.JobId and s.JobId ~= game.JobId and createdAt then
            if not visitedServers[s.JobId] then
                local info = analyzeServer(createdAt)

                local dominated = false
                if hydraOnly and not info.isHydra and not info.nextIsHydra then
                    dominated = true
                end

                if not dominated then
                    local joinThreshold = info.isHydra and HYDRA_JOIN_TTB or MIN_JOIN_TTB

                    if info.ttb <= joinThreshold or info.phase == "boss_alive" then
                        table.insert(immediatePool, {
                            jobId = s.JobId,
                            name = s.Name or "?",
                            createdAt = createdAt,
                            playerCount = s.PlayerCount or 0,
                            region = s.Region or "?",
                            age = info.age, ttb = info.ttb,
                            cycle = info.cycle, cycleNum = info.cycleNum,
                            isHydra = info.isHydra, nextIsHydra = info.nextIsHydra,
                            score = scoreServer(info),
                            phase = info.phase,
                        })
                    elseif info.isHydra or info.nextIsHydra then
                        addToWatch(s.JobId, createdAt, info)
                        watchCount = watchCount + 1
                    elseif not hydraOnly and info.ttb <= TIMER_DURATION then
                        addToWatch(s.JobId, createdAt, info)
                        watchCount = watchCount + 1
                    end

                    serverMemory[s.JobId] = {
                        jobId = s.JobId, name = s.Name or "?",
                        createdAt = createdAt, savedAt = now,
                        cycle = info.cycle, isHydra = info.isHydra, ttb = info.ttb,
                    }
                end
            end
        end
    end

    table.sort(immediatePool, function(a, b) return a.score < b.score end)

    serverQueue = {}
    for i = 1, math.min(#immediatePool, MAX_QUEUE) do
        table.insert(serverQueue, immediatePool[i])
    end

    saveMemory()
    saveWatchList()

    local hdCount = 0
    for _, s in ipairs(serverQueue) do if s.isHydra then hdCount = hdCount + 1 end end
    log("Scan #" .. totalScans .. ": " .. #rawServers .. " srv → Q=" .. #serverQueue .. " (HD=" .. hdCount .. ") Watch=" .. #watchList .. " (+" .. watchCount .. ")")
    setStatus("Q:" .. #serverQueue .. " W:" .. #watchList, COL.green, 3)
    pcall(function() setQueueInfo(serverQueue) end)
    pcall(function() setWatchInfo(watchList) end)
    isScanning = false
end

-- ─── Watch List Checker (background task) ───────────────────────
local function startWatchChecker()
    task.spawn(function()
        while true do
            task.wait(WATCH_RECHECK)
            if not isRunning then continue end
            if isFighting or isTeleporting then continue end
            if #watchList == 0 then continue end

            local promoted = promoteFromWatch()
            if promoted > 0 then
                log("Watch promoted " .. promoted .. " → queue now " .. #serverQueue)
                pcall(function() setQueueInfo(serverQueue) end)
                pcall(function() setWatchInfo(watchList) end)
            end
            lastWatchCheck = tick()
        end
    end)
end

-- ─── Smart Hop ──────────────────────────────────────────────────
local teleportFailed = false
local teleportFailReason = ""
TeleportService.TeleportInitFailed:Connect(function(player, result, errorMsg)
    if player == lp then
        teleportFailed = true
        isTeleporting = false
        teleportFailReason = tostring(errorMsg or result or "unknown")
    end
end)

local lastHopFailTime = 0
local HOP_FAIL_COOLDOWN = 30

local function smartHop()
    if isTeleporting or isFighting then return false end

    if tick() - lastHopFailTime < HOP_FAIL_COOLDOWN then
        local remaining = math.ceil(HOP_FAIL_COOLDOWN - (tick() - lastHopFailTime))
        setStatus("No servers — rescan in " .. remaining .. "s", COL.textSub)
        return false
    end

    promoteFromWatch()

    if #serverQueue == 0 and not isScanning then
        buildQueue()
    end
    if #serverQueue == 0 then
        promoteFromWatch()
    end
    if #serverQueue == 0 then
        visitedServers = {}
        log("Queue empty — reset visited, rescan in " .. HOP_FAIL_COOLDOWN .. "s")
        lastHopFailTime = tick()
        if not isScanning then buildQueue() end
        return false
    end

    local target = nil
    local targetIdx = nil
    for i, s in ipairs(serverQueue) do
        local freshInfo = analyzeServer(s.createdAt)
        s.ttb = freshInfo.ttb
        s.cycle = freshInfo.cycle
        s.isHydra = freshInfo.isHydra

        local joinThreshold = freshInfo.isHydra and HYDRA_JOIN_TTB or MIN_JOIN_TTB

        if freshInfo.ttb <= joinThreshold or freshInfo.phase == "boss_alive" then
            target = s
            targetIdx = i
            break
        else
            addToWatch(s.jobId, s.createdAt, freshInfo)
        end
    end

    if targetIdx then
        table.remove(serverQueue, targetIdx)
    end

    if not target then
        promoteFromWatch()
        if #serverQueue > 0 then
            target = table.remove(serverQueue, 1)
        end
    end

    if not target then
        if #serverQueue > 0 then
            target = table.remove(serverQueue, 1)
        else
            log("No viable server in queue — cooldown " .. HOP_FAIL_COOLDOWN .. "s")
            lastHopFailTime = tick()
            return false
        end
    end

    visitedServers[target.jobId] = true
    saveVisited()
    totalHops = totalHops + 1
    isTeleporting = true
    teleportFailed = false
    teleportFailReason = ""
    hopFailCount = 0

    local tag = target.isHydra and " [HYDRA]" or (" [" .. target.cycle .. "]")
    setStatus("Hop → " .. (target.name or "?") .. tag, COL.accent, 5)
    log("Hop #" .. totalHops .. " → " .. (target.name or "?") .. tag .. " TTB=" .. fmt(target.ttb))
    pcall(function() setQueueInfo(serverQueue) end)

    serverJoinedAt = tick()

    task.wait(0.5)
    local ok, tpErr = pcall(function()
        TeleportService:TeleportToPlaceInstance(PlaceID, target.jobId, lp)
    end)

    if not ok then
        log("Teleport error: " .. tostring(tpErr))
        isTeleporting = false
        hopFailCount = hopFailCount + 1
        if hopFailCount >= 3 then
            log("3 consecutive hop fails, rebuilding queue")
            hopFailCount = 0
            task.spawn(buildQueue)
        end
        return false
    end

    task.wait(1.5)
    if teleportFailed then
        local reason = teleportFailReason
        if reason:lower():find("full") or reason:lower():find("capacity") then
            log("Server FULL — skipping: " .. (target.name or "?"))
        else
            log("Teleport failed: " .. reason)
        end
        isTeleporting = false
        hopFailCount = hopFailCount + 1
        if hopFailCount >= 3 then
            hopFailCount = 0
            task.spawn(buildQueue)
        end
        return false
    end

    task.wait(10)
    isTeleporting = false
    serverJoinedAt = tick()
    hopFailCount = 0
    return true
end

-- ─── Pre-Spawned Chest Check ────────────────────────────────────
local function checkPreSpawnedChest()
    task.wait(5)
    if not isRunning then return end
    local islandPos, anchorName = findIslandAnchor()
    if not islandPos then return end
    local boss, _ = findBossModel()
    if boss then return end
    local timers = readTimers()
    if timers.sk == "UNLEASHED" or (type(timers.sk) == "number" and timers.sk <= 60) then
        local chestPos, nameList, tier = scanChestNear(islandPos, 1500)
        if not chestPos then return end
        setChestStatus("Pre-spawned chest! [" .. tier .. "]")
        sendChestDiscord(game.JobId, tier, nameList)
        log("Pre-spawned chest [" .. tier .. "] near " .. anchorName)
        if autoFight then
            isPostFight = true
            local hrp = getHRP()
            if hrp then hrp.CFrame = CFrame.new(chestPos + Vector3.new(0, 4, 0)) end
            task.wait(5)
            autoStoreFruits()
            task.wait(2)
            isPostFight = false
        else
            log("Pre-spawned chest detected but autoFight OFF, not teleporting")
        end
    end
end

-- ─── Chest Scanner Task ────────────────────────────────────────
local lastChestKey = nil
local chestScanActive = false

local function startChestScanTask()
    task.spawn(function()
        while true do
            task.wait(5)
            if not isRunning then continue end
            local islandPos, anchorName = findIslandAnchor()
            if not islandPos then lastChestKey = nil; chestScanActive = false; continue end

            local timers = readTimers()
            local shouldScan = false
            if timers.sk == "UNLEASHED" then shouldScan = true end
            if type(timers.sk) == "number" and timers.sk <= 120 then shouldScan = true end
            local boss, _ = findBossModel()
            if boss then shouldScan = true end
            if isPostFight then shouldScan = true end

            if not shouldScan then
                if chestScanActive then
                    lastChestKey = nil
                    chestScanActive = false
                end
                continue
            end

            chestScanActive = true
            local _, nameList, tier = scanChestNear(islandPos, 1500)
            if #nameList > 0 then
                local key = table.concat(nameList, ",")
                if key ~= lastChestKey then
                    lastChestKey = key
                    setChestStatus("Chest [" .. tier .. "] near " .. anchorName)
                    sendChestDiscord(game.JobId, tier, nameList)
                    log("Chest detected [" .. tier .. "] near " .. anchorName)
                end
            else
                lastChestKey = nil
            end
        end
    end)
end

-- ─── Main Loop ──────────────────────────────────────────────────
local function mainLoop()
    if not isCharLoaded() then
        log("Waiting for character...")
        if not lp.Character or not lp.Character:FindFirstChild("HumanoidRootPart") then
            lp.CharacterAdded:Wait()
            if lp.Character then lp.Character:WaitForChild("HumanoidRootPart", 15) end
        end
        log("Character ready!")
    end
    serverJoinedAt = tick()
    log("Main loop started (v23 Adaptive)")

    task.wait(3)
    if not isScanning then
        buildQueue()
    end
    log("Initial scan done. Q=" .. #serverQueue .. " Watch=" .. #watchList)

    local _loopTick = 0
    local _lastTimerLog = 0

    while true do
        task.wait(1)
        _loopTick = _loopTick + 1
        if not isRunning then continue end
        if isFighting or isPostFight or isTeleporting then
            if _loopTick % 10 == 0 then
                log("Loop: fight=" .. tostring(isFighting) .. " post=" .. tostring(isPostFight) .. " tp=" .. tostring(isTeleporting))
            end
            continue
        end

        local boss, bossName = findBossModel()
        if boss and bossName then
            foundCode = game.JobId
            sendBossDiscord(bossName, game.JobId)
            local dn = bossName == "HydraSeaKing" and "HYDRA" or "Sea King"
            setStatus("BOSS: " .. dn .. "!", COL.green, 3)
            log("BOSS FOUND: " .. dn)
            if autoFight and not isFighting then startFight(boss) end
            continue
        end

        if not autoHunt then
            if _loopTick % 15 == 1 then
                log("Hunt OFF — toggle Auto Hunt to start hopping")
            end
            setStatus("Hunt OFF — tap Config", COL.orange)
            continue
        end

        local sinceJoin = tick() - serverJoinedAt
        if sinceJoin < ARRIVAL_GRACE then
            setStatus("Loading... " .. math.floor(ARRIVAL_GRACE - sinceJoin) .. "s", COL.accent)
            continue
        end

        if tick() - lastScanTime > RESCAN_INTERVAL and not isScanning then
            task.spawn(buildQueue)
        end

        local timers = readTimers()

        if _loopTick - _lastTimerLog >= 15 then
            _lastTimerLog = _loopTick
            local skStr = timers.sk == nil and "nil" or tostring(timers.sk)
            log("Timer: SK=" .. skStr .. " HD=" .. tostring(timers.hd) .. " raw=" .. tostring(timers.skRaw) .. " Q=" .. #serverQueue)
        end

        if timers.sk == "UNLEASHED" then
            setStatus("Boss spawning!", COL.gold, 2)
            log("UNLEASHED — waiting for boss")
            for _ = 1, 30 do
                task.wait(1)
                if not isRunning then break end
                local b, bn = findBossModel()
                if b and bn then
                    foundCode = game.JobId
                    sendBossDiscord(bn, game.JobId)
                    local dn2 = bn == "HydraSeaKing" and "HYDRA" or "Sea King"
                    setStatus("BOSS: " .. dn2 .. "!", COL.green, 3)
                    if autoFight then startFight(b) end
                    break
                end
            end
            continue
        end

        if type(timers.sk) == "number" then
            if timers.hd and timers.sk <= MAX_WAIT_HD then
                setStatus("HYDRA in " .. fmt(timers.sk) .. " — waiting", COL.hydra, 2)
                continue
            end
            if not timers.hd and timers.sk <= MAX_WAIT_SK then
                setStatus("SK in " .. fmt(timers.sk), COL.text, 2)
                continue
            end

            if timers.hd and timers.sk <= HYDRA_JOIN_TTB then
                setStatus("HYDRA " .. fmt(timers.sk) .. " — staying", COL.hydra, 2)
                continue
            end

            local hopResult = smartHop()
            if not hopResult then
                local cd = math.ceil(math.max(0, HOP_FAIL_COOLDOWN - (tick() - lastHopFailTime)))
                setStatus("Boss " .. fmt(timers.sk) .. " | Q=0 rescan " .. cd .. "s", COL.orange, 2)
                task.wait(3)
            end
            continue
        end

        if sinceJoin < 20 then
            setStatus("Reading timers...", COL.textSub)
            continue
        end

        local hopResult2 = smartHop()
        if not hopResult2 then
            setStatus("No timer | Q=0 — waiting", COL.orange, 2)
            task.wait(3)
        end
    end
end

-- ═══════════════════════════════════════════════════════════════════
--  GUI v23 — LUNAR Sidebar + Watch Tab + Slide Toggles
-- ═══════════════════════════════════════════════════════════════════

if not lp:FindFirstChild("PlayerGui") then
    lp:WaitForChild("PlayerGui", 30)
end

pcall(function()
    local old = lp.PlayerGui:FindFirstChild("BossDetectorGui")
    if old then old:Destroy() end
    old = game:GetService("CoreGui"):FindFirstChild("BossDetectorGui")
    if old then old:Destroy() end
end)

local gui = Instance.new("ScreenGui")
gui.Name = "BossDetectorGui"
gui.ResetOnSpawn = false
gui.DisplayOrder = 999
gui.IgnoreGuiInset = true
local _guiOk = pcall(function() gui.Parent = game:GetService("CoreGui") end)
if not _guiOk then gui.Parent = lp.PlayerGui end

local Z = { bg = 190, side = 191, sideBtn = 192, content = 192, elem = 193, knob = 194 }

local floatBtn = Instance.new("TextButton")
floatBtn.Size = UDim2.new(0, 48, 0, 36)
floatBtn.Position = UDim2.new(0, 6, 0, 6)
floatBtn.BackgroundColor3 = COL.hydra
floatBtn.TextColor3 = COL.white
floatBtn.Text = "BD"
floatBtn.TextSize = 13
floatBtn.Font = Enum.Font.GothamBold
floatBtn.ZIndex = 200
floatBtn.Active = true
floatBtn.Parent = gui
Instance.new("UICorner", floatBtn).CornerRadius = UDim.new(0, 8)

do
    local UIS = game:GetService("UserInputService")
    local dragging = false
    local dragStart, startPos
    floatBtn.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
            or input.UserInputType == Enum.UserInputType.Touch then
            dragging = true
            dragStart = input.Position
            startPos = floatBtn.Position
            input.Changed:Connect(function()
                if input.UserInputState == Enum.UserInputState.End then dragging = false end
            end)
        end
    end)
    floatBtn.InputChanged:Connect(function(input)
        if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement
            or input.UserInputType == Enum.UserInputType.Touch) then
            local delta = input.Position - dragStart
            floatBtn.Position = UDim2.new(
                startPos.X.Scale, startPos.X.Offset + delta.X,
                startPos.Y.Scale, startPos.Y.Offset + delta.Y
            )
        end
    end)
    UIS.InputChanged:Connect(function(input)
        if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement
            or input.UserInputType == Enum.UserInputType.Touch) then
            local delta = input.Position - dragStart
            floatBtn.Position = UDim2.new(
                startPos.X.Scale, startPos.X.Offset + delta.X,
                startPos.Y.Scale, startPos.Y.Offset + delta.Y
            )
        end
    end)
end

local SIDE_W = 70
local W, H = 360, 340
local main = Instance.new("Frame")
main.Size = UDim2.new(0, W, 0, H)
main.Position = UDim2.new(0, 6, 0, 40)
main.BackgroundColor3 = Color3.fromRGB(14, 14, 24)
main.BackgroundTransparency = 0.02
main.BorderSizePixel = 0
main.Active = true; main.Draggable = true; main.Visible = false
main.ZIndex = Z.bg; main.Parent = gui
guiPanel = main
Instance.new("UICorner", main).CornerRadius = UDim.new(0, 10)
local ms = Instance.new("UIStroke", main); ms.Color = Color3.fromRGB(60, 40, 100); ms.Thickness = 1

local sidebar = Instance.new("Frame")
sidebar.Size = UDim2.new(0, SIDE_W, 1, 0)
sidebar.BackgroundColor3 = Color3.fromRGB(10, 10, 18)
sidebar.BorderSizePixel = 0; sidebar.ZIndex = Z.side; sidebar.Parent = main
Instance.new("UICorner", sidebar).CornerRadius = UDim.new(0, 10)
local sideClip = Instance.new("Frame")
sideClip.Size = UDim2.new(0, 10, 1, 0)
sideClip.Position = UDim2.new(1, -10, 0, 0)
sideClip.BackgroundColor3 = Color3.fromRGB(10, 10, 18)
sideClip.BorderSizePixel = 0; sideClip.ZIndex = Z.side; sideClip.Parent = sidebar

local titleLbl = Instance.new("TextLabel")
titleLbl.Size = UDim2.new(1, 0, 0, 26)
titleLbl.BackgroundTransparency = 1
titleLbl.Text = "BD v23"
titleLbl.TextColor3 = COL.hydra
titleLbl.TextSize = 10
titleLbl.Font = Enum.Font.GothamBold
titleLbl.ZIndex = Z.sideBtn; titleLbl.Parent = sidebar

local tabs = {
    { n = "Live",   i = ">" },
    { n = "Queue",  i = "Q" },
    { n = "Watch",  i = "W" },
    { n = "Config", i = "C" },
    { n = "Log",    i = "L" },
}
local tabBtns = {}
local tabPages = {}

for idx, tab in ipairs(tabs) do
    local tb = Instance.new("TextButton")
    tb.Size = UDim2.new(1, 0, 0, 22)
    tb.Position = UDim2.new(0, 0, 0, 26 + (idx - 1) * 23)
    tb.BackgroundColor3 = idx == 1 and Color3.fromRGB(30, 25, 45) or Color3.fromRGB(10, 10, 18)
    tb.BackgroundTransparency = idx == 1 and 0 or 1
    tb.TextColor3 = idx == 1 and COL.hydra or COL.textSub
    tb.Text = " " .. tab.i .. " " .. tab.n
    tb.TextSize = 8; tb.Font = Enum.Font.GothamBold
    tb.TextXAlignment = Enum.TextXAlignment.Left
    tb.BorderSizePixel = 0; tb.ZIndex = Z.sideBtn; tb.Parent = sidebar
    tabBtns[idx] = tb
end

local closeSide = Instance.new("TextButton")
closeSide.Size = UDim2.new(1, -8, 0, 18)
closeSide.Position = UDim2.new(0, 4, 1, -22)
closeSide.BackgroundColor3 = Color3.fromRGB(40, 20, 20)
closeSide.TextColor3 = COL.red; closeSide.Text = "Close"
closeSide.TextSize = 8; closeSide.Font = Enum.Font.GothamBold
closeSide.ZIndex = Z.sideBtn; closeSide.Parent = sidebar
Instance.new("UICorner", closeSide).CornerRadius = UDim.new(0, 4)

local contentFrame = Instance.new("Frame")
contentFrame.Size = UDim2.new(1, -SIDE_W, 1, 0)
contentFrame.Position = UDim2.new(0, SIDE_W, 0, 0)
contentFrame.BackgroundTransparency = 1; contentFrame.BorderSizePixel = 0
contentFrame.ZIndex = Z.content; contentFrame.ClipsDescendants = true; contentFrame.Parent = main

local function makeScrollPage(idx)
    local pg = Instance.new("ScrollingFrame")
    pg.Size = UDim2.new(1, 0, 1, 0)
    pg.CanvasSize = UDim2.new(0, 0, 0, 0)
    pg.AutomaticCanvasSize = Enum.AutomaticSize.Y
    pg.ScrollBarThickness = 2; pg.ScrollBarImageColor3 = COL.hydra
    pg.BackgroundTransparency = 1; pg.BorderSizePixel = 0
    pg.Visible = idx == 1; pg.ZIndex = Z.elem; pg.Parent = contentFrame
    local lay = Instance.new("UIListLayout", pg)
    lay.Padding = UDim.new(0, 3); lay.SortOrder = Enum.SortOrder.LayoutOrder
    local pad = Instance.new("UIPadding", pg)
    pad.PaddingLeft = UDim.new(0, 8); pad.PaddingRight = UDim.new(0, 6)
    pad.PaddingTop = UDim.new(0, 6); pad.PaddingBottom = UDim.new(0, 6)
    tabPages[idx] = pg; return pg
end
for i = 1, #tabs do makeScrollPage(i) end

local activeTab = 1
local function switchTab(idx)
    activeTab = idx
    for i, btn in ipairs(tabBtns) do
        btn.BackgroundColor3 = i == idx and Color3.fromRGB(30, 25, 45) or Color3.fromRGB(10, 10, 18)
        btn.BackgroundTransparency = i == idx and 0 or 1
        btn.TextColor3 = i == idx and COL.hydra or COL.textSub
        tabPages[i].Visible = i == idx
    end
end
for i, btn in ipairs(tabBtns) do
    btn.MouseButton1Click:Connect(function() switchTab(i) end)
end

local _ord = { 0, 0, 0, 0, 0 }

local function mkLabel(pg, text, col, bold, sz)
    _ord[pg] = _ord[pg] + 1
    local lbl = Instance.new("TextLabel")
    lbl.Size = UDim2.new(1, 0, 0, 0); lbl.AutomaticSize = Enum.AutomaticSize.Y
    lbl.BackgroundTransparency = 1; lbl.Text = text
    lbl.TextColor3 = col or COL.text; lbl.TextSize = sz or 10
    lbl.Font = bold and Enum.Font.GothamBold or Enum.Font.Gotham
    lbl.TextXAlignment = Enum.TextXAlignment.Left; lbl.TextWrapped = true
    lbl.LayoutOrder = _ord[pg]; lbl.ZIndex = Z.elem; lbl.Parent = tabPages[pg]
    return lbl
end

local function mkBtn(pg, text, col, h)
    _ord[pg] = _ord[pg] + 1
    local btn = Instance.new("TextButton")
    btn.Size = UDim2.new(1, 0, 0, h or 24)
    btn.BackgroundColor3 = col or COL.bgCard; btn.TextColor3 = COL.white
    btn.Text = text; btn.TextSize = 9; btn.Font = Enum.Font.GothamBold
    btn.LayoutOrder = _ord[pg]; btn.ZIndex = Z.elem; btn.Parent = tabPages[pg]
    Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 5)
    return btn
end

local function mkSlideToggle(pg, text, default, onColor)
    _ord[pg] = _ord[pg] + 1
    local TRACK_W, TRACK_H, KNOB_SZ = 36, 18, 14
    local onCol = onColor or COL.green
    local row = Instance.new("Frame")
    row.Size = UDim2.new(1, 0, 0, 22); row.BackgroundTransparency = 1
    row.LayoutOrder = _ord[pg]; row.ZIndex = Z.elem; row.Parent = tabPages[pg]
    local lbl = Instance.new("TextLabel")
    lbl.Size = UDim2.new(1, -(TRACK_W+6), 1, 0); lbl.BackgroundTransparency = 1
    lbl.Text = text; lbl.TextColor3 = COL.text; lbl.TextSize = 10
    lbl.Font = Enum.Font.Gotham; lbl.TextXAlignment = Enum.TextXAlignment.Left
    lbl.ZIndex = Z.elem; lbl.Parent = row
    local track = Instance.new("TextButton")
    track.Size = UDim2.new(0, TRACK_W, 0, TRACK_H)
    track.Position = UDim2.new(1, -TRACK_W, 0.5, -TRACK_H/2)
    track.BackgroundColor3 = default and onCol or Color3.fromRGB(45, 45, 65)
    track.Text = ""; track.AutoButtonColor = false; track.ZIndex = Z.elem; track.Parent = row
    Instance.new("UICorner", track).CornerRadius = UDim.new(1, 0)
    local knob = Instance.new("Frame")
    knob.Size = UDim2.new(0, KNOB_SZ, 0, KNOB_SZ)
    local offX, onX = 2, TRACK_W - KNOB_SZ - 2
    knob.Position = UDim2.new(0, default and onX or offX, 0.5, -KNOB_SZ/2)
    knob.BackgroundColor3 = COL.white; knob.ZIndex = Z.knob; knob.Parent = track
    Instance.new("UICorner", knob).CornerRadius = UDim.new(1, 0)
    local state = default or false
    local function apply(on)
        track.BackgroundColor3 = on and onCol or Color3.fromRGB(45, 45, 65)
        knob.Position = UDim2.new(0, on and onX or offX, 0.5, -KNOB_SZ/2)
    end
    track.MouseButton1Click:Connect(function() state = not state; apply(state) end)
    return {
        getState = function() return state end,
        setState = function(v) state = v; apply(state) end,
        onToggle = function(cb) track.MouseButton1Click:Connect(function() cb(state) end) end,
    }
end

local function mkSpacer(pg, h)
    _ord[pg] = _ord[pg] + 1
    local sp = Instance.new("Frame")
    sp.Size = UDim2.new(1, 0, 0, h or 4); sp.BackgroundTransparency = 1
    sp.LayoutOrder = _ord[pg]; sp.ZIndex = Z.elem; sp.Parent = tabPages[pg]
end

local function mkHdr(pg, text)
    _ord[pg] = _ord[pg] + 1
    local lbl = Instance.new("TextLabel")
    lbl.Size = UDim2.new(1, 0, 0, 14); lbl.BackgroundTransparency = 1
    lbl.Text = text; lbl.TextColor3 = COL.hydra; lbl.TextSize = 8
    lbl.Font = Enum.Font.GothamBold; lbl.TextXAlignment = Enum.TextXAlignment.Left
    lbl.LayoutOrder = _ord[pg]; lbl.ZIndex = Z.elem; lbl.Parent = tabPages[pg]
end

-- ═════════ PAGE 1: LIVE ═════════
mkHdr(1, "STATUS")
local statusLbl = mkLabel(1, "Loading...", COL.text, true, 11)
local chestLbl = mkLabel(1, "Chest: --", COL.gold, false, 9)
local timerLbl = mkLabel(1, "Timer: --", COL.textSub, false, 9)
mkSpacer(1, 4)
mkHdr(1, "STATS")
local statsLbl = mkLabel(1, "Scans: 0 | Hops: 0", COL.textSub, false, 9)
mkSpacer(1, 4)
mkHdr(1, "SERVER CODE")
local codeLbl = mkLabel(1, "--", COL.gold, true, 10)
local btnCopy = mkBtn(1, "Copy Code", Color3.fromRGB(30, 55, 120))
btnCopy.Visible = false
mkSpacer(1, 4)
mkHdr(1, "QUICK JOIN")
_ord[1] = _ord[1] + 1
local codeBox = Instance.new("TextBox")
codeBox.Size = UDim2.new(1, 0, 0, 24)
codeBox.BackgroundColor3 = Color3.fromRGB(16, 16, 30)
codeBox.TextColor3 = COL.white; codeBox.PlaceholderText = "Paste code..."
codeBox.PlaceholderColor3 = COL.textSub; codeBox.Text = ""
codeBox.TextSize = 9; codeBox.Font = Enum.Font.Gotham; codeBox.ClearTextOnFocus = false
codeBox.LayoutOrder = _ord[1]; codeBox.ZIndex = Z.elem; codeBox.Parent = tabPages[1]
Instance.new("UICorner", codeBox).CornerRadius = UDim.new(0, 5)
local btnJoinMan = mkBtn(1, "Join Manual", COL.purple)

-- ═════════ PAGE 2: QUEUE ═════════
mkHdr(2, "SERVER QUEUE (ready)")
local queueLbl = mkLabel(2, "(scanning...)", COL.textSub, false, 9)
mkSpacer(2, 4)
local btnRescan = mkBtn(2, "Rescan Now", Color3.fromRGB(40, 30, 70))
local btnHopNow = mkBtn(2, "Hop Now", Color3.fromRGB(40, 50, 90))

-- ═════════ PAGE 3: WATCH ═════════
mkHdr(3, "WATCH LIST (deferred)")
local watchLbl = mkLabel(3, "(none)", COL.textSub, false, 9)
mkSpacer(3, 4)
mkLabel(3, "Servers saved for later. Auto-promoted when TTB <= threshold.", COL.textSub, false, 8)
mkSpacer(3, 4)
local btnPromoteNow = mkBtn(3, "Check Watch Now", Color3.fromRGB(40, 50, 70))
local btnClearWatch = mkBtn(3, "Clear Watch List", Color3.fromRGB(60, 30, 30))

-- ═════════ PAGE 4: CONFIG ═════════
mkHdr(4, "AUTOMATION")
local huntToggle  = mkSlideToggle(4, "Auto Hunt (scan+hop)", true, COL.hydra)
local fightToggle = mkSlideToggle(4, "Auto Fight", true, COL.orange)
local storeToggle = mkSlideToggle(4, "Auto Store Fruit", false, COL.gold)
local hdOnlyToggle = mkSlideToggle(4, "Hydra Only", true, COL.purple)

mkSpacer(4, 6)
mkHdr(4, "MANUAL")
local btnStoreNow = mkBtn(4, "Store Fruit Now", Color3.fromRGB(130, 80, 220))

mkSpacer(4, 6)
mkHdr(4, "DATA")
local btnResetVisited = mkBtn(4, "Reset Visited", Color3.fromRGB(60, 30, 30))
local btnClearMem = mkBtn(4, "Clear Memory", Color3.fromRGB(60, 30, 30))
local btnCopyJob = mkBtn(4, "Copy JobId", Color3.fromRGB(30, 40, 70))

mkSpacer(4, 4)
mkLabel(4, "Boss Detector + Hunter v23", COL.hydra, true, 9)
mkLabel(4, "Adaptive Cycle + Watch List", COL.textSub, false, 8)

-- ═════════ PAGE 5: LOG ═════════
mkHdr(5, "ACTIVITY LOG")
local logLbl = mkLabel(5, "(no activity)", COL.textSub, false, 8)

-- ═════════ WIRE UP ═════════
setStatus = function(txt, color, lockSecs)
    if tick() < statusLockUntil and (not lockSecs or lockSecs == 0) then return end
    statusLbl.Text = txt; statusLbl.TextColor3 = color or COL.text
    if lockSecs and lockSecs > 0 then statusLockUntil = tick() + lockSecs end
end

local function forceStatus(txt, color)
    statusLockUntil = 0; setStatus(txt, color)
end

setChestStatus = function(txt) chestLbl.Text = txt end

addLog = function()
    logLbl.Text = table.concat(logLines, "\n")
end

setQueueInfo = function(queue)
    if #queue == 0 then queueLbl.Text = "(empty — rescan needed)"; return end
    local lines = {}
    for i, s in ipairs(queue) do
        local freshInfo = analyzeServer(s.createdAt)
        local tag = freshInfo.isHydra and " [HD]" or (" [" .. freshInfo.cycle .. "]")
        local src = s.fromWatch and " W" or ""
        table.insert(lines, i .. ". " .. (s.name or "?") .. tag .. " TTB=" .. fmt(freshInfo.ttb) .. src)
    end
    queueLbl.Text = table.concat(lines, "\n")
end

setWatchInfo = function(wlist)
    if #wlist == 0 then watchLbl.Text = "(no servers watching)"; return end
    local lines = {}
    for i, w in ipairs(wlist) do
        local freshInfo = analyzeServer(w.createdAt)
        local tag = freshInfo.isHydra and " [HD]" or (" [" .. freshInfo.cycle .. "]")
        local age = os.time() - w.savedAt
        table.insert(lines, i .. ". " .. w.jobId:sub(1, 12) .. "…" .. tag .. " TTB=" .. fmt(freshInfo.ttb) .. " (" .. math.floor(age/60) .. "m ago)")
    end
    watchLbl.Text = table.concat(lines, "\n")
end

do
    local _dragTotal = 0
    floatBtn.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
            or input.UserInputType == Enum.UserInputType.Touch then
            _dragTotal = 0
        end
    end)
    floatBtn.InputChanged:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseMovement
            or input.UserInputType == Enum.UserInputType.Touch then
            _dragTotal = _dragTotal + 1
        end
    end)
    floatBtn.MouseButton1Click:Connect(function()
        if _dragTotal < 5 then main.Visible = not main.Visible end
    end)
end
closeSide.MouseButton1Click:Connect(function() main.Visible = false end)

huntToggle.setState(autoHunt)
fightToggle.setState(autoFight)
storeToggle.setState(autoStore)
hdOnlyToggle.setState(hydraOnly)

huntToggle.onToggle(function(on)
    autoHunt = on; saveConfig()
    log("Toggle: autoHunt=" .. tostring(on))
end)
fightToggle.onToggle(function(on)
    autoFight = on
    if not on then isFighting = false; isPostFight = false; restoreMovement() end
    saveConfig()
    log("Toggle: autoFight=" .. tostring(on))
end)
storeToggle.onToggle(function(on)
    autoStore = on; saveConfig()
    log("Toggle: autoStore=" .. tostring(on))
    if on then task.spawn(autoStoreFruits) end
end)
hdOnlyToggle.onToggle(function(on)
    hydraOnly = on; saveConfig()
    log("Toggle: hydraOnly=" .. tostring(on))
end)

btnHopNow.MouseButton1Click:Connect(function()
    if not isTeleporting then task.spawn(smartHop) end
end)
btnStoreNow.MouseButton1Click:Connect(function()
    task.spawn(function()
        storeFailedSet = {}
        lastStoreAttempt = 0
        local savedAutoStore = autoStore
        autoStore = true
        log("Manual store triggered")
        autoStoreFruits()
        autoStore = savedAutoStore
    end)
end)
btnRescan.MouseButton1Click:Connect(function()
    if not isScanning then task.spawn(buildQueue) end
end)

btnCopy.MouseButton1Click:Connect(function()
    if foundCode then
        pcall(function() setclipboard(foundCode) end)
        btnCopy.Text = "Copied!"; task.delay(2, function() btnCopy.Text = "Copy Code" end)
    end
end)

btnJoinMan.MouseButton1Click:Connect(function()
    local code = codeBox.Text
    if code ~= "" then
        forceStatus("Joining...", COL.purple)
        pcall(function() TeleportService:TeleportToPlaceInstance(PlaceID, code, lp) end)
    else forceStatus("Enter code!", COL.red) end
end)

btnResetVisited.MouseButton1Click:Connect(function()
    visitedServers = {}
    local ok, err = pcall(function() writefile(VISITED_FILE, "[]") end)
    if ok then log("Visited reset!") else log("Visited reset (file error: " .. tostring(err) .. ")") end
end)

btnClearMem.MouseButton1Click:Connect(function()
    serverMemory = {}
    local ok, err = pcall(function() writefile(MEMORY_FILE, "[]") end)
    if ok then log("Memory cleared!") else log("Memory clear (file error: " .. tostring(err) .. ")") end
end)

btnCopyJob.MouseButton1Click:Connect(function()
    pcall(function() setclipboard(game.JobId) end)
    btnCopyJob.Text = "Copied!"; task.delay(2, function() btnCopyJob.Text = "Copy JobId" end)
end)

btnPromoteNow.MouseButton1Click:Connect(function()
    local p = promoteFromWatch()
    if p > 0 then
        log("Manual promote: " .. p .. " servers")
        pcall(function() setQueueInfo(serverQueue) end)
    else
        log("No watch list servers ready yet")
    end
    pcall(function() setWatchInfo(watchList) end)
end)

btnClearWatch.MouseButton1Click:Connect(function()
    watchList = {}
    saveWatchList()
    log("Watch list cleared!")
    pcall(function() setWatchInfo(watchList) end)
end)

task.spawn(function()
    local lastCode = nil
    while true do
        local timers = readTimers()
        local hdTag = timers.hd and " [HD!]" or ""
        timerLbl.Text = "Timer: SK=" .. timers.skRaw .. hdTag
        statsLbl.Text = "S:" .. totalScans .. " H:" .. totalHops .. " Q:" .. #serverQueue .. " W:" .. #watchList
        if foundCode ~= lastCode then
            lastCode = foundCode
            if foundCode then codeLbl.Text = foundCode; btnCopy.Visible = true end
        end
        pcall(function() setWatchInfo(watchList) end)
        task.wait(2)
    end
end)

-- ═══════════════════════════════════════════════════════════════════
--  START
-- ═══════════════════════════════════════════════════════════════════
loadConfig()
loadVisited()
loadMemory()
loadWatchList()

if _configLoaded then
    log("Config v23 loaded: hunt=" .. tostring(autoHunt) .. " fight=" .. tostring(autoFight) .. " store=" .. tostring(autoStore) .. " hd=" .. tostring(hydraOnly))
else
    log("Fresh v23 start — defaults: hunt=ON fight=ON store=OFF hd=ON")
    saveConfig()
end

huntToggle.setState(autoHunt)
fightToggle.setState(autoFight)
storeToggle.setState(autoStore)
hdOnlyToggle.setState(hydraOnly)

isRunning = true
log("States: autoHunt=" .. tostring(autoHunt) .. " autoFight=" .. tostring(autoFight) .. " isRunning=true")

task.spawn(function()
    while isRunning do
        local ok, err = pcall(mainLoop)
        if not ok then
            log("LOOP ERROR: " .. tostring(err))
            print("[v23] MAIN LOOP ERROR: " .. tostring(err))
            task.wait(3)
        end
    end
end)
task.spawn(startChestScanTask)
task.spawn(checkPreSpawnedChest)
task.spawn(startWatchChecker)
startFruitWatcher()
if autoStore then task.spawn(autoStoreFruits) end

setStatus("v23 ready!", COL.green, 3)
log("v23 active! Tap BD to open. Hunt=" .. (autoHunt and "ON" or "OFF"))
print("[BossDetector v23] Active. Adaptive hunting enabled.")
