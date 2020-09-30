-- Get directory of current running Lua file:
-- (from https://stackoverflow.com/questions/9145432/load-lua-files-by-relative-path)
local currentDir = (...):match("(.-)[^%.]+$")
local GlobalDefs = require(currentDir .. "GlobalDefs")

local TextRenderer = {} -- Module

-----------------
-- DEFINITIONS --
-----------------

------------
-- STATIC --
------------

function TextRenderer.new()
-------------
-- PRIVATE --
-------------

    local I = {} -- Interface, returned to the user

-------------
-- PUBLIC --
-------------

----------------------
-- Return interface --
----------------------
    return I
end

-------------------
-- Return module --
-------------------
return TextRenderer
