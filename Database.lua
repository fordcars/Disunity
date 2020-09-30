-- Notes:
---- Paths are used as unique identifiers for resources.

-- Get directory of current running Lua file:
-- (from https://stackoverflow.com/questions/9145432/load-lua-files-by-relative-path)
local currentDir = (...):match("(.-)[^%.]+$")
local GlobalDefs = require(currentDir .. "GlobalDefs")
local xml2lua = require(currentDir .. "lib.xml2lua.xml2lua")
local xml2luaHandler = require(currentDir .. "lib.xml2lua.xmlhandler.tree")

-- Note on xml2lua.toXml(): when there is no key associated with a subtable,
-- it is assumed to be an instance of the parent tag (multiplying
-- the number of times the parent tag will appear in the XML).
-- If there is a key for a subtable, that key becomes a new tag.

local Database = {} -- Module

-----------------
-- DEFINITIONS --
-----------------

Database.GlobalTag = "Disunity"

------------
-- STATIC --
------------

-- Creates a human-readable string from an array. Useful for debugging.
-- From https://stackoverflow.com/questions/9168058/how-to-dump-a-table-to-console
local function arrayToString(o)
    if type(o) == 'table' then
        local s = '{ '
        for k,v in pairs(o) do
            if type(k) ~= 'number' then k = '"'..k..'"' end
            s = s .. '['..k..'] = ' .. arrayToString(v) .. ','
        end
        return s .. '} '
    else
        return tostring(o)
    end
end

-- Returns true if a non-number key is found, false otherwise.
local function arrayIsMap(array)
    for k,v in pairs(array) do
        if(type(k) ~= "number") then
            -- We are dealing with a map!
            return true
        end
    end
    return false -- This array is not a map.
end

-- Looks for a key in an array. If it doesn't exist, create it (modifies array).
-- "Or as some people like to put it; all types are passed by value,
-- but function, table, userdata and thread are reference types."
-- Quote from https://stackoverflow.com/questions/6128152/function-variable-scope-pass-by-value-or-reference.
local function makeSureKeyExists(array, keyString)
    if(array[keyString] == nil) then
        -- Not found, so create it
        array[keyString] = {}
    end
end

-- Returns the key of the first instance of 'value', or false if nothing was found.
local function findValueInArray(array, value)
    for k,v in pairs(array) do
        if(v == value) then
            return k
        end
    end
    
    return false
end

-- Garantees at least 1 instance of the tag exists within tagInstances.
-- Modifies tagInstances.
local function makeSureInstanceOfTagExists(tagInstances)
    if(#tagInstances == 0) then
        table.insert(tagInstances, {})
    end
end

-- Will search through parentTagInstances for an instance of valueTag:value.
-- Will only search one level below parentTag.
-- If found, returns the index of the parentTag instance containing the valueTag:value,
-- and the index of the valueTag instance within the parent tag.
-- Returns false, false if nothing is found.
local function findValueInBufferTagInstances(parentTagInstances, valueTagName, value)
    for parentTagInstanceIndex,parentTagInstance in pairs(parentTagInstances) do
        -- Sanity check
        if(type(parentTagInstanceIndex) ~= "number") then
            Utils.warn("Could not look for value tag '" .. valueTagName ..
                "' and value '" .. value .. "' in parent tag instances: " ..
                "Parent tag instances do not have number keys! Make sure you are " ..
                "giving a table of instances of a buffer tag!")
            return false, false
        end

        -- If, within the tag instance, our valueTag exists, we must check all instances
        -- of said valueTag:
        local valueTagInstances = parentTagInstance[valueTagName]
        if(type(valueTagInstances) == "table") then
            for valueTagInstanceIndex,valueTagInstance in pairs(valueTagInstances) do
                -- Sanity check
                if(type(valueTagInstanceIndex) ~= "number") then
                    Utils.warn("Could not look for value tag '" .. valueTagName ..
                        "' and value '" .. value .. "' in buffer tag instances: " ..
                        "Value tag instances do not have number keys! Possible " ..
                        "buffer corruption?")
                    return false, false
                end

                if(valueTagInstance == value) then
                    -- We found our value!!
                    return parentTagInstanceIndex, valueTagInstanceIndex
                end
            end
        end
    end

    return false, false
end

-- Always call after reading database file with xml2lua!
--
-- Normally, an XML tag is an array of instances. However, if there is only
-- one instance, xml2Lua sets this tag as the instance itself. We have
-- to change that back into an array of instances for consistency.
-- In this function, when a tag is found, it makes sure its value
-- is an array of instances (even when singular), aka an array containing numerical keys!
--
-- Note: this function assumes the XML database does not contain tags parsed as actual numbers!
local function cleanXMLTable(table)
    for k,v in pairs(table) do
        -- Clean children first!
        if(type(v) == "table") then
            cleanXMLTable(v)
        end

        if(type(k) ~= "number") then
            -- We found a tag! Make sure it points to an array
            -- containing number keys (instances)!
            -- Note: "Boolean statements execute left to right until the result is inevitable."
            -- from http://www.troubleshooters.com/codecorn/lua/luaif.htm
            -- This enters the if-scope if we are dealing with either a literal or a map.
            -- If it is a map, we are dealing with an object instance. Wether we are dealing
            -- with a literal or object instance, we must make sure we have a subarray for it!
            if(type(v) ~= "table" or (type(v) == "table" and arrayIsMap(v))) then
                -- The tag does not contain a subarray of instances, but instead
                -- contains a single instance directly! Lets create a subarray to
                -- contain this instance.
                table[k] = {v} -- Was table[k] = v, now is table[k] = {v}.
            end
        end -- Do nothing if we have a numerical key.
    end        
end

-- Equivalent to Database.new = function () ...
-- Note: the 'local' keyword affects the function name variable, which
-- would make no sense in this case.
function Database.new()
-------------
-- PRIVATE --
-------------

    -- This method of creating a class in Lua is simple and allows
    -- private members, but may use resources unecessarily when copied.
    local I = {} -- Interface, returned to the user

    local mBuffer = {} -- Main data buffer

    -- Add resource of type resourceTypeName to the buffer.
    local function addResource(resourceTypeName, path)
        makeSureKeyExists(mBuffer, "Resources")
        makeSureInstanceOfTagExists(mBuffer.Resources)

        -- Make sure the resource type exists in the first (and only) 'Resource' instance.
        makeSureKeyExists(mBuffer.Resources[1], resourceTypeName)

        -- Make sure we don't add the same one twice.
        -- Checks every instance of resourceTypeName for our path.
        -- (Note: there should always be only 1 'Resources' tag instance)
        local resourceInstanceIndex, pathIndex =
            findValueInBufferTagInstances(mBuffer.Resources[1][resourceTypeName], "Path", path)
        if(resourceInstanceIndex ~= false and pathIndex ~= false) then
            Utils.warn("Cannot add " .. resourceTypeName .. " at '" .. path ..
                "': Resource already exists in database.")
            return
        end

        -- Append resource instance.
        local newInstance = {}
        newInstance.Path = {path} -- Path instances.

        table.insert(mBuffer.Resources[1][resourceTypeName], newInstance)
    end

    -- Remove resource of type resourceTypeName from the buffer using its path.
    -- Returns true on success, false on failure.
    local function removeResource(resourceTypeName, path)
        makeSureKeyExists(mBuffer, "Resources") -- For safety; this should always exist anyways.
        makeSureInstanceOfTagExists(mBuffer.Resources) -- So should this.

        -- Check if the resource type even exists in the buffer.
        if(mBuffer.Resources[1][resourceTypeName] ~= nil) then
            -- Find resource:
            -- Checks every instance of resourceTypeName for our path.
            -- (Note: there should always be only 1 'Resources' tag)
            local resourceInstanceIndex, pathIndex =
                findValueInBufferTagInstances(mBuffer.Resources[1][resourceTypeName], "Path", path)

            if(resourceInstanceIndex ~= false and pathIndex ~= false) then
                table.remove(mBuffer.Resources[1][resourceTypeName], resourceInstanceIndex)
                return true
            end
        end

        Utils.warn("Cannot remove " .. resourceTypeName .. " at '" .. path ..
                "': Resource not found in database.")
        return false
    end

-------------
-- PUBLIC --
-------------

    -- Returns true on success, false otherwise.
    -- Since we use closures and not 'self', we don't need the ':' syntax for methods.
    function I.readFromDisk(path)
        local file, err = io.open(path, "r")
        if(file == nil) then
            Utils.warn("Could not read database file '" .. path ..
                "'! Error msg: '" .. err .. "'")
            return false
        end

        io.input(file)
        local contents = io.read("*all")
        io.close(file)

        -- Check if contents are empty. This check is not done by xml2lua.
        if(string.len(contents) == 0) then
            Utils.warn("Could not parse database file '" .. path .. "': File empty!")
            -- Do not modify mBuffer.
            return false
        end

        local parser = xml2lua.parser(xml2luaHandler)
        parser:parse(contents)
        mBuffer = xml2luaHandler.root -- Uses the 'Database' closure instead of 'self'.

        -- Make sure our buffer is always valid, just in-case.
        if(mBuffer == nil) then
            mBuffer = {}
            Utils.warn("Could not parse database file '" .. path .. "': Parsing returned nil object!")
            return false
        end

        -- Look for global tag. Must only be one global tag in the file.
        if(mBuffer[Database.GlobalTag] == nil) then
            Utils.warn("Could not parse database file '" .. path .. "': Global tag '<" ..
                Database.GlobalTag .. ">' missing!")
            mBuffer = {} -- Remove whatever we read, probably garbage (wrong XML file?).
            return false
        end

        -- Remove reference to global tag (buffer doesn't include it for ease of use).
        mBuffer = mBuffer[Database.GlobalTag]

        -- Important! Clean buffer returned by xml2lua.
        cleanXMLTable(mBuffer)

        return true
    end

    function I.writeToDisk(path)
        -- Generate XML
        local generatedXml = xml2lua.toXml(mBuffer, Database.GlobalTag) ..
            -- Work around bug in xml2lua v1.4-2, see: https://github.com/manoelcampos/xml2lua/issues/50
            "\n</" .. Database.GlobalTag .. ">"

        -- Write to file (overwrite all)
        local file, err = io.open(path, "w+")
        if(file == nil) then
            Utils.warn("Could not open file '" .. path ..
                "' for writing database! Error msg: '" .. err .. "'")
            return false, err
        end

        io.output(file)
        io.write(generatedXml)
        io.close(file)
    end

    -- Please don't modify the buffer directly! Use database functions instead, thanks.
    function I.getBuffer()
        return mBuffer -- This is a reference, but I wish this returned a const reference.
    end

------------
-- Shader --
------------

    function I.addShader(vertexShaderPath, fragmentShaderPath)
        addResource("VertexShader", vertexShaderPath)
        addResource("FragmentShader", fragmentShaderPath)
    end

    function I.removeShader(vertexShaderPath, fragmentShaderPath)
        removeResource("VertexShader", vertexShaderPath)
        removeResource("FragmentShader", fragmentShaderPath)
    end

    -- Both shader paths must already exist in the database to get a shader back.
    -- Returns VertexShader,FragmentShader tag references, or false,false if not found.
    function I.findShader(vertexShaderPath, fragmentShaderPath)
        local vertexIndex =
            findValueInBufferTagInstances(mBuffer.Resources[1].VertexShader, "Path", vertexShaderPath)

        local fragmentIndex =
            findValueInBufferTagInstances(mBuffer.Resources[1].FragmentShader, "Path", fragmentShaderPath)

        return mBuffer.Resources[1].VertexShader[vertexIndex], mBuffer.Resources[1].FragmentShader[fragmentIndex]
    end

-------------
-- Texture --
-------------

    function I.addTexture(path)
        addResource("Texture", path)
    end

    function I.removeTexture(path)
        removeResource("Texture", path)
    end

    -- Returns a reference to the Texture tag within the buffer, or false if not found.
    function I.findTexture(texturePath)
        local index =
            findValueInBufferTagInstances(mBuffer.Resources[1].Texture, "Path", texturePath)
        return mBuffer.Resources[1].Texture[index]
    end

-------------------------
-- ObjectGeometryGroup --
-------------------------

    function I.addObjectGeometryGroup(path)
        addResource("ObjectGeometryGroup", path)
    end

    function I.removeObjectGeometryGroup(path)
        removeResource("ObjectGeometryGroup", path)
    end

    -- Returns a reference to the ObjectGeometryGroup tag within the buffer, or false if not found.
    function I.findObjectGeometryGroup(objectGeometryGroupPath)
        local index =
            findValueInBufferTagInstances(mBuffer.Resources[1].ObjectGeometryGroup, "Path", objectGeometryGroupPath)
        return mBuffer.Resources[1].ObjectGeometryGroup[index]
    end

-----------
-- Sound --
-----------

    function I.addSound(path)
        addResource("Sound", path)
    end

    function I.removeSound(path)
        removeResource("Sound", path)
    end

    -- Returns a reference to the Sound tag within the buffer, or false if not found.
    function I.findSound(soundPath)
        local index =
            findValueInBufferTagInstances(mBuffer.Resources[1].Sound, "Path", soundPath)
        return mBuffer.Resources[1].Sound[index]
    end


----------------------
-- Return interface --
----------------------
    return I
end

-------------------
-- Return module --
-------------------
return Database
