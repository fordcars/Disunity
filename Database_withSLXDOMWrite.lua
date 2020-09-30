-- Get directory of current running Lua file:
-- (from https://stackoverflow.com/questions/9145432/load-lua-files-by-relative-path)
local currentDir = (...):match("(.-)[^%.]+$")
local GlobalDefs = require(currentDir .. "GlobalDefs")
local xml2lua = require(currentDir .. "lib.xml2lua.xml2lua")
local xml2luaHandler = require(currentDir .. "lib.xml2lua.xmlhandler.tree")
local SLAXML = require(currentDir .. "lib.SLAXML.slaxdom")

-- Lua table to Xml: when there is no key associated with a subtable,
-- it is assumed to be an instance of the parent tag (multiplying
-- the number of times the parent tag will appear in the Xml).
-- If there is a key for a subtable, that key becomes a new tag.

local Database = {} -- Module

-- Equivalent to Database.new = function () ...
-- The 'local' keyword affects the function name, which makes no sense
-- in this case.
function Database.new()
	-- This method of creating a class in Lua is simple and allows
	-- private members, but may use resources unecessarily.
	local I = {} -- Interface, returned to the user

	local mBuffer = {} -- Main data buffer

-------------
-- PRIVATE --
-------------

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

	-- Looks for a key in an array. If it doesn't exist, create it.
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

	local function createSLAXDOMTextNode(value)
		local textNode = {}
		textNode.type = "text"
		textNode.name = "#text"
		textNode.cdata = false
		textNode.value = value
		-- 'parent' attribute not needed; we are making a 'simple' DOM.
		-- Check SLAXML documentation for 'simple' DOM.

		return textNode
	end

	local function createSLAXDOMElement(name, kids)
		local element = {}
		element.type = "element"
		element.name = name
		element.attr = {}
		element.kids = kids
		-- 'parent' and 'el' attributes not needed; we are making a 'simple' DOM.
		-- Check SLAXML documentation for 'simple' DOM.

		return element
	end

	-- Get a SLAXDOM object from buffer to give to SLAXML when converting to XML.
	-- This assumes that under any table having string keys, there is either
	-- a table having number keys, or an empty table.
	-- 'buffer' is a table of tags.
	-- If isTopLevel is true, will insert the global tag at the top level of the SLAXDOM.
	-- Returns SLAXDOM,errmsg. If it was a success, errmsg will be nil.
	local function bufferToSLAXDOM(buffer, isTopLevel)
		local dom = {}

		for elementName,instances in pairs(buffer) do
			if(type(elementName) == "string") then
				if(type(instances) ~= "table") then
					return dom, "Could not convert key '" .. elementName ..
						"' to SLAXDOM: associated value is not a subarray of instances! " ..
						"Buffer may be corrupt."
				end

				-- We assume the sub-array will have number keys (we are now
				-- iterating through instances of 'elementName')!
				for index,instance in pairs(instances) do
					-- Simple check incase we messed up
					if(type(index) ~= "number") then
						return dom, "Could not convert key '" .. elementName ..
						"' to SLAXDOM: " .. "subkey '" .. index .. "' is " ..
						"not a number! Buffer may be corrupt."
					end

					-- We have a number key! Time to create another element of
					-- type 'elementName', and populate it with either a text, or a table
					-- of children elements.
					-- Remember, we are currently iterating through instances of 'elementName'!

					local newElement = {}
					if(type(instance) == "string") then
						-- We have a string! Create a text node.
						local textNode = createSLAXDOMTextNode(instance)

						-- Then, create a new 'elementName' element to hold our text node.
						-- If there is a text node, this text node will be the
						-- only child of this new 'elementName' element.
						newElement = createSLAXDOMElement(elementName, {textNode})
					elseif(type(instance) == "number") then
						-- Also create a text node if we have a number.
						local textNode = createSLAXDOMTextNode(tostring(instance))

						-- Then, create a new 'elementName' element to hold our text node.
						newElement = createSLAXDOMElement(elementName, {textNode})
					elseif(type(instance) == "table") then
						-- We have a bunch of children! We give kids
						-- directly to a new 'elementName' parent element.
						local kids, errmsg = bufferToSLAXDOM(instance) -- Create children DOM elements.

						if(errmsg ~= nil and errmsg ~= "") then
							return dom, errmsg
						else
							-- Create our new element instance.
							newElement = createSLAXDOMElement(elementName, kids)
						end
					end

					table.insert(dom, newElement)
				end
			else
				-- Key is not a string! Should not happen, since arrays with number keys
				-- are always subarrays of arrays containing string keys, which are
				-- processed above.
				return dom, "Could not convert key '" .. elementName .. "' to SLAXDOM: " ..
					"this key must be a string! Buffer may be corrupt."
			end
		end

		-- Add global tag to DOM if we are the top level.
		if(isTopLevel == true) then
			dom = createSLAXDOMElement(GlobalDefs.globalTag, dom)
		end

		return dom, nil
	end

-------------
-- PUBLIC --
-------------

	-- Returns false on error
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
			Utils.warn("Could not parse database file '" .. path .. "'! File empty.")
			return false
		end

		local parser = xml2lua.parser(xml2luaHandler)
		parser:parse(contents)
		mBuffer = xml2luaHandler.root -- Uses the 'Database' closure instead of 'self'.

		-- Make sure our buffer is always valid, just in-case.
		if(mBuffer == nil) then
			mBuffer = {}
			Utils.warn("Parsing database file '" .. path .. "' returned nil object!")
			return false
		end

		-- Look for global tag. Must only be one global tag in the file.
		if(mBuffer[GlobalDefs.globalTag] == nil) then
			Utils.warn("Could not parse database file '" .. path .. "'! Global tag '<" ..
				GlobalDefs.globalTag .. ">' missing.")
			mBuffer = {} -- Remove whatever we read, probably garbage (wrong XML file?).
			return false
		end

		-- Remove reference to global tag (buffer doesn't include it for ease of use).
		mBuffer = mBuffer[GlobalDefs.globalTag]

-------------------		cleanXMLTable(mBuffer)
	end

	function I.writeToDisk(path)
		-- Generate SLAXDOM
		local generatedDOM, errmsg = bufferToSLAXDOM(mBuffer, true)
		if(errmsg ~= nil) then
			Utils.warn("Could not write database to disk! SLAXDOM generation error:\n" .. errmsg)
		end

		-- Generate XML
		local generatedXml = SLAXML:xml(generatedDOM, {
			indent = 4 -- Each tag will be on its own line with 2 space identation.
		})

		-- Write to file
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

	function I.addObjectGeometryGroup(path)
		makeSureKeyExists(mBuffer, "resources")
		-- Make sure it exists in the first (and only) 'resources' instance.
		makeSureKeyExists(mBuffer.resources[1], "objectGeometryGroup")

		-- Make sure we don't add the same one twice.
		-- Checks every instance of objectGeometryGroup for our path.
		-- (Note: there should always be only 1 'resources' tag instance)
		local objectGeometryGroupIndex, pathIndex =
			findValueInBufferTagInstances(mBuffer.resources[1].objectGeometryGroup, "path", path)
		if(objectGeometryGroupIndex ~= false and pathIndex ~= false) then
			Utils.warn("Cannot add ObjectGeometryGroup at '" .. path ..
				"': Resource already exists in database.")
			return
		end

		-- Append ObjectGeometryGroup entry
		local oGGEntry = {}
		oGGEntry.path = path

--table.insert(mBuffer.resources.objectGeometryGroup, oGGEntry)
	end

	function I.removeObjectGeometryGroup(path)
		makeSureKeyExists(mBuffer, "resources")
		-- Make sure it exists in the first (and hopefully only) 'resources' instance.
		makeSureKeyExists(mBuffer.resources[1], "objectGeometryGroup")
		
		-- Find resource
		-- Checks every instance of objectGeometryGroup for our path.
		-- (Note: there should always be only 1 resources tag)
		local objectGeometryGroupIndex, pathIndex =
			findValueInBufferTagInstances(mBuffer.resources[1].objectGeometryGroup, "path", path)
		if(objectGeometryGroupIndex ~= false and pathIndex ~= false) then
			table.remove(mBuffer.resources[1].objectGeometryGroup, objectGeometryGroupIndex)
		else
			Utils.warn("Cannot remove ObjectGeometryGroup at '" .. path ..
				"': Resource not found in database.")
		end
	end

	return I
end

return Database -- Module
