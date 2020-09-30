-- DEFAULT CBFG values for a good font:
---- Image: 1024x1024
---- 93x40 cells
---- Font size: 40

-- Notes:
--- * Filtering makes small texts look better, but also makes distant texts
--- dissapear sooner.
--- * Generally, 0.07 is the smallest size you can have without getting noticeable
--- quality loss.

-- Get directory of current running Lua file:
-- (from https://stackoverflow.com/questions/9145432/load-lua-files-by-relative-path)
local currentDir = (...):match("(.-)[^%.]+$")
local GlobalDefs = require(currentDir .. "GlobalDefs")

local TextDrawer = {} -- Module

-------------------------
-- USER DEFINED VALUES --
-------------------------

-- Font texture values
TextDrawer.TextureWidth = 1024
TextDrawer.TextureHeight = 1024
TextDrawer.TextureCellWidth = 40
TextDrawer.TextureCellHeight = 93

-----------------
-- DEFINITIONS --
-----------------

-- Cell width and height in UV coords instead of pixels:
TextDrawer.TextureUVCellWidth = TextDrawer.TextureCellWidth / TextDrawer.TextureWidth
TextDrawer.TextureUVCellHeight = TextDrawer.TextureCellHeight / TextDrawer.TextureHeight

TextDrawer.TextureCellAspectRatio = TextDrawer.TextureCellWidth / TextDrawer.TextureCellHeight

-- Normally ASCII value of ' ', the first character in the font texture.
TextDrawer.TextureFirstCharValue = string.byte(' ')

-- Number of chars per row.
TextDrawer.TextureRowLength = math.floor(TextDrawer.TextureWidth / TextDrawer.TextureCellWidth)

TextDrawer.LeftAligned = 1
TextDrawer.CenterAligned = 2
TextDrawer.RightAligned = 3

------------
-- STATIC --
------------

-- Holds 4 colors, used for text color.
local ColorsContainer = {}
function ColorsContainer.new(topLeft, bottomLeft, bottomRight, topRight)
    local colors = {}

    colors.topLeft = topLeft
    colors.bottomLeft = bottomLeft
    colors.bottomRight = bottomRight
    colors.topRight = topRight

    return colors
end

function ColorsContainer.clone(colorsContainer)
    local colorsClone = {}

    colorsClone.topLeft = colorsContainer.topLeft
    colorsClone.bottomLeft = colorsContainer.bottomLeft
    colorsClone.bottomRight = colorsContainer.bottomRight
    colorsClone.topRight = colorsContainer.topRight

    return colorsClone
end

-- Holds attributes for a text.
-- Useful for tracking!
local TextAttribs = {}
function TextAttribs.new()
    local attribs = {}

    -- Default values:
    attribs.string = ""

    attribs.shader = nil
    attribs.fontTexture = nil
    attribs.colors = ColorsContainer.new(
        Vec3(0, 0, 0),
        Vec3(0, 0, 0),
        Vec3(0, 0, 0),
        Vec3(0, 0, 0)
    )

    attribs.size = 1
    attribs.alignment = TextDrawer.LeftAligned

    attribs.is3D = false

    -- Since it comes from PhysicsBody, ALWAYS IN METERS.
    -- You have to take this into account when modifying TextAttribs directly.
    attribs.position = Vec3(0, 0, 0)
    attribs.rotation = Vec3(0, 0, 0)

    return attribs
end

function TextAttribs.clone(textAttribs)
    local attribsClone = {}

    -- In Lua, numbers and strings are deep-copied. Anything else is a
    -- shallow-copied (copies the reference instead of the value).
    attribsClone.string = textAttribs.string           -- Copy

    attribsClone.shader = textAttribs.shader           -- Reference
    attribsClone.fontTexture = textAttribs.fontTexture -- Reference
    attribsClone.colors = ColorsContainer.clone(textAttribs.colors)  -- Copy

    attribsClone.size = textAttribs.size               -- Copy
    attribsClone.alignment = textAttribs.alignment     -- Copy

    attribsClone.is3D = textAttribs.is3D               -- Copy
    attribsClone.position = GlobalDefs.cloneVec3(textAttribs.position) -- Copy
    attribsClone.rotation = GlobalDefs.cloneVec3(textAttribs.rotation) -- Copy

    return attribsClone
end

-- Generates a CCW quad geometry, used for drawing a single character.
-- Local origin is top left corner.
--
-- positionOffset: Vec3, offsets top-left corner
-- size: quad width
-- UVOffset: Vec2, offsets bottom-left corner (UV origin)
-- colors: color container for the single quad
local function generateQuadObjectGeometry(positionOffset, size, UVOffset, colors)
    -- Width will always be 'scaling', while height will be dependent of cell aspect ratio.
    local width = size
    local height = width / TextDrawer.TextureCellAspectRatio
    local positions = {
        Vec3.add(positionOffset, Vec3(0, 0, 0)),           -- Top left
        Vec3.add(positionOffset, Vec3(0, -height, 0)),     -- Bottom left
        Vec3.add(positionOffset, Vec3(width, -height, 0)), -- Bottom right
        Vec3.add(positionOffset, Vec3(width, 0, 0))        -- Top right
    }

    -- UVs have a bottom-left origin.
    -- (Note: they are set here as place-holders; they will be modified later.)
    local UVs = {
        Vec2.add(UVOffset, Vec2(0, TextDrawer.TextureUVCellHeight)), -- Top left
        Vec2.add(UVOffset, Vec2(0, 0)),                              -- Bottom left
        Vec2.add(UVOffset, Vec2(TextDrawer.TextureUVCellWidth, 0)),                             -- Bottom right
        Vec2.add(UVOffset, Vec2(TextDrawer.TextureUVCellWidth, TextDrawer.TextureUVCellHeight)) -- Top right
    }

    local normals = {
        colors.topLeft,      -- Top left
        colors.bottomLeft,   -- Bottom left
        colors.bottomRight,  -- Bottom right
        colors.topRight      -- Top right
    }

    -- 0-based, of course:
    local indices = {
        0, 1, 3,          -- Top left, bottom left, top right
        1, 2, 3           -- Bottom left, bottom right, top right
    }

    return ObjectGeometry("Quad", indices, positions, UVs, normals)
end

-- Returns the Vec2 at the bottom left corner of the specified char in the
-- font texture.
local function getUVOffsetFromChar(char)
    local charValue = string.byte(char)
    -- Calculate char index (linear form of char matrix, 0-based):
    local charIndex = charValue - TextDrawer.TextureFirstCharValue

    -- 0-based for simplicity:
    local row = math.floor(charIndex / TextDrawer.TextureRowLength)
    local col = charIndex - row*TextDrawer.TextureRowLength

    return Vec2(
        col*TextDrawer.TextureUVCellWidth, -- X
        1 - row*TextDrawer.TextureUVCellHeight - TextDrawer.TextureUVCellHeight -- Y
    )
end

-- Creates a new text with specified attribs, and adds it to the game.
-- If is3D is false, will draw text directly onto the screen using x and y
-- coords between -1 and 1. In this case, only the z-axis rotation will be
-- taken into account.
-- If is3D is true, will draw text in 3D space.
--
-- When creating a gradient with text colors, keep in mind that the colors are the
-- same accross all char quads. This means the gradient effect will be for each
-- individual character instead of accross the entire text.  
--
-- Returns a reference to the new text.
local function drawTextFromAttribs(attribs)
    local newText = {} -- Array of objects (quads + TextAttribs)
    local length = string.len(attribs.string)

    local game = getGame()

    -- Calculate alignment
    local alignmentOffset = 0
    if(attribs.alignment == TextDrawer.LeftAligned) then
        alignmentOffset = 0
    elseif(attribs.alignment == TextDrawer.CenterAligned) then
        -- Character (quad) width is always equal to size.
        alignmentOffset = (attribs.size * length)/2
    elseif(attribs.alignment == TextDrawer.RightAligned) then
        alignmentOffset = attribs.size * length
    else
        Utils.warn("Invalid alignment when drawing text '" .. attribs.string .. "'!")
    end

    for i=1,length do
        local char = string.sub(attribs.string, i, i)

        -- Generate quad object geometry for each object (to enable us to modify each
        -- object individually):
        local quadObjectGeometry = generateQuadObjectGeometry(
            Vec3((i - 1)*attribs.size - alignmentOffset, 0, 0),
            attribs.size,
            getUVOffsetFromChar(char),
            attribs.colors
        )

        -- Create our object!
        -- ShadedObject to be able to give normals (which are colors in our case).
        local quad = ShadedObject(quadObjectGeometry, attribs.shader, attribs.fontTexture,
            true, PhysicsBodyType.Ignored)

        -- Set rotation and position
        quad:getPhysicsBody():setPosition(attribs.position)

        -- Limit rotations if we are dealing with 2D text:
        if(attribs.is3D) then
            quad:getPhysicsBody():setRotation(attribs.rotation)
        else
            quad:getPhysicsBody():setRotation(Vec3(
                0,
                0,
                -- In the shader, the z coord is perpendicular to the screen
                attribs.rotation.z
            ))
        end

        table.insert(newText, quad) -- Keep a reference of the new (Lord) char quad
        game:getEntityManager():addObject(quad) -- ... and add it to the game!
    end

    -- Copy attribs to our new text!
    newText.attribs = TextAttribs.clone(attribs)

    return newText -- Return reference
end

-- Must specify a compliant shader and font texture!
function TextDrawer.new(shader, fontTexture)

-------------
-- PRIVATE --
-------------

    local I = {} -- Interface, returned to the user

    -- Keep track of our text attribs state. These will be copied to new texts for ease of use.
    local mTextAttribs = TextAttribs.new()
    mTextAttribs.shader = shader           -- Current shader
    mTextAttribs.fontTexture = fontTexture -- Current font texture

    -- Tracking table (references to all texts).
    -- A text is a table of quads for each character. A text table also has
    -- an ["attribs"] entry, holding the current attributes for the text.
    -- Modifying the text quads directly without modifying the .attribs
    -- will result in inconsistency when regenerating a string is necessary.
    local mTexts = {}

-------------
-- PUBLIC --
-------------

    -- Relatively heavy: will regenerate the specified text.
    -- This is useful for when you change text attribs manually.
    function I.regenerateText(index)
        -- Save attribs from the text we are about to delete.
        local attribs = mTexts[index].attribs -- No need to clone

        I.deleteText(index) -- Removes from game and from tracking table.
        local newText = drawTextFromAttribs(attribs)

        -- Track our new text using the same index (useful for user):
        if(index == #mTexts+1) then
            -- We deleted the last text
            table.insert(mTexts, newText)
        else
            -- We deleted somewhere in the middle
            table.insert(mTexts, index, newText)
        end
    end

    function I.getText(index)
        return mTexts[index]
    end

    -- Removes a text from the game and from our tracking table.
    function I.deleteText(index)
        -- First, we must remove all char quads from the game.
        -- Using a numeric loop to avoid getting the ["attribs"] entry:
        for quadIndex=1,#(mTexts[index]) do
            getGame():getEntityManager():removeObject(mTexts[index][quadIndex])
        end

        -- Remove text from our tracking table.
        table.remove(mTexts, index)
    end

    function I.getNumberOfTexts()
        return #mTexts
    end

-- String
    -- Returns string of specified text.
    function I.getTextString(index)
        return mTexts[index].attribs.string
    end

    -- Heavy!! Will regenerate text.
    -- Changes string of specified text.
    function I.changeTextString(index, newString)
        mTexts[index].attribs.string = newString
        I.regenerateText(index)
    end

-- Shader
    -- Set the shader to use for the subsequent texts.
    function I.setShader(shader)
        mTextAttribs.shader = shader
    end

    function I.getShader()
        return mTextAttribs.shader
    end

    function I.setTextShader(index, shader)
        for i,quad in ipairs(mTexts[index]) do
            quad:setShader(shader)
        end

        -- Update attribs
        mTexts[index].attribs.shader = shader
    end

    function I.getTextShader(index)
        return mTexts[index].attribs.shader
    end

-- Font
    -- Set the font to use for the subsequent texts.
    function I.setFont(fontTexture)
        mTextAttribs.fontTexture = fontTexture
    end

    function I.getFont()
        return mTextAttribs.fontTexture
    end

    function I.setTextFont(index, fontTexture)
        for i,quad in ipairs(mTexts[index]) do
            quad:setTexture(fontTexture)
        end

        -- Update attribs
        mTexts[index].attribs.fontTexture = fontTexture
    end

    function I.getTextFont(index)
        return mTexts[index].attribs.fontTexture
    end

-- Color
    -- Sets the colors of the 4 corners of texts.
    -- Useful for gradients!
    function I.setColors(topLeftColor, bottomLeftColor, bottomRightColor, topRightColor)
        mTextAttribs.colors = ColorsContainer.new(
            topLeftColor, bottomLeftColor, bottomRightColor, topRightColor)
    end

    -- Sets a single color for texts.
    function I.setColor(color)
        mTextAttribs.colors = ColorsContainer.new(
            color, color, color, color)
    end

    -- Returns a ColorsContainer
    function I.getColors()
        return mTextAttribs.colors
    end

    -- Heavy! Regenerates the text.
    -- Sets the colors of the 4 corners of the specified text.
    function I.changeTextColors(index, topLeftColor, bottomLeftColor, bottomRightColor, topRightColor)
        mTexts[index].attribs.colors = ColorsContainer.new(
            topLeftColor, bottomLeftColor, bottomRightColor, topRightColor)
    end

    -- Heavy! Regenerates the text.
    -- Sets the specified text a single color.
    function I.changeTextColor(index, color)
        mTexts[index].attribs.colors = ColorsContainer.new(color, color, color, color)
    end

    -- Returns a ColorsContainer.
    function I.getTextColors(index)
        return mTexts[index].attribs.colors
    end

-- Position
    -- If we are in 2D, position is in pixels for ease of use.
    -- position is always a Vec3 for consistency.
    function I.setTextPosition(index, position)
        local positionInMeters = 0

        if(mTexts[index].attribs.is3D) then
            positionInMeters = position

            for i,quad in ipairs(mTexts[index]) do
                quad:getPhysicsBody():setPosition(positionInMeters)
            end
        else
            -- If in 3D, we gave a position in pixels, not meters!
            positionInMeters = GlobalDefs.pixelsToMeters(position)

            -- Only set x and y coords!
            for i,quad in ipairs(mTexts[index]) do
                quad:getPhysicsBody():setPosition(Vec3(positionInMeters.x, positionInMeters.y, 0))
            end
        end

        -- Update attribs
        mTexts[index].attribs.position = positionInMeters
    end

    -- If we are in 2D, position is in pixels for ease of use.
    -- Always returns a Vec3.
    function I.getTextPosition(index)
        if(mTexts[index].attribs.is3D) then
            return mTexts[index].attribs.position
        else
            -- If in 2D, we want pixels!
            return GlobalDefs.metersToPixels(mTexts[index].attribs.position)
        end
    end

-- Rotation
    function I.setTextRotation(index, rotation)
        for i,quad in ipairs(mTexts[index]) do
            if(mTexts[index].attribs.is3D) then
                quad:getPhysicsBody():setRotation(rotation)
            else
                --If 2D text, only set z-axis rotation!
                quad:getPhysicsBody():setRotation(Vec3(0, 0, rotation.z))
            end
        end

        -- Update attribs
        mTexts[index].attribs.rotation = rotation
    end

    function I.getTextRotation(index)
        -- Should be the same for all quads in this text.
        return mTexts[index].attribs.rotation
    end

-- Size
    -- Set the size to use for the subsequent texts.
    function I.setSize(size)
        mTextAttribs.size = size
    end

    function I.getSize()
        return mTextAttribs.size
    end

    function I.getTextSize(index)
        return mTexts[index].attribs.size
    end

    -- Heavy!! Will regenerate text.
    function I.changeTextSize(index, size)
        mTexts[index].attribs.size = size
        I.regenerateText(index)
    end

-- Alignment
    -- Set the alignment to use for the subsequent texts.
    function I.setAlignment(alignment)
        mTextAttribs.alignment = alignment
    end

    function I.getAlignment()
        return mTextAttribs.alignment
    end

    -- Creates a new text.
    -- If we are not in 3D, position is in pixels.
    -- Returns the index of the newly drawn text.
    function I.drawText(string, position, rotation, is3D)
        local newAttribs = TextAttribs.clone(mTextAttribs)

        -- Update our text attribs with the arguments:
        newAttribs.string = string
        newAttribs.rotation = rotation
        newAttribs.is3D = is3D

        -- Calculate position in meters:
        if(newAttribs.is3D) then
            newAttribs.position = position
        else
            -- If 2D text, we gave a position in pixels! We need to convert it to meters.
            newAttribs.position = GlobalDefs.pixelsToMeters(position)
        end

        -- ... and create (and track) our new text!
        table.insert(mTexts, drawTextFromAttribs(newAttribs))
        return #mTexts -- Index of new text
    end

----------------------
-- Return interface --
----------------------
    return I
end

-------------------
-- Return module --
-------------------
return TextDrawer
