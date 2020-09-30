-- For global definitions
local GlobalDefs = {}

-- This value is only accessible in later SDL3D versions.
GlobalDefs.pixelsPerMeter = 10

-- Helper functions
function GlobalDefs.pixelsToMeters(vec3)
    return Vec3.scalarDiv(vec3, GlobalDefs.pixelsPerMeter)
end

function GlobalDefs.metersToPixels(vec3)
    return Vec3.scalarMul(vec3, GlobalDefs.pixelsPerMeter)
end

function GlobalDefs.cloneVec2(vec)
    return Vec2(vec.x, vec.y)
end

function GlobalDefs.cloneVec3(vec)
    return Vec3(vec.x, vec.y, vec.z)
end

function GlobalDefs.cloneVec4(vec)
    return Vec4(vec.x, vec.y, vec.z, vec.w)
end


return GlobalDefs
