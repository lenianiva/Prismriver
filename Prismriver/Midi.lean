namespace Prismriver

@[extern "prismriver_mystery"]
opaque mystery : UInt8 → UInt8
@[extern "prismriver_ping"]
opaque ping : UInt8 → IO Unit
