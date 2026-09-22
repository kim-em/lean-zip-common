module

import ZipCommon

/-! Check the API through the root module, using only exported declarations. -/

example (v : UInt64) : Binary.readUInt64LE (Binary.writeUInt64LE v) 0 = v :=
  Binary.readUInt64LE_writeUInt64LE v

example (v : UInt16) : (Binary.writeUInt16LE v).size = 2 := rfl

example (br : ZipCommon.BitReader) : br.bitPos = br.pos * 8 + br.bitOff := rfl

example (br : ZipCommon.BitReader) : br.readBits 0 = .ok (0, br) := rfl

example (br : ZipCommon.BitReader) (acc : UInt32) (shift : Nat) :
    ZipCommon.BitReader.readBits.go br acc shift 0 = .ok (acc, br) := rfl

example (br br' : ZipCommon.BitReader) (n : Nat) (v : UInt32)
    (h : br.readBits n = .ok (v, br')) : br'.data = br.data :=
  ZipCommon.readBits_data_eq br br' n v h

-- The simp attribute must also survive the public import chain.
example (v : UInt32) : (Binary.writeUInt32LE v).size = 4 := by simp

example : IO.FS.Handle → UInt64 → IO Unit := Handle.seek
example : IO.FS.Handle → IO UInt64 := Handle.fileSize
example : String → String → IO Unit := Handle.createSymlink
