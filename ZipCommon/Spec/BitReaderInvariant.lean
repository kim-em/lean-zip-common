import ZipCommon.BitReader

/-!
# BitReader invariant preservation (generic)

Generic properties of `BitReader.readBit` and `BitReader.readBits`:
- Data preservation
- Position invariant (`bitOff = 0 ∨ pos < data.size`)
- `bitPos` advancement (readBit by 1, readBits by n)
- `pos ≤ data.size` bounds

These are characterizing properties of the BitReader, independent of any
particular compression format. Used by both DEFLATE and Zstd spec proofs.

Split from the original `BitReaderInvariant.lean` which also contained
DEFLATE-specific invariants (HuffTree, decodeStored, etc.).
-/

namespace Zip.Native

/-- `readBit` preserves the data field. -/
theorem readBit_data_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) : br'.data = br.data := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> rfl

/-- `readBits.go` preserves the data field. -/
theorem readBits_go_data_eq (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    br'.data = br.data := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hd₁ := readBit_data_eq br br₁ bit hrb
      have hd' := ih br₁ _ _ h
      rw [hd', hd₁]

/-- `readBits` preserves the data field. -/
theorem readBits_data_eq (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br')) :
    br'.data = br.data := by
  exact readBits_go_data_eq br br' 0 0 n val h

/-- After a successful `readBit`, the hpos invariant `bitOff = 0 ∨ pos < data.size` holds. -/
theorem readBit_hpos (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- `readBits.go` preserves the hpos invariant. -/
theorem readBits_go_hpos (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hpos
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hpos₁ := readBit_hpos br br₁ bit hrb hpos
      have hd₁ := readBit_data_eq br br₁ bit hrb
      exact ih br₁ _ _ h (hd₁ ▸ hpos₁)

/-- `readBits` preserves the hpos invariant. -/
theorem readBits_hpos (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  exact readBits_go_hpos br br' 0 0 n val h hpos

/-- `alignToByte.pos ≤ data.size` when `pos ≤ data.size`. In the `bitOff ≠ 0` case,
    we need the stronger `pos < data.size` (from the hpos invariant). -/
theorem alignToByte_pos_le (br : BitReader)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hle : br.pos ≤ br.data.size) :
    br.alignToByte.pos ≤ br.data.size := by
  simp only [BitReader.alignToByte]
  split
  · exact hle
  · rename_i hne
    cases hpos with
    | inl h => exact absurd (by rw [h]; decide) hne
    | inr h => dsimp only; omega

/-! ### BitReader bitPos advancement

`readBit` advances `bitPos` by exactly 1, and `readBits n` advances by exactly `n`.
These are characterizing properties — they describe the quantitative behavior
of the BitReader, not just invariant preservation. -/

/-- The total bit position of a BitReader: byte position * 8 + bit offset. -/
def BitReader.bitPos (br : BitReader) : Nat := br.pos * 8 + br.bitOff

/-- A successful `readBit` always produces `bitOff < 8`. -/
theorem readBit_bitOff_lt (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.bitOff < 8 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- Reading one bit advances bitPos by exactly 1 (requires `bitOff < 8`). -/
theorem readBit_bitPos_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + 1 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp only [BitReader.bitPos] <;> omega

/-- `readBits.go` reading `n` bits advances bitPos by exactly `n`. -/
theorem readBits_go_bitPos_eq (br br' : BitReader)
    (acc : UInt32) (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + n := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; omega
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hbo₁ := readBit_bitOff_lt br br₁ bit hrb
      have h₁ := readBit_bitPos_eq br br₁ bit hrb hbo
      have h₂ := ih br₁ _ _ h hbo₁
      omega

/-- Reading `n` bits advances bitPos by exactly `n` (requires `bitOff < 8`). -/
theorem readBits_bitPos_eq (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + n :=
  readBits_go_bitPos_eq br br' 0 0 n val h hbo

/-! ### Combined invariant preservation

Bundle data preservation, hpos, and `pos ≤ data.size` into single lemmas. -/

/-- Combined: readBit preserves data, hpos, and gives pos ≤ data.size. -/
theorem readBit_inv (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> (exact ⟨rfl, by omega, by omega⟩)

/-- Combined: readBits.go preserves data, hpos, and pos ≤ data.size. -/
theorem readBits_go_inv (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := readBit_inv br br₁ bit hrb hpos
      have ⟨hd', hpos', hple'⟩ := ih br₁ _ _ h hpos₁ hple₁
      exact ⟨hd'.trans hd₁, hpos', hple'⟩

/-- Combined: readBits preserves data, hpos, and pos ≤ data.size. -/
theorem readBits_inv (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  readBits_go_inv br br' 0 0 n val h hpos hple

/-! ### BitReader pos_le_size — unconditional position bounds

`readBit` and `readBits` guarantee `pos ≤ data.size` on success.
`readBit_pos_le_size` is fully unconditional — the success of `readBit`
implies the guard `pos < data.size` passed. `readBits_pos_le_size`
requires `br.pos ≤ br.data.size` for the `n = 0` base case (which
returns the reader unchanged). -/

/-- After a successful `readBit`, the resulting `pos ≤ data.size`. Unconditional. -/
theorem readBit_pos_le_size (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- `readBits.go` preserves `pos ≤ data.size`. -/
theorem readBits_go_pos_le_size (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hple : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hple
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      exact ih br₁ _ _ h (readBit_pos_le_size br br₁ bit hrb)

/-- After a successful `readBits`, the resulting `pos ≤ data.size`. -/
theorem readBits_pos_le_size (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hple : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size :=
  readBits_go_pos_le_size br br' 0 0 n val h hple

end Zip.Native
