import ZipForStd.Array

/-!
# ByteArray lemmas for the standard library

Generic lemmas about `ByteArray` indexing that bridge between
`ByteArray` get-element, `Array` get-element, and `List` get-element.
Candidates for upstreaming to Lean's standard library.

## Upstream status (Lean 4.33)

Core now has the `push`/`set!` lemmas in the `getElem!` and proven-bounds forms
this file used to provide (`getElem!_push_lt`, `getElem!_push_eq`, `size_set!`,
`getElem!_set!_self`, `getElem!_set!_ne`, `getElem_set!_ne`,
`getElem_set!_self`), each with the same signature as the copy that lived here,
so call sites resolve to core's. What remains has no upstream equivalent: the
`Array.toList` bridging lemmas and the specialized extracts
(`extract_append_ge`, `extract_append_left`).
-/

namespace ByteArray

/-- `ByteArray` indexing agrees with `Array.toList` indexing. -/
theorem getElem_toList (data : ByteArray) (i : Nat) (h : i < data.size)
    (h' : i < data.data.toList.length := by simp only [Array.length_toList]; exact h) :
    (data[i]'h : UInt8) = data.data.toList[i] := by
  show data.data[i] = data.data.toList[i]
  rw [← Array.getElem_toList]

/-- `ByteArray.getElem!` agrees with `Array.toList` indexing when in bounds. -/
theorem getElem!_toList (data : ByteArray) (i : Nat) (h : i < data.size) :
    data[i]! = data.data.toList[i]'(by simp only [Array.length_toList]; exact h) := by
  rw [getElem!_pos data i h]
  exact getElem_toList data i h

/-- `ByteArray.data.toList.length` equals `ByteArray.size`. -/
theorem data_toList_length (data : ByteArray) :
    data.data.toList.length = data.size :=
  Array.length_toList

/-- Extract from `a ++ b` starting at or past `a.size` gives an extract of `b`. -/
theorem extract_append_ge (a b : ByteArray) (i j : Nat) (h : i ≥ a.size) :
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  apply ByteArray.ext
  simp only [data_extract, data_append, Array.extract_append, size_data,
        Array.append_left_eq_self, Array.extract_eq_empty_iff]
  omega

/-- Extracting from 0 to `a.size` in `a ++ b` gives `a`. -/
theorem extract_append_left (a b : ByteArray) :
    (a ++ b).extract 0 a.size = a := by
  apply ByteArray.ext
  simp only [data_extract, data_append, Array.extract_append, size_data, Nat.zero_le,
        Nat.sub_eq_zero_of_le, Array.extract_zero, Array.append_empty,
        Array.extract_eq_self_iff, size_eq_zero_iff, Std.le_refl, and_self, or_true]

/-- `ByteArray.push` appends one element to `data.toList`.
    Upstream building blocks: `ByteArray.data_push`, `Array.toList_push`. -/
theorem push_data_toList (buf : ByteArray) (b : UInt8) :
    (buf.push b).data.toList = buf.data.toList ++ [b] := by
  simp only [ByteArray.data_push, Array.toList_push]

end ByteArray
