import ZipForStd.List

/-!
# Array lemmas for the standard library

Generic lemmas about `Array.set!` and `getElem!` that are useful beyond the
Huffman module. Candidates for upstreaming to Lean's standard library.

## Upstream status (Lean 4.33)

Core now has the `getElem!`/`set!` convenience wrappers this file used to
provide: `Array.size_set!`, `Array.getElem!_set!_ne`,
`Array.getElem!_set!_self`, and `Array.getElem?_eq_some_getElem!`, each with the
same signature as the copy that lived here, so call sites resolve to core's. The
`extract`/`set` decomposition lemmas below have no upstream equivalent.
-/

namespace Array

/-! ## extract/set decomposition -/

/-- `set!` at index `idx` followed by `extract 0 (idx+1)` gives
    the original prefix mapped to Nat, plus the new value's Nat. -/
theorem extract_set_map_append (arr : Array UInt8) (idx : Nat) (val : UInt8)
    (hidx : idx < arr.size) :
    ((arr.set! idx val).extract 0 (idx + 1)).toList.map UInt8.toNat =
    (arr.extract 0 idx).toList.map UInt8.toNat ++ [val.toNat] := by
  rw [Array.set!, Array.toList_extract, Array.toList_setIfInBounds, Array.toList_extract]
  simp only [List.extract, Nat.sub_zero, List.drop_zero]
  rw [List.take_set_succ _ _ _ (by rw [Array.length_toList]; exact hidx)]
  simp only [List.map_append, List.map_take, List.map_cons, List.map_nil]

/-- The last element of a mapped extract equals the mapped array element. -/
theorem extract_map_getLast_eq (arr : Array UInt8) (idx : Nat)
    (hidx : 0 < idx) (hle : idx ≤ arr.size) :
    ((arr.extract 0 idx).toList.map UInt8.toNat).getLast! = arr[idx - 1]!.toNat := by
  simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero, List.map_take]
  have hlen : (List.take idx (List.map UInt8.toNat arr.toList)).length = idx := by
    simp only [List.length_take, List.length_map, length_toList, Nat.min_eq_left hle]
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, hlen,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  rw [getElem!_pos arr _ (by omega),
    @List.getElem_take _ (arr.toList.map UInt8.toNat) idx (idx - 1) (by rw [hlen]; omega)]
  simp only [List.getElem_map, getElem_toList]

end Array
