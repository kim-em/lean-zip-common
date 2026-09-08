module

import ZipForStd

/-! Each family of lemmas must be accessible through the root module. -/

example (f : Nat → Nat) (init : Nat) (xs : List Nat) :
    xs.foldl (fun acc x => acc + f x) init =
      init + xs.foldl (fun acc x => acc + f x) 0 :=
  List.foldl_add_init f init xs

example (arr : Array UInt8) (idx : Nat) (v : UInt8) (h : idx < arr.size) :
    ((arr.set! idx v).extract 0 (idx + 1)).toList.map UInt8.toNat =
      (arr.extract 0 idx).toList.map UInt8.toNat ++ [v.toNat] :=
  Array.extract_set_map_append arr idx v h

example (a b : ByteArray) : (a ++ b).extract 0 a.size = a :=
  ByteArray.extract_append_left a b
