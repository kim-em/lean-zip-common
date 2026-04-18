# Lean4 Upstreaming Resume Plan

This file records the current state of the `ZipForStd` upstreaming work so it can be resumed later
without redoing the audit.

## Scope

Goal:

- upstream the genuinely missing `ZipForStd` lemmas to `lean4` in separate PRs
- avoid upstreaming redundant aliases when current `lean4` `master` already has stronger lemmas
- later delete or shrink `ZipForStd` here and update downstream projects to use upstream lemmas

Audit baseline:

- `lean4` GitHub `master` checked at commit `592eb02bb2d2191ddd728165129ae9e52a880daf`
- audit date: `2026-04-18`

## Implemented Lean4 Branches

These were created as separate worktrees off a local clone of `lean4` `master` under `/tmp`.

### 1. List PR

- Branch: `zipforstd-list`
- Commit: `7ade4d5`
- Worktree: `/tmp/lean4-pr-list`

Files changed:

- `/tmp/lean4-pr-list/src/Init/Data/List/Lemmas.lean`
- `/tmp/lean4-pr-list/src/Init/Data/List/TakeDrop.lean`

Added:

- `List.foldl_add_init`
- `List.foldl_count_init`
- `List.foldl_set_length`
- `List.foldl_set_getElem_not_mem`
- `List.foldl_set_getElem_mem`
- `List.take_set_succ`
- `List.flatMap_drop_mul`
- `List.flatMap_uniform_drop`
- `List.drop_cons_tail`

Not included intentionally:

- `List.getLast?_getD_eq_getLast!`
  already covered by `List.getLast!_eq_getLast?_getD`
- `List.IsPrefix_of_IsPrefix_append`
  already covered by `List.prefix_or_prefix_of_prefix` plus `List.prefix_append`

### 2. Array + Vector `set!` PR

- Branch: `zipforstd-array-vector`
- Commit: `0988ac9`
- Worktree: `/tmp/lean4-pr-array-vector`

Files changed:

- `/tmp/lean4-pr-array-vector/src/Init/Data/Array/Lemmas.lean`
- `/tmp/lean4-pr-array-vector/src/Init/Data/Vector/Lemmas.lean`

Added to `Array`:

- `Array.getElem?_eq_some_getElem!`
- `Array.size_set!`
- `Array.getElem!_set!_self`
- `Array.getElem!_set!_ne`
- `Array.toList_set!`
- `Array.getElem!_le_set!_incr`

Added to `Vector` for parity:

- `Vector.toList_set!`
- `Vector.set!_eq_setIfInBounds`
- `Vector.getElem_set!`
- `Vector.getElem_set!_self`
- `Vector.getElem_set!_ne`
- `Vector.getElem?_set!`
- `Vector.getElem?_set!_self`
- `Vector.getElem?_set!_self_of_lt`
- `Vector.getElem?_set!_ne`

Not included intentionally:

- `Array.extract_set_map_append`
- `Array.extract_map_getLast_eq`

These are downstream proof composites, not good stdlib API additions.

### 3. ByteArray PR

- Branch: `zipforstd-bytearray`
- Commit: `599658e`
- Worktree: `/tmp/lean4-pr-bytearray`

Files changed:

- `/tmp/lean4-pr-bytearray/src/Init/Data/ByteArray/Lemmas.lean`

Added:

- `ByteArray.getElem_toList`
- `ByteArray.getElem!_toList`
- `ByteArray.push_getElem!_lt`
- `ByteArray.push_getElem!_eq`
- `ByteArray.size_set!`
- `ByteArray.getElem!_set!_self`
- `ByteArray.getElem!_set!_ne`
- `ByteArray.getElem_set!_ne`
- `ByteArray.getElem_set!_self`

Not included intentionally:

- `ByteArray.data_toList_length`
- `ByteArray.push_data_toList`
- `ByteArray.extract_append_ge`
- `ByteArray.extract_append_left`

These are either derivable from stronger upstream lemmas already on `master`, or phrased in terms
of `.data` and not worth expanding as stdlib surface area.

### 4. Nat PR

- Branch: `zipforstd-nat`
- Commit: `ae77bd1`
- Worktree: `/tmp/lean4-pr-nat`

Files changed:

- `/tmp/lean4-pr-nat/src/Init/Data/Nat/Bitwise/Lemmas.lean`

Added:

- `Nat.or_two_pow_eq_add`

## Current Local Repo State

This repo:

- `/Users/kim/projects/lean/lean-zip-common`

Status when this note was written:

- local `lean-toolchain` was already modified before this handoff
- `PLAN.md` is new
- no `ZipForStd` cleanup has been done yet in this repo

Downstream repos with unrelated local edits present at the time:

- `/Users/kim/projects/lean/lean-zip`
- `/Users/kim/projects/lean/lean-zstd`

Those edits were deliberately not touched.

## Next Steps

### A. Finish the Lean4 side properly

1. Move or cherry-pick the four commits onto a full local `lean4` checkout.
2. Build and test each branch in a real full checkout, not just the sparse `/tmp` worktrees.
3. Fix any theorem-style, linter, or proof breakage found by the Lean4 CI/build.
4. Push each branch to a fork.
5. Open four separate Lean4 PRs.

Suggested PR grouping:

- PR 1: `List`
- PR 2: `Array` + `Vector`
- PR 3: `ByteArray`
- PR 4: `Nat`

### B. Write PR descriptions

Each PR description should say:

- which `ZipForStd` lemmas it is upstreaming
- why the additions are still missing on current `master`
- which local lemmas were intentionally not upstreamed because `master` already has stronger API
- why the grouping is coherent

### C. Do not upstream the redundant local lemmas

Keep these out of Lean4 unless new evidence appears:

- `List.getLast?_getD_eq_getLast!`
- `List.IsPrefix_of_IsPrefix_append`
- `Array.extract_set_map_append`
- `Array.extract_map_getLast_eq`
- `ByteArray.data_toList_length`
- `ByteArray.push_data_toList`
- `ByteArray.extract_append_ge`
- `ByteArray.extract_append_left`

## After Lean4 PRs Are Merged

Once the relevant PRs are merged into `lean4` `master`, wait for a Lean release or nightly that
contains them.

Then:

1. Update `lean-toolchain` here to a version containing the merged PRs.
2. Build `lean-zip-common`.
3. Remove the corresponding lemmas from `ZipForStd`, or reduce them to temporary aliases only if
   needed during migration.
4. Update imports in this repo so any remaining `ZipForStd` files only contain lemmas that are
   still truly local.
5. Build again and make sure no deleted theorem is still referenced by name internally.

## Downstream Migration After New Lean Version Is Available

Apply the new Lean version in:

- `/Users/kim/projects/lean/lean-zip`
- `/Users/kim/projects/lean/lean-zstd`

Then migrate proofs away from local `ZipForStd` lemmas.

### Rewrites in `lean-zip`

Expected direct replacements:

- replace `List.getLast?_getD_eq_getLast!` with `simp` or `List.getLast!_eq_getLast?_getD`
- replace `List.IsPrefix_of_IsPrefix_append` with
  `List.prefix_or_prefix_of_prefix hp (List.prefix_append _ _)`
- replace `ByteArray.extract_append_ge` / `extract_append_left` with existing upstream
  `ByteArray.extract_append_size_add`, `ByteArray.extract_append_eq_left`, or `ByteArray.extract_append`
- rewrite uses of `Array.extract_set_map_append` and `Array.extract_map_getLast_eq` using existing
  upstream lemmas and the new `List.take_set_succ`
- replace `ByteArray.data_toList_length` with `ByteArray.size_data` plus `Array.length_toList`
- replace `ByteArray.push_data_toList` with existing `Array` / `ByteArray` lemmas rather than
  preserving a `.data.toList` helper

Lemmas expected to become direct upstream imports:

- all upstreamed `List` lemmas
- `Array.size_set!`
- `Array.getElem!_set!_self`
- `Array.getElem!_set!_ne`
- `Array.getElem!_le_set!_incr`
- `Array.getElem?_eq_some_getElem!`
- all upstreamed `ByteArray` push / `set!` lemmas
- `Nat.or_two_pow_eq_add`

### Rewrites in `lean-zstd`

Expected main dependency:

- `ByteArray.push_getElem!_lt`
- `ByteArray.push_getElem!_eq`

Check whether any `ZipForStd.Array` import remains after Lean upgrade. It may become unnecessary.

## Final Cleanup Goal

Best outcome:

- `ZipForStd` disappears entirely from this repo

Acceptable temporary outcome:

- `ZipForStd` remains only as thin compatibility shims during the upgrade window

Not desirable:

- carrying duplicate local lemmas long-term after upstream support is available

## Quick Resume Checklist

When resuming this work later:

1. Check whether the four Lean4 commits above were already pushed or merged.
2. Check whether a released Lean version includes them.
3. If not merged yet:
   continue with the four Lean4 PRs.
4. If merged but not released:
   decide whether to use a nightly or wait for release.
5. If released:
   bump `lean-toolchain` here, then migrate `lean-zip-common`, `lean-zip`, and `lean-zstd`.
