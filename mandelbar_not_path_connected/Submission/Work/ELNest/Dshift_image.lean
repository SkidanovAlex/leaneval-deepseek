/-
# `Dshift_image`: the inverse branch `g6` maps level `n` of the `b₂`-nest onto level `n+1`

Let `S : NestData c` be the interface of the two nests of the equator-leak argument and let
`g6 = S.g6` be the inverse branch of `F6 c = (T_c)^6` on the level-`0` region
`Δ̂₀ = S.D 0` of the nest at the branch point `b₂` (`g6_left`, `g6_mem`, `pbD`).

This file proves that `g6` intertwines *all* levels of the nest:

    S.g6 '' S.D n = S.D (n + 1)     for every `n : ℕ`.

The argument is identical to that of `Qshift_image`, with `F c` replaced by `F6 c`.

* **`⊆`.**  `g6` is a right inverse of `F6 c` on `Δ̂₀` (`g6_left`) and maps `Δ̂₀` into
  `Δ̂₁ = S.D 1` (`g6_mem`).  If `z ∈ Δ̂ₙ` and `w ∈ Δ̂_{n+1}` has `F6 c w = z` (surjectivity
  of `polyPullback`, `pbD n`), then both `g6 z` and `w` lie in `Δ̂₁` (nesting `D_succ_subset`),
  where `F6 c` is injective (`pbD 0`); since `F6 c (g6 z) = z = F6 c w`, they are equal, so
  `g6 z = w ∈ Δ̂_{n+1}`.

* **`⊇`.**  If `w ∈ Δ̂_{n+1}`, the point `z = F6 c w` lies in `Δ̂ₙ` (`pbD n`).  Both `g6 z` and
  `w` lie in `Δ̂₁` and have the same image `z` under `F6 c`, so by injectivity of `F6 c` on
  `Δ̂₁` (`pbD 0`) they are equal: `w = g6 z` with `z ∈ Δ̂ₙ`.

Both directions use only that the levels are nested, `Δ̂_{n+1} ⊆ Δ̂ₙ ⊆ … ⊆ Δ̂₀`
(`D_succ_subset`), so that `g6`'s defining properties, stated at level `0`, apply.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.isOpen_D

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- The levels of the `b₂`-nest are nested: `Δ̂_{n+1} ⊆ Δ̂ₙ`. -/
theorem D_succ_subset {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    S.D (n + 1) ⊆ S.D n :=
  S.Dnest_sub n

/-- The levels of the `b₂`-nest are nested: `Δ̂_k ⊆ Δ̂_m` whenever `m ≤ k`. -/
theorem D_anti {c : ℂ} (S : Work.ELNest.NestData c) {m k : ℕ} (hmk : m ≤ k) :
    S.D k ⊆ S.D m := by
  induction hmk with
  | refl => exact subset_rfl
  | step _ ih => exact (D_succ_subset S _).trans ih

/-- **The inverse branch shifts the nest by one level.**  The branch `g6` of `F6 c = (T_c)^6`
on `Δ̂₀` maps each level `Δ̂ₙ` of the `b₂`-nest onto the next level `Δ̂_{n+1}`. -/
theorem Dshift_image {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    S.g6 '' S.D n = S.D (n + 1) := by
  ext w
  constructor
  · -- `g6` sends `Δ̂ₙ` into `Δ̂_{n+1}`: `g6 z` is the unique preimage of `z` in `Δ̂_{n+1}`.
    rintro ⟨z, hz, rfl⟩
    have hz0 : z ∈ S.D 0 := D_anti S (Nat.zero_le n) hz
    have hgz1 : S.g6 z ∈ S.D 1 := S.g6_mem z hz0
    obtain ⟨w', hw', hFw'⟩ := (S.pbD n).surjOn hz
    have hw'1 : w' ∈ S.D 1 := D_anti S (Nat.succ_le_succ (Nat.zero_le n)) hw'
    have hFgz : F6 c (S.g6 z) = z := S.g6_left z hz0
    have heq : S.g6 z = w' := (S.pbD 0).injOn hgz1 hw'1 (by rw [hFgz, hFw'])
    rw [heq]; exact hw'
  · -- every `w ∈ Δ̂_{n+1}` is `g6 (F6 c w)` with `F6 c w ∈ Δ̂ₙ`.
    intro hw
    have hzmem : F6 c w ∈ S.D n := (S.pbD n).mapsTo hw
    refine ⟨F6 c w, hzmem, ?_⟩
    have hz0 : F6 c w ∈ S.D 0 := D_anti S (Nat.zero_le n) hzmem
    have hgz1 : S.g6 (F6 c w) ∈ S.D 1 := S.g6_mem (F6 c w) hz0
    have hw1 : w ∈ S.D 1 := D_anti S (Nat.succ_le_succ (Nat.zero_le n)) hw
    refine (S.pbD 0).injOn hgz1 hw1 ?_
    rw [S.g6_left (F6 c w) hz0]

end Work.ELNest
