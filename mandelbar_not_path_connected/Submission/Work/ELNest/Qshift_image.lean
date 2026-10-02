/-
# `Qshift_image`: the inverse branch `g` maps level `n` of the `z₁`-nest onto level `n+1`

Let `S : NestData c` be the interface of the two nests of the equator-leak argument and let
`g = S.g` be the inverse branch of `F c = (T_c)^{10}` on the level-`0` region `Q̂₀ = S.Q 0` of the
nest at the parabolic point `z₁` (`g_left`, `g_mem`).

This file proves that `g` intertwines *all* levels of the nest:

    S.g '' S.Q n = S.Q (n + 1)     for every `n : ℕ`.

The two inclusions have different ingredients, both already in the workspace.

* **`⊆`.**  `g` is a right inverse of `F c` on `Q̂₀` (`g_left`) and maps `Q̂₀` into `Q̂₁ = S.Q 1`
  (`g_mem`).  If `z ∈ Q̂ₙ` and `w ∈ Q̂_{n+1}` has `F c w = z` (surjectivity of `polyPullback`,
  `pbQ n`), then both `g z` and `w` lie in `Q̂₁`, where `F c` is injective (`pbQ 0`); since
  `F c (g z) = z = F c w`, they are equal, so `g z = w ∈ Q̂_{n+1}`.

* **`⊇`.**  If `w ∈ Q̂_{n+1}`, the point `z = F c w` lies in `Q̂ₙ` (`pbQ n`).  Both `g z` and `w`
  lie in `Q̂₁` and have the same image `z` under `F c`, so by injectivity of `F c` on `Q̂₁`
  (`pbQ 0`) they are equal: `w = g z` with `z ∈ Q̂ₙ`.

Both directions use only that the levels are nested, `Q̂_{n+1} ⊆ Q̂ₙ ⊆ … ⊆ Q̂₀`
(`Q_succ_subset`), so that `g`'s defining properties, stated at level `0`, apply.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.tendsto_iterate_g

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

/-- The level-`n` regions of the nest are nested: `Q̂_k ⊆ Q̂_m` whenever `m ≤ k`. -/
theorem Q_anti {c : ℂ} (S : Work.ELNest.NestData c) {m k : ℕ} (hmk : m ≤ k) :
    S.Q k ⊆ S.Q m := by
  induction hmk with
  | refl => exact subset_rfl
  | step _ ih => exact (NestData.Q_succ_subset S _).trans ih

/-- **The inverse branch shifts the nest by one level.**  The branch `g` of `F c` on `Q̂₀` maps
each level `Q̂ₙ` of the `z₁`-nest onto the next level `Q̂_{n+1}`. -/
theorem Qshift_image {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    S.g '' S.Q n = S.Q (n + 1) := by
  ext w
  constructor
  · -- `g` sends `Q̂ₙ` into `Q̂_{n+1}`: `g z` is the unique preimage of `z` in `Q̂_{n+1}`.
    rintro ⟨z, hz, rfl⟩
    have hz0 : z ∈ S.Q 0 := Q_anti S (Nat.zero_le n) hz
    have hgz1 : S.g z ∈ S.Q 1 := S.g_mem z hz0
    obtain ⟨w', hw', hFw'⟩ := (S.pbQ n).surjOn hz
    have hw'1 : w' ∈ S.Q 1 := Q_anti S (Nat.succ_le_succ (Nat.zero_le n)) hw'
    have hFgz : F c (S.g z) = z := S.g_left z hz0
    have heq : S.g z = w' := (S.pbQ 0).injOn hgz1 hw'1 (by rw [hFgz, hFw'])
    rw [heq]; exact hw'
  · -- every `w ∈ Q̂_{n+1}` is `g (F c w)` with `F c w ∈ Q̂ₙ`.
    intro hw
    have hzmem : F c w ∈ S.Q n := (S.pbQ n).mapsTo hw
    refine ⟨F c w, hzmem, ?_⟩
    have hz0 : F c w ∈ S.Q 0 := Q_anti S (Nat.zero_le n) hzmem
    have hgz1 : S.g (F c w) ∈ S.Q 1 := S.g_mem (F c w) hz0
    have hw1 : w ∈ S.Q 1 := Q_anti S (Nat.succ_le_succ (Nat.zero_le n)) hw
    refine (S.pbQ 0).injOn hgz1 hw1 ?_
    rw [S.g_left (F c w) hz0]

end Work.ELNest
