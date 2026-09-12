import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Commons.Lattice.Minkowski.covolume_zeroDim_dim0
import Submission.Commons.LinearAlgebra.Submodule.realSpan_zero_iff_bot

/-!
# P1-general: rank-0 data endpoint of a general lattice (`g(0) = 0`)

The per-rank data of the Grayson polygon of a general lattice `Λ ≤ ℝᵈ` will be

    `g_Λ(j) := sInf { log covol(W) | W ≤ Λ, dim_ℝ(span_ℝ W) = j }`.

This module establishes the **rank-0 endpoint**: the only rank-`0` discrete subgroup of
`Λ` is the trivial one, and its Grayson value vanishes,

    `subDim W = 0 ↔ W = ⊥`,   `log covol(⊥) = 0`,

so that `g_Λ(0) = 0` (the polygon then starts at `0`; for unimodular `Λ` the rank-`d`
endpoint is `log covol Λ = 0` by the same vocabulary, so
`largestConvexMinorant_ends_zero` of the discrete-convex API applies).

All declarations are Mathlib + Submission.GraysonLattice + Commons (L72, L73) only.
-/

noncomputable section

open Set Module Real
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.GraysonLattice

open Submission.GraysonData

/-- A `ℤ`-submodule has real dimension `0` iff it is the trivial submodule (the only
rank-0 discrete subgroup of a lattice is `⊥`). -/
lemma subDim_eq_zero_iff_bot {d : ℕ} (W : Submodule ℤ (E d)) :
    subDim W = 0 ↔ W = ⊥ := by
  change Module.finrank ℝ (Submodule.span ℝ (W : Set (E d))) = 0 ↔ W = ⊥
  exact Commons.LinearAlgebra.Submodule.realSpan_zero_iff_bot (E := E d) W

/-- The real span of the trivial subgroup is the zero subspace. -/
lemma realSpan_bot {d : ℕ} : realSpan (⊥ : Submodule ℤ (E d)) = ⊥ := by
  dsimp [realSpan]
  simp

/-- The intrinsic covolume of the trivial subgroup is `1` (its real span is
zero-dimensional, and the covolume of the zero lattice in a zero-dimensional inner product
space is `1`). -/
lemma latticeCovol_bot {d : ℕ} : latticeCovol (⊥ : Submodule ℤ (E d)) = 1 := by
  classical
  unfold Submission.GraysonData.latticeCovol
  dsimp
  let S : Submodule ℝ (E d) := Submodule.span ℝ ((⊥ : Submodule ℤ (E d)) : Set (E d))
  have hS : S = ⊥ := by
    dsimp [S]
    simp
  have hfin : Module.finrank ℝ S = 0 := by
    rw [hS]
    simp
  have hker : (S.subtype.restrictScalars ℤ).ker = ⊥ := by
    refine LinearMap.ker_eq_bot.mpr ?_
    intro a b h
    apply Subtype.ext
    exact h
  have hcov : ZLattice.covolume (E := S) (⊥ : Submodule ℤ S) MeasureTheory.volume = 1 :=
    Commons.Lattice.Minkowski.covolume_zeroDim_dim0 (E := S) hfin
  simpa [S, hker] using hcov

/-- The log-Grayson value of the trivial subgroup is `0` (the rank-`0` data endpoint). -/
lemma logCovol_bot {d : ℕ} : Real.log (latticeCovol (⊥ : Submodule ℤ (E d))) = 0 := by
  rw [latticeCovol_bot]
  simp

end Submission.GraysonLattice

end
