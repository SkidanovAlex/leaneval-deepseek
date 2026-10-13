/-
Copyright: work module for the Elgindi finite-time singularity project.

# The single-slice angular functionals of the `θ`-Poincaré estimate with boundary traces

The target of this chapter (`Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace`) compares the
weighted `ℋ^k`-norms of `f`, `∂_θ f` and `∂_θ² f` for data `f` which is merely `C^∞` on the
*open* quadrant `(0,∞) × (0,π/2)` and whose angular boundary behaviour is only known as a
*limit*: for every `j ≤ k` and `z > 0` the slice `θ ↦ D_z^j f z θ` tends to `0` at `θ → 0⁺`
and at `θ → π/2⁻`.

Because the weights of the norm depend on `θ` only and `D_z` acts inside each angular slice,
the estimate splits into statements about a *single* slice `u : ℝ → ℝ`, of class `C^∞` on
`(0,π/2)` with vanishing endpoint *limits*.  This module fixes the one-dimensional functional
carried by such a slice:

`sliceW K α u θ = (u θ)² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ K} (L^i u θ)² sin(2θ)^{-γ}`,  `L = D_θ`,

and its integral `sliceF K α u = ∫_{Iθ} sliceW K α u`.  This is exactly the `j`-th slice group
of the `ℋ^k`-integrand rescaled by `w(z)^{-2}` (see
`Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum` and the pointwise identities of
`Submission/Work/FTS/EllSol/VopAux/SliceGroupIdent.lean`).

The two one-dimensional estimates on `sliceF` (proved in the siblings
`SliceTraceSlope`/`SliceTraceDerivSlope`) are

* `sliceF K α u ≤ C_K · sliceF K α (u'')`   (the `∂_θ²`-case), and
* `sliceF K α u' ≤ C_K · sliceF K α (u'')`  (the `∂_θ`-case),

both with the same hypotheses on `u` (smooth on the open interval, vanishing endpoint limits,
and the two integrability hypotheses on the data `u''`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false

/-- The angular integrand attached to a single slice `u`:
`(u θ)² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ K} (D_θ^i u θ)² sin(2θ)^{-γ}`. -/
def sliceW (K : ℕ) (α : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    + ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ

/-- The integral over `Iθ` of the slice functional `sliceW`. -/
def sliceF (K : ℕ) (α : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sliceW K α u θ

theorem sliceF_eq_integral (K : ℕ) (α : ℝ) (u : ℝ → ℝ) :
    sliceF K α u = ∫ θ in Work.Spaces.Iθ, sliceW K α u θ := rfl

/-- The slice functional `sliceW` is nonnegative on `Iθ`. -/
theorem sliceW_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ sliceW K α u θ := by
  rw [sliceW]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)) ?_
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ)

/-- `sliceF` is nonnegative. -/
theorem sliceF_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) : 0 ≤ sliceF K α u := by
  rw [sliceF]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact sliceW_nonneg K α u hθ

/-- The slice functional is monotone in the level `K`, pointwise on `Iθ`. -/
theorem sliceW_mono {K K' : ℕ} (hKK : K ≤ K') (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    sliceW K α u θ ≤ sliceW K' α u θ := by
  rw [sliceW, sliceW]
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
  intro i hi
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, le_trans (Finset.mem_Icc.mp hi).2 hKK⟩

end Work.FTS.EllSol.VopAux
