/-
Work module for the Elgindi finite-time singularity project.

# Integrability of a single mixed summand of the `ℋ^k`-integrand

The `ℋ^k`-integrand of the paper (Elgindi, Annals 194 (3) 2021, §Notation) is the sum of
the squared weighted derivatives `(D_z^j D_θ^i F · W)²`, `1 ≤ i`, `i + j ≤ k`.  This module
shows that, for a source `F` which is `C^∞` on the open quadrant (`SmoothOpen`) and honestly
in `ℋ^k` (`Work.Spaces.HkMem`), each *single* mixed summand is an honest integrable function
of `θ` on the angular interval `Iθ = [0, π/2]`, for every `z ∈ Iz`.

This is the mixed companion of `Work.FTS.EllipticEst.integrableOn_zSummand` (the pure
`D_z`-summand), and it is what the Cauchy–Schwarz estimates of the `θ`-slice estimates need
in order to treat each mixed term of the integrand separately.

The route is the standard domination one:

* the summand is a square of a product of two factors, each of which is measurable: the
  angular slice `θ ↦ D_z^j D_θ^i F z θ` is a.e. strongly measurable because the uncurried
  derivative is continuous on the open quadrant, and `θ ↦ W(α,z,θ)` is a real power of
  `sin(2θ)` times a constant;
* it is pointwise dominated by the full integrand `HkIntegrand α k F z θ`, of which it is
  one of the (nonnegative) summands (`Work.Spaces.sq_le_HkIntegrand_mixed`), and the full
  integrand is integrable on `Iθ` by `HkMem`.

At `z = 0` the weight `W(α,0,θ) = w(0)·sin(2θ)^{-γ/2}` vanishes, so there the summand is
identically zero and the conclusion is immediate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The uncurried mixed summand `(z,θ) ↦ D_z^j D_θ^i F z θ · W(α,z,θ)` is continuous on the
open quadrant, being the product of the continuous uncurried derivative (`SmoothOpen`) and the
continuous weight. -/
private theorem continuousOn_mixedSummand_Q0 {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (α : ℝ) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  ((hF.mixed j i).continuousOn).mul (Work.FTS.EllipticEst.continuousOn_Wt_Q0 α)

/-- For `z > 0` the angular slice `θ ↦ D_z^j D_θ^i F z θ · W(α,z,θ)` is a.e. strongly
measurable w.r.t. `volume.restrict Iθ`: it is the slice of a function continuous on the open
quadrant (the endpoints of `Iθ` being null). -/
private theorem aesm_slice_mixedSummand {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
    (continuousOn_mixedSummand_Q0 hF α j i) hz

theorem integrableOn_mixedSummand (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial factor of the weight vanishes, so the summand is `0`
    subst hz0
    have hzero : (fun θ : ℝ => (Work.Spaces.mixed j i F 0 θ * Work.Spaces.Wt α 0 θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.Spaces.Wt, Work.Spaces.w]
      norm_num
    rw [hzero]
    exact integrableOn_zero
  · -- at `z > 0` the summand is dominated by the honest integrand `HkIntegrand α k F`
    refine Integrable.mono' (hmem.1 z hz)
      ((aesm_slice_mixedSummand hF α j i hzpos).pow 2) ?_
    refine Eventually.of_forall fun θ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij

end Work.FTS.EllipticEst.TT
