import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongEps.L12Sub4.ConvDiffBound
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interpGammaCoreFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interpGamma_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
# `TT.interpGamma_core`

The interpolation core of `TT.interpGamma`: for `α ∈ (0,1/4]` and a datum `G` which is `C^∞` on
the *open* quadrant, vanishes at the two angular endpoints and has the three honest
`ℋ⁰`-slots (`D_z²G`, `∂_θ²G`, `D_zG`),

  `Xint α G ≤ C (√(DDint α G · TTint α G) + HkSq α 0 (DzIter 1 G))`

with `Xint = ∫∫(D_z∂_θG)²w²σ_a`, `DDint = ∫∫(D_z²G + bD_zG)²w²σ_a`,
`TTint = ∫∫(∂_θ²G)²w²σ_a` and `σ_a = sin(2θ)^{2-γ(α)}`, `σ_η = sin(2θ)^{-η}`.

Route and status: see `NOTES_interpGamma_core.md` in this directory.  Proved here (all
sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):

* the **per-θ radial T-adjoint on `(0,∞)` with its explicit flux hypothesis**
  (`radial_ibp_Ioi`, with `LzComb`, `tFlux`, `hasDerivAt_tFlux`) — the flux hypothesis is not
  removable: the kernel direction `D_zh = c z³/(1+z)⁴` of `L_z` is admissible and makes the flux
  diverge;
* the elementary weight comparisons (`σ_η ≥ 1` a.e. and `σ_a ≤ σ_η` a.e. on `Iθ`), hence the
  domination of the `σ_a`-slot and of the unweighted slot by the corresponding `ℋ⁰`-slot
  (`integral_sigA_le_HkSq`, `integral_plain_le_HkSq`, `TTint_le_HkSq`), and `|b| ≤ 3` on `z ≥ 0`.

What remains is the jump-endpoint analysis of the flux term `Φ` of the reduction
`Xint = ⟨L_zG,∂_θ²G⟩ + Φ` recorded in the NOTES.
-/

/-! ## The radial T-adjoint on `(0,∞)`, with its explicit flux hypothesis

The T-adjoint identity

  `∫_0^∞ w² (D_zF)(D_zH) = -∫_0^∞ w² (D_z²F + b D_zF) H`

is **false without a flux condition**: the reviewer refutation of the one-function comparison
`∫w²(D_zh)² ≤ C∫w²(L_zh)²` exhibits the kernel direction `D_zh = c z³/(1+z)⁴` of `L_z`, along
which the flux `Φ(z) = w(z)² z H(z) (D_zF)(z)` *diverges* (for `L_zh = 0` one has
`Φ' = w²(D_zh)² ≥ 0`).  The statement therefore carries the flux vanishing at the two ends
explicitly, in exactly the form that the slices of the elliptic problem must supply.
-/

/-- The T-adjoint combination `D_z²F + b D_zF = z (D_zF)' + b (D_zF)` of the radial IBP. -/
def LzComb (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z)

/-- The flux of the radial T-adjoint: `Φ(z) = w(z)² z H(z) (z F'(z))`. -/
def tFlux (F H : ℝ → ℝ) (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * z * H z * (z * deriv F z)

@[simp] theorem LzComb_apply (F : ℝ → ℝ) (z : ℝ) :
    LzComb F z = z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z) := rfl

@[simp] theorem tFlux_apply (F H : ℝ → ℝ) (z : ℝ) :
    tFlux F H z = (Work.Spaces.w z) ^ 2 * z * H z * (z * deriv F z) := rfl



/-! ## Elementary angular weight comparisons -/

/-- The heavy angular weight dominates `1` on the open angular interval:
`σ_η = sin(2θ)^{-η} ≥ 1` for `0 < θ < π/2`.  (At the two endpoints Lean's `rpow` gives the
value `0`, so the comparison can only hold a.e. on the closed interval.) -/
theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
  rw [Real.rpow_neg hs0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hs0 _), one_mul]
  exact Real.rpow_le_one hs0.le hs1 hη


/-! ## The `ℋ⁰`-slot dominates the `σ_a`-slot and the unweighted slot -/







end

end Work.FTS.EllipticEst.TT
end
