import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `n.choose k ≤ 2^n ≤ 16` for `n ≤ 4`, hence `(n.choose k : ℝ)² ≤ 256`. -/
private lemma binom_sq_le_256 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    (n.choose k : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have h2 : n.choose k ≤ 16 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 16 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]


/-! ## The two blocks of `mulSlotRHS`, as explicit sums -/











/-! ## Every Leibniz summand of `mulSlotRHS` is small enough -/



/-! ## The pure `D_z`-slots of `HkIntegrand α 4 (χ · f)` -/


/-! ## The mixed slots of `HkIntegrand α 4 (χ · f)` -/


/-! ## The product rule -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.H2.T3Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The per-term bound, in the interior class

This is the verbatim port of `Work.FTS.H2.Transport3Aux.Z3.TM_abs_le` from the analytic class
`Work.Spaces.SmoothNbhd` (with `θ` in the closed quadrant `Iθ`) to the interior class
`Work.FTS.LocData.SmoothQuad` (with `θ` in the open quadrant `(0,π/2)`): the only change is the
multiplier bound `Work.FTS.H2.Transport3Aux.abs_mixed_le_WlInf` replaced by
`Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (both with the constant `30 |f|_{𝒲^{4,∞}}`).  The
`g`-side AM–GM lemma `Work.FTS.H2.Transport3Aux.abs_mixed_pair_mul_weight_le_HkIntegrand`, the
elementary facts `Work.FTS.H2.Wm_nonneg` / `Work.FTS.H2.Whz_Wm_sq` and the index bookkeeping
`Work.FTS.H2.Transport3Aux.Z3.mx_index_le` are class-free in `f` and are reused verbatim. -/



end Work.FTS.H2.T3Q
end
end
