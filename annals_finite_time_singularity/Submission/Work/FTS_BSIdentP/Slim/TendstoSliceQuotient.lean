import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.BiotSavart
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSIdent.Bundle.ansatzBundleSub_of_r_mul_V =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Bundle




end Work.FTS.BSIdent.Bundle
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.Quadrant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise bounds on the open quadrant

`Work.FTS.BSIdent.Cyl.abs_combination_bound` bounds the two derivative terms of the chain rule
by `decayKzr p c C₀ q lam b / (1+ρ)`; the two corollaries specialise it to `∂_z psiCore` and
`∂_r psiCore`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise bound on the open quadrant -/

/-- The two terms `c (X ∂_wG + Y ∂_θG)` of the chain rule are bounded by
`decayKzr p c C₀ q lam b / (1+ρ)` as soon as `|X| ≤ p ρ w`, `|Y| ≤ ρ` and the profile satisfies
the three `hrate`-style bounds at the point. -/
theorem abs_combination_bound {G : ℝ → ℝ → ℝ} {p c b C₀ q lam r z zc X Y : ℝ}
    (hC₀ : 0 ≤ C₀) (hq : 2 < q) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 3 ≤ p * lam) (hzc : |zc| ≤ Work.Cyl.rhoP r z)
    (hX : |X| ≤ p * Work.Cyl.rhoP r z * (Work.Cyl.rhoP r z ^ p / b))
    (hY : |Y| ≤ Work.Cyl.rhoP r z)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ q
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z) ^ (q - 1)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |2 * zc * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (X * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              + Y * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))|
      ≤ decayKzr p c C₀ q lam b / (1 + Work.Cyl.rhoP r z) := by
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set S := Real.pi / 2 - θ with hS
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθpos : 0 < θ := by
    rw [hθ, Work.Cyl.thetaP]
    exact Real.arctan_pos.mpr (div_pos hz hr)
  have hθlt : θ < Real.pi / 2 := by rw [hθ]; exact thetaP_lt_pi_div_two r z
  have hSpos : 0 < S := by rw [hS]; linarith
  have hSnn : 0 ≤ S := hSpos.le
  have hSle : S ≤ Real.pi / 2 := by rw [hS]; linarith
  have hwpos : 0 < w := by
    rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hwnn : 0 ≤ w := hwpos.le
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hRpos : 0 < R := by rw [hR]; exact Real.rpow_pos_of_pos h1w _
  have hRnn : 0 ≤ R := hRpos.le
  have hq1 : (0 : ℝ) ≤ q - 1 := by linarith
  have h2pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hP2nn : (0 : ℝ) ≤ (Real.pi / 2) ^ (q - 1) := Real.rpow_nonneg h2pi.le _
  have hval' : |G w θ| ≤ C₀ * S ^ q * R := hval
  have hwd' : |Work.Cyl.pdR G w θ| ≤ C₀ * S ^ q * (1 + w) ^ (-lam - 1) := hwd
  have hth' : |Work.Cyl.pdZ G w θ| ≤ C₀ * S ^ (q - 1) * R := hth
  have hX' : |X| ≤ p * ρ * w := hX
  have hY' : |Y| ≤ ρ := hY
  have hzcb : |zc| ≤ ρ := by rw [hρ]; exact hzc
  -- the elementary comparisons
  have hSq : S ^ q ≤ Real.pi / 2 * S ^ (q - 1) := by
    have h : S ^ q = S ^ (q - 1) * S := by
      conv_lhs => rw [show q = q - 1 + 1 by ring]
      rw [Real.rpow_add hSpos, Real.rpow_one]
    rw [h]
    calc S ^ (q - 1) * S ≤ S ^ (q - 1) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hSle (Real.rpow_nonneg hSnn _)
      _ = Real.pi / 2 * S ^ (q - 1) := by ring
  have hSq1 : S ^ (q - 1) ≤ (Real.pi / 2) ^ (q - 1) :=
    Real.rpow_le_rpow hSnn hSle hq1
  have hwR2 : w * (1 + w) ^ (-lam - 1) ≤ R := by
    have e1 : (1 + w) ^ (-lam - 1) = R * (1 + w)⁻¹ := by
      have e2 : (1 + w) ^ (-lam - 1) = (1 + w) ^ (-lam) * (1 + w) ^ (-1 : ℝ) := by
        rw [show -lam - 1 = -lam + (-1) by ring, Real.rpow_add h1w]
      rw [e2, ← hR, Real.rpow_neg_one]
    have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show w ≤ 1 + w by linarith)
        (inv_nonneg.mpr h1w.le)
      rwa [mul_inv_cancel₀ (ne_of_gt h1w)] at h
    calc w * (1 + w) ^ (-lam - 1) = (w * (1 + w)⁻¹) * R := by rw [e1]; ring
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right hw1 hRnn
      _ = R := one_mul R
  have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
    have h := DecayAux.rho_mul_rpow_weight_le hp hlam hb hρnn hpl
    rw [← hw, ← hR] at h
    exact h
  -- the three term bounds
  have hT1 : 2 * |zc| * |c| * (C₀ * S ^ q * R)
      ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) := by
    have hs1 : C₀ * S ^ q * R ≤ C₀ * (Real.pi / 2 * S ^ (q - 1)) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSq hC₀) hRnn
    have hz2 : 2 * |zc| ≤ 2 * ρ := mul_le_mul_of_nonneg_left hzcb (by norm_num)
    have hz2c : 2 * |zc| * |c| ≤ 2 * ρ * |c| :=
      mul_le_mul_of_nonneg_right hz2 (abs_nonneg c)
    calc 2 * |zc| * |c| * (C₀ * S ^ q * R)
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2 * S ^ (q - 1)) * R) :=
          mul_le_mul hz2c hs1 (mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hSnn _)) hRnn)
            (mul_nonneg (mul_nonneg (by norm_num) hρnn) (abs_nonneg c))
      _ = (2 * (Real.pi / 2)) * (|c| * C₀ * S ^ (q - 1) * (ρ * R)) := by ring
      _ ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hSq1 (mul_nonneg (abs_nonneg c) hC₀))
              (mul_nonneg hρnn hRnn))
            (mul_nonneg (by norm_num) h2pi.le)
  have hT2 : |c| * ((p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)))
      ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) := by
    have hs1 : C₀ * S ^ q * (1 + w) ^ (-lam - 1)
        ≤ C₀ * (Real.pi / 2 * S ^ (q - 1)) * (1 + w) ^ (-lam - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSq hC₀)
        (Real.rpow_nonneg h1w.le _)
    have h1 : |c| * ((p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)))
        ≤ |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2 * S ^ (q - 1))
            * (1 + w) ^ (-lam - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs1 (mul_nonneg (mul_nonneg hp.le hρnn) hwnn))
        (abs_nonneg c)
    have h2 : |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2 * S ^ (q - 1))
          * (1 + w) ^ (-lam - 1)))
        = (p * (Real.pi / 2))
          * (|c| * C₀ * S ^ (q - 1) * (ρ * (w * (1 + w) ^ (-lam - 1)))) := by ring
    have h3 : (p * (Real.pi / 2))
          * (|c| * C₀ * S ^ (q - 1) * (ρ * (w * (1 + w) ^ (-lam - 1))))
        ≤ (p * (Real.pi / 2)) * (|c| * C₀ * S ^ (q - 1) * (ρ * R)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwR2 hρnn)
          (mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) (Real.rpow_nonneg hSnn _)))
        (mul_nonneg hp.le h2pi.le)
    have h4 : (p * (Real.pi / 2)) * (|c| * C₀ * S ^ (q - 1) * (ρ * R))
        ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSq1 (mul_nonneg (abs_nonneg c) hC₀))
          (mul_nonneg hρnn hRnn))
        (mul_nonneg hp.le h2pi.le)
    exact h1.trans (h2.trans_le (h3.trans h4))
  have hT3 : |c| * (ρ * (C₀ * S ^ (q - 1) * R))
      ≤ 1 * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) := by
    have h : |c| * (ρ * (C₀ * S ^ (q - 1) * R)) = |c| * C₀ * S ^ (q - 1) * (ρ * R) := by ring
    rw [h]
    simpa using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSq1 (mul_nonneg (abs_nonneg c) hC₀))
      (mul_nonneg hρnn hRnn)
  have hsum : 2 * |zc| * |c| * (C₀ * S ^ q * R)
        + (|c| * ((p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * S ^ (q - 1) * R)))
      ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) := by
    have h := add_le_add hT1 (add_le_add hT2 hT3)
    calc 2 * |zc| * |c| * (C₀ * S ^ q * R)
          + (|c| * ((p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)))
            + |c| * (ρ * (C₀ * S ^ (q - 1) * R)))
        ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R))
          + ((p * (Real.pi / 2)) * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R))
            + 1 * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R))) := h
      _ = (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)) := by ring
  have hfin : (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R))
      ≤ decayKzr p c C₀ q lam b / (1 + ρ) := by
    have hA : (0 : ℝ) ≤ |c| * C₀ * (Real.pi / 2) ^ (q - 1) :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) hP2nn
    have hb1 : |c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R)
        ≤ |c| * C₀ * (Real.pi / 2) ^ (q - 1) * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
      mul_le_mul_of_nonneg_left hρR hA
    have hcoef : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
      have := mul_nonneg hp.le h2pi.le; linarith
    calc (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (Real.pi / 2) ^ (q - 1) * (ρ * R))
        ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
            * (|c| * C₀ * (Real.pi / 2) ^ (q - 1)
              * (2 * max 1 (b ^ lam) / (1 + ρ))) := mul_le_mul_of_nonneg_left hb1 hcoef
      _ = decayKzr p c C₀ q lam b / (1 + ρ) := by rw [decayKzr]; ring
  -- assembling
  have h1a : |2 * zc * c * G w θ| = 2 * |zc| * |c| * |G w θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h1b : |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      = |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := abs_mul c _
  have h1c : |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ|
      ≤ |X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ| :=
    (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_mul]))
  have h1 : |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      ≤ 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by
    calc |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
        ≤ |2 * zc * c * G w θ| + |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)| :=
          abs_add_le _ _
      _ = 2 * |zc| * |c| * |G w θ|
            + |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := by rw [h1a, h1b]
      _ ≤ 2 * |zc| * |c| * |G w θ|
            + |c| * (|X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ|) := by
          have hc := mul_le_mul_of_nonneg_left h1c (abs_nonneg c)
          linarith
      _ = 2 * |zc| * |c| * |G w θ|
            + (|c| * (|X| * |Work.Cyl.pdR G w θ|)
              + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by rw [mul_add]
  have h2 : 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|))
      ≤ 2 * |zc| * |c| * (C₀ * S ^ q * R)
        + (|c| * ((p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * S ^ (q - 1) * R))) := by
    have hA : 2 * |zc| * |c| * |G w θ| ≤ 2 * |zc| * |c| * (C₀ * S ^ q * R) :=
      mul_le_mul_of_nonneg_left hval'
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg zc)) (abs_nonneg c))
    have hB : |X| * |Work.Cyl.pdR G w θ| ≤ (p * ρ * w) * (C₀ * S ^ q * (1 + w) ^ (-lam - 1)) :=
      mul_le_mul hX' hwd' (abs_nonneg _) (mul_nonneg (mul_nonneg hp.le hρnn) hwnn)
    have hD : |Y| * |Work.Cyl.pdZ G w θ| ≤ ρ * (C₀ * S ^ (q - 1) * R) :=
      mul_le_mul hY' hth' (abs_nonneg _) hρnn
    exact add_le_add hA (add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg c))
      (mul_le_mul_of_nonneg_left hD (abs_nonneg c)))
  exact h1.trans (h2.trans (hsum.trans hfin))

end Work.FTS.BSIdent.Cyl
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.DecayTwoDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The constants of the sharp (`q = 1`) meridian decay estimate

The `Cyl.DecayAux` chain proves the decay of `merPsiT` with a profile rate `(π/2-θ)^q`, `q > 2`,
and needs `3 ≤ p·λ`.  The sharp version needed by the reconstruction (`Weyl.Levels`) has the
profile rate with `q = 1` (the weight `π/2 - θ` in the leading order only, the `θ`-derivative
losing that weight entirely) and only `2 ≤ p·λ`.  The two total constants of that estimate live
here so that the several files producing it agree on their values.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Weyl.Levels

set_option autoImplicit false

/-- The constant in the `(1+ρ)^{-1}` bound for the two partial derivatives `∂_z ψ`, `∂_r ψ`
of the meridian stream function, in the sharp (`q = 1`) regime.  It is
`(2·(π/2) + p·(π/2) + 1)·|c|·C₀·(2·max 1 (b^λ))`: the three chain-rule terms contribute
`2·(π/2)`, `p·(π/2)` and `1` times the common factor `|c|·C₀·(ρ·(1+w)^{-λ})`, and the last is
bounded by `2·max 1 (b^λ)/(1+ρ)`. -/
noncomputable def decayKzrOne (p c C₀ lam b : ℝ) : ℝ :=
  (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * (|c| * C₀ * (2 * max 1 (b ^ lam)))

/-- The constant in the `(1+ρ)^{-1}` bound for `ψ/r`, in the sharp (`q = 1`) regime:
`|c|·C₀·(π/2)·(2·max 1 (b^λ))`, the `π/2` coming from Jordan's inequality
`π/2 - θ ≤ (π/2)·cos θ = (π/2)·r/ρ`. -/
noncomputable def decayKqOne (c C₀ lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) * (2 * max 1 (b ^ lam))

theorem decayKzrOne_nonneg {p c C₀ lam b : ℝ} (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) :
    0 ≤ decayKzrOne p c C₀ lam b := by
  have h1 : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
    have := mul_nonneg hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith [Real.pi_pos]
  have h2 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  rw [decayKzrOne]
  exact mul_nonneg h1 (mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) h2)


end Work.FTS.BSIdent.Weyl.Levels
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels._dev2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev2

open Filter Set MeasureTheory
open scoped Topology

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The odd extension of `Φ(·,·,τ)` as a two-variable function. -/
noncomputable def GG (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ


theorem abs_pi_div_two_lt : |Real.pi / 2| < Real.pi / 2 + 1 := by
  rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith

/-- The slice-in-`θ` version of `hsm`. -/
theorem contDiffAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : -1 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  hsm w θ hw (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])

theorem continuousAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : -1 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  (contDiffAt_Phi hsm hw hθ).continuousAt

theorem continuousAt_pdR_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : -1 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdR_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

theorem continuousAt_pdZ_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : -1 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdZ_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

/-! ## The slice identities for `GG` -/

theorem GG_of_pos {w θ : ℝ} (hθ : 0 < θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ.le

theorem GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ

theorem GG_of_neg {w θ : ℝ} (hθ : θ < 0) : GG Φ τ w θ = -(Φ w (-θ) τ) :=
  Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ)

theorem pdR_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_pos (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdR (GG Φ τ) w θ = -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => -(Φ w' (-θ) τ)) := by
    funext w'; exact GG_of_neg (Φ := Φ) (τ := τ) hθ
  have h2 : deriv (fun w' : ℝ => -(Φ w' (-θ) τ)) w
      = -deriv (fun w' : ℝ => Φ w' (-θ) τ) w := by
    rw [show (fun w' : ℝ => -(Φ w' (-θ) τ)) = -(fun w' : ℝ => Φ w' (-θ) τ) from rfl,
      deriv.neg]
  simp only [Work.Cyl.pdR, h, h2]

theorem pdZ_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w θ := by
  simp only [Work.Cyl.pdZ]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hθ] with θ' hθ'
  exact GG_of_pos (Φ := Φ) (τ := τ) hθ'

theorem pdZ_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w (-θ) := by
  simp only [Work.Cyl.pdZ]
  have h : (fun θ' => GG Φ τ w θ') =ᶠ[𝓝 θ] (fun θ' => -(Φ w (-θ') τ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hθ] with θ' hθ'
    exact GG_of_neg (Φ := Φ) (τ := τ) hθ'
  rw [Filter.EventuallyEq.deriv_eq h]
  have h3 : deriv (fun θ' : ℝ => -(Φ w (-θ') τ)) θ
      = - deriv (fun θ' : ℝ => Φ w (-θ') τ) θ := by
    rw [show (fun θ' : ℝ => -(Φ w (-θ') τ)) = -(fun θ' : ℝ => Φ w (-θ') τ) from rfl,
      deriv.neg]
  have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ
      = - deriv (fun θ'' : ℝ => Φ w θ'' τ) (-θ) :=
    deriv_comp_neg (fun θ'' : ℝ => Φ w θ'' τ) θ
  rw [h3, h2, neg_neg]

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` near `θ = ±π/2` -/

theorem continuousAt_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ) (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2)) (g := fun q : ℝ × ℝ => Φ q.1 q.2 τ) h1 hneg
  have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdR_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdR_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdZ_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdZ_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : -1 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.congr hev

/-! ## Continuity of `GG`, `pdR GG` at `θ = 0` -/

theorem continuousAt_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, 0) := by
  have hval : GG Φ τ w₀ 0 = 0 := by
    rw [GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl]; exact h0 w₀ hw₀
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (-1:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [h0 w₀ hw₀] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hnegΦ : Tendsto (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (w₀, 0) :=
        continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have hbase := hcont.tendsto.comp hneg
      rwa [h0 w₀ hw₀] at hbase
    have hc : Tendsto (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ))
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hnegΦ.neg
    have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

theorem continuousAt_pdR_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, 0) := by
  have hslice : (fun w' => GG Φ τ w' 0) = (fun w' => Φ w' 0 τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl
  have hval : Work.Cyl.pdR (GG Φ τ) w₀ 0 = 0 := by
    show deriv (fun w' => GG Φ τ w' 0) w₀ = 0
    rw [hslice]
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hpdR0 : Work.Cyl.pdR (fun w θ => Φ w θ τ) w₀ 0 = 0 := by
    show deriv (fun w' => Φ w' 0 τ) w₀ = 0
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (-1:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [hpdR0] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hbaseΦ : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
          (w₀, 0) := continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have h1' := hcont.tendsto.comp hneg
      rwa [hpdR0] at h1'
    have hc : Tendsto (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hbaseΦ.neg
    have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` at interior points -/







end Work.FTS.BSIdent.Weyl.Dev2
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

/-!
# The slice difference quotient of a `C²` function

If a two-variable function `f` is `C²` near `(w₀, θ₀)` and vanishes identically on the vertical
line `θ = θ₀` (near `w₀`), then the difference quotient `(w, θ) ↦ f w θ / (θ - θ₀)` extends
continuously to `(w₀, θ₀)` with value `∂_θ f (w₀, θ₀)`.

The proof is the mean value theorem applied to the `θ`-slice `s ↦ f w s`: the quotient equals
`∂_θ f (w, ξ)` for some `ξ` strictly between `θ` and `θ₀`, and the map
`(w, ξ) ↦ ∂_θ f (w, ξ)` is continuous at `(w₀, θ₀)` because `f` is `C²` there.  (The latter is
the statement that `fderiv ℝ` of a `C¹` map is continuous, together with the identification of
the one-dimensional `deriv` of the slice with `fderiv` of the uncurried function evaluated in
the direction `(0,1)`.)
-/

/-- The affine map `s ↦ (w, s)` has derivative the linear map `(0, 1)`. -/
private lemma hasFDerivAt_prodMk_const_left (w s : ℝ) :
    HasFDerivAt (fun s' : ℝ => ((w, s') : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) s :=
  (hasFDerivAt_const (x := s) w).prodMk (hasFDerivAt_id (x := s))

/-- The `θ`-slice derivative `(w, θ) ↦ ∂_θ f (w, θ)` of a `C²` function is continuous. -/
private lemma continuousAt_slice_deriv {f : ℝ → ℝ → ℝ} {w₀ θ₀ : ℝ}
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀)) :
    ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) := by
  set F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 with hFdef
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), DifferentiableAt ℝ F p :=
    (h.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (w₀, θ₀) := h.fderiv_right (m := 1) (by norm_num)
  have hΦ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) (w₀, θ₀) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.continuousAt.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  -- the `deriv` of the slice is `fderiv F` evaluated at `(0,1)` (chain rule)
  have hcomp := hp.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_const_left p.1 p.2)
  have h1 : deriv (fun s : ℝ => f p.1 s) p.2
      = ((fderiv ℝ F p).comp ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 :=
    hcomp.hasDerivAt.deriv
  rw [h1, ContinuousLinearMap.comp_apply]
  simp

/-- A point of the interval `[min a b, max a b]` is at least as close to `b` as `a` is. -/
private lemma abs_sub_le_of_mem_Icc_min_max {a b s : ℝ}
    (hs : s ∈ Set.Icc (min a b) (max a b)) : |s - b| ≤ |a - b| := by
  rcases le_total a b with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
    linarith [hs.1]
  · rw [min_eq_right hle, max_eq_left hle] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
    linarith [hs.2]

/-- Continuity of a slice of a function that is `C²` at every relevant point. -/
private lemma continuousOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    ContinuousOn (fun s => f w s) U := fun s hs =>
  ((h s hs).continuousAt.comp (hasFDerivAt_prodMk_const_left w s).continuousAt).continuousWithinAt

/-- Differentiability of a slice of a function that is `C²` at every relevant point. -/
private lemma differentiableOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    DifferentiableOn ℝ (fun s => f w s) U := fun s hs =>
  (((h s hs).differentiableAt (by norm_num)).comp s
    (hasFDerivAt_prodMk_const_left w s).differentiableAt).differentiableWithinAt

/-- **Mean value theorem for the slice quotient.**  If the slice `s ↦ f w s` is continuous on
`[min θ θ₀, max θ θ₀]` and differentiable on the open interval, and `f w θ₀ = 0`, then the
difference quotient `f w θ / (θ - θ₀)` is the value of the slice derivative at some interior
point. -/
private lemma slice_quotient_eq_deriv {f : ℝ → ℝ → ℝ} {w θ θ₀ : ℝ} (hne : θ ≠ θ₀)
    (hz : f w θ₀ = 0)
    (hcont : ContinuousOn (fun s => f w s) (Set.Icc (min θ θ₀) (max θ θ₀)))
    (hdiff : DifferentiableOn ℝ (fun s => f w s) (Set.Ioo (min θ θ₀) (max θ θ₀))) :
    ∃ ξ ∈ Set.Ioo (min θ θ₀) (max θ θ₀),
      deriv (fun s => f w s) ξ = f w θ / (θ - θ₀) := by
  have hlt : min θ θ₀ < max θ θ₀ := min_lt_max.mpr hne
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun s => f w s) hlt hcont hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [hξeq]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, hz, zero_sub,
      show θ₀ - θ = -(θ - θ₀) from by ring, div_neg, neg_div, neg_neg]
  · rw [min_eq_right h.le, max_eq_left h.le, hz, sub_zero]

/-- Every point of `[min θ θ₀, max θ θ₀]` lies within the `δ`-neighbourhood of `θ₀` whenever
`θ` does. -/
private lemma slice_contDiffAt_of_mem_Icc {f : ℝ → ℝ → ℝ} {w w₀ θ₀ θ δ : ℝ}
    (hw : |w - w₀| < δ) (hθ : |θ - θ₀| < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ)) :
    ∀ s ∈ Set.Icc (min θ θ₀) (max θ θ₀),
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s) := by
  intro s hs
  have hs' : |s - θ₀| < δ := lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max hs) hθ
  exact hsm w s hw hs'

theorem tendsto_slice_quotient {f : ℝ → ℝ → ℝ} {w₀ θ₀ δ : ℝ} (hδ : 0 < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ))
    (hz : ∀ w, |w - w₀| < δ → f w θ₀ = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / (p.2 - θ₀))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀))
      (𝓝 (deriv (fun θ => f w₀ θ) θ₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- `f` is `C²` at the base point, so the slice derivative is continuous there
  have hbase : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀) :=
    hsm w₀ θ₀ (by simpa using hδ) (by simpa using hδ)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) :=
    continuousAt_slice_deriv hbase
  obtain ⟨η₁, hη₁pos, hη₁⟩ :=
    Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcont ε hε)
  -- shrink the neighbourhood so that it stays inside the `δ`-box
  set η : ℝ := min η₁ δ with hηdef
  have hηpos : 0 < η := lt_min hη₁pos hδ
  have hηδ : η ≤ δ := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hbox : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), |p.1 - w₀| < η ∧ |p.2 - θ₀| < η := by
    filter_upwards [Metric.ball_mem_nhds (w₀, θ₀) hηpos] with p hp
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
    exact hp
  have hboxS : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      |p.1 - w₀| < η ∧ |p.2 - θ₀| < η :=
    hbox.filter_mono nhdsWithin_le_nhds
  have hSne : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      p.2 ≠ θ₀ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.2.2
  refine (hboxS.and hSne).mono ?_
  rintro p ⟨⟨hp1, hp2⟩, hpne⟩
  rw [Real.dist_eq]
  have hwδ : |p.1 - w₀| < δ := lt_of_lt_of_le hp1 hηδ
  have hθδ : |p.2 - θ₀| < δ := lt_of_lt_of_le hp2 hηδ
  have hz' : f p.1 θ₀ = 0 := hz p.1 hwδ
  -- the mean value theorem on the `θ`-slice at fixed first coordinate
  have hC2 := slice_contDiffAt_of_mem_Icc hwδ hθδ hsm
  obtain ⟨ξ, hξ, hξeq⟩ := slice_quotient_eq_deriv hpne hz'
    (continuousOn_slice hC2)
    (differentiableOn_slice (fun s hs => hC2 s (Ioo_subset_Icc_self hs)))
  -- `(p.1, ξ)` is still in the small box, so the derivative is close to the limit
  have hξb : |ξ - θ₀| < η :=
    lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max (Ioo_subset_Icc_self hξ)) hp2
  have hdist : dist ((p.1, ξ) : ℝ × ℝ) (w₀, θ₀) < η := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hp1, hξb⟩
  have hb := hη₁ (y := (p.1, ξ)) (lt_of_lt_of_le hdist hηη₁)
  rw [Real.dist_eq] at hb
  rw [← hξeq]
  exact hb

end Work.FTS.BSIdent.Weyl.Levels
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWeightAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FireFix.Clauses.PsiWeightAux`

The vocabulary and the two analytic pointwise lemmas underlying
`Work.FTS.FireFix.Clauses.integrableOn_psi_weight`:

* `psiWq1` .. `psiWq4` -- the four summands of the majorant (`1_{q.1 <= L}`, `sin^{a-1}cos^{2a}`,
  `(D_theta g)^2 sin(2theta)^{-gamma}`, `cos^2 theta sin(2theta)^{gamma-2}`);
* `psiWinner`, `psiWmaj`, `psiWpsi` -- the inner bracket, the majorant and the goal integrand;
* `psiMeasurableRpowConst` -- `x |-> x^r` is measurable for every real `r`;
* `psiIntegrableOnConstMul` -- `IntegrableOn` is stable under left multiplication by a constant;
* `psiTwoMulSqrtLe` -- the AM-GM inequality `2 sqrt a sqrt b <= a + b`;
* `psiWmajNonneg` -- the majorant is nonnegative on the strip;
* `psiWpsiLeWmaj` -- the pointwise bound `|psiWpsi q| <= psiWmaj q` on the strip off `q.2 = 0`.

The proof of `psiWpsiLeWmaj` is an explicit case analysis on `q.1 <= L` with the rpow bookkeeping
`(b q.1)^s q.1^{1/a-1} = b^s q.1^{2/(3a)-1}` etc.; the `|d_theta g|` block is closed by AM-GM
`2 sqrt(A^2 s2^{-g}) sqrt(c^2 s2^{g-2}) <= A^2 s2^{-g} + c^2 s2^{g-2}`.
-/

open MeasureTheory Set Filter Topology

namespace Work.FTS.FireFix.Clauses

set_option maxHeartbeats 1000000


/-- The `(q.1 ≤ L)` cutoff. -/
noncomputable def psiWq1 (L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => if q.1 ≤ L then (1 : ℝ) else 0

/-- The angular `sin^{α-1}cos^{2α}` piece. -/
noncomputable def psiWq2 (α L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α) * psiWq1 L q

/-- The `(D_θg)² sin(2θ)^{-γ}` piece. -/
noncomputable def psiWq3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Work.Spaces.Dth f q.1 (abs q.2)) ^ 2
    * (Real.sin (2 * abs q.2)) ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α)))

/-- The `cos²θ sin(2θ)^{γ-2}` piece. -/
noncomputable def psiWq4 (γ L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Real.cos q.2) ^ 2 * (Real.sin (2 * abs q.2)) ^ (γ - 2) * psiWq1 L q

/-- The inner bracket of the goal integrand. -/
noncomputable def psiWinner (α Ca Cb Cc : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
    + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
    + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
      / ((B τ * q.1) ^ (1 / (3 * α)))

/-- The majorant. -/
noncomputable def psiWmaj (α Ca Cb Cc L : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q =>
    (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
        + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q
      + Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          * psiWq2 α L q
      + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q
      + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q

/-- The goal integrand. -/
noncomputable def psiWpsi (α Ca Cb Cc L : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q : ℝ × ℝ =>
    (if q.1 ≤ L then psiWinner α Ca Cb Cc B g τ q else 0) * q.1 ^ (1 / α - 1) * Real.cos q.2

/-- `x ↦ x^r` is measurable for every real `r`. -/
theorem psiMeasurableRpowConst (r : ℝ) : Measurable (fun x : ℝ => x ^ r) := by
  by_cases hr : 0 ≤ r
  · exact (Real.continuous_rpow_const hr).measurable
  · push_neg at hr
    have hcomp : (fun x : ℝ => x ^ r) = (fun y : ℝ => y ^ (-r)) ∘ (fun x : ℝ => x⁻¹) := by
      funext x
      have hx : x ^ r = x⁻¹ ^ (-r) := by
        conv_lhs => rw [show r = -(-r) from by ring]
        rw [Real.rpow_neg_eq_inv_rpow]
      simpa [Function.comp_apply] using hx
    rw [hcomp]
    exact ((Real.continuous_rpow_const (by linarith)).measurable).comp measurable_inv

theorem psiIntegrableOnConstMul {c : ℝ} {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : MeasureTheory.IntegrableOn f s) :
    MeasureTheory.IntegrableOn (fun q => c * f q) s := by
  change MeasureTheory.Integrable (fun q => c * f q) (MeasureTheory.volume.restrict s)
  change MeasureTheory.Integrable f (MeasureTheory.volume.restrict s) at hf
  exact hf.const_mul c

/-- `2 √a √b ≤ a + b`. -/
theorem psiTwoMulSqrtLe {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- Nonnegativity of the majorant on the strip. -/
theorem psiWmajNonneg {α Ca Cb Cc L : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hb : 0 < B τ) (hL : 0 ≤ L)
    {q : ℝ × ℝ} (hq : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ psiWmaj α Ca Cb Cc L B g τ q := by
  have hcos : 0 ≤ Real.cos q.2 := le_of_lt (Real.cos_pos_of_mem_Ioo hq)
  have habs : |q.2| < Real.pi / 2 := abs_lt.mpr hq
  have hsin2 : 0 ≤ Real.sin (2 * |q.2|) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    linarith [Real.pi_pos]
  have hsina : 0 ≤ Real.sin |q.2| :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  have h1 : 0 ≤ psiWq1 L q := by simp only [psiWq1]; split <;> norm_num
  have h2 : 0 ≤ psiWq2 α L q := by
    simp only [psiWq2]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hsina _)
      (Real.rpow_nonneg hcos _)) h1
  have h4 : 0 ≤ psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q := by
    simp only [psiWq4]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin2 _)) h1
  have h3 : 0 ≤ psiWq3 α (Work.FTS.Regularity.gSlice g τ) q := by
    simp only [psiWq3]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin2 _)
  have hb1 : 0 ≤ (B τ) ^ (- (1 / (3 * α))) := Real.rpow_nonneg hb.le _
  have hm1 : 0 ≤ L ^ (2 / (3 * α) - 1) := Real.rpow_nonneg hL _
  have hm2 : 0 ≤ L ^ (2 / (3 * α)) := Real.rpow_nonneg hL _
  have hb2 : 0 ≤ (B τ) ^ (1 - 1 / (3 * α)) := Real.rpow_nonneg hb.le _
  unfold psiWmaj
  have e1 : 0 ≤ (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
      + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hCa hb1) hm1)
      (mul_nonneg (mul_nonneg hCb hb2) hm2)) h1
  have e2 : 0 ≤ Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
      * psiWq2 α L q :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (by norm_num))
      (sq_nonneg α)) hb1) hm1) h2
  have e3 : 0 ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
      * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCc hb1) hm1) (by norm_num)) h3
  have e4 : 0 ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
      * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCc hb1) hm1) (by norm_num)) h4
  linarith

/-- The pointwise bound. -/
theorem psiWpsiLeWmaj {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {Ca Cb Cc L : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hL : 0 ≤ L)
    {q : ℝ × ℝ} (hq1 : 0 < q.1)
    (hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hq0 : q.2 ≠ 0) :
    ‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q := by
  have hα : 0 < α := h.hα
  have hb : 0 < B τ := h.hB τ hτ
  have hcos : 0 < Real.cos q.2 := Real.cos_pos_of_mem_Ioo hq2
  have hcosne : Real.cos q.2 ≠ 0 := ne_of_gt hcos
  have hcosle : Real.cos q.2 ≤ 1 := Real.cos_le_one _
  have habsx : |q.2| < Real.pi / 2 := abs_lt.mpr hq2
  have hsin2pos : 0 < Real.sin (2 * |q.2|) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    linarith [Real.pi_pos]
  have h3a : (3 : ℝ) * α ≠ 0 := by positivity
  have hαne : α ≠ 0 := ne_of_gt hα
  have hsina : 0 ≤ Real.sin |q.2| :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  have hA1 : (1 : ℝ) / α = 3 / (3 * α) := by
    rw [div_eq_div_iff hαne h3a]; ring
  have hkey1 : 1 / α - 1 + (- (1 / (3 * α))) = 2 / (3 * α) - 1 := by
    have h3 : (3 : ℝ) / (3 * α) - 1 / (3 * α) = 2 / (3 * α) := by
      rw [div_sub_div_same]; norm_num
    rw [hA1]; linarith
  have hkey2 : 1 - 1 / (3 * α) + (1 / α - 1) = 2 / (3 * α) := by
    have h3 : (3 : ℝ) / (3 * α) - 1 / (3 * α) = 2 / (3 * α) := by
      rw [div_sub_div_same]; norm_num
    rw [hA1]; linarith
  have hkey3 : (3 * α - 1) / (3 * α) = 1 - 1 / (3 * α) := by
    rw [← div_sub_div_same, div_self h3a]
  have hexp1 : (0 : ℝ) ≤ 2 / (3 * α) - 1 := by
    rw [sub_nonneg, one_le_div (by positivity : (0 : ℝ) < 3 * α)]; linarith [h.hα13]
  by_cases hLq : q.1 ≤ L
  · have hqL : q.1 ≤ L := hLq
    have hXpos : 0 < (B τ * q.1) ^ (1 / (3 * α)) :=
      Real.rpow_pos_of_pos (mul_pos hb hq1) _
    have hYnn : 0 ≤ (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) :=
      Real.rpow_nonneg (mul_nonneg hb.le hq1.le) _
    have hZnn : 0 ≤ q.1 ^ (1 / α - 1) := Real.rpow_nonneg hq1.le _
    have hsann : 0 ≤ (Real.sin (abs q.2)) ^ (α - 1) := Real.rpow_nonneg hsina _
    have hc2nn : 0 ≤ (Real.cos q.2) ^ (2 * α - 1) := Real.rpow_nonneg hcos.le _
    have hWnn : 0 ≤ (Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (Real.cos q.2) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α)))) * q.1 ^ (1 / α - 1) * Real.cos q.2 := by
      have h1 : 0 ≤ Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2) :=
        div_nonneg hCa (le_of_lt (mul_pos hXpos hcos))
      have h2 : 0 ≤ Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) := mul_nonneg hCb hYnn
      have h3 : 0 ≤ Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
          * (Real.cos q.2) ^ (2 * α - 1)
          + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α))) :=
        div_nonneg (mul_nonneg hCc (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 200) (sq_nonneg α))
            hsann) hc2nn) (abs_nonneg _))) hXpos.le
      exact mul_nonneg (mul_nonneg (add_nonneg (add_nonneg h1 h2) h3) hZnn) hcos.le
    have hcancel : ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * Real.cos q.2
        = ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ := by
      rw [mul_inv, show ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ * (Real.cos q.2)⁻¹ * Real.cos q.2
        = ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ * ((Real.cos q.2)⁻¹ * Real.cos q.2) from by ring,
        inv_mul_cancel₀ hcosne, mul_one]
    have hZinv : ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        = (B τ) ^ (- (1 / (3 * α))) * q.1 ^ (- (1 / (3 * α))) := by
      rw [← Real.rpow_neg (mul_nonneg hb.le hq1.le), Real.mul_rpow hb.le hq1.le]
    have hZmul : q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        = (B τ) ^ (- (1 / (3 * α))) * q.1 ^ (2 / (3 * α) - 1) := by
      rw [hZinv,
        show q.1 ^ (1 / α - 1) * ((B τ) ^ (- (1 / (3 * α))) * q.1 ^ (- (1 / (3 * α))))
          = (B τ) ^ (- (1 / (3 * α))) * (q.1 ^ (1 / α - 1) * q.1 ^ (- (1 / (3 * α)))) from by
            ring,
        ← Real.rpow_add hq1, hkey1]
    have hZmul3 : q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        ≤ (B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1) := by
      rw [hZmul]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq1.le hqL hexp1)
        (Real.rpow_nonneg hb.le _)
    have hZmul2 : (B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)
        = (B τ) ^ (1 - 1 / (3 * α)) * q.1 ^ (2 / (3 * α)) := by
      rw [Real.mul_rpow hb.le hq1.le,
        show (B τ ^ (1 - 1 / (3 * α)) * q.1 ^ (1 - 1 / (3 * α))) * q.1 ^ (1 / α - 1)
          = (B τ) ^ (1 - 1 / (3 * α)) * (q.1 ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) from by
            ring,
        ← Real.rpow_add hq1, hkey2]
    have hZmul4 : (B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)
        ≤ (B τ) ^ (1 - 1 / (3 * α)) * L ^ (2 / (3 * α)) := by
      rw [hZmul2]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq1.le hqL (by positivity))
        (Real.rpow_nonneg hb.le _)
    have hterm1 : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) := by
      have heq : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Ca * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹) := by
        rw [div_eq_mul_inv,
          show Ca * ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * q.1 ^ (1 / α - 1)
            * Real.cos q.2
            = Ca * (((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * Real.cos q.2)
              * q.1 ^ (1 / α - 1) from by ring,
          hcancel]
        ring
      rw [heq]
      calc Ca * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
          ≤ Ca * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
            mul_le_mul_of_nonneg_left hZmul3 hCa
        _ = Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) := by ring
    have hterm2 : Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))) := by
      have heq : Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * Real.cos q.2 := by
        rw [hkey3]; ring
      rw [heq]
      have hYnn2 : 0 ≤ (B τ * q.1) ^ (1 - 1 / (3 * α)) :=
        Real.rpow_nonneg (mul_nonneg hb.le hq1.le) _
      have hb2 : 0 ≤ Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) :=
        mul_nonneg hCb (mul_nonneg hYnn2 hZnn)
      calc Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * Real.cos q.2
          ≤ Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * 1 :=
            mul_le_mul_of_nonneg_left hcosle hb2
        _ = Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) := by ring
        _ ≤ Cb * ((B τ) ^ (1 - 1 / (3 * α)) * L ^ (2 / (3 * α))) :=
            mul_le_mul_of_nonneg_left hZmul4 hCb
        _ = Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))) := by ring
    have hterm3 : Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
          * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)) := by
      have hcpow : (Real.cos q.2) ^ (2 * α - 1) * Real.cos q.2
          = (Real.cos q.2) ^ (2 * α) := by
        have h := Real.rpow_add hcos (2 * α - 1) 1
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        ring
      have heq : Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * ((Real.cos q.2) ^ (2 * α - 1) * Real.cos q.2) := by
        rw [div_eq_mul_inv]; ring
      rw [heq, hcpow]
      have hc2nn2 : 0 ≤ (Real.cos q.2) ^ (2 * α) := Real.rpow_nonneg hcos.le _
      have hstep : Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (Real.cos q.2) ^ (2 * α)
          ≤ Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1))
            * (Real.cos q.2) ^ (2 * α) := by
        refine mul_le_mul_of_nonneg_right ?_ hc2nn2
        exact mul_le_mul_of_nonneg_left hZmul3
          (mul_nonneg (mul_nonneg (mul_nonneg hCc (by norm_num)) (sq_nonneg α)) hsann)
      calc _ ≤ _ := hstep
        _ = Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
              * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)) := by ring
    have hterm4 : Cc * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|
          / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * ((Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)) ^ 2
              * (Real.sin (2 * abs q.2))
                  ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α)))
            + (Real.cos q.2) ^ 2
              * (Real.sin (2 * abs q.2))
                  ^ (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 2)) := by
      set P := Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2) with hP
      set D := Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2) with hD
      set s2 := Real.sin (2 * abs q.2) with hs2
      set gc := Work.Spaces.gam (Work.FTS.Regularity.pExp α) with hgc
      have hDdef : D = s2 * P := by rw [hD, hs2, hP]; rfl
      have hs2pos : 0 < s2 := by rw [hs2]; exact hsin2pos
      have hD2 : D ^ 2 = s2 ^ (2 : ℝ) * P ^ 2 := by
        rw [hDdef, mul_pow, Real.rpow_two]
      have hA3 : D ^ 2 * s2 ^ (- gc) = P ^ 2 * s2 ^ (2 - gc) := by
        have e1 : s2 ^ (2 : ℝ) * s2 ^ (- gc) = s2 ^ ((2 : ℝ) - gc) := by
          rw [← Real.rpow_add hs2pos (x := s2) (y := (2 : ℝ)) (z := -gc),
            show (2 : ℝ) + -gc = 2 - gc from by ring]
        rw [hD2,
          show s2 ^ (2 : ℝ) * P ^ 2 * s2 ^ (- gc)
            = P ^ 2 * (s2 ^ (2 : ℝ) * s2 ^ (- gc)) from by ring, e1]
      have hW3 : (0:ℝ) ≤ D ^ 2 * s2 ^ (- gc) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs2pos.le _)
      have hW4 : (0:ℝ) ≤ (Real.cos q.2) ^ 2 * s2 ^ (gc - 2) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs2pos.le _)
      have hprod : D ^ 2 * s2 ^ (- gc) * ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
          = (|P| * Real.cos q.2) ^ 2 := by
        have e2 : s2 ^ (2 - gc) * s2 ^ (gc - 2) = 1 := by
          rw [← Real.rpow_add hs2pos (x := s2) (y := 2 - gc) (z := gc - 2)]
          rw [show 2 - gc + (gc - 2) = 0 from by ring, Real.rpow_zero]
        rw [hA3,
          show P ^ 2 * s2 ^ (2 - gc) * ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
            = P ^ 2 * (Real.cos q.2) ^ 2 * (s2 ^ (2 - gc) * s2 ^ (gc - 2)) from by ring,
          e2, mul_one,
          show (|P| * Real.cos q.2) ^ 2 = P ^ 2 * (Real.cos q.2) ^ 2 from by
            rw [mul_pow, sq_abs]]
      have hsqrt : Real.sqrt (D ^ 2 * s2 ^ (- gc))
            * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
          = |P| * Real.cos q.2 := by
        rw [← Real.sqrt_mul hW3, hprod, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mul_nonneg (abs_nonneg _) hcos.le)]
      have heq : Cc * |P| / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1)
            * Real.cos q.2
          = Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (|P| * Real.cos q.2) := by
        rw [div_eq_mul_inv]; ring
      rw [heq, ← hsqrt]
      have hbnd : Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
          ≤ Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
        mul_le_mul_of_nonneg_left hZmul3 hCc
      have hsnn : 0 ≤ Real.sqrt (D ^ 2 * s2 ^ (- gc))
          * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hconstnn : 0 ≤ Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
        mul_nonneg hCc (mul_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hL _))
      calc Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (Real.sqrt (D ^ 2 * s2 ^ (- gc))
              * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2)))
          ≤ (Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)))
            * (Real.sqrt (D ^ 2 * s2 ^ (- gc))
              * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))) :=
            mul_le_mul_of_nonneg_right hbnd hsnn
        _ ≤ (Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)))
            * ((D ^ 2 * s2 ^ (- gc) + (Real.cos q.2) ^ 2 * s2 ^ (gc - 2)) / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hconstnn
            linarith [psiTwoMulSqrtLe hW3 hW4]
        _ = (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
            * ((D ^ 2 * s2 ^ (- gc)
              + (Real.cos q.2) ^ 2 * s2 ^ (gc - 2))) := by ring
    simp only [psiWpsi, psiWinner, psiWmaj, psiWq1, psiWq2, psiWq3, psiWq4, if_pos hLq, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hWnn]
    have hsum : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
              * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
            * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cc * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|
            / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
            + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))))
          + (Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
              * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)))
          + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
              * ((Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)) ^ 2
                  * (Real.sin (2 * abs q.2))
                      ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
          + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
              * ((Real.cos q.2) ^ 2
                  * (Real.sin (2 * abs q.2))
                      ^ (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 2)) := by
      linarith [hterm1, hterm2, hterm3, hterm4]
    refine le_trans (le_of_eq ?_) hsum
    ring
  · have hW : psiWpsi α Ca Cb Cc L B g τ q = 0 := by
      simp only [psiWpsi, psiWinner, if_neg hLq, zero_mul]
    rw [hW, norm_zero]
    exact psiWmajNonneg hCa hCb hCc hb hL hq2


end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.PhysData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix


/-! ## The clock data at the amplitude normalisation `C.A = 2A` -/

/-- **The derivative datum of the clock transport.**  If `C.A = 2·A` on the fake-time half-line
(design correction 2), then `d t := (C.A (τ(t)))⁻¹` is bounded and `α`-Hölder on `[0,S']` whenever
`τ = Work.FTS.Physical.clockInv C` maps `[0,S']` into `[0,Sel]` and is Lipschitz — the hypotheses of
`bsAdmissibleStripFull_comp_clock`.  The content is that `d = (1/2)·(A ∘ τ)⁻¹`, and the statement
for `(A ∘ τ)⁻¹` is `Prime.RegPkgClockData.regPkg_clock_data`. -/
theorem clock_deriv_data {α S Sel S' : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock} (hreg : Work.FTS.RegPkgGal.RegPkg' α Sel A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) S', Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
      |Work.FTS.Physical.clockInv C t - Work.FTS.Physical.clockInv C t'| ≤ L * |t - t'|) :
    (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', |(C.A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ L) ∧
      (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
        |(C.A (Work.FTS.Physical.clockInv C t))⁻¹ - (C.A (Work.FTS.Physical.clockInv C t'))⁻¹| ≤ L * |t - t'| ^ α) := by
  obtain ⟨hbddA, hholdA⟩ :=
    Prime.regPkg_clock_data (α := α) (S := Sel) (T := S') hreg hmem
      (fun t _ => rfl) hlip
  have hAτ : ∀ t ∈ Set.Icc (0 : ℝ) S', C.A (Work.FTS.Physical.clockInv C t) = 2 * A (Work.FTS.Physical.clockInv C t) :=
    fun t ht => hAeq _ (hmem t ht).1
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := hbddA
    refine ⟨L / 2, fun t ht => ?_⟩
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by rw [hAτ t ht]
    rw [h1, _root_.mul_inv_rev, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹| * (2 : ℝ)⁻¹
        ≤ L * (2 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (hL t ht) (by norm_num)
      _ = L / 2 := by ring
  · obtain ⟨L, hL⟩ := hholdA
    refine ⟨L / 2, fun t ht t' ht' => ?_⟩
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by rw [hAτ t ht]
    have h2 : (C.A (Work.FTS.Physical.clockInv C t'))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t'))⁻¹ := by rw [hAτ t' ht']
    have h3 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          - (C.A (Work.FTS.Physical.clockInv C t'))⁻¹
        = ((A (Work.FTS.Physical.clockInv C t))⁻¹
            - (A (Work.FTS.Physical.clockInv C t'))⁻¹) * (2 : ℝ)⁻¹ := by
      rw [h1, h2, _root_.mul_inv_rev, _root_.mul_inv_rev]; ring
    rw [h3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹ - (A (Work.FTS.Physical.clockInv C t'))⁻¹|
            * (2 : ℝ)⁻¹
        ≤ (L * |t - t'| ^ α) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hL t ht t' ht') (by norm_num)
      _ = L / 2 * |t - t'| ^ α := by ring

/-! ## The per-strip admissible bundles of the (negated) physical vorticity -/

/-- **THE PER-STRIP BUNDLE OF THE PHYSICAL VORTICITY (sign of correction 1).**  For every physical
strip `S' ∈ (0, C.T)` there is a radius `R > 0` such that the negated physical vorticity
`x ↦ −physOmega α A B g C x t` satisfies the full admissible-strip bundle `BSAdmissibleStripFull`
on `[0,S']`.

This is the design's correction 3: the *single* radius is replaced by one radius per strip, read
off `Prime.PhysVortBundle.physVort_bundle` at the fake strip `[0, Work.FTS.Physical.clockInv C S']` and transported
along the clock.  No uniform-in-`τ` support hypothesis (`hZ`) and no bound on the scaling (`hb`) is
needed. -/
theorem physOmega_bundle {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ) :
    ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S' := by
  intro S' hS'
  have hS'pos : 0 < S' := hS'.1
  have hS'T : S' < C.T := hS'.2
  have hS'mem : S' ∈ Set.Ico 0 C.T := ⟨hS'pos.le, hS'T⟩
  set Sel : ℝ := Work.FTS.Physical.clockInv C S' with hSeldef
  have hSelpos : 0 < Sel := by rw [hSeldef]; exact Work.FTS.Physical.clockInv_pos_of_pos C hS'
  have hsel : Work.FTS.RegPkgGal.RegPkg' (α : ℝ) Sel A B g := hreg Sel hSelpos
  obtain ⟨R', hR'pos, hbunsel⟩ := Prime.physVort_bundle hsel
  rw [Work.FTS.Physical.nnreal_mk_coe_eq α] at hbunsel
  -- the clock maps `[0,S']` into `[0,Sel]`
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) S', Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel := by
    intro t ht
    have htT : t ∈ Set.Ico 0 C.T := ⟨ht.1, lt_of_le_of_lt ht.2 hS'T⟩
    refine ⟨Work.FTS.Physical.clockInv_nonneg C htT, ?_⟩
    rw [hSeldef]
    exact Work.FTS.Physical.clockInv_mono C htT hS'mem ht.2
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) S',
      HasDerivAt (Work.FTS.Physical.clockInv C) ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      simpa using Work.FTS.Physical.clockInv_hasDerivAt_zero C
    · exact Work.FTS.Physical.clockInv_hasDerivAt C ⟨h0, lt_of_le_of_lt ht.2 hS'T⟩
  -- the a priori bound on the derivative
  obtain ⟨a₀, _a₁, ha₀pos, ha⟩ := hsel.hAb
  have hbddA : ∀ t ∈ Set.Icc (0 : ℝ) S', |(A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ max (a₀⁻¹) 0 := by
    intro t ht
    have hAt : a₀ ≤ A (Work.FTS.Physical.clockInv C t) := (ha _ (hmem t ht)).1
    have hApos : 0 < A (Work.FTS.Physical.clockInv C t) := lt_of_lt_of_le ha₀pos hAt
    rw [abs_of_pos (inv_pos.mpr hApos)]
    exact le_trans (by simpa [one_div] using one_div_le_one_div_of_le ha₀pos hAt)
      (le_max_left (a₀⁻¹) 0)
  have hbddC : ∀ t ∈ Set.Icc (0 : ℝ) S',
      |(C.A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ max (a₀⁻¹) 0 / 2 := by
    intro t ht
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by
      rw [hAeq _ (hmem t ht).1]
    rw [h1, _root_.mul_inv_rev, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹| * (2 : ℝ)⁻¹
        ≤ max (a₀⁻¹) 0 * (2 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (hbddA t ht) (by norm_num)
      _ = max (a₀⁻¹) 0 / 2 := by ring
  have hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
      |Work.FTS.Physical.clockInv C t - Work.FTS.Physical.clockInv C t'| ≤ L * |t - t'| :=
    Prime.lipschitz_of_hasDerivAt_bounded
      (div_nonneg (le_max_right (a₀⁻¹) 0) (by norm_num)) hderiv hbddC
  -- the two clauses of the derivative datum at the amplitude `C.A = 2A`
  obtain ⟨hdbb, hdhold⟩ := clock_deriv_data (S := Sel) (C := C) hsel hAeq hmem hlip
  have htrans := Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
    (α := α) hSelpos hS'pos hbunsel hmem hderiv hlip hdbb hdhold
  exact ⟨R', BSAdmissibleStripFull_neg htrans⟩

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Const =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## The self-similar pair of `CoreResiduals` as an instance of the dynamical ansatz -/



/-! ## `(E)` at the constant rate -/




end Work.FTS.MeridianDyn
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_win =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd_win`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are odd in the axial variable `z` *on the time window*
`(0,T)`, off the axis `z = 0`.

This is the windowed variant of `Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne`: the oddness of
`W r · ·` and `ψ r · ·` is only known for times `s ∈ Ioo 0 T`, and the conclusion is likewise only
claimed for `t ∈ Ioo 0 T`.  The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, so it suffices to know the
parity of each ingredient at the point `(r,z,t)`:

* the time derivative `∂ₜ`: the two time-slices `s ↦ W r (-z) s` and `s ↦ -(W r z s)` agree on
  the neighbourhood `Ioo 0 T` of `t ∈ Ioo 0 T`, and `deriv` only sees the germ, so
  `Filter.EventuallyEq.deriv_eq` followed by `deriv.neg` gives the oddness;
* the radial derivative `∂_r`: for fixed `(-z)` (resp. `z`) with `z ≠ 0`, the `r`-slices agree
  with their negations on a neighbourhood of `r ≠ 0` (which avoids the origin), so again
  `Filter.EventuallyEq.deriv_eq` + `deriv.neg`;
* the axial derivative `∂_z`: oddness in `z` makes the derivative even.  Since the axial
  coordinate is held at a *fixed* `t ∈ Ioo 0 T`, this is exactly `deriv_neg_of_odd_ne` of the
  sibling `meridianResid_odd_ne` (which needs `z ≠ 0` and the oddness only away from the origin);
* the undifferentiated values are odd by hypothesis.

The residual is then an odd·even / odd·odd combination, hence odd.
-/

open scoped Topology

namespace Work.FTS.MeridianDyn.Odd

/-- **Windowed oddness of the meridian residual.**  If `W r (-z) t = -W r z t` and
`ψ r (-z) t = -ψ r z t` for all `r ≠ 0`, `z ≠ 0` and `t ∈ Ioo 0 T`, then
`meridianResid W ψ` is odd in `z` on that same window. -/
theorem meridianResid_odd_win {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hW : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T → W r (-z) t = -W r z t)
    (hψ : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T → ψ r (-z) t = -ψ r z t) :
    ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T →
      Work.CoreResiduals.meridianResid W ψ r (-z) t
        = -Work.CoreResiduals.meridianResid W ψ r z t := by
  intro r z t hr hz ht
  -- time derivative: the two time-slices agree on the neighbourhood `Ioo 0 T` of `t`
  have h1 : deriv (fun s : ℝ => W r (-z) s) t = -deriv (fun s : ℝ => W r z s) t := by
    have hev : (fun s : ℝ => W r (-z) s) =ᶠ[𝓝 t] fun s => -(W r z s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hW r z s hr hz hs
    rw [hev.deriv_eq]
    exact deriv.neg
  -- `∂_z`: even in `z` (odd function of `z`, at the fixed time `t`)
  have h2 : deriv (fun z' : ℝ => ψ r z' t) (-z) = deriv (fun z' : ℝ => ψ r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => ψ r z' t) (fun x hx => hψ r x t hr hx ht) hz
  have h3 : deriv (fun z' : ℝ => W r z' t) (-z) = deriv (fun z' : ℝ => W r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => W r z' t) (fun x hx => hW r x t hr hx ht) hz
  -- `∂_r`: odd in `z` (germ at `r ≠ 0`, hence avoiding the origin)
  have h4 : deriv (fun r' : ℝ => ψ r' (-z) t) r = -deriv (fun r' : ℝ => ψ r' z t) r := by
    have hev : (fun r' : ℝ => ψ r' (-z) t) =ᶠ[𝓝 r] fun r' => -(ψ r' z t) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with r' hr'
      exact hψ r' z t hr' hz ht
    rw [hev.deriv_eq]
    exact deriv.neg
  have h5 : deriv (fun r' : ℝ => W r' (-z) t) r = -deriv (fun r' : ℝ => W r' z t) r := by
    have hev : (fun r' : ℝ => W r' (-z) t) =ᶠ[𝓝 r] fun r' => -(W r' z t) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with r' hr'
      exact hW r' z t hr' hz ht
    rw [hev.deriv_eq]
    exact deriv.neg
  -- the undifferentiated values
  have h6 : W r (-z) t = -W r z t := hW r z t hr hz ht
  have h7 : ψ r (-z) t = -ψ r z t := hψ r z t hr hz ht
  simp only [Work.CoreResiduals.meridianResid, Work.Cyl.pdZ, Work.Cyl.pdR]
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.MeridianDyn.Odd
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.DecayTwoDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The constants of the sharp (`q = 1`) meridian decay estimate

The `Cyl.DecayAux` chain proves the decay of `merPsiT` with a profile rate `(π/2-θ)^q`, `q > 2`,
and needs `3 ≤ p·λ`.  The sharp version needed by the reconstruction (`Weyl.Levels`) has the
profile rate with `q = 1` (the weight `π/2 - θ` in the leading order only, the `θ`-derivative
losing that weight entirely) and only `2 ≤ p·λ`.  The two total constants of that estimate live
here so that the several files producing it agree on their values.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

set_option autoImplicit false

/-- The constant in the `(1+ρ)^{-1}` bound for the two partial derivatives `∂_z ψ`, `∂_r ψ`
of the meridian stream function, in the sharp (`q = 1`) regime.  It is
`(2·(π/2) + p·(π/2) + 1)·|c|·C₀·(2·max 1 (b^λ))`: the three chain-rule terms contribute
`2·(π/2)`, `p·(π/2)` and `1` times the common factor `|c|·C₀·(ρ·(1+w)^{-λ})`, and the last is
bounded by `2·max 1 (b^λ)/(1+ρ)`. -/
noncomputable def decayKzrOne (p c C₀ lam b : ℝ) : ℝ :=
  (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * (|c| * C₀ * (2 * max 1 (b ^ lam)))

/-- The constant in the `(1+ρ)^{-1}` bound for `ψ/r`, in the sharp (`q = 1`) regime:
`|c|·C₀·(π/2)·(2·max 1 (b^λ))`, the `π/2` coming from Jordan's inequality
`π/2 - θ ≤ (π/2)·cos θ = (π/2)·r/ρ`. -/
noncomputable def decayKqOne (c C₀ lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) * (2 * max 1 (b ^ lam))

theorem decayKzrOne_nonneg {p c C₀ lam b : ℝ} (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) :
    0 ≤ decayKzrOne p c C₀ lam b := by
  have h1 : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
    have := mul_nonneg hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith [Real.pi_pos]
  have h2 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  rw [decayKzrOne]
  exact mul_nonneg h1 (mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) h2)


end Work.FTS.BSIdentP.Levels
end
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev2

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The odd extension of `Φ(·,·,τ)` as a two-variable function. -/
noncomputable def GG (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ


theorem abs_pi_div_two_lt : |Real.pi / 2| < Real.pi / 2 + 1 := by
  rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith

/-- The slice-in-`θ` version of `hsm`. -/
theorem contDiffAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  hsm w θ hw (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])

theorem continuousAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  (contDiffAt_Phi hsm hw hθ).continuousAt

theorem continuousAt_pdR_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdR_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

theorem continuousAt_pdZ_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdZ_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

/-! ## The slice identities for `GG` -/

theorem GG_of_pos {w θ : ℝ} (hθ : 0 < θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ.le

theorem GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ

theorem GG_of_neg {w θ : ℝ} (hθ : θ < 0) : GG Φ τ w θ = -(Φ w (-θ) τ) :=
  Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ)

theorem pdR_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_pos (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdR (GG Φ τ) w θ = -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => -(Φ w' (-θ) τ)) := by
    funext w'; exact GG_of_neg (Φ := Φ) (τ := τ) hθ
  have h2 : deriv (fun w' : ℝ => -(Φ w' (-θ) τ)) w
      = -deriv (fun w' : ℝ => Φ w' (-θ) τ) w := by
    rw [show (fun w' : ℝ => -(Φ w' (-θ) τ)) = -(fun w' : ℝ => Φ w' (-θ) τ) from rfl,
      deriv.neg]
  simp only [Work.Cyl.pdR, h, h2]

theorem pdZ_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w θ := by
  simp only [Work.Cyl.pdZ]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hθ] with θ' hθ'
  exact GG_of_pos (Φ := Φ) (τ := τ) hθ'

theorem pdZ_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w (-θ) := by
  simp only [Work.Cyl.pdZ]
  have h : (fun θ' => GG Φ τ w θ') =ᶠ[𝓝 θ] (fun θ' => -(Φ w (-θ') τ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hθ] with θ' hθ'
    exact GG_of_neg (Φ := Φ) (τ := τ) hθ'
  rw [Filter.EventuallyEq.deriv_eq h]
  have h3 : deriv (fun θ' : ℝ => -(Φ w (-θ') τ)) θ
      = - deriv (fun θ' : ℝ => Φ w (-θ') τ) θ := by
    rw [show (fun θ' : ℝ => -(Φ w (-θ') τ)) = -(fun θ' : ℝ => Φ w (-θ') τ) from rfl,
      deriv.neg]
  have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ
      = - deriv (fun θ'' : ℝ => Φ w θ'' τ) (-θ) :=
    deriv_comp_neg (fun θ'' : ℝ => Φ w θ'' τ) θ
  rw [h3, h2, neg_neg]

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` near `θ = ±π/2` -/

theorem continuousAt_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ) (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2)) (g := fun q : ℝ × ℝ => Φ q.1 q.2 τ) h1 hneg
  have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdR_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdR_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdZ_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdZ_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.congr hev

/-! ## Continuity of `GG`, `pdR GG` at `θ = 0` -/

theorem continuousAt_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, 0) := by
  have hval : GG Φ τ w₀ 0 = 0 := by
    rw [GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl]; exact h0 w₀ hw₀
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (0:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [h0 w₀ hw₀] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hnegΦ : Tendsto (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (w₀, 0) :=
        continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have hbase := hcont.tendsto.comp hneg
      rwa [h0 w₀ hw₀] at hbase
    have hc : Tendsto (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ))
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hnegΦ.neg
    have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

theorem continuousAt_pdR_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, 0) := by
  have hslice : (fun w' => GG Φ τ w' 0) = (fun w' => Φ w' 0 τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl
  have hval : Work.Cyl.pdR (GG Φ τ) w₀ 0 = 0 := by
    show deriv (fun w' => GG Φ τ w' 0) w₀ = 0
    rw [hslice]
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hpdR0 : Work.Cyl.pdR (fun w θ => Φ w θ τ) w₀ 0 = 0 := by
    show deriv (fun w' => Φ w' 0 τ) w₀ = 0
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (0:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [hpdR0] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hbaseΦ : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
          (w₀, 0) := continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have h1' := hcont.tendsto.comp hneg
      rwa [hpdR0] at h1'
    have hc : Tendsto (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hbaseΦ.neg
    have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` at interior points -/







end Work.FTS.BSIdentP.Dev2
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

open Filter Set
open scoped Topology

/-!
# The slice difference quotient of a `C²` function

If a two-variable function `f` is `C²` near `(w₀, θ₀)` and vanishes identically on the vertical
line `θ = θ₀` (near `w₀`), then the difference quotient `(w, θ) ↦ f w θ / (θ - θ₀)` extends
continuously to `(w₀, θ₀)` with value `∂_θ f (w₀, θ₀)`.

The proof is the mean value theorem applied to the `θ`-slice `s ↦ f w s`: the quotient equals
`∂_θ f (w, ξ)` for some `ξ` strictly between `θ` and `θ₀`, and the map
`(w, ξ) ↦ ∂_θ f (w, ξ)` is continuous at `(w₀, θ₀)` because `f` is `C²` there.  (The latter is
the statement that `fderiv ℝ` of a `C¹` map is continuous, together with the identification of
the one-dimensional `deriv` of the slice with `fderiv` of the uncurried function evaluated in
the direction `(0,1)`.)
-/

/-- The affine map `s ↦ (w, s)` has derivative the linear map `(0, 1)`. -/
private lemma hasFDerivAt_prodMk_const_left (w s : ℝ) :
    HasFDerivAt (fun s' : ℝ => ((w, s') : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) s :=
  (hasFDerivAt_const (x := s) w).prodMk (hasFDerivAt_id (x := s))

/-- The `θ`-slice derivative `(w, θ) ↦ ∂_θ f (w, θ)` of a `C²` function is continuous. -/
private lemma continuousAt_slice_deriv {f : ℝ → ℝ → ℝ} {w₀ θ₀ : ℝ}
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀)) :
    ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) := by
  set F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 with hFdef
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), DifferentiableAt ℝ F p :=
    (h.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (w₀, θ₀) := h.fderiv_right (m := 1) (by norm_num)
  have hΦ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) (w₀, θ₀) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.continuousAt.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  -- the `deriv` of the slice is `fderiv F` evaluated at `(0,1)` (chain rule)
  have hcomp := hp.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_const_left p.1 p.2)
  have h1 : deriv (fun s : ℝ => f p.1 s) p.2
      = ((fderiv ℝ F p).comp ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 :=
    hcomp.hasDerivAt.deriv
  rw [h1, ContinuousLinearMap.comp_apply]
  simp

/-- A point of the interval `[min a b, max a b]` is at least as close to `b` as `a` is. -/
private lemma abs_sub_le_of_mem_Icc_min_max {a b s : ℝ}
    (hs : s ∈ Set.Icc (min a b) (max a b)) : |s - b| ≤ |a - b| := by
  rcases le_total a b with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
    linarith [hs.1]
  · rw [min_eq_right hle, max_eq_left hle] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
    linarith [hs.2]

/-- Continuity of a slice of a function that is `C²` at every relevant point. -/
private lemma continuousOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    ContinuousOn (fun s => f w s) U := fun s hs =>
  ((h s hs).continuousAt.comp (hasFDerivAt_prodMk_const_left w s).continuousAt).continuousWithinAt

/-- Differentiability of a slice of a function that is `C²` at every relevant point. -/
private lemma differentiableOn_slice {f : ℝ → ℝ → ℝ} {w : ℝ} {U : Set ℝ}
    (h : ∀ s ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s)) :
    DifferentiableOn ℝ (fun s => f w s) U := fun s hs =>
  (((h s hs).differentiableAt (by norm_num)).comp s
    (hasFDerivAt_prodMk_const_left w s).differentiableAt).differentiableWithinAt

/-- **Mean value theorem for the slice quotient.**  If the slice `s ↦ f w s` is continuous on
`[min θ θ₀, max θ θ₀]` and differentiable on the open interval, and `f w θ₀ = 0`, then the
difference quotient `f w θ / (θ - θ₀)` is the value of the slice derivative at some interior
point. -/
private lemma slice_quotient_eq_deriv {f : ℝ → ℝ → ℝ} {w θ θ₀ : ℝ} (hne : θ ≠ θ₀)
    (hz : f w θ₀ = 0)
    (hcont : ContinuousOn (fun s => f w s) (Set.Icc (min θ θ₀) (max θ θ₀)))
    (hdiff : DifferentiableOn ℝ (fun s => f w s) (Set.Ioo (min θ θ₀) (max θ θ₀))) :
    ∃ ξ ∈ Set.Ioo (min θ θ₀) (max θ θ₀),
      deriv (fun s => f w s) ξ = f w θ / (θ - θ₀) := by
  have hlt : min θ θ₀ < max θ θ₀ := min_lt_max.mpr hne
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun s => f w s) hlt hcont hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [hξeq]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, hz, zero_sub,
      show θ₀ - θ = -(θ - θ₀) from by ring, div_neg, neg_div, neg_neg]
  · rw [min_eq_right h.le, max_eq_left h.le, hz, sub_zero]

/-- Every point of `[min θ θ₀, max θ θ₀]` lies within the `δ`-neighbourhood of `θ₀` whenever
`θ` does. -/
private lemma slice_contDiffAt_of_mem_Icc {f : ℝ → ℝ → ℝ} {w w₀ θ₀ θ δ : ℝ}
    (hw : |w - w₀| < δ) (hθ : |θ - θ₀| < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ)) :
    ∀ s ∈ Set.Icc (min θ θ₀) (max θ θ₀),
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, s) := by
  intro s hs
  have hs' : |s - θ₀| < δ := lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max hs) hθ
  exact hsm w s hw hs'

theorem tendsto_slice_quotient {f : ℝ → ℝ → ℝ} {w₀ θ₀ δ : ℝ} (hδ : 0 < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ))
    (hz : ∀ w, |w - w₀| < δ → f w θ₀ = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / (p.2 - θ₀))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀))
      (𝓝 (deriv (fun θ => f w₀ θ) θ₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- `f` is `C²` at the base point, so the slice derivative is continuous there
  have hbase : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w₀, θ₀) :=
    hsm w₀ θ₀ (by simpa using hδ) (by simpa using hδ)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => deriv (fun s => f p.1 s) p.2) (w₀, θ₀) :=
    continuousAt_slice_deriv hbase
  obtain ⟨η₁, hη₁pos, hη₁⟩ :=
    Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcont ε hε)
  -- shrink the neighbourhood so that it stays inside the `δ`-box
  set η : ℝ := min η₁ δ with hηdef
  have hηpos : 0 < η := lt_min hη₁pos hδ
  have hηδ : η ≤ δ := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hbox : ∀ᶠ p : ℝ × ℝ in 𝓝 (w₀, θ₀), |p.1 - w₀| < η ∧ |p.2 - θ₀| < η := by
    filter_upwards [Metric.ball_mem_nhds (w₀, θ₀) hηpos] with p hp
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
    exact hp
  have hboxS : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      |p.1 - w₀| < η ∧ |p.2 - θ₀| < η :=
    hbox.filter_mono nhdsWithin_le_nhds
  have hSne : ∀ᶠ p : ℝ × ℝ in
      𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀),
      p.2 ≠ θ₀ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.2.2
  refine (hboxS.and hSne).mono ?_
  rintro p ⟨⟨hp1, hp2⟩, hpne⟩
  rw [Real.dist_eq]
  have hwδ : |p.1 - w₀| < δ := lt_of_lt_of_le hp1 hηδ
  have hθδ : |p.2 - θ₀| < δ := lt_of_lt_of_le hp2 hηδ
  have hz' : f p.1 θ₀ = 0 := hz p.1 hwδ
  -- the mean value theorem on the `θ`-slice at fixed first coordinate
  have hC2 := slice_contDiffAt_of_mem_Icc hwδ hθδ hsm
  obtain ⟨ξ, hξ, hξeq⟩ := slice_quotient_eq_deriv hpne hz'
    (continuousOn_slice hC2)
    (differentiableOn_slice (fun s hs => hC2 s (Ioo_subset_Icc_self hs)))
  -- `(p.1, ξ)` is still in the small box, so the derivative is close to the limit
  have hξb : |ξ - θ₀| < η :=
    lt_of_le_of_lt (abs_sub_le_of_mem_Icc_min_max (Ioo_subset_Icc_self hξ)) hp2
  have hdist : dist ((p.1, ξ) : ℝ × ℝ) (w₀, θ₀) < η := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hp1, hξb⟩
  have hb := hη₁ (y := (p.1, ξ)) (lt_of_lt_of_le hdist hηη₁)
  rw [Real.dist_eq] at hb
  rw [← hξeq]
  exact hb

end Work.FTS.BSIdentP.Levels
end
