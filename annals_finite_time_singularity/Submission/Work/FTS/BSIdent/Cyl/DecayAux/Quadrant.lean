import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.rho_mul_rpow_weight_le
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_deriv_zero_le_of_bound_right
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le

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
