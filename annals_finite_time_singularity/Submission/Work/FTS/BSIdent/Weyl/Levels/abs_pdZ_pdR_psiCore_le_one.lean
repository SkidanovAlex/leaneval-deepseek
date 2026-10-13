import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Weyl.Levels.DecayTwoDefs
import Submission.Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Quadrant
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Wrapper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp (`q = 1`) pointwise decay of `∂_z ψ`, `∂_r ψ`

This is the `q = 1` counterpart of `Work.FTS.BSIdent.Cyl.abs_combination_bound`: the profile
bounds lose the *whole* rate `(π/2 - θ)` (for `∂_θG`) resp. one power of `(π/2 - θ)` (for
`∂_wG`), no `(π/2-θ)^{q-2}` slack is available, and the exponent hypothesis is only
`2 ≤ p·λ`.  The combination bound is therefore reproved from scratch (`q = 1` makes the
`(π/2 - θ)`-bookkeeping trivial: the only thing used is `π/2 - θ ≤ π/2`), and the weight
estimate `ρ (1+ρ^p/b)^{-λ} ≤ 2 max 1 (b^λ)/(1+ρ)` is the sharp one
`rho_mul_rpow_weight_le_two`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Weyl.Levels

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise bound in the sharp regime -/

/-- The two terms `c (X ∂_wG + Y ∂_θG)` of the chain rule are bounded by
`decayKzrOne p c C₀ lam b / (1+ρ)` as soon as `|X| ≤ p ρ w`, `|Y| ≤ ρ` and the profile
satisfies the three *sharp* (`q = 1`) bounds at the point. -/
theorem abs_combination_bound_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z zc X Y : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam) (hzc : |zc| ≤ Work.Cyl.rhoP r z)
    (hX : |X| ≤ p * Work.Cyl.rhoP r z * (Work.Cyl.rhoP r z ^ p / b))
    (hY : |Y| ≤ Work.Cyl.rhoP r z)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |2 * zc * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (X * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              + Y * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))|
      ≤ decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set S := Real.pi / 2 - θ with hS
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθlt : θ < Real.pi / 2 := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r z
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  have hSle : S ≤ Real.pi / 2 := by rw [hS]; linarith
  have hwpos : 0 < w := by
    rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hwnn : 0 ≤ w := hwpos.le
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hRpos : 0 < R := by rw [hR]; exact Real.rpow_pos_of_pos h1w _
  have hRnn : 0 ≤ R := hRpos.le
  have h2pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hval' : |G w θ| ≤ C₀ * S * R := hval
  have hwd' : |Work.Cyl.pdR G w θ| ≤ C₀ * S * (1 + w) ^ (-lam - 1) := hwd
  have hth' : |Work.Cyl.pdZ G w θ| ≤ C₀ * R := hth
  have hX' : |X| ≤ p * ρ * w := hX
  have hY' : |Y| ≤ ρ := hY
  have hzcb : |zc| ≤ ρ := by rw [hρ]; exact hzc
  -- the elementary comparisons
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
    have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
    rw [← hw, ← hR] at h
    exact h
  -- the three term bounds
  have hT1 : 2 * |zc| * |c| * (C₀ * S * R)
      ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * R ≤ C₀ * (Real.pi / 2) * R := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * R ≤ (C₀ * (Real.pi / 2)) * R := mul_le_mul_of_nonneg_right h1 hRnn
        _ = C₀ * (Real.pi / 2) * R := by ring
    have hz2 : 2 * |zc| ≤ 2 * ρ := by linarith [hzcb]
    have hz2c : 2 * |zc| * |c| ≤ 2 * ρ * |c| := mul_le_mul_of_nonneg_right hz2 (abs_nonneg c)
    calc 2 * |zc| * |c| * (C₀ * S * R)
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2) * R) :=
          mul_le_mul hz2c hCS (mul_nonneg (mul_nonneg hC₀ hSnn) hRnn)
            (mul_nonneg (mul_nonneg (by norm_num) hρnn) (abs_nonneg c))
      _ = (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by ring
  have hT2 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
      ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * (1 + w) ^ (-lam - 1)
        ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * (1 + w) ^ (-lam - 1)
          ≤ (C₀ * (Real.pi / 2)) * (1 + w) ^ (-lam - 1) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h1w.le _)
        _ = C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by ring
    have h1 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
        ≤ |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hCS (mul_nonneg (mul_nonneg hp.le hρnn) hwnn))
        (abs_nonneg c)
    have h2 : |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1)))
        = (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1)))) := by ring
    have h3 : (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1))))
        ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwR2 hρnn)
          (mul_nonneg (abs_nonneg c) hC₀))
        (mul_nonneg hp.le h2pi.le)
    exact h1.trans (h2.trans_le h3)
  have hT3 : |c| * (ρ * (C₀ * R)) ≤ 1 * (|c| * C₀ * (ρ * R)) := by
    have h : |c| * (ρ * (C₀ * R)) = 1 * (|c| * C₀ * (ρ * R)) := by ring
    rw [h]
  have hsum : 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R)))
      ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R)) := by
    have h := add_le_add hT1 (add_le_add hT2 hT3)
    calc 2 * |zc| * |c| * (C₀ * S * R)
          + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
            + |c| * (ρ * (C₀ * R)))
        ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
          + ((p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
            + 1 * (|c| * C₀ * (ρ * R))) := h
      _ = (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R)) := by ring
  have hfin : (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R))
      ≤ decayKzrOne p c C₀ lam b / (1 + ρ) := by
    have hA : (0 : ℝ) ≤ |c| * C₀ := mul_nonneg (abs_nonneg c) hC₀
    have hb1 : |c| * C₀ * (ρ * R) ≤ |c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
      mul_le_mul_of_nonneg_left hρR hA
    have hcoef : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
      have := mul_nonneg hp.le h2pi.le; linarith [Real.pi_pos]
    calc (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R))
        ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
            * (|c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ))) :=
          mul_le_mul_of_nonneg_left hb1 hcoef
      _ = decayKzrOne p c C₀ lam b / (1 + ρ) := by rw [decayKzrOne]; ring
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
      ≤ 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R))) := by
    have hA : 2 * |zc| * |c| * |G w θ| ≤ 2 * |zc| * |c| * (C₀ * S * R) :=
      mul_le_mul_of_nonneg_left hval'
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg zc)) (abs_nonneg c))
    have hB : |X| * |Work.Cyl.pdR G w θ| ≤ (p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)) :=
      mul_le_mul hX' hwd' (abs_nonneg _) (mul_nonneg (mul_nonneg hp.le hρnn) hwnn)
    have hD : |Y| * |Work.Cyl.pdZ G w θ| ≤ ρ * (C₀ * R) :=
      mul_le_mul hY' hth' (abs_nonneg _) hρnn
    exact add_le_add hA (add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg c))
      (mul_le_mul_of_nonneg_left hD (abs_nonneg c)))
  exact h1.trans (h2.trans (hsum.trans hfin))

/-! ## The theorem -/

theorem abs_pdZ_pdR_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdent.Weyl.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdent.Weyl.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := (Work.Cyl.rhoP_pos hr z).le
  have hwp : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
    div_nonneg (Real.rpow_nonneg hρnn p) hb.le
  constructor
  · rw [Work.FTS.BSIdent.Cyl.pdZ_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := z)
      (X := p * z * (Work.Cyl.rhoP r z ^ p / b)) (Y := r)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hwp]
      have h2 : p * |z| ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
  · rw [Work.FTS.BSIdent.Cyl.pdR_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := r)
      (X := p * r * (Work.Cyl.rhoP r z ^ p / b)) (Y := -z)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hr.le, abs_of_nonneg hwp]
      have h2 : p * r ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_neg]
      exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z

end Work.FTS.BSIdent.Weyl.Levels
