/-
# Auxiliary estimates for the divisor lower bound on the cusp-`0` tile `E`

This file collects the two-term cusp expansions and the elementary geometry used by
`Work.Asymptotics.divisor_lower_E`.

The CKMRV divisor at the cusp `0` is

  `Δ(i/t) · (j(w) - j(i/t)) = Δ(i/t) j(W) - E₄(i/t)³`   (`W = S • w`, `j(w) = j(W)`),

so the analysis needs the leading term of `Δ` and `E₄` at the cusp `0` (i.e. at `i/t` with
`t → 0`), and the leading term of `j` on the funnel `{Im ≥ 2}`:

* `Δ(z) = q(z) + O(‖q(z)‖²)` for `Im z ≥ 1` (`Work.Residues.DeltaExpansion`);
* `E₄(z) = 1 + O(‖q(z)‖)` for `Im z ≥ 1` (`Work.Asymptotics.E4Fun_sub_one_explicit`);

hence `Δ(i/t) e^{2π/t} = 1 + O(e^{-2π/t})`, `E₄(i/t)³ = 1 + O(e^{-2π/t})`,
`j(i/t) e^{-2π/t} = 1 + O(e^{-2π/t})` (for `0 < t ≤ T`), and
`j(W) q(W) = 1 + O(‖q(W)‖)` (for `Im W ≥ 2`), together with the two-sided growth bound
`‖j(W)‖ ≍ e^{2π Im W}` on the funnel.

The geometric part records the orbit points `γ_c • (it) = S • (i/t - c)` of the imaginary axis
point `it` and the resulting *lattice separation*: a point `w` whose orbit distance from `it`
is at least `ρ t²` has coordinates `x = Re (S • w)`, `κ = Im (S • w) - 1/t` at distance at least
`ρ (1 - t)` from the lattice `ℤ × {0}` (provided `κ ≥ -1`).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Asymptotics.growthPrefactor_lower_atZero
import Submission.Work.Asymptotics.exp_lattice_lower
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane Topology

namespace Work.Asymptotics

open Work.Kernels

namespace DivisorLowerE

/-! ## Elementary normalisation lemmas -/

lemma norm_ofReal_exp (x : ℝ) : ‖((Real.exp x : ℝ) : ℂ)‖ = Real.exp x := by
  have h : ‖((Real.exp x : ℝ) : ℂ)‖ ^ 2 = (Real.exp x) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [h, norm_nonneg (((Real.exp x : ℝ) : ℂ)), Real.exp_pos x]

lemma exp_cancel (a : ℝ) :
    Real.exp (-a) * Real.exp (-a) * Real.exp a = Real.exp (-a) := by
  rw [show Real.exp (-a) * Real.exp (-a) * Real.exp a
      = Real.exp (-a) * (Real.exp (-a) * Real.exp a) by ring, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- `1000 ≤ exp (2π/t)` for `0 < t ≤ 1/2`. -/
lemma thousand_le_exp (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    (1000 : ℝ) ≤ Real.exp (2 * Real.pi / t) := by
  have h1 : 4 * Real.pi ≤ 2 * Real.pi / t := by
    rw [le_div_iff₀ ht]; nlinarith [Real.pi_pos, ht1]
  have h2 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 12 ≤ Real.exp (2 * Real.pi / t) := Real.exp_le_exp.mpr (le_trans h2 h1)
  have h4 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (1000 : ℝ) ≤ (Real.exp 1) ^ 12 := by
    calc (1000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
      _ ≤ (Real.exp 1) ^ 12 :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
  linarith [h3, h4 ▸ h5]

/-- `exp (-(2π/t)) ≤ 1/1000` for `0 < t ≤ 1/2`. -/
lemma exp_neg_le_thousand (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-(2 * Real.pi / t)) ≤ 1 / 1000 := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (thousand_le_exp t ht ht1)

/-- `exp (-(2π Im W)) ≤ 1/1000` for `Im W ≥ 2`. -/
lemma exp_neg_im_le_thousand (W : ℍ) (hW : 2 ≤ W.im) :
    Real.exp (-(2 * Real.pi * W.im)) ≤ 1 / 1000 := by
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  have h1 : (4 * Real.pi : ℝ) ≤ 2 * Real.pi * W.im := by nlinarith [Real.pi_pos, hW]
  have h2 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 12 ≤ Real.exp (2 * Real.pi * W.im) :=
    Real.exp_le_exp.mpr (le_trans h2 h1)
  have h4 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (1000 : ℝ) ≤ (Real.exp 1) ^ 12 := by
    calc (1000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
      _ ≤ (Real.exp 1) ^ 12 :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
  linarith [h3, h4 ▸ h5]

/-! ## The value of `q` on the imaginary axis -/

lemma qParamFun_imagAxis (t : ℝ) (ht : 0 < t) :
    qParamFun (imagAxis t ht) = ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
  rw [qParamFun_eq_qParam]
  have h : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [h, qParam_imagAxis]

lemma imagAxis_im (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  have h : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [← UpperHalfPlane.coe_im, h]
  simp

lemma norm_qParamFun_imagAxis (t : ℝ) (ht : 0 < t) :
    ‖qParamFun (imagAxis t ht)‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [norm_qParamFun, imagAxis_im]

/-! ## The two-term expansion of `Δ` at the cusp `0` -/

/-- `Δ(i/t) · e^{2π/t} = 1 + O(e^{-2π/t})` for `0 < t ≤ 1/2`. -/
theorem DeltaFun_inv_imagAxis_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 / 2 →
      ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) - 1‖
        ≤ C * Real.exp (-(2 * Real.pi / t)) := by
  obtain ⟨C, hC0, hC⟩ := Work.Residues.DeltaExpansion
  refine ⟨C, hC0, fun t ht ht1 => ?_⟩
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have h1 : (1 : ℝ) ≤ (imagAxis t⁻¹ hs).im := by
    rw [imagAxis_im]; exact (one_le_inv₀ ht).mpr (by linarith)
  have hb := hC (imagAxis t⁻¹ hs) h1
  have hEpt : Work.Residues.Ept (imagAxis t⁻¹ hs) ^ 2 = qParamFun (imagAxis t⁻¹ hs) := by
    rw [Work.Residues.Ept, qParamFun, sq, ← Complex.exp_add]
    congr 1
    ring
  have hEptnorm : ‖Work.Residues.Ept (imagAxis t⁻¹ hs)‖ = Real.exp (-(Real.pi / t)) := by
    rw [Work.Residues.norm_Ept, imagAxis_im]
    ring_nf
  have hstep : DeltaFun (imagAxis t⁻¹ hs) * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) - 1
      = (DeltaFun (imagAxis t⁻¹ hs) - qParamFun (imagAxis t⁻¹ hs))
          * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) := by
    have hmul : qParamFun (imagAxis t⁻¹ hs) * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) = 1 := by
      rw [qParamFun_imagAxis, ← Complex.ofReal_mul, ← Real.exp_add]
      have hz : -(2 * Real.pi * t⁻¹) + 2 * Real.pi / t = 0 := by ring
      rw [hz, Real.exp_zero, Complex.ofReal_one]
    rw [sub_mul, hmul]
  rw [hstep, norm_mul, norm_ofReal_exp]
  have hb' : ‖DeltaFun (imagAxis t⁻¹ hs) - qParamFun (imagAxis t⁻¹ hs)‖
      ≤ C * (Real.exp (-(2 * Real.pi / t))) ^ 2 := by
    have hEq4 : ‖Work.Residues.Ept (imagAxis t⁻¹ hs)‖ ^ 4
        = (Real.exp (-(2 * Real.pi / t))) ^ 2 := by
      rw [hEptnorm,
        show Real.exp (-(Real.pi / t)) ^ 4 = Real.exp ((4 : ℕ) * (-(Real.pi / t))) from
          (Real.exp_nat_mul _ 4).symm,
        show Real.exp (-(2 * Real.pi / t)) ^ 2 = Real.exp ((2 : ℕ) * (-(2 * Real.pi / t))) from
          (Real.exp_nat_mul _ 2).symm]
      congr 1
      push_cast
      ring
    rw [hEpt, hEq4] at hb
    exact hb
  calc ‖DeltaFun (imagAxis t⁻¹ hs) - qParamFun (imagAxis t⁻¹ hs)‖ * Real.exp (2 * Real.pi / t)
      ≤ (C * (Real.exp (-(2 * Real.pi / t))) ^ 2) * Real.exp (2 * Real.pi / t) :=
        mul_le_mul_of_nonneg_right hb' (Real.exp_pos _).le
    _ = C * (Real.exp (-(2 * Real.pi / t)) * Real.exp (-(2 * Real.pi / t))
          * Real.exp (2 * Real.pi / t)) := by
        rw [sq]; ring
    _ = C * Real.exp (-(2 * Real.pi / t)) := by rw [exp_cancel]

/-- `E₄(i/t)³ = 1 + O(e^{-2π/t})` for `0 < t ≤ 1/2`. -/
theorem E4Fun_inv_imagAxis_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 / 2 →
      ‖E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 3 - 1‖
        ≤ C * Real.exp (-(2 * Real.pi / t)) := by
  refine ⟨10000000, by norm_num, fun t ht ht1 => ?_⟩
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have h1 : (1 : ℝ) ≤ (imagAxis t⁻¹ hs).im := by
    rw [imagAxis_im]; exact (one_le_inv₀ ht).mpr (by linarith)
  have hu := E4Fun_sub_one_explicit h1
  have hq : ‖qParamFun (imagAxis t⁻¹ hs)‖ = Real.exp (-(2 * Real.pi / t)) := by
    rw [norm_qParamFun_imagAxis]
    ring_nf
  rw [hq] at hu
  have hqle : Real.exp (-(2 * Real.pi / t)) ≤ 1 / 1000 := exp_neg_le_thousand t ht ht1
  have hE1 : ‖E4Fun (imagAxis t⁻¹ hs) - 1‖ ≤ 20 := by
    have : (20000 : ℝ) * Real.exp (-(2 * Real.pi / t)) ≤ 20 := by linarith
    linarith [hu, this]
  have hEb : ‖E4Fun (imagAxis t⁻¹ hs)‖ ≤ 21 := by
    have hsplit : E4Fun (imagAxis t⁻¹ hs)
        = (E4Fun (imagAxis t⁻¹ hs) - 1) + 1 := by ring
    have h1 := norm_add_le (E4Fun (imagAxis t⁻¹ hs) - 1) (1 : ℂ)
    rw [norm_one] at h1
    rw [hsplit]
    linarith
  have hfac : ‖E4Fun (imagAxis t⁻¹ hs) ^ 2 + E4Fun (imagAxis t⁻¹ hs) + 1‖ ≤ 21 ^ 2 + 21 + 1 := by
    have h2 : ‖E4Fun (imagAxis t⁻¹ hs) ^ 2‖ ≤ 21 ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hEb 2
    calc ‖E4Fun (imagAxis t⁻¹ hs) ^ 2 + E4Fun (imagAxis t⁻¹ hs) + 1‖
        ≤ ‖E4Fun (imagAxis t⁻¹ hs) ^ 2 + E4Fun (imagAxis t⁻¹ hs)‖ + ‖(1 : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (‖E4Fun (imagAxis t⁻¹ hs) ^ 2‖ + ‖E4Fun (imagAxis t⁻¹ hs)‖) + 1 := by
          rw [norm_one]
          linarith [norm_add_le (E4Fun (imagAxis t⁻¹ hs) ^ 2) (E4Fun (imagAxis t⁻¹ hs))]
      _ ≤ (21 ^ 2 + 21) + 1 := by linarith
  have hkey : E4Fun (imagAxis t⁻¹ hs) ^ 3 - 1
      = (E4Fun (imagAxis t⁻¹ hs) - 1)
        * (E4Fun (imagAxis t⁻¹ hs) ^ 2 + E4Fun (imagAxis t⁻¹ hs) + 1) := by ring
  rw [hkey, norm_mul]
  have hfacnn : (0 : ℝ) ≤ 21 ^ 2 + 21 + 1 := by norm_num
  calc ‖E4Fun (imagAxis t⁻¹ hs) - 1‖
        * ‖E4Fun (imagAxis t⁻¹ hs) ^ 2 + E4Fun (imagAxis t⁻¹ hs) + 1‖
      ≤ (20000 * Real.exp (-(2 * Real.pi / t))) * (21 ^ 2 + 21 + 1) :=
        mul_le_mul hu hfac (norm_nonneg _) (by positivity)
    _ = 9260000 * Real.exp (-(2 * Real.pi / t)) := by ring
    _ ≤ 10000000 * Real.exp (-(2 * Real.pi / t)) := by
        have := Real.exp_pos (-(2 * Real.pi / t))
        nlinarith


/-! ## `exp (-4π) ≤ 1/10000` -/

lemma exp_neg_four_pi_le : Real.exp (-(4 * Real.pi)) ≤ 1 / 100000 := by
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  have h2 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 12 ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr h2
  have h4 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (100000 : ℝ) ≤ (Real.exp 1) ^ 12 := by
    have h6 : (2.7182818283 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
    have h7 : (100000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
    linarith
  linarith [h3, h4 ▸ h5]

/-! ## The growth of `j` on the funnel -/

/-- `‖Δ(W)‖ ≍ ‖q(W)‖` on the funnel: the sharp two-sided discriminant bound. -/
lemma DeltaFun_funnel_two_sided (W : ℍ) (hW : 2 ≤ W.im) :
    (1 / 2) * ‖qParamFun W‖ ≤ ‖DeltaFun W‖ ∧ ‖DeltaFun W‖ ≤ 2 * ‖qParamFun W‖ := by
  rw [norm_qParamFun]
  exact ⟨DeltaFun_funnel_lower_sharp hW, DeltaFun_upper_sharp W (by linarith)⟩

/-- **Two-sided growth of `j` on the funnel.**  For `Im W ≥ 2`,
`(2/5) e^{2π Im W} ≤ ‖j(W)‖ ≤ (13/5) e^{2π Im W}`. -/
theorem jInvariantFun_funnel_growth :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ W : ℍ, 2 ≤ W.im →
      c * Real.exp (2 * Real.pi * W.im) ≤ ‖jInvariantFun W‖ ∧
      ‖jInvariantFun W‖ ≤ C * Real.exp (2 * Real.pi * W.im) := by
  refine ⟨1 / 5, 4, by norm_num, by norm_num, fun W hW => ?_⟩
  have hqpos : 0 < ‖qParamFun W‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hqle : ‖qParamFun W‖ ≤ Real.exp (-(4 * Real.pi)) := by
    rw [norm_qParamFun, Real.exp_le_exp]; nlinarith [Real.pi_pos, hW]
  have hqsmall : ‖qParamFun W‖ ≤ 1 / 100000 := le_trans hqle exp_neg_four_pi_le
  have hu := E4Fun_sub_one_explicit (by linarith : (1 : ℝ) ≤ W.im)
  have hE1 : ‖E4Fun W - 1‖ ≤ 1 / 5 := by
    have : (20000 : ℝ) * ‖qParamFun W‖ ≤ 1 / 5 := by nlinarith
    linarith [hu]
  have hEup : ‖E4Fun W‖ ≤ 6 / 5 := by
    have h1 := norm_add_le (E4Fun W - 1) (1 : ℂ)
    rw [norm_one] at h1
    have h2 : E4Fun W = (E4Fun W - 1) + 1 := by ring
    rw [h2]; linarith
  have hElo : (4 / 5 : ℝ) ≤ ‖E4Fun W‖ := by
    have h1 := abs_norm_sub_norm_le (E4Fun W) (1 : ℂ)
    rw [norm_one] at h1
    have h3 := abs_le.mp (le_trans h1 hE1)
    linarith [h3.1]
  have hDlo : (1 / 2) * ‖qParamFun W‖ ≤ ‖DeltaFun W‖ := (DeltaFun_funnel_two_sided W hW).1
  have hDup : ‖DeltaFun W‖ ≤ 2 * ‖qParamFun W‖ := (DeltaFun_funnel_two_sided W hW).2
  have hDpos : 0 < ‖DeltaFun W‖ := lt_of_lt_of_le (by positivity) hDlo
  have hEd : ‖E4Fun W ^ 3‖ = ‖E4Fun W‖ ^ 3 := norm_pow _ _
  have heq : Real.exp (2 * Real.pi * W.im) * ‖qParamFun W‖ = 1 := by
    rw [norm_qParamFun, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hj : jInvariantFun W = E4Fun W ^ 3 / DeltaFun W := rfl
  constructor
  · have h3 : (2 / 5 : ℝ) ≤ ‖E4Fun W‖ ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4/5) hElo 3
      norm_num at h ⊢
      linarith
    rw [hj, norm_div, norm_pow, le_div_iff₀ hDpos]
    have h2 : Real.exp (2 * Real.pi * W.im) * ‖DeltaFun W‖ ≤ 2 := by
      nlinarith [hDup, heq, hqpos]
    have hstep : (1 / 5 : ℝ) * (Real.exp (2 * Real.pi * W.im) * ‖DeltaFun W‖) ≤ 2 / 5 := by
      nlinarith [h2]
    have hgoal : (1 / 5 : ℝ) * Real.exp (2 * Real.pi * W.im) * ‖DeltaFun W‖
        = (1 / 5) * (Real.exp (2 * Real.pi * W.im) * ‖DeltaFun W‖) := by ring
    rw [hgoal]
    linarith
  · have h3 : ‖E4Fun W‖ ^ 3 ≤ 216 / 125 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hEup 3
      norm_num at h ⊢
      linarith
    rw [hj, norm_div, norm_pow, div_le_iff₀ hDpos]
    have h2 : (2 : ℝ) ≤ 4 * Real.exp (2 * Real.pi * W.im) * ‖DeltaFun W‖ := by
      nlinarith [hDlo, heq, hqpos]
    linarith

/-! ## The two-term expansion of `j` at the cusp `0` and on the funnel -/

lemma Ept_sq_eq_qParamFun (W : ℍ) : Work.Residues.Ept W ^ 2 = qParamFun W := by
  rw [Work.Residues.Ept, qParamFun, sq, ← Complex.exp_add]
  congr 1
  ring

/-- `j(i/t) · e^{-2π/t} = 1 + O(e^{-2π/t})`. -/
theorem jInvariantFun_inv_imagAxis_two_term :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ T ≤ 1 / 2 ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        ‖jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht))
            * ((Real.exp (-(2 * Real.pi / t)) : ℝ) : ℂ) - 1‖
          ≤ C * Real.exp (-(2 * Real.pi / t)) := by
  obtain ⟨C₁, hC₁0, hΔ⟩ := DeltaFun_inv_imagAxis_two_term
  obtain ⟨C₃, hC₃0, hE4⟩ := E4Fun_inv_imagAxis_three
  obtain ⟨T₀, hT₀0, hT₀⟩ := exists_le_exp_two_pi_div (2 * C₁)
  refine ⟨2 * (C₁ + C₃), min T₀ (1 / 2), by positivity, lt_min hT₀0 (by norm_num),
    min_le_right _ _, fun t ht htT => ?_⟩
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have ht1 : t ≤ 1 / 2 := le_trans htT (min_le_right _ _)
  have ht0 : t ≤ T₀ := le_trans htT (min_le_left _ _)
  set D := DeltaFun (imagAxis t⁻¹ hs) with hDdef
  set E := E4Fun (imagAxis t⁻¹ hs) ^ 3 with hEdef
  set R := ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) with hRdef
  set r := ((Real.exp (-(2 * Real.pi / t)) : ℝ) : ℂ) with hrdef
  have hδ1 : ‖D * R - 1‖ ≤ C₁ * Real.exp (-(2 * Real.pi / t)) := hΔ t ht ht1
  have hδ3 : ‖E - 1‖ ≤ C₃ * Real.exp (-(2 * Real.pi / t)) := hE4 t ht ht1
  have hexp : (2 * C₁ : ℝ) ≤ Real.exp (2 * Real.pi / t) := hT₀ t ht ht0
  have hsmall1 : ‖D * R - 1‖ ≤ 1 / 2 := by
    have h2 : C₁ * Real.exp (-(2 * Real.pi / t)) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have h3 : C₁ * (Real.exp (2 * Real.pi / t))⁻¹ ≤ C₁ * (2 * C₁)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁0.le
        exact inv_anti₀ (by positivity) hexp
      have h4 : C₁ * (2 * C₁)⁻¹ = 1 / 2 := by field_simp
      linarith [h3, h4.le, h4.ge]
    linarith [hδ1, h2]
  have hrR : r * R = 1 := by
    rw [hrdef, hRdef, ← Complex.ofReal_mul, ← Real.exp_add]
    have hz : -(2 * Real.pi / t) + 2 * Real.pi / t = 0 := by ring
    rw [hz, Real.exp_zero, Complex.ofReal_one]
  have hD0 : D ≠ 0 := by
    rw [hDdef]
    exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hR0 : R ≠ 0 := by
    rw [hRdef]
    simp
  have hDRne : D * R ≠ 0 := mul_ne_zero hD0 hR0
  have hjr : jInvariantFun (imagAxis t⁻¹ hs) * r = E / (D * R) := by
    have hj0 : jInvariantFun (imagAxis t⁻¹ hs) = E / D := by
      rw [jInvariantFun, hEdef, hDdef]
    rw [hj0, div_mul_eq_mul_div]
    have h1 : E * r / D = (E * (r * R)) / (D * R) := by
      field_simp
    have h2 : E * (r * R) / (D * R) = E / (D * R) := by rw [hrR, mul_one]
    rw [h1, h2]
  have hid : jInvariantFun (imagAxis t⁻¹ hs) * r - 1 = ((E - 1) - (D * R - 1)) / (D * R) := by
    rw [hjr, eq_div_iff hDRne, sub_mul, div_mul_cancel₀ _ hDRne, one_mul]
    ring
  rw [hid, norm_div]
  have hnum : ‖(E - 1) - (D * R - 1)‖ ≤ (C₃ + C₁) * Real.exp (-(2 * Real.pi / t)) := by
    have h := norm_sub_le (E - 1) (D * R - 1)
    nlinarith [hδ1, hδ3, h, Real.exp_pos (-(2 * Real.pi / t))]
  have hden : (1 / 2 : ℝ) ≤ ‖D * R‖ := by
    have h := abs_norm_sub_norm_le (D * R) (1 : ℂ)
    rw [norm_one] at h
    have h2 := abs_le.mp (le_trans h hsmall1)
    linarith [h2.1]
  have hdenpos : 0 < ‖D * R‖ := lt_of_lt_of_le (by norm_num) hden
  have hfin : (C₃ + C₁) * Real.exp (-(2 * Real.pi / t)) / (1 / 2)
      ≤ 2 * (C₁ + C₃) * Real.exp (-(2 * Real.pi / t)) := by
    have := Real.exp_pos (-(2 * Real.pi / t))
    nlinarith
  calc ‖(E - 1) - (D * R - 1)‖ / ‖D * R‖
      ≤ (C₃ + C₁) * Real.exp (-(2 * Real.pi / t)) / (1 / 2) := by
        refine div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ ≤ 2 * (C₁ + C₃) * Real.exp (-(2 * Real.pi / t)) := hfin

/-- `j(W) q(W) = 1 + O(‖q(W)‖)` on the funnel. -/
theorem jInvariantFun_funnel_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℍ, 2 ≤ W.im →
      ‖jInvariantFun W * qParamFun W - 1‖ ≤ C * ‖qParamFun W‖ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.Residues.DeltaExpansion
  refine ⟨150000 + 2 * C₁ + 1, by positivity, fun W hW => ?_⟩
  have hqpos : 0 < ‖qParamFun W‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hqle : ‖qParamFun W‖ ≤ 1 / 100000 := by
    have h : ‖qParamFun W‖ ≤ Real.exp (-(4 * Real.pi)) := by
      rw [norm_qParamFun, Real.exp_le_exp]; nlinarith [Real.pi_pos, hW]
    exact le_trans h exp_neg_four_pi_le
  have hD1 : ‖DeltaFun W - qParamFun W‖ ≤ C₁ * ‖qParamFun W‖ ^ 2 := by
    have h := hC₁ W (by linarith : (1 : ℝ) ≤ W.im)
    rw [Ept_sq_eq_qParamFun] at h
    have h4 : ‖Work.Residues.Ept W‖ ^ 4 = ‖qParamFun W‖ ^ 2 := by
      rw [show ‖Work.Residues.Ept W‖ ^ 4 = (‖Work.Residues.Ept W‖ ^ 2) ^ 2 by ring,
        ← norm_pow, Ept_sq_eq_qParamFun]
    rwa [h4] at h
  have hDlo : (1 / 2) * ‖qParamFun W‖ ≤ ‖DeltaFun W‖ :=
    (DeltaFun_funnel_two_sided W hW).1
  have hDpos : 0 < ‖DeltaFun W‖ := lt_of_lt_of_le (by positivity) hDlo
  have hratio : ‖qParamFun W / DeltaFun W - 1‖ ≤ 2 * C₁ * ‖qParamFun W‖ := by
    have h1 : qParamFun W / DeltaFun W - 1 = (qParamFun W - DeltaFun W) / DeltaFun W := by
      rw [eq_div_iff (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero W), sub_mul,
        div_mul_cancel₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero W), one_mul]
    rw [h1, norm_div]
    have h2 : ‖qParamFun W - DeltaFun W‖ / ‖DeltaFun W‖
        ≤ (C₁ * ‖qParamFun W‖ ^ 2) / ((1 / 2) * ‖qParamFun W‖) := by
      exact div_le_div₀ (by positivity) (by simpa [norm_sub_rev] using hD1) (by positivity) hDlo
    have h3 : (C₁ * ‖qParamFun W‖ ^ 2) / ((1 / 2) * ‖qParamFun W‖)
        = 2 * C₁ * ‖qParamFun W‖ := by
      field_simp
    rw [h3] at h2
    exact h2
  have hE1 : ‖E4Fun W - 1‖ ≤ 20000 * ‖qParamFun W‖ :=
    E4Fun_sub_one_explicit (by linarith : (1 : ℝ) ≤ W.im)
  have hEup : ‖E4Fun W‖ ≤ 6 / 5 := by
    have h := norm_add_le (E4Fun W - 1) (1 : ℂ)
    rw [norm_one] at h
    have h2 : E4Fun W = (E4Fun W - 1) + 1 := by ring
    rw [h2]
    have : 20000 * ‖qParamFun W‖ ≤ 1 / 5 := by nlinarith
    linarith
  have hE3 : ‖E4Fun W ^ 3 - 1‖ ≤ 72800 * ‖qParamFun W‖ := by
    have hfac : ‖E4Fun W ^ 2 + E4Fun W + 1‖ ≤ (6 / 5) ^ 2 + 6 / 5 + 1 := by
      have h2 : ‖E4Fun W ^ 2‖ ≤ (6 / 5) ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hEup 2
      have h := norm_add_le (E4Fun W ^ 2 + E4Fun W) (1 : ℂ)
      rw [norm_one] at h
      have h3 := norm_add_le (E4Fun W ^ 2) (E4Fun W)
      linarith
    have hkey : E4Fun W ^ 3 - 1
        = (E4Fun W - 1) * (E4Fun W ^ 2 + E4Fun W + 1) := by ring
    rw [hkey, norm_mul]
    have h4 : 20000 * ‖qParamFun W‖ * ((6 / 5) ^ 2 + 6 / 5 + 1) ≤ 72800 * ‖qParamFun W‖ := by
      nlinarith [hqpos]
    exact le_trans (mul_le_mul hE1 hfac (norm_nonneg _) (by positivity)) h4
  have hsplit : jInvariantFun W * qParamFun W - 1
      = (E4Fun W ^ 3 - 1) * (qParamFun W / DeltaFun W) + (qParamFun W / DeltaFun W - 1) := by
    rw [jInvariantFun]
    field_simp [ne_of_gt hDpos]
    ring
  rw [hsplit]
  have hb1 : ‖E4Fun W ^ 3 - 1‖ * ‖qParamFun W / DeltaFun W‖ ≤ 72800 * ‖qParamFun W‖ * 2 := by
    refine mul_le_mul hE3 ?_ (norm_nonneg _) (by positivity)
    have h2 : qParamFun W / DeltaFun W = (qParamFun W) * (DeltaFun W)⁻¹ := by ring
    rw [h2, norm_mul]
    have h3 : ‖(DeltaFun W)⁻¹‖ ≤ 2 / ‖qParamFun W‖ := by
      rw [norm_inv]
      have hden : 0 < (1 / 2) * ‖qParamFun W‖ := by positivity
      have h := (inv_le_inv₀ hDpos hden).mpr hDlo
      have h2 : ((1 / 2) * ‖qParamFun W‖)⁻¹ = 2 / ‖qParamFun W‖ := by field_simp
      linarith [h, h2.le, h2.ge]
    have h4 : ‖qParamFun W‖ * ‖(DeltaFun W)⁻¹‖
        ≤ ‖qParamFun W‖ * (2 / ‖qParamFun W‖) :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have h5 : ‖qParamFun W‖ * (2 / ‖qParamFun W‖) = 2 := by field_simp
    linarith [h4, h5.le, h5.ge]
  have hfin : 72800 * ‖qParamFun W‖ * 2 + 2 * C₁ * ‖qParamFun W‖
      ≤ (150000 + 2 * C₁ + 1) * ‖qParamFun W‖ := by nlinarith [hqpos]
  calc ‖(E4Fun W ^ 3 - 1) * (qParamFun W / DeltaFun W) + (qParamFun W / DeltaFun W - 1)‖
      ≤ ‖(E4Fun W ^ 3 - 1) * (qParamFun W / DeltaFun W)‖ + ‖qParamFun W / DeltaFun W - 1‖ :=
        norm_add_le _ _
    _ ≤ 72800 * ‖qParamFun W‖ * 2 + 2 * C₁ * ‖qParamFun W‖ := by
        rw [norm_mul]; linarith [hb1, hratio]
    _ ≤ (150000 + 2 * C₁ + 1) * ‖qParamFun W‖ := hfin

/-! ## The orbit of the imaginary axis point `it`

The points of the `SL(2,ℤ)`-orbit of `it` that accumulate at the cusp `0` are

  `γ_c • (it) = S • (i/t - c)`,  `γ_c = S · T^{-c} · S`  (`c ∈ ℤ`),

recorded below as an identity of half-plane points, together with the Möbius identity
`S u - S v = (u - v)/(uv)`.
-/

lemma S_smul_sub (u v : ℍ) :
    ((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)
      = ((u : ℂ) - (v : ℂ)) / ((u : ℂ) * (v : ℂ)) := by
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hv : (v : ℂ) ≠ 0 := v.ne_zero
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    UpperHalfPlane.coe_mk]
  field_simp
  ring

lemma orbit_point_eq (c : ℤ) (t : ℝ) (ht : 0 < t) :
    (ModularGroup.S * ModularGroup.T ^ (-c) * ModularGroup.S
        : Matrix.SpecialLinearGroup (Fin 2) ℤ) • imagAxis t ht
      = ModularGroup.S • UpperHalfPlane.ofComplex ((t : ℂ)⁻¹ * Complex.I - (c : ℂ)) := by
  have him : 0 < ((t : ℂ)⁻¹ * Complex.I - (c : ℂ)).im := by
    have h1 : ((t : ℂ)⁻¹ * Complex.I).im = ((t : ℂ)⁻¹).re := by
      rw [Complex.mul_im]; simp
    rw [Complex.sub_im, h1, Complex.intCast_im, sub_zero]
    rw [Complex.inv_re, Complex.normSq_ofReal]
    have ht0 : (0 : ℝ) < t * t := mul_pos ht ht
    exact div_pos ht ht0
  have h1 : (ModularGroup.T ^ (-c) : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      • imagAxis t⁻¹ (inv_pos.mpr ht)
      = UpperHalfPlane.ofComplex ((t : ℂ)⁻¹ * Complex.I - (c : ℂ)) := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq, UpperHalfPlane.ofComplex_apply_of_im_pos him]
    show ((imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ) + (((-c : ℤ) : ℝ) : ℂ)
      = (t : ℂ)⁻¹ * Complex.I - (c : ℂ)
    have h2 : ((imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ) = (t : ℂ)⁻¹ * Complex.I := by
      show ((t⁻¹ : ℝ) : ℂ) * Complex.I = (t : ℂ)⁻¹ * Complex.I
      rw [Complex.ofReal_inv]
    rw [h2]
    push_cast
    ring
  rw [mul_smul, mul_smul, imagAxis_smul_S, h1]

/-- **The orbit constraint gives a lattice separation.** -/
theorem constraint_lattice_sep {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (ht1 : t ≤ 1) {w : ℍ}
    (hcon : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • imagAxis t ht : ℍ)) : ℂ)‖)
    (hκ : -1 ≤ ((ModularGroup.S • w : ℍ) : ℂ).im - t⁻¹)
    (c : ℤ) :
    ρ ^ 2 * (1 - t) ^ 2 ≤ (((ModularGroup.S • w : ℍ) : ℂ).re + (c : ℝ)) ^ 2
      + (((ModularGroup.S • w : ℍ) : ℂ).im - t⁻¹) ^ 2 := by
  set W : ℍ := ModularGroup.S • w with hW
  set u : ℍ := UpperHalfPlane.ofComplex ((t : ℂ)⁻¹ * Complex.I - (c : ℂ)) with hu
  have hdist := hcon (ModularGroup.S * ModularGroup.T ^ (-c) * ModularGroup.S)
  rw [orbit_point_eq c t ht] at hdist
  have hwS : w = ModularGroup.S • W := by rw [hW, S_smul_S_smul]
  have hwcoe : (w : ℂ) = ((ModularGroup.S • W : ℍ) : ℂ) := by rw [← hwS]
  rw [hwcoe, S_smul_sub W u, norm_div, norm_mul] at hdist
  have him : 0 < ((t : ℂ)⁻¹ * Complex.I - (c : ℂ)).im := by
    have h1 : ((t : ℂ)⁻¹ * Complex.I).im = ((t : ℂ)⁻¹).re := by
      rw [Complex.mul_im]; simp
    rw [Complex.sub_im, h1, Complex.intCast_im, sub_zero, Complex.inv_re, Complex.normSq_ofReal]
    exact div_pos ht (mul_pos ht ht)
  have hueq : (u : ℂ) = -(c : ℂ) + (t : ℂ)⁻¹ * Complex.I := by
    rw [hu, UpperHalfPlane.ofComplex_apply_of_im_pos him]
    simp only [UpperHalfPlane.coe_mk]
    ring
  have hucoelim : (u : ℂ).im = t⁻¹ := by
    have h3 : ((-(c : ℂ) + (t : ℂ)⁻¹ * Complex.I)).im = ((t : ℂ)⁻¹).re := by
      rw [Complex.add_im, Complex.neg_im, Complex.intCast_im, Complex.mul_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, neg_zero, zero_add]
    rw [hueq, h3, Complex.inv_re, Complex.normSq_ofReal]
    field_simp
    simp
  have hunorm : t⁻¹ ≤ ‖(u : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (u : ℂ)
    rw [hucoelim, abs_of_pos (inv_pos.mpr ht)] at h
    exact h
  have hWnorm : (1 - t) / t ≤ ‖(W : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (W : ℂ)
    have hWim : t⁻¹ - 1 ≤ (W : ℂ).im := by linarith [hκ]
    have h1 : t⁻¹ - 1 = (1 - t) / t := by field_simp
    have h2 : 0 ≤ (1 - t) / t := by
      rw [← h1]
      exact sub_nonneg.mpr ((one_le_inv₀ ht).mpr ht1)
    have h4 : 0 ≤ (W : ℂ).im := by rw [h1] at hWim; linarith [hWim, h2]
    rw [abs_of_nonneg h4] at h
    linarith [h, hWim, h1.le, h1.ge]
  have hnormpos : 0 < ‖(W : ℂ)‖ * ‖(u : ℂ)‖ := by
    have h1 : 0 < ‖(W : ℂ)‖ := norm_pos_iff.mpr W.ne_zero
    have h2 : 0 < ‖(u : ℂ)‖ := lt_of_lt_of_le (inv_pos.mpr ht) hunorm
    positivity
  have hmain : ‖(W : ℂ) - (u : ℂ)‖ ≥ ρ * (1 - t) := by
    have h1 : ρ * t ^ 2 * (‖(W : ℂ)‖ * ‖(u : ℂ)‖) ≤ ‖(W : ℂ) - (u : ℂ)‖ := by
      have := (le_div_iff₀ hnormpos).mp hdist
      linarith [this]
    have h2 : ρ * t ^ 2 * ((1 - t) / t * t⁻¹) ≤ ρ * t ^ 2 * (‖(W : ℂ)‖ * ‖(u : ℂ)‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hρ.le (sq_nonneg t))
      exact mul_le_mul hWnorm hunorm (by positivity) (norm_nonneg _)
    have h3 : ρ * t ^ 2 * ((1 - t) / t * t⁻¹) = ρ * (1 - t) := by
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  have hsq : ‖(W : ℂ) - (u : ℂ)‖ ^ 2
      = ((W : ℂ).re + (c : ℝ)) ^ 2 + ((W : ℂ).im - t⁻¹) ^ 2 := by
    have hueq : (u : ℂ) = -(c : ℂ) + (t : ℂ)⁻¹ * Complex.I := by
      rw [hu, UpperHalfPlane.ofComplex_apply_of_im_pos him]
      ring
    rw [hueq, ← Complex.ofReal_inv, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, mul_zero, mul_one, sub_zero, add_zero,
      neg_zero, zero_add]
    ring_nf
  have hpos : 0 ≤ ρ * (1 - t) := mul_nonneg hρ.le (by linarith)
  rw [← hsq]
  nlinarith [hmain, norm_nonneg ((W : ℂ) - (u : ℂ))]

/-! ## The orbit in Möbius coordinates -/

/-- The numerator `a·(i t) + b` of the coefficient of `γ • (it)`. -/
def orbitNum (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) : ℂ) * (Complex.I * (t : ℂ))
    + (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) : ℂ)

/-- The denominator `c·(i t) + d` of the coefficient of `γ • (it)`. -/
def orbitDen (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) : ℂ) * (Complex.I * (t : ℂ))
    + (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) : ℂ)

lemma orbitDen_ne_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ} (ht : 0 < t) :
    orbitDen γ t ≠ 0 := by
  intro h
  have hre : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) : ℂ) = 0 := by
    have := congrArg Complex.re h
    simp only [orbitDen, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero] at this
    simpa using this
  have him : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) : ℂ) * (t : ℂ) = 0 := by
    have := congrArg Complex.im h
    simp only [orbitDen, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero] at this
    simpa using this
  have hc : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' (by simp [ht.ne'])
  have hcZ : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = 0 := by exact_mod_cast hc
  have hdZ : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = 0 := by
    have h' : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) = 0 := by exact_mod_cast hre
    exact_mod_cast h'
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  rw [hcZ, hdZ] at hdet
  norm_num at hdet

lemma orbit_coeff (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t) :
    ((γ • imagAxis t ht : ℍ) : ℂ) = orbitNum γ t / orbitDen γ t := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hz : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [hz]
  have halg : ∀ x : ℤ, (((algebraMap ℤ ℝ x : ℝ)) : ℂ) = (((x : ℤ)) : ℂ) := by
    intro x
    simp
  simp only [orbitNum, orbitDen, halg]
  push_cast
  ring

lemma orbit_condition_iff {ρ t : ℝ} (ht : 0 < t) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (w : ℍ) :
    ρ * t ^ 2 ≤ ‖(w : ℂ) - ((γ • imagAxis t ht : ℍ) : ℂ)‖ ↔
      ρ * t ^ 2 * ‖orbitDen γ t‖ ≤ ‖(w : ℂ) * orbitDen γ t - orbitNum γ t‖ := by
  have hD := orbitDen_ne_zero γ ht
  have hDpos : 0 < ‖orbitDen γ t‖ := norm_pos_iff.mpr hD
  rw [orbit_coeff γ t ht]
  have hsplit : (w : ℂ) - orbitNum γ t / orbitDen γ t
      = ((w : ℂ) * orbitDen γ t - orbitNum γ t) / orbitDen γ t := by
    rw [eq_div_iff hD]
    field_simp
  rw [hsplit, norm_div, le_div_iff₀ hDpos]

/-! ## Elementary bounds on the cusp-`0` tile `E` -/

lemma norm_ofReal_eq (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [h, norm_nonneg (((x : ℝ) : ℂ)), abs_nonneg x, sq_abs x, sq_nonneg (‖((x:ℝ):ℂ)‖ - |x|),
    mul_nonneg (norm_nonneg (((x:ℝ):ℂ))) (abs_nonneg x)]

lemma S_smul_coe (w : ℍ) : (((ModularGroup.S • w : ℍ)) : ℂ) = -((w : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  simp

lemma neg_inv_im (z : ℂ) : (-z⁻¹).im = z.im / ‖z‖ ^ 2 := by
  rw [Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

lemma KEpsilon_im_S (w : ℍ) :
    (((ModularGroup.S • w : ℍ)) : ℂ).im = ((w : ℂ)).im / ‖(w : ℂ)‖ ^ 2 := by
  rw [S_smul_coe, neg_inv_im]

lemma KEpsilon_disk (w : ℍ) (hw : w ∈ KEpsilon) :
    ((w : ℂ)).re ^ 2 + (((w : ℂ)).im - 1 / 4) ^ 2 ≤ 1 / 16 := by
  have h2 : 2 ≤ ((w : ℂ)).im / ‖(w : ℂ)‖ ^ 2 := by
    have h := hw.2
    rw [← UpperHalfPlane.coe_im, KEpsilon_im_S] at h
    exact h
  have hnorm : 0 < ‖(w : ℂ)‖ ^ 2 := by
    have := norm_pos_iff.mpr w.ne_zero; positivity
  have h3 : 2 * ‖(w : ℂ)‖ ^ 2 ≤ ((w : ℂ)).im := by
    rw [le_div_iff₀ hnorm] at h2; linarith [h2]
  have h4 : ‖(w : ℂ)‖ ^ 2 = ((w : ℂ)).re ^ 2 + ((w : ℂ)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h4] at h3
  nlinarith [h3]

lemma KEpsilon_re_le (w : ℍ) (hw : w ∈ KEpsilon) : |((w : ℂ)).re| ≤ 1 / 4 := by
  have h := KEpsilon_disk w hw
  have h2 : ((w : ℂ)).re ^ 2 ≤ 1 / 16 := by nlinarith [h, sq_nonneg (((w:ℂ)).im - 1/4)]
  nlinarith [h2, sq_abs (((w:ℂ)).re), abs_nonneg (((w:ℂ)).re)]

lemma KEpsilon_im_le (w : ℍ) (hw : w ∈ KEpsilon) : ((w : ℂ)).im ≤ 1 / 2 := by
  have h := KEpsilon_disk w hw
  have him : 0 < ((w : ℂ)).im := w.im_pos
  nlinarith [h, sq_nonneg (((w:ℂ)).re)]

lemma KEpsilon_im_ge (w : ℍ) (hw : w ∈ KEpsilon) {C : ℝ}
    (hC : ((ModularGroup.S • w : ℍ) : ℂ).im ≤ C) (hC2 : 2 ≤ C) :
    2 / (1 + C ^ 2) ≤ ((w : ℂ)).im := by
  set W : ℍ := ModularGroup.S • w with hW
  have hWim : ((W : ℂ)).im = ((w : ℂ)).im / ‖(w : ℂ)‖ ^ 2 := by rw [hW, KEpsilon_im_S]
  have hWs : w = ModularGroup.S • W := by rw [hW, S_smul_S_smul]
  have hcoe : ((w : ℂ)) = -((W : ℂ))⁻¹ := by rw [hWs, S_smul_coe]
  have hnorm : ‖(w : ℂ)‖ ^ 2 = (‖(W : ℂ)‖ ^ 2)⁻¹ := by
    rw [hcoe, norm_neg, norm_inv]; ring
  have hWnorm : ‖(W : ℂ)‖ ^ 2 ≤ 1 + C ^ 2 := by
    have h4 : ‖(W : ℂ)‖ ^ 2 = ((W : ℂ)).re ^ 2 + ((W : ℂ)).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hre : |((W : ℂ)).re| < 1 := by
      have hD := S_smul_mem_DomainD hw.1
      have hb := re_bounds_of_mem_DomainD hD
      have h1 : ((W : ℂ)).re = W.re := rfl
      rw [h1, abs_lt]; exact ⟨hb.1, hb.2⟩
    have hre2 : ((W : ℂ)).re ^ 2 ≤ 1 := by
      nlinarith [hre, abs_nonneg (((W:ℂ)).re), sq_abs (((W:ℂ)).re)]
    have him2 : ((W : ℂ)).im ^ 2 ≤ C ^ 2 := by
      have h2 : ((W : ℂ)).im ≤ C := hC
      have h3 : 2 ≤ ((W : ℂ)).im := by simpa [hW, UpperHalfPlane.coe_im] using hw.2
      nlinarith [h2, h3, hC2]
    linarith [h4, hre2, him2]
  have hWpos : 0 < ‖(W : ℂ)‖ ^ 2 := by
    have := norm_pos_iff.mpr W.ne_zero; positivity
  have hWim2 : 2 ≤ ((W : ℂ)).im := hw.2
  have hkey : ((w : ℂ)).im = ((W : ℂ)).im / ‖(W : ℂ)‖ ^ 2 := by
    have h1 : ((w : ℂ)).im = ((W : ℂ)).im * ‖(w : ℂ)‖ ^ 2 := by
      rw [hWim, div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr w.ne_zero))]
    rw [h1, hnorm, div_eq_mul_inv]
  rw [hkey, le_div_iff₀ hWpos]
  have h1 : 2 / (1 + C ^ 2) * ‖(W : ℂ)‖ ^ 2 ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hWnorm]
  linarith [h1, hWim2]
/-! ## The compactness half of `divisor_lower_E` -/

lemma exp_two_pi_div_ge (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (100 : ℝ) ≤ Real.exp (2 * Real.pi / t) := by
  have h1 : 2 * Real.pi ≤ 2 * Real.pi / t := by
    rw [le_div_iff₀ ht]; nlinarith [Real.pi_pos, ht1]
  have h2 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 6 ≤ Real.exp (2 * Real.pi / t) := Real.exp_le_exp.mpr (le_trans h2 h1)
  have h4 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (100 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    calc (100 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.exp 1) ^ 6 :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
  linarith [h3, h4 ▸ h5]

lemma ofComplex_I_eq_imagAxis (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) = imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht), UpperHalfPlane.coe_mk]
  show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I
  ring

lemma continuousOn_ofComplex_I_inv :
    ContinuousOn (fun p : ℍ × ℝ => UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹))
      {p : ℍ × ℝ | 0 < p.2} := by
  have hinv : ContinuousOn (fun p : ℍ × ℝ => (p.2)⁻¹) {p | 0 < p.2} := by
    refine ContinuousOn.inv₀ continuous_snd.continuousOn ?_
    intro p hp
    exact ne_of_gt hp
  have hcomp := UpperHalfPlane.continuousOn_ofComplex_I_mul.comp hinv
    (fun p hp => by
      have hp' : 0 < p.2 := hp
      simpa using inv_pos.mpr hp')
  refine hcomp.congr (fun p hp => ?_)
  simp [Function.comp_def, Complex.ofReal_inv]

lemma continuous_jInvariantFun : Continuous (fun τ : ℍ => jInvariantFun τ) := by
  have hE4c : Continuous (fun τ : ℍ => E4Fun τ) := (ModularForm.holo' ModularForm.E₄).continuous
  have hΔc : Continuous (fun τ : ℍ => DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  simp only [jInvariantFun, E4Fun]
  exact (hE4c.pow 3).div hΔc (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

lemma continuous_DeltaFun : Continuous (fun τ : ℍ => DeltaFun τ) :=
  (CuspForm.holo' CuspForm.discriminant).continuous

/-! ## The compact box, the far case, and the theorem -/

lemma ofComplex_I_inv_eq (t : ℝ) (ht : 0 < t) :
    UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)⁻¹) = imagAxis t⁻¹ (inv_pos.mpr ht) := by
  rw [← Complex.ofReal_inv, ofComplex_I_eq_imagAxis]

/-- The compact box of parameters `(w,t)` with `Im (S • w) ≤ C₂` and orbit separation. -/
def KLarge (C₂ ρ t₀ : ℝ) : Set (ℍ × ℝ) :=
  {p : ℍ × ℝ | |p.1.re| ≤ 1 / 4} ∩ {p | 2 / (1 + C₂ ^ 2) ≤ p.1.im} ∩
    {p | p.1.im ≤ 1 / 2} ∩ {p | t₀ ≤ p.2} ∩ {p | p.2 ≤ 1} ∩
    {p | ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖
        ≤ ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖}

lemma mem_KLarge {C₂ ρ t₀ : ℝ} {p : ℍ × ℝ} :
    p ∈ KLarge C₂ ρ t₀ ↔ |p.1.re| ≤ 1 / 4 ∧ 2 / (1 + C₂ ^ 2) ≤ p.1.im ∧
      p.1.im ≤ 1 / 2 ∧ t₀ ≤ p.2 ∧ p.2 ≤ 1 ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖ ≤ ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖ := by
  simp only [KLarge]
  constructor
  · intro h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩ := h
    exact ⟨ha, hb, hc, hd, he, hf⟩
  · rintro ⟨ha, hb, hc, hd, he, hf⟩
    exact ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩

lemma isClosed_KLarge (C₂ ρ t₀ : ℝ) : IsClosed (KLarge C₂ ρ t₀) := by
  have h1 : IsClosed {p : ℍ × ℝ | |p.1.re| ≤ 1 / 4} :=
    isClosed_le ((UpperHalfPlane.continuous_re.comp continuous_fst).abs) continuous_const
  have h2 : IsClosed {p : ℍ × ℝ | 2 / (1 + C₂ ^ 2) ≤ p.1.im} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_fst)
  have h3 : IsClosed {p : ℍ × ℝ | p.1.im ≤ 1 / 2} :=
    isClosed_le (UpperHalfPlane.continuous_im.comp continuous_fst) continuous_const
  have h4 : IsClosed {p : ℍ × ℝ | t₀ ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h5 : IsClosed {p : ℍ × ℝ | p.2 ≤ 1} := isClosed_le continuous_snd continuous_const
  have h6 : IsClosed {p : ℍ × ℝ | ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖
        ≤ ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖} := by
    rw [show {p : ℍ × ℝ | ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖
          ≤ ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖}
        = ⋂ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          {p : ℍ × ℝ | ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖
            ≤ ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖} from by
      ext p; simp]
    refine isClosed_iInter (fun γ => isClosed_le
      (f := fun p : ℍ × ℝ => ρ * p.2 ^ 2 * ‖orbitDen γ p.2‖)
      (g := fun p : ℍ × ℝ => ‖(p.1 : ℂ) * orbitDen γ p.2 - orbitNum γ p.2‖) ?_ ?_)
    · have hD : Continuous fun p : ℍ × ℝ => orbitDen γ p.2 := by
        simp only [orbitDen]; fun_prop
      have h2 : Continuous fun p : ℍ × ℝ => ρ * p.2 ^ 2 :=
        continuous_const.mul (continuous_snd.pow 2)
      exact h2.mul (hD.norm)
    · have hD : Continuous fun p : ℍ × ℝ => orbitDen γ p.2 := by
        simp only [orbitDen]; fun_prop
      have hN : Continuous fun p : ℍ × ℝ => orbitNum γ p.2 := by
        simp only [orbitNum]; fun_prop
      have hc : Continuous fun p : ℍ × ℝ => (p.1 : ℂ) :=
        UpperHalfPlane.continuous_coe.comp continuous_fst
      exact ((hc.mul hD).sub hN).norm
  unfold KLarge
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

lemma isCompact_KLarge {C₂ ρ t₀ : ℝ} (hC₂ : 2 ≤ C₂) (ht₀ : 0 < t₀) :
    IsCompact (KLarge C₂ ρ t₀) := by
  set τ₀ : ℍ := ⟨(1 / 4 : ℂ) * Complex.I, by simp⟩ with hτ₀def
  set Rl : ℝ := (1 / 2) / Real.sqrt ((2 / (1 + C₂ ^ 2)) * (1 / 4)) with hRldef
  have hsub : KLarge C₂ ρ t₀ ⊆ (Metric.closedBall τ₀ Rl) ×ˢ Set.Icc t₀ 1 := by
    intro p hp
    rw [mem_KLarge] at hp
    obtain ⟨hre, himlo, himhi, ht0, ht1, hcon⟩ := hp
    refine ⟨?_, ⟨ht0, ht1⟩⟩
    rw [Metric.mem_closedBall, hRldef]
    have hτ₀im : τ₀.im = 1 / 4 := by simp [τ₀]
    have hpos : 0 < (2 / (1 + C₂ ^ 2)) * (1 / 4) := by
      have : (0:ℝ) < 1 + C₂ ^ 2 := by positivity
      positivity
    have hsqrt : 0 < Real.sqrt ((2 / (1 + C₂ ^ 2)) * (1 / 4)) := Real.sqrt_pos.mpr hpos
    have hdist : ‖(p.1 : ℂ) - (τ₀ : ℂ)‖ ≤ 1 / 2 := by
      have hcoe : (τ₀ : ℂ) = (1 / 4 : ℂ) * Complex.I := rfl
      have hcoe' : (1 / 4 : ℂ) = (((1 / 4 : ℝ)) : ℂ) := by norm_num
      have h4 : ‖(p.1 : ℂ) - (τ₀ : ℂ)‖ ^ 2
          = ((p.1 : ℂ)).re ^ 2 + (((p.1 : ℂ)).im - 1 / 4) ^ 2 := by
        rw [hcoe, hcoe', Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero]
        ring
      have hre2 : ((p.1 : ℂ)).re ^ 2 ≤ (1 / 4) ^ 2 := by
        have h1 : |((p.1 : ℂ)).re| ≤ 1 / 4 := by
          have h2 : ((p.1 : ℂ)).re = p.1.re := rfl
          rw [h2]; exact hre
        nlinarith [h1, abs_nonneg (((p.1:ℂ)).re), sq_abs (((p.1:ℂ)).re)]
      have him2 : (((p.1 : ℂ)).im - 1 / 4) ^ 2 ≤ (1 / 4) ^ 2 := by
        have h2 : ((p.1 : ℂ)).im = p.1.im := rfl
        have h5 : (((p.1 : ℂ)).im - 1 / 4) ≤ 1 / 4 := by rw [h2]; linarith
        have h6 : -1 / 4 ≤ (((p.1 : ℂ)).im - 1 / 4) := by rw [h2]; linarith
        nlinarith [h5, h6]
      have h9 : ‖(p.1 : ℂ) - (τ₀ : ℂ)‖ ^ 2 ≤ 1 / 8 := by
        rw [h4]; linarith
      nlinarith [h9, norm_nonneg ((p.1 : ℂ) - (τ₀ : ℂ))]
    calc dist p.1 τ₀ ≤ dist (p.1 : ℂ) (τ₀ : ℂ) / Real.sqrt (p.1.im * τ₀.im) :=
          UpperHalfPlane.dist_le_dist_coe_div_sqrt p.1 τ₀
      _ = ‖(p.1 : ℂ) - (τ₀ : ℂ)‖ / Real.sqrt (p.1.im * τ₀.im) := by rw [dist_eq_norm]
      _ ≤ (1 / 2) / Real.sqrt ((2 / (1 + C₂ ^ 2)) * (1 / 4)) := by
          refine div_le_div₀ (by norm_num) hdist (Real.sqrt_pos.mpr hpos) ?_
          rw [hτ₀im]
          refine Real.sqrt_le_sqrt ?_
          exact mul_le_mul_of_nonneg_right himlo (by norm_num)
      _ = Rl := by rw [hRldef]
  refine IsCompact.of_isClosed_subset ?_ (isClosed_KLarge C₂ ρ t₀) hsub
  exact (isCompact_closedBall τ₀ Rl).prod isCompact_Icc

/-- Admissible parameters with `Im (S • w) ≤ C₂` lie in the compact box. -/
lemma mem_KLarge_of {C₂ ρ t₀ : ℝ} (hC₂ : 2 ≤ C₂) {w : ℍ} {t : ℝ} (ht : 0 < t)
    (hwE : w ∈ KEpsilon) (ht0 : t₀ ≤ t) (ht1 : t ≤ 1)
    (hcon : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • imagAxis t ht : ℍ)) : ℂ)‖)
    (hσ : (((ModularGroup.S • w : ℍ)) : ℂ).im ≤ C₂) :
    (w, t) ∈ KLarge C₂ ρ t₀ := by
  rw [mem_KLarge]
  refine ⟨?_, ?_, ?_, ht0, ht1, ?_⟩
  · have h := KEpsilon_re_le w hwE
    have h2 : ((w : ℂ)).re = w.re := rfl
    rwa [h2] at h
  · have h := KEpsilon_im_ge w hwE hσ hC₂
    have h2 : ((w : ℂ)).im = w.im := rfl
    rwa [h2] at h
  · have h := KEpsilon_im_le w hwE
    have h2 : ((w : ℂ)).im = w.im := rfl
    rwa [h2] at h
  · intro γ
    have h2 : ρ * t ^ 2 * ‖orbitDen γ t‖ ≤ ‖(w : ℂ) * orbitDen γ t - orbitNum γ t‖ :=
      (orbit_condition_iff ht γ w).mp (hcon γ)
    have h3 : ((w, t) : ℍ × ℝ).1 = w := rfl
    rw [h3]
    rw [show ((w : ℂ) * orbitDen γ t - orbitNum γ t) = ((w : ℂ) * orbitDen γ t - orbitNum γ t) from rfl]
    exact h2

/-- The function whose zero set is the coincidence set `j w = j (i/t)`. -/
def PsiE : ℍ × ℝ → ℝ := fun p =>
  ‖DeltaFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹)) *
    (jInvariantFun p.1 - jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹)))‖

lemma continuousOn_PsiE {C₂ ρ t₀ : ℝ} (ht₀ : 0 < t₀) : ContinuousOn PsiE (KLarge C₂ ρ t₀) := by
  have hcoe : ContinuousOn (fun p : ℍ × ℝ => UpperHalfPlane.ofComplex (Complex.I * (p.2:ℂ)⁻¹))
      (KLarge C₂ ρ t₀) := continuousOn_ofComplex_I_inv.mono (fun p hp => by
        rw [mem_KLarge] at hp
        exact lt_of_lt_of_le ht₀ hp.2.2.2.1)
  have hΔ : ContinuousOn (fun p : ℍ × ℝ =>
      DeltaFun (UpperHalfPlane.ofComplex (Complex.I * (p.2:ℂ)⁻¹))) (KLarge C₂ ρ t₀) :=
    continuous_DeltaFun.comp_continuousOn hcoe
  have hj : ContinuousOn (fun p : ℍ × ℝ =>
      jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2:ℂ)⁻¹))) (KLarge C₂ ρ t₀) :=
    continuous_jInvariantFun.comp_continuousOn hcoe
  have hj1 : ContinuousOn (fun p : ℍ × ℝ => jInvariantFun p.1) (KLarge C₂ ρ t₀) :=
    continuous_jInvariantFun.comp_continuousOn continuous_fst.continuousOn
  unfold PsiE
  exact (hΔ.mul (hj1.sub hj)).norm

/-- `PsiE` is positive on the compact box. -/
lemma PsiE_pos {C₂ ρ t₀ : ℝ} (hρ : 0 < ρ) (ht₀ : 0 < t₀) {p : ℍ × ℝ}
    (hp : p ∈ KLarge C₂ ρ t₀) : 0 < PsiE p := by
  rw [mem_KLarge] at hp
  obtain ⟨hre, himlo, himhi, ht0, ht1, hcon⟩ := hp
  have htpos : 0 < p.2 := lt_of_lt_of_le ht₀ ht0
  have hne : DeltaFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹)) ≠ 0 :=
    Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  unfold PsiE
  rw [norm_pos_iff]
  intro hzero
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact hne hz
  · have hsub : jInvariantFun p.1
        = jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹)) := sub_eq_zero.mp hz
    have h2 : UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)⁻¹)
        = imagAxis (p.2)⁻¹ (inv_pos.mpr htpos) := ofComplex_I_inv_eq p.2 htpos
    have hmain : jInvariantFun (imagAxis (p.2)⁻¹ (inv_pos.mpr htpos)) = jInvariantFun p.1 := by
      rw [← h2]; exact hsub.symm
    obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq hmain
    have hcon' : ρ * p.2 ^ 2
        ≤ ‖(p.1 : ℂ) - ((((γ⁻¹ * ModularGroup.S) • imagAxis p.2 htpos : ℍ)) : ℂ)‖ :=
      (orbit_condition_iff htpos (γ⁻¹ * ModularGroup.S) p.1).mpr (hcon (γ⁻¹ * ModularGroup.S))
    have hcoe : ((((γ⁻¹ * ModularGroup.S) • imagAxis p.2 htpos : ℍ)) : ℂ) = (p.1 : ℂ) := by
      rw [mul_smul, imagAxis_smul_S, ← hγ, inv_smul_smul]
    rw [hcoe, sub_self, norm_zero] at hcon'
    have hpos : 0 < ρ * p.2 ^ 2 := by positivity
    nlinarith [hcon', hpos]

/-- The far case: `Im (S • w) > C₂` makes `Δ(i/t) j(w)` dominate `E₄(i/t)³`. -/
lemma far_case {cΔ C₂ cg : ℝ} {w : ℍ} {t : ℝ} (ht : 0 < t)
    (hcΔ : 0 < cΔ) (hcg : 0 < cg)
    (hΔlo : cΔ ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖)
    (hEup : ‖E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 3‖ ≤ 201 ^ 3)
    (hgro : cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
      ≤ ‖jInvariantFun (ModularGroup.S • w)‖)
    (hexpC₂ : 2 * 201 ^ 3 ≤ cΔ * cg * Real.exp (2 * Real.pi * C₂))
    (hσ : C₂ ≤ (ModularGroup.S • w).im) :
    cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) - 201 ^ 3
      ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
          (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  set W : ℍ := ModularGroup.S • w with hW
  have hjeq : jInvariantFun w = jInvariantFun W := by
    have hw : w = ModularGroup.S • W := by rw [hW, S_smul_S_smul]
    rw [hw, Work.Kernels.KernelFacts.jInvariantFun_S_smul]
  have h1 : cΔ * (cg * Real.exp (2 * Real.pi * W.im))
      ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) * jInvariantFun W‖ := by
    rw [norm_mul]
    have hgro' : cg * Real.exp (2 * Real.pi * W.im) ≤ ‖jInvariantFun W‖ := hgro
    calc cΔ * (cg * Real.exp (2 * Real.pi * W.im)) ≤ cΔ * ‖jInvariantFun W‖ :=
          mul_le_mul_of_nonneg_left hgro' hcΔ.le
      _ ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖ * ‖jInvariantFun W‖ :=
          mul_le_mul_of_nonneg_right hΔlo (norm_nonneg _)
  have h2 : ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))
      * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖ ≤ 201 ^ 3 := by
    have h5 : jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht))
        = E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 3
            / DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) := rfl
    rw [h5, mul_div_cancel₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)]
    exact hEup
  have h3 : DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))
      * (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))
      = DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) * jInvariantFun W
        - DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))
          * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)) := by
    rw [← hjeq]; ring
  have h4 := norm_sub_norm_le
    (DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) * jInvariantFun W)
    (DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))
      * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))
  rw [h3]
  linarith [h1, h2, h4]

/-- **The divisor is bounded below on the range `t₀ ≤ t ≤ 1`.** -/
theorem divisor_lower_E_large_t (ρ t₀ : ℝ) (hρ : 0 < ρ) (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : ℍ) (t : ℝ) (ht : 0 < t),
      w ∈ KEpsilon → t₀ ≤ t → t ≤ 1 →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • imagAxis t ht : ℍ)) : ℂ)‖) →
      c ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
            (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨cg, Cg, hcg0, hCg0, hgrowth⟩ := jInvariantFun_funnel_growth
  set cΔ : ℝ := (1 / 2 : ℝ) ^ 24 * Real.exp (-(2 * Real.pi / t₀)) with hcΔdef
  have hcΔ0 : 0 < cΔ := by rw [hcΔdef]; positivity
  have hΔlo : ∀ (t : ℝ) (ht : 0 < t), t₀ ≤ t → t ≤ 1 →
      cΔ ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖ := by
    intro t ht ht0 ht1
    have hs : 0 < t⁻¹ := inv_pos.mpr ht
    have hq0 : 0 ≤ Real.exp (-(2 * Real.pi * t⁻¹)) := (Real.exp_pos _).le
    have hq3 : Real.exp (-(2 * Real.pi * t⁻¹)) ≤ 1 / 3 := by
      have h4 : Real.exp (2 * Real.pi / t) ≤ Real.exp (2 * Real.pi * t⁻¹) := by
        refine Real.exp_le_exp.mpr ?_
        rw [div_eq_mul_inv]
      have h3 : (3 : ℝ) ≤ Real.exp (2 * Real.pi * t⁻¹) :=
        le_trans (by norm_num) (le_trans (exp_two_pi_div_ge t ht ht1) h4)
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h3
    obtain ⟨hlo, -⟩ := tprod_one_sub_pow24_mem _ hq0 hq3
    have hprodnn : (0 : ℝ) ≤ ∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t⁻¹))) ^ (n + 1)) ^ 24 :=
      le_trans (by norm_num) hlo
    rw [DeltaFun_imagAxis_eq t⁻¹ hs, norm_mul, norm_ofReal_exp, norm_ofReal_eq,
      abs_of_nonneg hprodnn]
    have he : Real.exp (-(2 * Real.pi / t₀)) ≤ Real.exp (-(2 * Real.pi * t⁻¹)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : t⁻¹ ≤ t₀⁻¹ := (inv_le_inv₀ ht ht₀).mpr ht0
      rw [div_eq_mul_inv]
      nlinarith [Real.pi_pos, h1]
    have h3 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t⁻¹)) := (Real.exp_pos _).le
    calc cΔ = (1 / 2 : ℝ) ^ 24 * Real.exp (-(2 * Real.pi / t₀)) := hcΔdef
      _ ≤ (1 / 2 : ℝ) ^ 24 * Real.exp (-(2 * Real.pi * t⁻¹)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ Real.exp (-(2 * Real.pi * t⁻¹))
            * ∏' n : ℕ, (1 - (Real.exp (-(2 * Real.pi * t⁻¹))) ^ (n + 1)) ^ 24 := by
          nlinarith [hlo, h3, Real.exp_pos (-(2 * Real.pi * t⁻¹))]
  have hEup : ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 3‖ ≤ 201 ^ 3 := by
    intro t ht ht1
    have hs : 0 < t⁻¹ := inv_pos.mpr ht
    have h1 : (1 : ℝ) ≤ (imagAxis t⁻¹ hs).im := by
      rw [imagAxis_im]; exact (one_le_inv₀ ht).mpr ht1
    have hu := E4Fun_sub_one_explicit h1
    have hq : ‖qParamFun (imagAxis t⁻¹ hs)‖ = Real.exp (-(2 * Real.pi / t)) := by
      rw [norm_qParamFun_imagAxis]
      ring_nf
    rw [hq] at hu
    have hqle : Real.exp (-(2 * Real.pi / t)) ≤ 1 / 100 := by
      have h3 : (100 : ℝ) ≤ Real.exp (2 * Real.pi / t) := exp_two_pi_div_ge t ht ht1
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h3
    have hE1 : ‖E4Fun (imagAxis t⁻¹ hs) - 1‖ ≤ 200 := by
      have : (20000 : ℝ) * Real.exp (-(2 * Real.pi / t)) ≤ 200 := by nlinarith [hqle]
      linarith [hu, this]
    have hEb : ‖E4Fun (imagAxis t⁻¹ hs)‖ ≤ 201 := by
      have h2 : E4Fun (imagAxis t⁻¹ hs) = (E4Fun (imagAxis t⁻¹ hs) - 1) + 1 := by ring
      have h3 := norm_add_le (E4Fun (imagAxis t⁻¹ hs) - 1) (1 : ℂ)
      rw [norm_one] at h3
      rw [h2]
      linarith
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hEb 3
  set C₂ : ℝ := max 2 (Real.log (max (2 * 201 ^ 3 / (cΔ * cg)) 1) / (2 * Real.pi) + 1)
    with hC₂def
  have hC₂2 : 2 ≤ C₂ := le_max_left _ _
  have hexpC₂ : 2 * 201 ^ 3 ≤ cΔ * cg * Real.exp (2 * Real.pi * C₂) := by
    have h7 : Real.exp (Real.log (max (2 * 201 ^ 3 / (cΔ * cg)) 1)) ≤ Real.exp (2 * Real.pi * C₂) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : Real.log (max (2 * 201 ^ 3 / (cΔ * cg)) 1) / (2 * Real.pi) + 1 ≤ C₂ :=
        le_max_right _ _
      have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
      have h5 := mul_le_mul_of_nonneg_right h1 h2.le
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h2), one_mul] at h5
      linarith [h5, h2]
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _))] at h7
    have h8 : (0 : ℝ) < cΔ * cg := by positivity
    have h9 : max (2 * 201 ^ 3 / (cΔ * cg)) 1 * (cΔ * cg) ≥ 2 * 201 ^ 3 := by
      have h10 : (2 * 201 ^ 3 / (cΔ * cg)) ≤ max (2 * 201 ^ 3 / (cΔ * cg)) 1 := le_max_left _ _
      have h11 : (2 * 201 ^ 3 / (cΔ * cg)) * (cΔ * cg) = 2 * 201 ^ 3 := by field_simp
      nlinarith [h10, h8, h11.le, h11.ge]
    nlinarith [h7, h9]
  rcases (KLarge C₂ ρ t₀).eq_empty_or_nonempty with hemp | hne
  · refine ⟨min cΔ (201 ^ 3), lt_min hcΔ0 (by norm_num), ?_⟩
    intro w t ht hwE ht0 ht1 hcon
    set A : ℝ := cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) with hA
    set Q : ℝ := ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
      (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ with hQ
    change min cΔ (201 ^ 3) ≤ Q
    have hσ : C₂ ≤ (ModularGroup.S • w).im := by
      by_contra hlt
      have hle : (((ModularGroup.S • w : ℍ)) : ℂ).im ≤ C₂ := by
        have h2 : (((ModularGroup.S • w : ℍ)) : ℂ).im = (ModularGroup.S • w).im := rfl
        rw [h2]; linarith [not_le.mp hlt]
      have hmem := mem_KLarge_of hC₂2 ht hwE ht0 ht1 hcon hle
      rw [hemp] at hmem
      exact hmem
    have hfar : A - 201 ^ 3 ≤ Q := by
      rw [hA, hQ]
      exact far_case ht hcΔ0 hcg0 (hΔlo t ht ht0 ht1) (hEup t ht ht1)
        ((hgrowth (ModularGroup.S • w) hwE.2).1) hexpC₂ hσ
    have h6 : 2 * 201 ^ 3 ≤ A := by
      rw [hA]
      have h7 : Real.exp (2 * Real.pi * C₂)
          ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
        Real.exp_le_exp.mpr (by nlinarith [hσ, Real.pi_pos])
      have h8 : cΔ * cg * Real.exp (2 * Real.pi * C₂)
          ≤ cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
        calc cΔ * cg * Real.exp (2 * Real.pi * C₂)
            = cΔ * (cg * Real.exp (2 * Real.pi * C₂)) := by ring
          _ ≤ cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h7 hcg0.le) hcΔ0.le
      linarith [hexpC₂, h8]
    have h201 : (201 : ℝ) ^ 3 ≤ A - 201 ^ 3 := by linarith
    exact le_trans (min_le_right cΔ ((201 : ℝ) ^ 3)) (le_trans h201 hfar)
  · obtain ⟨p₀, hp₀, hp₀min⟩ := (isCompact_KLarge hC₂2 ht₀).exists_isMinOn hne
      (continuousOn_PsiE ht₀)
    have hp₀pos : 0 < PsiE p₀ := PsiE_pos hρ ht₀ hp₀
    refine ⟨min (min cΔ (201 ^ 3)) (PsiE p₀), lt_min (lt_min hcΔ0 (by norm_num)) hp₀pos, ?_⟩
    intro w t ht hwE ht0 ht1 hcon
    set A : ℝ := cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) with hA
    set Q : ℝ := ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
      (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ with hQ
    have hQt : Q = PsiE (w, t) := by
      rw [hQ]
      unfold PsiE
      rw [ofComplex_I_inv_eq t ht]
    rw [hQt]
    by_cases hσ : C₂ ≤ (ModularGroup.S • w).im
    · have hfar : A - 201 ^ 3 ≤ PsiE (w, t) := by
        rw [hA, ← hQt]
        exact far_case ht hcΔ0 hcg0 (hΔlo t ht ht0 ht1) (hEup t ht ht1)
          ((hgrowth (ModularGroup.S • w) hwE.2).1) hexpC₂ hσ
      have h6 : 2 * 201 ^ 3 ≤ A := by
        rw [hA]
        have h7 : Real.exp (2 * Real.pi * C₂)
            ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
          Real.exp_le_exp.mpr (by nlinarith [hσ, Real.pi_pos])
        have h8 : cΔ * cg * Real.exp (2 * Real.pi * C₂)
            ≤ cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
          calc cΔ * cg * Real.exp (2 * Real.pi * C₂)
              = cΔ * (cg * Real.exp (2 * Real.pi * C₂)) := by ring
            _ ≤ cΔ * (cg * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h7 hcg0.le) hcΔ0.le
        linarith [hexpC₂, h8]
      have h201 : (201 : ℝ) ^ 3 ≤ A - 201 ^ 3 := by linarith
      have hmin : min (min cΔ (201 ^ 3)) (PsiE p₀) ≤ (201 : ℝ) ^ 3 := by
        have h4 : min (min cΔ (201 ^ 3)) (PsiE p₀) ≤ min cΔ (201 ^ 3) := min_le_left _ _
        exact le_trans h4 (min_le_right _ _)
      exact le_trans hmin (le_trans h201 hfar)
    · have hle : (((ModularGroup.S • w : ℍ)) : ℂ).im ≤ C₂ := by
        have h2 : (((ModularGroup.S • w : ℍ)) : ℂ).im = (ModularGroup.S • w).im := rfl
        rw [h2]; exact le_of_lt (not_le.mp hσ)
      have hmem := mem_KLarge_of hC₂2 ht hwE ht0 ht1 hcon hle
      have hmin := (isMinOn_iff.mp hp₀min) (w, t) hmem
      exact le_trans (min_le_right _ _) hmin
/-! ## The asymptotic half of `divisor_lower_E` -/

/-- `i * (x + y i) = -y + x i`. -/
lemma I_mul_add_I (x y : ℝ) :
    Complex.I * ((x : ℂ) + (y : ℂ) * Complex.I) = -(y : ℂ) + (x : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]


theorem divisor_lower_E_small_t (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ T ≤ 1 / 2 ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → t ≤ T →
        (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • imagAxis t ht : ℍ)) : ℂ)‖) →
        c ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨CΔ, hCΔ0, hΔ2⟩ := DeltaFun_inv_imagAxis_two_term
  obtain ⟨C₃, hC₃0, hE43⟩ := E4Fun_inv_imagAxis_three
  obtain ⟨Cj, hCj0, hj2⟩ := jInvariantFun_funnel_two_term
  obtain ⟨cδ, hcδ0, hlat⟩ := exp_lattice_lower (ρ / 2) (by linarith)
  set ε : ℝ := min (1 - Real.exp (-(2 * Real.pi))) cδ with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    refine lt_min ?_ hcδ0
    have h1 : Real.exp (-(2 * Real.pi)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith only [Real.pi_pos]
    linarith only [h1]
  have hε1 : ε ≤ 1 - Real.exp (-(2 * Real.pi)) := by rw [hεdef]; exact min_le_left _ _
  have hε2 : ε ≤ cδ := by rw [hεdef]; exact min_le_right _ _
  have hεle : ε ≤ 1 := by
    have h1 : (0 : ℝ) < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
    linarith only [hε1, h1]
  set K : ℝ := 4 * CΔ + Cj + 4 * CΔ * Cj + C₃ with hKdef
  set MAX : ℝ := K + 1 with hMAXdef
  have hMAX0 : 0 < MAX := by rw [hMAXdef]; have := hCΔ0; have := hCj0; have := hC₃0; positivity
  have hCΔMAX : CΔ ≤ MAX := by rw [hMAXdef, hKdef]; nlinarith only [hCΔ0, hCj0, hC₃0]
  have hCjMAX : Cj ≤ MAX := by rw [hMAXdef, hKdef]; nlinarith only [hCΔ0, hCj0, hC₃0]
  have hC₃MAX : C₃ ≤ MAX := by rw [hMAXdef, hKdef]; nlinarith only [hCΔ0, hCj0, hC₃0]
  set M : ℝ := 4 * MAX / ε + 1 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; positivity
  obtain ⟨T₀, hT₀0, hT₀⟩ := exists_le_exp_two_pi_div M
  refine ⟨ε / 2, min T₀ (1 / 2), by positivity, lt_min hT₀0 (by norm_num),
    min_le_right _ _, ?_⟩
  intro w t ht hwE htT hcon
  have htT0 : t ≤ T₀ := le_trans htT (min_le_left _ _)
  have ht12 : t ≤ 1 / 2 := le_trans htT (min_le_right _ _)
  have ht1 : t ≤ 1 := by linarith only [ht12]
  set W : ℍ := ModularGroup.S • w with hW
  have hW2 : 2 ≤ W.im := by rw [hW]; exact hwE.2
  have hjw : jInvariantFun w = jInvariantFun W := by
    have hw : w = ModularGroup.S • W := by rw [hW, S_smul_S_smul]
    rw [hw, Work.Kernels.KernelFacts.jInvariantFun_S_smul]
  set E0 : ℝ := Real.exp (-(2 * Real.pi / t)) with hE0def
  have hE0pos : 0 < E0 := by rw [hE0def]; positivity
  have hE0le1 : E0 ≤ 1 := by
    rw [hE0def, Real.exp_le_one_iff]; exact neg_nonpos.mpr (by positivity)
  have hE0sq : E0 * E0 ≤ E0 := by
    simpa using mul_le_mul_of_nonneg_right hE0le1 hE0pos.le
  have hE0quarter : MAX * E0 ≤ ε / 4 := by
    have hMt : M ≤ Real.exp (2 * Real.pi / t) := hT₀ t ht htT0
    have h1 : E0 ≤ 1 / M := by
      rw [hE0def, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hM0 hMt
    have h2 : MAX * (1 / M) ≤ ε / 4 := by
      rw [hMdef, mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * MAX / ε + 1)]
      have h3 : (ε / 4) * (4 * MAX / ε + 1) = MAX + ε / 4 := by
        field_simp <;> ring
      linarith only [h3, hε0]
    calc MAX * E0 ≤ MAX * (1 / M) := mul_le_mul_of_nonneg_left h1 hMAX0.le
      _ ≤ ε / 4 := h2
  set x : ℝ := (W : ℂ).re with hxdef
  set σ : ℝ := (W : ℂ).im with hσdef
  set κ : ℝ := σ - t⁻¹ with hκdef
  set E1 : ℝ := Real.exp (2 * Real.pi * κ) with hE1def
  have hE1pos : 0 < E1 := by rw [hE1def]; positivity
  set e2 : ℝ := Real.exp (-(2 * Real.pi * σ)) with he2def
  have he2pos : 0 < e2 := by rw [he2def]; positivity
  set z : ℂ := ((2 * Real.pi * κ : ℝ) : ℂ) + ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I with hzdef
  set qW : ℂ := qParamFun W with hqW
  have hqWnorm : ‖qW‖ = e2 := by
    rw [hqW, he2def, norm_qParamFun, hσdef, UpperHalfPlane.coe_im]
  have hzre : z.re = 2 * Real.pi * κ := by
    rw [hzdef]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      add_zero]
    ring
  have hznorm : ‖Complex.exp z‖ = E1 := by rw [Complex.norm_exp, hzre, hE1def]
  have hσrel : e2 * E1 = E0 := by
    rw [he2def, hE1def, hE0def, ← Real.exp_add]
    congr 1
    rw [hκdef, hσdef]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hzeq : 2 * (Real.pi : ℂ) * ((κ : ℂ) - ((x:ℝ):ℂ) * Complex.I) = z := by
    rw [hzdef]
    push_cast
    ring
  have hzval : ((E0 : ℝ) : ℂ) * (qW)⁻¹ = Complex.exp z := by
    rw [hE0def, hqW, hzdef, qParamFun, Complex.ofReal_exp, ← Complex.exp_neg,
      ← Complex.exp_add]
    congr 1
    have hWc : (W : ℂ) = ((x : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * Complex.I := by
      rw [hxdef, hσdef]; exact (Complex.re_add_im _).symm
    rw [hWc,
      show (2 * (Real.pi : ℂ) * Complex.I) * ((x : ℂ) + (σ : ℂ) * Complex.I)
        = 2 * (Real.pi : ℂ) * (Complex.I * ((x : ℂ) + (σ : ℂ) * Complex.I)) by ring,
      I_mul_add_I]
    rw [hκdef]
    push_cast
    ring
  set Δt : ℂ := DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) with hΔt
  set Et : ℂ := E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) with hEt
  set R : ℂ := ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) with hR
  set δ1 : ℂ := Δt * R - 1 with hδ1def
  set δ2 : ℂ := jInvariantFun W * qW - 1 with hδ2def
  set δ3 : ℂ := Et ^ 3 - 1 with hδ3def
  have hδ1b : ‖δ1‖ ≤ CΔ * E0 := by
    rw [hδ1def, hΔt, hR, hE0def]
    exact hΔ2 t ht ht12
  have hδ3b : ‖δ3‖ ≤ C₃ * E0 := by
    rw [hδ3def, hEt, hE0def]
    exact hE43 t ht ht12
  have hδ2b : ‖δ2‖ ≤ Cj * e2 := by
    rw [hδ2def, hqW, ← hqWnorm, hqW]
    exact hj2 W hW2
  have hδ1le : ‖δ1‖ ≤ ε / 4 := by
    have h1 : ‖δ1‖ ≤ MAX * E0 := le_trans hδ1b (mul_le_mul_of_nonneg_right hCΔMAX hE0pos.le)
    linarith only [h1, hE0quarter]
  have hδ3le : ‖δ3‖ ≤ ε / 4 := by
    have h1 : ‖δ3‖ ≤ MAX * E0 := le_trans hδ3b (mul_le_mul_of_nonneg_right hC₃MAX hE0pos.le)
    linarith only [h1, hE0quarter]
  have hjDt : Δt * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)) = Et ^ 3 := by
    rw [hΔt, hEt]
    exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun _
  have hrD : Δt = (1 + δ1) * ((E0 : ℝ) : ℂ) := by
    rw [hδ1def, hE0def, hR]
    rw [show (1 : ℂ) + (Δt * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) - 1)
        = Δt * ((Real.exp (2 * Real.pi / t) : ℝ) : ℂ) by ring]
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show 2 * Real.pi / t + -(2 * Real.pi / t) = 0 by ring, Real.exp_zero,
      Complex.ofReal_one, mul_one]
  have hrj : jInvariantFun W = (1 + δ2) * qW⁻¹ := by
    have hq : qW ≠ 0 := by rw [hqW]; exact Complex.exp_ne_zero _
    rw [hδ2def]
    field_simp
    ring
  have hQE : Δt * (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))
      = (1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3) := by
    have h1 : Δt * (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))
        = Δt * jInvariantFun W - Et ^ 3 := by
      rw [hjw, ← hjDt]; ring
    have h2 : Δt * jInvariantFun W = ((1 + δ1) * ((E0 : ℝ) : ℂ)) * ((1 + δ2) * qW⁻¹) := by
      rw [hrD, hrj]
    have h3 : ((1 + δ1) * ((E0 : ℝ) : ℂ)) * ((1 + δ2) * qW⁻¹) - Et ^ 3
        = (1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3) := by
      rw [hδ3def, hEt, ← hzval]
      ring
    rw [h1, h2, h3]
  have htri1 : ‖(δ1 + δ2 + δ1 * δ2) * Complex.exp z‖
      ≤ ‖δ1‖ * E1 + ‖δ2‖ * E1 + ‖δ1‖ * ‖δ2‖ * E1 := by
    rw [norm_mul, hznorm]
    have h2 : ‖δ1 + δ2 + δ1 * δ2‖ ≤ ‖δ1‖ + ‖δ2‖ + ‖δ1‖ * ‖δ2‖ := by
      calc ‖δ1 + δ2 + δ1 * δ2‖ ≤ ‖δ1 + δ2‖ + ‖δ1 * δ2‖ := norm_add_le _ _
        _ ≤ (‖δ1‖ + ‖δ2‖) + ‖δ1‖ * ‖δ2‖ := by
            rw [norm_mul]
            linarith only [norm_add_le δ1 δ2]
        _ = ‖δ1‖ + ‖δ2‖ + ‖δ1‖ * ‖δ2‖ := by ring
    calc ‖δ1 + δ2 + δ1 * δ2‖ * E1 ≤ (‖δ1‖ + ‖δ2‖ + ‖δ1‖ * ‖δ2‖) * E1 :=
          mul_le_mul_of_nonneg_right h2 hE1pos.le
      _ = ‖δ1‖ * E1 + ‖δ2‖ * E1 + ‖δ1‖ * ‖δ2‖ * E1 := by ring
  have herr : ‖(δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3‖
      ≤ ‖δ1‖ * E1 + ‖δ2‖ * E1 + ‖δ1‖ * ‖δ2‖ * E1 + ‖δ3‖ := by
    have h := norm_sub_le ((δ1 + δ2 + δ1 * δ2) * Complex.exp z) δ3
    linarith only [h, htri1]
  have hdecompA : (1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)
      = (Complex.exp z - 1) + ((δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3) := by ring
  have hzt : 1 - E1 ≤ ‖Complex.exp z - 1‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.exp z)
    rw [norm_one, hznorm, norm_sub_rev] at h1
    linarith only [h1]
  -- ============ small case ============
  have hQs : E1 ≤ 4 → ε / 2 ≤ ‖(1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)‖ := by
    intro hE1le4
    have hBE1 : ‖δ2‖ * E1 ≤ Cj * E0 := by
      calc ‖δ2‖ * E1 ≤ (Cj * e2) * E1 := mul_le_mul_of_nonneg_right hδ2b hE1pos.le
        _ = Cj * (e2 * E1) := by ring
        _ = Cj * E0 := by rw [hσrel]
    have hAE1 : ‖δ1‖ * E1 ≤ 4 * CΔ * E0 := by
      calc ‖δ1‖ * E1 ≤ (CΔ * E0) * E1 := mul_le_mul_of_nonneg_right hδ1b hE1pos.le
        _ = CΔ * E0 * E1 := by ring
        _ ≤ CΔ * E0 * 4 := mul_le_mul_of_nonneg_left hE1le4 (by positivity)
        _ = 4 * CΔ * E0 := by ring
    have hABE1 : ‖δ1‖ * ‖δ2‖ * E1 ≤ 4 * CΔ * Cj * E0 := by
      have hmul : ‖δ1‖ * ‖δ2‖ ≤ (CΔ * E0) * (Cj * e2) :=
        mul_le_mul hδ1b hδ2b (norm_nonneg _) (by positivity)
      have h1 : ‖δ1‖ * ‖δ2‖ * E1 ≤ (CΔ * E0) * (Cj * e2) * E1 :=
        mul_le_mul_of_nonneg_right hmul hE1pos.le
      calc ‖δ1‖ * ‖δ2‖ * E1 ≤ (CΔ * E0) * (Cj * e2) * E1 := h1
        _ = CΔ * Cj * (E0 * (e2 * E1)) := by ring
        _ = CΔ * Cj * (E0 * E0) := by rw [hσrel]
        _ = (CΔ * Cj * E0) * E0 := by ring
        _ ≤ (CΔ * Cj * E0) * 1 := by
            exact mul_le_mul_of_nonneg_left hE0le1 (by positivity)
        _ = CΔ * Cj * E0 := by ring
        _ ≤ 4 * CΔ * Cj * E0 := by
            have h4 : (0:ℝ) ≤ CΔ * Cj * E0 := by positivity
            linarith only [h4]
    have herrA : ‖(δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3‖ ≤ ε / 4 := by
      have hK : 4 * CΔ * E0 + Cj * E0 + 4 * CΔ * Cj * E0 + C₃ * E0 ≤ ε / 4 := by
        have h1 : 4 * CΔ * E0 + Cj * E0 + 4 * CΔ * Cj * E0 + C₃ * E0 = K * E0 := by
          rw [hKdef]; ring
        rw [h1]
        calc K * E0 ≤ MAX * E0 :=
              mul_le_mul_of_nonneg_right (by rw [hMAXdef]; linarith) hE0pos.le
          _ ≤ ε / 4 := hE0quarter
      linarith only [herr, hAE1, hBE1, hABE1, hδ3b, hK]
    have hE1low : ε ≤ ‖Complex.exp z - 1‖ := by
      by_cases hκ2 : -1 ≤ κ
      · have hκ2' : -1 ≤ ((ModularGroup.S • w : ℍ) : ℂ).im - t⁻¹ := by
          have h1 : (W : ℂ).im - t⁻¹ = ((ModularGroup.S • w : ℍ) : ℂ).im - t⁻¹ := by
            rw [hW]
          rw [hκdef, hσdef] at hκ2
          rwa [h1] at hκ2
        have hxeq : ((ModularGroup.S • w : ℍ) : ℂ).re = x := by rw [hxdef, hW]
        have hκeq : ((ModularGroup.S • w : ℍ) : ℂ).im - t⁻¹ = κ := by
          rw [hκdef, hσdef, hW]
        have hsep : ∀ c : ℤ, (ρ / 2) ^ 2 ≤ (x + (c : ℝ)) ^ 2 + κ ^ 2 := by
          intro c
          have h := constraint_lattice_sep hρ ht ht1 hcon hκ2' c
          rw [hxeq, hκeq] at h
          have h2 : ρ ^ 2 * (1 / 2) ^ 2 ≤ ρ ^ 2 * (1 - t) ^ 2 := by
            have h8 : (0 : ℝ) < ρ ^ 2 := by positivity
            have h9 : (1 / 2 : ℝ) ≤ 1 - t := by linarith only [ht12]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h9 2) h8.le
          nlinarith only [h, h2]
        have h3 : cδ ≤ ‖Complex.exp (2 * (Real.pi : ℂ)
            * ((κ : ℂ) - ((x : ℝ) : ℂ) * Complex.I)) - 1‖ := by
          refine hlat ((κ : ℂ) - ((x : ℝ) : ℂ) * Complex.I) ?_
          intro m
          have h4 := hsep m
          have h5 : ‖((κ : ℂ) - ((x : ℝ) : ℂ) * Complex.I) - (m : ℂ) * Complex.I‖ ^ 2
              = κ ^ 2 + (x + (m : ℝ)) ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
              Complex.intCast_re, Complex.intCast_im, mul_one, mul_zero, zero_mul, sub_zero,
              add_zero]
            ring
          have h4' : (ρ / 2) ^ 2 ≤ κ ^ 2 + (x + (m : ℝ)) ^ 2 := by linarith only [h4]
          have h6 : (ρ / 2) ^ 2
              ≤ ‖((κ : ℂ) - ((x : ℝ) : ℂ) * Complex.I) - (m : ℂ) * Complex.I‖ ^ 2 := by
            rw [h5]; exact h4'
          have h7 := sq_le_sq.mp h6
          rwa [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at h7
        rw [hzeq] at h3
        exact le_trans hε2 h3
      · have h2 : E1 ≤ Real.exp (-(2 * Real.pi)) := by
          rw [hE1def]
          exact Real.exp_le_exp.mpr (by nlinarith only [not_le.mp hκ2, Real.pi_pos])
        have h5 : 1 - Real.exp (-(2 * Real.pi)) ≤ ‖Complex.exp z - 1‖ := by
          linarith only [hzt, h2]
        exact le_trans hε1 h5
    have h4 : ε / 2 ≤ ‖Complex.exp z - 1‖ - ε / 4 := by linarith only [hE1low, hε0]
    have htri : ‖Complex.exp z - 1‖ - ε / 4
        ≤ ‖(Complex.exp z - 1) + ((δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3)‖ := by
      have h1 : ‖Complex.exp z - 1‖
          ≤ ‖(Complex.exp z - 1) + ((δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3)‖
            + ‖(δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3‖ := by
        calc ‖Complex.exp z - 1‖
            = ‖((Complex.exp z - 1) + ((δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3))
                - ((δ1 + δ2 + δ1 * δ2) * Complex.exp z - δ3)‖ := by congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      linarith only [h1, herrA]
    calc ε / 2 ≤ ‖Complex.exp z - 1‖ - ε / 4 := h4
      _ ≤ _ := htri
      _ = ‖(1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)‖ := by rw [← hdecompA]
  -- ============ large case ============
  have hQl : 4 ≤ E1 → ε / 2 ≤ ‖(1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)‖ := by
    intro hE1ge4
    have hδ2le : ‖δ2‖ ≤ ε / 4 := by
      have hσ1 : t⁻¹ ≤ σ := by
        have h1 : (1 : ℝ) < E1 := lt_of_lt_of_le (by norm_num) hE1ge4
        rw [hE1def, Real.one_lt_exp_iff] at h1
        have h2 : 0 < κ := by nlinarith only [Real.pi_pos, h1]
        rw [hκdef] at h2
        linarith only [h2]
      have he2le : e2 ≤ E0 := by
        rw [he2def, hE0def, Real.exp_le_exp, div_eq_mul_inv]
        nlinarith only [Real.pi_pos, hσ1]
      have h2 : Cj * e2 ≤ MAX * E0 :=
        mul_le_mul hCjMAX he2le (le_of_lt he2pos) hMAX0.le
      linarith only [hδ2b, h2, hE0quarter]
    have hA1 : (1 : ℝ) - ε / 4 ≤ ‖1 + δ1‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-δ1)
      rw [norm_one, norm_neg] at h
      have h2 : (1 : ℂ) - -δ1 = 1 + δ1 := by ring
      rw [h2] at h
      linarith only [h, hδ1le]
    have hA2 : (1 : ℝ) - ε / 4 ≤ ‖1 + δ2‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-δ2)
      rw [norm_one, norm_neg] at h
      have h2 : (1 : ℂ) - -δ2 = 1 + δ2 := by ring
      rw [h2] at h
      linarith only [h, hδ2le]
    have hA3 : ‖1 + δ3‖ ≤ 1 + ε / 4 := by
      have h := norm_add_le (1 : ℂ) δ3
      rw [norm_one] at h
      linarith only [h, hδ3le]
    have hnorm : ‖(1 + δ1) * (1 + δ2) * Complex.exp z‖ = ‖1 + δ1‖ * ‖1 + δ2‖ * E1 := by
      rw [norm_mul, norm_mul, hznorm]
    have hprod : (1 - ε / 4) * (1 - ε / 4) * E1 ≤ ‖1 + δ1‖ * ‖1 + δ2‖ * E1 := by
      have h0 : (0 : ℝ) ≤ 1 - ε / 4 := by linarith only [hεle]
      have hmul : (1 - ε / 4) * (1 - ε / 4) ≤ ‖1 + δ1‖ * ‖1 + δ2‖ :=
        mul_le_mul hA1 hA2 h0 (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hmul hE1pos.le
    have hkey : ε / 2 ≤ (1 - ε / 4) * (1 - ε / 4) * E1 - (1 + ε / 4) := by
      have h1 : 1 - ε / 2 ≤ (1 - ε / 4) * (1 - ε / 4) := by nlinarith only [hε0]
      have h2 : (0:ℝ) ≤ (1 - ε / 4) * (1 - ε / 4) := by nlinarith only [hεle]
      have h3 : (1 - ε / 2) * 4 ≤ (1 - ε / 4) * (1 - ε / 4) * E1 := by
        calc (1 - ε / 2) * 4 ≤ (1 - ε / 4) * (1 - ε / 4) * 4 :=
              mul_le_mul_of_nonneg_right h1 (by norm_num)
          _ ≤ (1 - ε / 4) * (1 - ε / 4) * E1 :=
              mul_le_mul_of_nonneg_left hE1ge4 h2
      nlinarith only [h3, hεle, hε0]
    have h5 : ‖(1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)‖
        ≥ (1 - ε / 4) * (1 - ε / 4) * E1 - (1 + ε / 4) := by
      have h := abs_norm_sub_norm_le ((1 + δ1) * (1 + δ2) * Complex.exp z) (1 + δ3)
      have h6 : ‖(1 + δ1) * (1 + δ2) * Complex.exp z‖ - ‖1 + δ3‖
          ≤ ‖(1 + δ1) * (1 + δ2) * Complex.exp z - (1 + δ3)‖ :=
        le_trans (le_abs_self _) h
      rw [hnorm] at h6
      linarith only [h6, hprod, hA3]
    linarith only [h5, hkey]
  have hfin : ε / 2 ≤ ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) *
      (jInvariantFun w - jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
    rw [← hΔt, hQE]
    by_cases h4 : E1 ≤ 4
    · exact hQs h4
    · exact hQl (le_of_lt (not_le.mp h4))
  exact hfin

end DivisorLowerE

end Work.Asymptotics
