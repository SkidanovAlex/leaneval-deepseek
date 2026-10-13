/-
# The constants and the closing arithmetic of the a-priori bound (design §2.1–2.3)

This module contains the explicit constants of the a-priori estimate and the numerical
inequalities that make the energy bootstrap close:

* `kappa_pos`, `C0_pos`, `alphaCl_pos`, `alpha5_pos` — positivity of the constants;
* `C0_ge` — `2C_N ≤ κ·C₀`, the consequence of `C₀ ≥ 2C_N/κ` that the closure uses;
* `Ccs_lt_lower` — `Ccs < clo·C₀²`, the consequence of `C₀ ≥ 2√(Ccs/clo)` used for `hInit`;
* `alphaCl_key` — `(C₀+C₀²)√α + C₀³α^{3/2} < 1` for `α ≤ alphaCl C₀`;
* `Pbd_mono` — `Pbd α ·` is monotone on `[0,∞)`;
* `Pbd_at` — the exact value `Pbd α (C₀α²) = α⁴(C₀ + (C₀²+C₀³)√α + C₀⁴α^{3/2})`;
* `energy_closing` — the closing inequality `C_N·Pbd α (C₀α²) < κC₀²α⁴` for `α ≤ α₅`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Apriori.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Nonlin

set_option autoImplicit false

/-! ## Positivity and comparison of the constants -/

theorem kappa_pos {cc clo Cup : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup) :
    0 < kappa cc clo Cup := div_pos (mul_pos hcc hclo) hCup

theorem C0_pos {CcN cc clo Cup Ccs : ℝ} (hCcN : 0 < CcN) (hcc : 0 < cc) (hclo : 0 < clo)
    (hCup : 0 < Cup) (hCcs : 0 < Ccs) : 0 < C0 CcN cc clo Cup Ccs :=
  lt_max_iff.mpr (Or.inl (div_pos (by linarith) (kappa_pos hcc hclo hCup)))

/-- The positivity of `C₀` needs only `Ccs > 0` and `clo > 0` (the second branch of the max). -/
theorem C0_pos' {CcN cc clo Cup Ccs : ℝ} (hclo : 0 < clo) (hCcs : 0 < Ccs) :
    0 < C0 CcN cc clo Cup Ccs :=
  lt_of_lt_of_le (by positivity : 0 < 2 * Real.sqrt (Ccs / clo)) (le_max_right _ _)

/-- The comparison `2C_N ≤ κC₀` that the closing inequality uses: it is exactly
`C₀ ≥ 2C_N/κ` multiplied by `κ > 0`. -/
theorem C0_ge {CcN cc clo Cup Ccs : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup) :
    2 * CcN ≤ kappa cc clo Cup * C0 CcN cc clo Cup Ccs := by
  have hκ := kappa_pos hcc hclo hCup
  have hle : 2 * CcN / kappa cc clo Cup ≤ C0 CcN cc clo Cup Ccs := le_max_left _ _
  rw [div_le_iff₀ hκ] at hle
  linarith [hle, mul_comm (C0 CcN cc clo Cup Ccs) (kappa cc clo Cup)]

/-- The comparison `Ccs < clo·C₀²` used for the initial datum: it is exactly
`C₀ ≥ 2√(Ccs/clo)` squared. -/
theorem Ccs_lt_lower {CcN cc clo Cup Ccs : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup)
    (hCcs : 0 < Ccs) : Ccs < clo * C0 CcN cc clo Cup Ccs ^ 2 := by
  have hle : 2 * Real.sqrt (Ccs / clo) ≤ C0 CcN cc clo Cup Ccs := le_max_right _ _
  have hnn : 0 ≤ 2 * Real.sqrt (Ccs / clo) := by positivity
  have hsq : (2 * Real.sqrt (Ccs / clo)) ^ 2 ≤ (C0 CcN cc clo Cup Ccs) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hle
  have hval : (2 * Real.sqrt (Ccs / clo)) ^ 2 = 4 * Ccs / clo := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hCcs.le hclo.le)]
    norm_num
    ring
  rw [hval, div_le_iff₀ hclo] at hsq
  linarith

theorem alphaCl_pos {C₀ : ℝ} (hC₀ : 0 < C₀) : 0 < alphaCl C₀ := by
  refine lt_min_iff.mpr ⟨by norm_num, ?_⟩
  have h : 0 < (C₀ + C₀ ^ 2 + C₀ ^ 3) ^ 2 := by positivity
  positivity

theorem alphaCl_le_one (C₀ : ℝ) : alphaCl C₀ ≤ 1 := min_le_left _ _

theorem alpha5_pos {CcN cc clo Cup Ccs α₂ α₄ : ℝ} (hCcN : 0 < CcN) (hcc : 0 < cc)
    (hclo : 0 < clo) (hCup : 0 < Cup) (hCcs : 0 < Ccs) (hα₂ : 0 < α₂) (hα₄ : 0 < α₄) :
    0 < alpha5 CcN cc clo Cup Ccs α₂ α₄ := by
  refine lt_min_iff.mpr ⟨lt_min_iff.mpr ⟨by norm_num, hα₂⟩, lt_min_iff.mpr ⟨hα₄, ?_⟩⟩
  refine lt_min_iff.mpr ⟨alphaCl_pos (C0_pos hCcN hcc hclo hCup hCcs), ?_⟩
  exact Real.rpow_pos_of_pos (C0_pos hCcN hcc hclo hCup hCcs) _

theorem alpha5_le_alphaCl {CcN cc clo Cup Ccs α₂ α₄ : ℝ} :
    alpha5 CcN cc clo Cup Ccs α₂ α₄ ≤ alphaCl (C0 CcN cc clo Cup Ccs) :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

theorem alpha5_le_alpha4 {CcN cc clo Cup Ccs α₂ α₄ : ℝ} :
    alpha5 CcN cc clo Cup Ccs α₂ α₄ ≤ α₄ :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- `α₅ ≤ C₀^{-4}`: the term of the threshold that makes `C₀α² ≤ α^{7/4}` available. -/
theorem alpha5_le_C0pow {CcN cc clo Cup Ccs α₂ α₄ : ℝ} :
    alpha5 CcN cc clo Cup Ccs α₂ α₄ ≤ (C0 CcN cc clo Cup Ccs) ^ (-(4 : ℝ)) :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

theorem alpha5_le_alpha2 {CcN cc clo Cup Ccs α₂ α₄ : ℝ} :
    alpha5 CcN cc clo Cup Ccs α₂ α₄ ≤ α₂ :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem alpha5_le_quarter {CcN cc clo Cup Ccs α₂ α₄ : ℝ} :
    alpha5 CcN cc clo Cup Ccs α₂ α₄ ≤ 1 / 4 :=
  le_trans (min_le_left _ _) (min_le_left _ _)

/-- **The threshold of the closing inequality**: for `α ≤ alphaCl C₀`,
`(C₀+C₀²)√α + C₀³α^{3/2} < 1`. -/
theorem alphaCl_key {C₀ α : ℝ} (hC₀ : 0 < C₀) (hα : 0 < α) (hαCl : α ≤ alphaCl C₀) :
    (C₀ + C₀ ^ 2) * Real.sqrt α + C₀ ^ 3 * α ^ (3 / 2 : ℝ) < 1 := by
  set D : ℝ := C₀ + C₀ ^ 2 + C₀ ^ 3 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hα1 : α ≤ 1 := le_trans hαCl (alphaCl_le_one C₀)
  have hαinv : α ≤ 1 / (16 * D ^ 2) := le_trans hαCl (min_le_right _ _)
  have hsqrt : Real.sqrt α ≤ 1 / (4 * D) := by
    have h := Real.sqrt_le_sqrt hαinv
    have hval : Real.sqrt (1 / (16 * D ^ 2)) = 1 / (4 * D) := by
      rw [show (1 : ℝ) / (16 * D ^ 2) = (1 / (4 * D)) ^ 2 by field_simp; ring]
      rw [Real.sqrt_sq (by positivity)]
    rwa [hval] at h
  have hsqrtnn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have h32 : α ^ (3 / 2 : ℝ) ≤ Real.sqrt α := by
    have h : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [h]
    nlinarith [hsqrtnn, hα1]
  have h1 : (C₀ + C₀ ^ 2) * Real.sqrt α ≤ 1 / 4 := by
    have h2 : (C₀ + C₀ ^ 2) * Real.sqrt α ≤ (C₀ + C₀ ^ 2) * (1 / (4 * D)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h3 : (C₀ + C₀ ^ 2) * (1 / (4 * D)) = (C₀ + C₀ ^ 2) / (4 * D) := by ring
    rw [h3] at h2
    have h4 : (C₀ + C₀ ^ 2) / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
      nlinarith [hD]
    linarith
  have h2 : C₀ ^ 3 * α ^ (3 / 2 : ℝ) ≤ 1 / 4 := by
    have h2a : C₀ ^ 3 * α ^ (3 / 2 : ℝ) ≤ C₀ ^ 3 * Real.sqrt α :=
      mul_le_mul_of_nonneg_left h32 (by positivity)
    have h2b : C₀ ^ 3 * Real.sqrt α ≤ C₀ ^ 3 * (1 / (4 * D)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h2c : C₀ ^ 3 * (1 / (4 * D)) = C₀ ^ 3 / (4 * D) := by ring
    rw [h2c] at h2b
    have h2d : C₀ ^ 3 / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
      nlinarith [hD]
    linarith
  linarith

/-! ## The polynomial `Pbd` -/

theorem Pbd_mono {α X Y : ℝ} (hα : 0 < α) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    Pbd α X ≤ Pbd α Y := by
  have hY : 0 ≤ Y := le_trans hX hXY
  have h1 : α ^ 2 * X ≤ α ^ 2 * Y := mul_le_mul_of_nonneg_left hXY (sq_nonneg α)
  have hX2 : X ^ 2 ≤ Y ^ 2 := by nlinarith
  have h2 : Real.sqrt α * X ^ 2 ≤ Real.sqrt α * Y ^ 2 :=
    mul_le_mul_of_nonneg_left hX2 (Real.sqrt_nonneg α)
  have hX3 : X ^ 3 ≤ Y ^ 3 := by
    have h := mul_le_mul hX2 hXY hX (by positivity : (0:ℝ) ≤ Y ^ 2)
    nlinarith [h]
  have h3 : α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * Y ^ 3 :=
    mul_le_mul_of_nonneg_left hX3 (Real.rpow_nonneg hα.le _)
  have hX4 : X ^ 4 ≤ Y ^ 4 := by
    have h := mul_le_mul hX2 hX2 (by positivity) (by positivity)
    nlinarith [h]
  have h4 : α ^ (-(5 / 2 : ℝ)) * X ^ 4 ≤ α ^ (-(5 / 2 : ℝ)) * Y ^ 4 :=
    mul_le_mul_of_nonneg_left hX4 (Real.rpow_nonneg hα.le _)
  simp only [Pbd]
  linarith

/-- Helper: `α^{3/2} = (√α)³`. -/
theorem rpow_three_halves {α : ℝ} (hα : 0 < α) :
    α ^ (3 / 2 : ℝ) = (Real.sqrt α) ^ 3 := by
  have h : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h, show (Real.sqrt α) ^ 3 = (Real.sqrt α) ^ 2 * Real.sqrt α by ring,
    Real.sq_sqrt hα.le]

/-- Helper: `α^{5/2} = (√α)⁵`. -/
theorem rpow_five_halves {α : ℝ} (hα : 0 < α) :
    α ^ (5 / 2 : ℝ) = (Real.sqrt α) ^ 5 := by
  have h : α ^ (5 / 2 : ℝ) = α ^ 2 * Real.sqrt α := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_two,
      Real.sqrt_eq_rpow]
  rw [h, show (Real.sqrt α) ^ 5 = ((Real.sqrt α) ^ 2) ^ 2 * Real.sqrt α by ring,
    Real.sq_sqrt hα.le]

/-- The exact value of `Pbd` at `C₀α²`. -/
theorem Pbd_at {α C₀ : ℝ} (hα : 0 < α) :
    Pbd α (C₀ * α ^ 2)
      = α ^ 4 * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ)) := by
  set s : ℝ := Real.sqrt α with hsdef
  have hs2 : s ^ 2 = α := by rw [hsdef]; exact Real.sq_sqrt hα.le
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hα
  have hα2 : α ^ 2 = s ^ 4 := by rw [← hs2]; ring
  have hα4 : α ^ 4 = s ^ 8 := by rw [← hs2]; ring
  have h32 : α ^ (3 / 2 : ℝ) = s ^ 3 := rpow_three_halves hα
  have h52 : α ^ (5 / 2 : ℝ) = s ^ 5 := rpow_five_halves hα
  have hn3 : α ^ (-(3 / 2 : ℝ)) = (s ^ 3)⁻¹ := by rw [Real.rpow_neg hα.le, h32]
  have hn5 : α ^ (-(5 / 2 : ℝ)) = (s ^ 5)⁻¹ := by rw [Real.rpow_neg hα.le, h52]
  have hm : Pbd α (C₀ * α ^ 2) = s ^ 8 * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * s + C₀ ^ 4 * s ^ 3) := by
    rw [Pbd, ← hsdef]
    rw [hn3, hn5, hα2]
    field_simp
    ring
  rw [hm, hα4, h32]

/-- **The smallness of the a-priori ball**: for `α ≤ C₀^{-4}` the a-priori bound `C₀α²` is below
the paper's smallness threshold `α^{7/4}` (this is what lets N4's pairing estimate be applied at
the barrier level). -/
theorem C0_mul_sq_le {CcN cc clo Cup Ccs α : ℝ} (hC₀ : 0 < C0 CcN cc clo Cup Ccs) (hα : 0 < α)
    (hα5 : α ≤ (C0 CcN cc clo Cup Ccs) ^ (-(4 : ℝ))) :
    C0 CcN cc clo Cup Ccs * α ^ 2 ≤ α ^ (7 / 4 : ℝ) := by
  have h1 : α ^ (1 / 4 : ℝ) ≤ (C0 CcN cc clo Cup Ccs) ^ (-(1 : ℝ)) := by
    have h := Real.rpow_le_rpow hα.le hα5 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_mul hC₀.le,
      show -(4 : ℝ) * (1 / 4) = -(1 : ℝ) by norm_num] at h
  have h2 : C0 CcN cc clo Cup Ccs * α ^ (1 / 4 : ℝ) ≤ 1 := by
    calc C0 CcN cc clo Cup Ccs * α ^ (1 / 4 : ℝ)
        ≤ C0 CcN cc clo Cup Ccs * (C0 CcN cc clo Cup Ccs) ^ (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hC₀.le
      _ = 1 := by
          rw [Real.rpow_neg hC₀.le, Real.rpow_one, mul_inv_cancel₀ (ne_of_gt hC₀)]
  have h3 : C0 CcN cc clo Cup Ccs ≤ α ^ (-(1 / 4) : ℝ) := by
    have h4 : 0 < α ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hα _
    rw [Real.rpow_neg hα.le, inv_eq_one_div, le_div_iff₀ h4]
    exact h2
  calc C0 CcN cc clo Cup Ccs * α ^ 2 ≤ α ^ (-(1 / 4) : ℝ) * α ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = α ^ (7 / 4 : ℝ) := by
        rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα]
        norm_num

/-- **The closing inequality**: for `α ≤ α₅`, the dissipation at the barrier level dominates the
nonlinearity, `C_N·Pbd α (C₀α²) < κC₀²α⁴`. -/
theorem energy_closing {CcN cc clo Cup Ccs α₂ α₄ α : ℝ} (hCcN : 0 < CcN) (hcc : 0 < cc)
    (hclo : 0 < clo) (hCup : 0 < Cup) (hCcs : 0 < Ccs) (hα : 0 < α)
    (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) :
    CcN * Pbd α (C0 CcN cc clo Cup Ccs * α ^ 2)
      < kappa cc clo Cup * C0 CcN cc clo Cup Ccs ^ 2 * α ^ 4 := by
  set C₀ : ℝ := C0 CcN cc clo Cup Ccs with hC₀def
  have hC₀ : 0 < C₀ := C0_pos hCcN hcc hclo hCup hCcs
  have hkey : (C₀ + C₀ ^ 2) * Real.sqrt α + C₀ ^ 3 * α ^ (3 / 2 : ℝ) < 1 :=
    alphaCl_key hC₀ hα (le_trans hα5 alpha5_le_alphaCl)
  have hB : (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ) < C₀ := by
    have h := mul_lt_mul_of_pos_left hkey hC₀
    nlinarith [h]
  have hC : CcN * ((C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ)) < CcN * C₀ :=
    mul_lt_mul_of_pos_left hB hCcN
  have hD : 2 * (CcN * C₀) ≤ kappa cc clo Cup * C₀ ^ 2 := by
    have h := C0_ge (CcN := CcN) (Ccs := Ccs) hcc hclo hCup
    rw [← hC₀def] at h
    nlinarith [h, hC₀]
  have hE : CcN * (C₀ + ((C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ)))
      < kappa cc clo Cup * C₀ ^ 2 := by
    nlinarith [hC, hD]
  have hF := mul_lt_mul_of_pos_right hE (pow_pos hα 4)
  rw [Pbd_at hα]
  nlinarith [hF]

end Work.FTS.Apriori
