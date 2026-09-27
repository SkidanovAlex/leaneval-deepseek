import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.GermNumeric
import Submission.Work.EQ.germAlgebra
import Submission.Work.EQ.Gnl_lipschitz
import Submission.Work.EQ.Gnl_analytic
import Submission.Work.EQ.lam_resolvent
import Submission.Work.EQ.sum_Glin_mul

set_option maxHeartbeats 1000000

/-!
# Construction of the stable germ

This file assembles the fixed point argument: the operator `ThetaOf a` is a contraction on the
unit ball of bounded functions on the disc of radius `germR a`, and its fixed point yields the
germ `hOf ρ` solving `GermFE`.
-/

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

variable {a : ℝ}

section Tsum

/-- The geometric sum `∑_j λ^{4j+2} = λ²/(1-λ⁴)`. -/
lemma tsum_lam_pow (ha0 : 0 < a) (ha1 : a < 1) :
    (∑' j : ℕ, (lamC a) ^ (4 * j + 2)) = (((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4) : ℝ) : ℂ) := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h4 : (eqLam a) ^ 4 < 1 := pow_lt_one₀ (le_of_lt h0) h1 (by norm_num)
  have hreal : (∑' j : ℕ, (eqLam a) ^ (4 * j + 2))
      = (eqLam a) ^ 2 / (1 - (eqLam a) ^ 4) := by
    have hnorm : ‖(eqLam a) ^ 4‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h4
    have hgeo : (∑' j : ℕ, ((eqLam a) ^ 4) ^ j) = (1 - (eqLam a) ^ 4)⁻¹ :=
      tsum_geometric_of_norm_lt_one hnorm
    have hsplit : (∑' j : ℕ, (eqLam a) ^ (4 * j + 2))
        = (eqLam a) ^ 2 * ∑' j : ℕ, ((eqLam a) ^ 4) ^ j := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by rw [← pow_mul, ← pow_add]; ring_nf
    rw [hsplit, hgeo]
    ring
  have hcoe : ∀ j : ℕ, (lamC a) ^ (4 * j + 2) = (((eqLam a) ^ (4 * j + 2) : ℝ) : ℂ) := by
    intro j
    simp only [lamC, Complex.ofReal_pow]
  simp_rw [hcoe]
  rw [← Complex.ofReal_tsum, hreal]

lemma summable_lamC_pow (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun j : ℕ => (lamC a) ^ (4 * j + 2)) := by
  have h0 := eqLam_pos ha0 ha1
  have hnorm : ‖(eqLam a) ^ 4‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ (le_of_lt h0) (eqLam_lt_one ha0 ha1) (by norm_num)
  have hgeom : Summable (fun j : ℕ => ((eqLam a) ^ 4) ^ j) :=
    summable_geometric_of_norm_lt_one hnorm
  have h2 : Summable (fun j : ℕ => (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j) := hgeom.mul_left _
  have hcoe : ∀ j : ℕ, (lamC a) ^ (4 * j + 2)
      = (((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j : ℝ) : ℂ) := by
    intro j
    simp only [lamC, Complex.ofReal_pow, Complex.ofReal_mul]
    ring_nf
  have hbound : ∀ j : ℕ, ‖(lamC a) ^ (4 * j + 2)‖ ≤ (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j := by
    intro j
    rw [hcoe j, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := h2.of_norm_bounded hbound
  simpa only [hcoe] using this

lemma norm_lamC_pow (n : ℕ) : ‖(lamC a) ^ n‖ = |eqLam a| ^ n := by
  rw [norm_pow]
  congr 1
  rw [lamC, norm_real, Real.norm_eq_abs]

lemma norm_lamC_pow_four {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ‖(lamC a) ^ (4 * j + 2)‖ = (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j := by
  rw [norm_lamC_pow, abs_of_nonneg (le_of_lt (eqLam_pos ha0 ha1)), ← pow_mul, ← pow_add]
  ring_nf

end Tsum

section Theta

/-- The elementary estimate behind the contraction: summing the shifted residuals against the
geometric weights. -/
lemma norm_tsum_lamC_mul_le (ha0 : 0 < a) (ha1 : a < 1) {g : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v, ‖v‖ ≤ eqLam a * germR a → ‖g v‖ ≤ C) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    ‖(a : ℂ)⁻¹ * ∑' j : ℕ, (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖
      ≤ (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) * C := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  have h4 : ‖(eqLam a) ^ 4‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ h0' h1 (by norm_num)
  rw [norm_mul]
  have hainv : ‖(a : ℂ)⁻¹‖ = 1 / a := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0), inv_eq_one_div]
  rw [hainv]
  have hstep : ∀ j : ℕ, ‖(lamC a) ^ (2 * j + 1) * u‖ ≤ eqLam a * germR a := by
    intro j
    rw [norm_mul, norm_lamC_pow]
    have h1' : |eqLam a| ^ (2 * j + 1) ≤ eqLam a := by
      rw [abs_of_nonneg h0']
      calc (eqLam a) ^ (2 * j + 1) ≤ (eqLam a) ^ 1 :=
            pow_le_pow_of_le_one h0' (le_of_lt h1) (by omega)
        _ = eqLam a := pow_one _
    calc |eqLam a| ^ (2 * j + 1) * ‖u‖ ≤ eqLam a * ‖u‖ :=
          mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
      _ ≤ eqLam a * germR a := mul_le_mul_of_nonneg_left hu h0'
  have hnorm_bound : ∀ j : ℕ,
      ‖(lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖
        ≤ C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j) := by
    intro j
    rw [norm_mul, norm_lamC_pow_four ha0 ha1]
    calc (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j * ‖g ((lamC a) ^ (2 * j + 1) * u)‖
        ≤ (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j * C :=
          mul_le_mul_of_nonneg_left (hbound _ (hstep j)) (by positivity)
      _ = C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j) := by ring
  have hgeom : Summable (fun j : ℕ => C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j)) :=
    ((summable_geometric_of_norm_lt_one h4).mul_left ((eqLam a) ^ 2)).mul_left C
  have hsum : Summable (fun j : ℕ => (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)) :=
    Summable.of_norm_bounded hgeom hnorm_bound
  have hgeosum : (∑' j : ℕ, C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j))
      = C * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_norm_lt_one h4, inv_eq_one_div]
    ring
  have hmain : ‖∑' j : ℕ, (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖
      ≤ C * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) := by
    calc ‖∑' j : ℕ, (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖
        ≤ ∑' j : ℕ, ‖(lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖ :=
          norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' j : ℕ, C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j) :=
          Summable.tsum_le_tsum hnorm_bound hsum.norm hgeom
      _ = C * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) := hgeosum
  calc (1 / a) * ‖∑' j : ℕ, (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)‖
      ≤ (1 / a) * (C * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) * C := by ring

end Theta

section Bounds

/-- `WOf 0 u = 1/(1 + (1+u²)^{1/2})`. -/
lemma WOf_at_zero (u : ℂ) : WOf (fun _ : ℂ => (0 : ℂ)) u = 1 / (1 + sqHalf (u ^ 2)) := by
  have hb : betaOf (fun _ : ℂ => (0 : ℂ)) u = -1 := by simp [betaOf]
  have hs : SOf (fun _ : ℂ => (0 : ℂ)) u = sqHalf (u ^ 2) := by
    simp only [SOf, hb, sqHalf]
    norm_num
  rw [WOf, hb, hs]
  norm_num

/-- The "constant" size of the non-linear residual: `‖Gnl(0)‖ ≤ a κ · 2/3`. -/
lemma norm_Gnl_zero_le (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ}
    (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖GnlOf a (fun _ : ℂ => (0 : ℂ)) u‖ ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) := by
  have h0 := eqLam_pos ha0 ha1
  have hκ : 0 ≤ (eqLam a)⁻¹ - eqLam a := kapC_nonneg ha0 ha1
  have huz : ‖u ^ 2‖ ≤ 1 / 256 := by
    rw [norm_pow]
    have h1 : ‖u‖ ^ 2 ≤ (eqLam a * germR a) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    rw [show (eqLam a * germR a) ^ 2 = (eqLam a)^2 * (germR a)^2 by ring] at h1
    exact le_trans h1 (lam_sq_mul_germR_sq_le ha0 ha1)
  have huz1 : ‖u ^ 2‖ < 1 := by linarith
  have hW : ‖WOf (fun _ : ℂ => (0 : ℂ)) u‖ ≤ 2 / 3 := by
    rw [WOf_at_zero, norm_div, norm_one]
    have hSbound : ‖sqHalf (u ^ 2) - 1‖ ≤ 1 / 256 :=
      le_trans (norm_sqHalf_sub_one_le huz1) huz
    have hden : (3:ℝ) / 2 ≤ ‖1 + sqHalf (u ^ 2)‖ := by
      have h := norm_sub_norm_le (2 : ℂ) (1 - sqHalf (u ^ 2))
      have h2 : ‖(2:ℂ) - (1 - sqHalf (u ^ 2))‖ = ‖1 + sqHalf (u ^ 2)‖ := by
        congr 1
        ring
      have h3 : ‖(1:ℂ) - sqHalf (u ^ 2)‖ = ‖sqHalf (u ^ 2) - 1‖ := by
        rw [← norm_neg]
        congr 1
        ring
      have h4 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h4, h3, h2] at h
      linarith
    have hpos : (0:ℝ) < ‖1 + sqHalf (u ^ 2)‖ := by linarith
    rw [div_le_iff₀ hpos]
    linarith
  have hmain : GnlOf a (fun _ : ℂ => (0 : ℂ)) u
      = -((a : ℂ) * kapC a * WOf (fun _ : ℂ => (0 : ℂ)) u) := by
    simp only [GnlOf, A1Of, A2Of, A3Of, betaOf]
    ring
  rw [hmain, norm_neg]
  simp only [norm_mul]
  have hkappa : ‖kapC a‖ = (eqLam a)⁻¹ - eqLam a := by
    simp only [kapC]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  rw [hkappa, hanorm]
  calc a * ((eqLam a)⁻¹ - eqLam a) * ‖WOf (fun _ : ℂ => (0 : ℂ)) u‖
      ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) := rfl

section ThetaEstimates

/-- `(1/a) * λ²/(1-λ⁴) = λ²/((1-λ)²(1+λ²))`. -/
lemma one_div_a_mul_lamSum {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
      = (eqLam a) ^ 2 / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) := by
  have h1l := one_sub_eqLam_gs ha0
  have h4l : 1 - (eqLam a) ^ 4 = a * (1 + eqLam a) ^ 2 * (1 + (eqLam a) ^ 2) := by
    rw [show (1:ℝ) - (eqLam a) ^ 4
        = (1 - eqLam a) * (1 + eqLam a) * (1 + (eqLam a) ^ 2) by ring, h1l]
    ring
  have hsq : (1 - eqLam a) ^ 2 = a ^ 2 * (1 + eqLam a) ^ 2 := by
    rw [h1l]; ring
  rw [h4l, hsq]
  field_simp

/-- `a κ = (1-λ)²/λ`. -/
lemma a_mul_kapC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    a * ((eqLam a)⁻¹ - eqLam a) = (1 - eqLam a) ^ 2 / eqLam a := by
  have h0 := eqLam_pos ha0 ha1
  have h1 : eqLam a ≠ 0 := ne_of_gt h0
  field_simp
  rw [show (1:ℝ) - eqLam a ^ 2 = (1 - eqLam a) * (1 + eqLam a) by ring,
    show (1:ℝ) - eqLam a = a * (1 + eqLam a) from one_sub_eqLam_gs ha0]
  ring

lemma div_lamSum_mul_kapC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) * (a * ((eqLam a)⁻¹ - eqLam a))
      = eqLam a / (1 + (eqLam a) ^ 2) := by
  have h0 := eqLam_pos ha0 ha1
  have h1 : eqLam a ≠ 0 := ne_of_gt h0
  have h2 : 1 + (eqLam a) ^ 2 ≠ 0 := by positivity
  have h3 : 1 - eqLam a ≠ 0 := by
    have := eqLam_lt_one ha0 ha1
    linarith
  rw [one_div_a_mul_lamSum ha0 ha1, a_mul_kapC ha0 ha1]
  field_simp

lemma div_lamSum_mul_const' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
        * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)
      = (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
          / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) := by
  rw [one_div_a_mul_lamSum ha0 ha1]
  ring

lemma div_lamSum_mul_const {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (M : ℝ) :
    (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
        * (M * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a))
      = M * ((eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
          / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2))) := by
  rw [show (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
        * (M * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a))
      = M * ((1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
        * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)) by ring,
    div_lamSum_mul_const' ha0 ha1]

lemma two_thirds_mul_lam_div_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (2 / 3 : ℝ) * (eqLam a / (1 + (eqLam a) ^ 2)) ≤ 1 / 3 := by
  have hh : (0:ℝ) < 3 * (1 + (eqLam a) ^ 2) := by positivity
  have heq : (2 / 3 : ℝ) * (eqLam a / (1 + (eqLam a) ^ 2))
      = (2 * eqLam a) / (3 * (1 + (eqLam a) ^ 2)) := by
    field_simp
  rw [heq, div_le_iff₀ hh]
  nlinarith [sq_nonneg (eqLam a - 1)]

/-- Summability of the shifted residual series, from a uniform bound. -/
lemma summable_lamC_mul_of_bound (ha0 : 0 < a) (ha1 : a < 1) {g : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v, ‖v‖ ≤ eqLam a * germR a → ‖g v‖ ≤ C) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    Summable (fun j : ℕ => (lamC a) ^ (4 * j + 2) * g ((lamC a) ^ (2 * j + 1) * u)) := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  have h4 : ‖(eqLam a) ^ 4‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ h0' h1 (by norm_num)
  have hgeom : Summable (fun j : ℕ => C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j)) :=
    ((summable_geometric_of_norm_lt_one h4).mul_left ((eqLam a) ^ 2)).mul_left C
  refine Summable.of_norm_bounded hgeom (fun j => ?_)
  have hstep : ‖(lamC a) ^ (2 * j + 1) * u‖ ≤ eqLam a * germR a := by
    rw [norm_mul, norm_lamC_pow]
    have h1' : |eqLam a| ^ (2 * j + 1) ≤ eqLam a := by
      rw [abs_of_nonneg h0']
      calc (eqLam a) ^ (2 * j + 1) ≤ (eqLam a) ^ 1 :=
            pow_le_pow_of_le_one h0' (le_of_lt h1) (by omega)
        _ = eqLam a := pow_one _
    calc |eqLam a| ^ (2 * j + 1) * ‖u‖ ≤ eqLam a * ‖u‖ :=
          mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
      _ ≤ eqLam a * germR a := mul_le_mul_of_nonneg_left hu h0'
  rw [norm_mul, norm_lamC_pow_four ha0 ha1]
  calc (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j * ‖g ((lamC a) ^ (2 * j + 1) * u)‖
      ≤ (eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j * C :=
        mul_le_mul_of_nonneg_left (hbound _ hstep) (by positivity)
    _ = C * ((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j) := by ring

/-- A uniform bound on `Gnl(ρ)` on the disc of radius `λ r`, for `‖ρ‖ ≤ 1` there. -/
lemma norm_Gnl_le (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) {v : ℂ}
    (hv : ‖v‖ ≤ eqLam a * germR a) :
    ‖GnlOf a ρ v‖ ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
      + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a := by
  have hlip := Gnl_lipschitz (a := a) ha0 ha1 (ρ₁ := ρ) (ρ₂ := fun _ : ℂ => (0 : ℂ))
    hρ (fun z _ => by simp) (M := 1) (hM := fun z hz => by simpa using hρ z hz) hv
  have hzero := norm_Gnl_zero_le ha0 ha1 hv
  calc ‖GnlOf a ρ v‖
      = ‖(GnlOf a ρ v - GnlOf a (fun _ : ℂ => (0 : ℂ)) v) + GnlOf a (fun _ : ℂ => (0 : ℂ)) v‖ := by
        ring_nf
    _ ≤ ‖GnlOf a ρ v - GnlOf a (fun _ : ℂ => (0 : ℂ)) v‖
          + ‖GnlOf a (fun _ : ℂ => (0 : ℂ)) v‖ := norm_add_le _ _
    _ ≤ (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a + a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) :=
        add_le_add (by simpa using hlip) hzero
    _ = a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
          + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a := by ring

/-- Bound on `Θ` in terms of a uniform bound on `Gnl(ρ)`. -/
lemma norm_Theta_le_of_bound (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v, ‖v‖ ≤ eqLam a * germR a → ‖GnlOf a ρ v‖ ≤ C) {u : ℂ}
    (hu : ‖u‖ ≤ germR a) :
    ‖ThetaOf a ρ u‖ ≤ (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4)) * C := by
  simp only [ThetaOf]
  exact norm_tsum_lamC_mul_le ha0 ha1 hC hbound hu

/-- The operator `Θ` sends the unit ball of the disc of radius `r` to itself. -/
lemma norm_Theta_le_one (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    ‖ThetaOf a ρ u‖ ≤ 1 := by
  have h0 := eqLam_pos ha0 ha1
  have hκ : 0 ≤ (eqLam a)⁻¹ - eqLam a := kapC_nonneg ha0 ha1
  have hK0 := gLipK_nonneg ha0 ha1
  have hC : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a :=
    add_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha0) hκ) (by norm_num))
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK0)
  have h1' := norm_Theta_le_of_bound ha0 ha1 hC (fun v hv => norm_Gnl_le ha0 ha1 hρ hv) hu
  have hexp : (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
      * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)
      = (2 / 3) * (eqLam a / (1 + (eqLam a) ^ 2))
        + (eqLam a) ^ 4 * (germR a) ^ 2 * gLipK a
          / ((1 - eqLam a) ^ 2 * (1 + (eqLam a) ^ 2)) := by
    rw [mul_add,
      show (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
          * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3))
        = ((1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
            * (a * ((eqLam a)⁻¹ - eqLam a))) * (2 / 3) by ring,
      div_lamSum_mul_kapC ha0 ha1, div_lamSum_mul_const' ha0 ha1]
    ring
  rw [hexp] at h1'
  have hnum1 := two_thirds_mul_lam_div_le ha0 ha1
  have hnum2 := lam_four_mul_germR_sq_mul_gLipK_div_le ha0 ha1
  linarith

/-- `Θ` is `1/2`-Lipschitz for the sup-norm on the disc of radius `r`. -/
lemma norm_Theta_sub_le (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℂ → ℂ}
    (h₁ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z‖ ≤ 1) (h₂ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₂ z‖ ≤ 1)
    {M : ℝ} (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M) {u : ℂ}
    (hu : ‖u‖ ≤ germR a) :
    ‖ThetaOf a ρ₁ u - ThetaOf a ρ₂ u‖ ≤ (1 / 2) * M := by
  have h0 := eqLam_pos ha0 ha1
  have hK0 := gLipK_nonneg ha0 ha1
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (by rw [norm_zero]; exact le_of_lt (germR_pos ha0 ha1)))
  have hC : 0 ≤ M * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a) :=
    mul_nonneg hM0 (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hK0)
  have hC1 : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
      + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a :=
    add_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha0) (kapC_nonneg ha0 ha1)) (by norm_num))
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK0)
  have hsum1 := summable_lamC_mul_of_bound (a := a) ha0 ha1 hC1
    (fun v hv => norm_Gnl_le ha0 ha1 h₁ hv) hu
  have hsum2 := summable_lamC_mul_of_bound (a := a) ha0 ha1 hC1
    (fun v hv => norm_Gnl_le ha0 ha1 h₂ hv) hu
  have hsub : ThetaOf a ρ₁ u - ThetaOf a ρ₂ u
      = (a : ℂ)⁻¹ * ∑' j : ℕ, (lamC a) ^ (4 * j + 2)
          * (GnlOf a ρ₁ ((lamC a) ^ (2 * j + 1) * u)
              - GnlOf a ρ₂ ((lamC a) ^ (2 * j + 1) * u)) := by
    simp only [ThetaOf]
    rw [← mul_sub, ← Summable.tsum_sub hsum1 hsum2]
    congr 1
    exact tsum_congr (fun j => by ring)
  rw [hsub]
  have hmain := norm_tsum_lamC_mul_le (a := a) ha0 ha1 hC
    (fun v hv => Gnl_lipschitz (a := a) ha0 ha1 h₁ h₂ hM hv) hu
  rw [div_lamSum_mul_const ha0 ha1 M] at hmain
  have hcontr := lam_four_mul_germR_sq_mul_gLipK_div_le ha0 ha1
  nlinarith [hmain, hcontr, hM0]

/-- The value of the constant part: `Θ(0)` is bounded by `1/3`. -/
lemma norm_Theta_zero_le (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    ‖ThetaOf a (fun _ : ℂ => (0 : ℂ)) u‖ ≤ 1 / 3 := by
  have hκ : 0 ≤ (eqLam a)⁻¹ - eqLam a := kapC_nonneg ha0 ha1
  have hC : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) :=
    mul_nonneg (mul_nonneg (le_of_lt ha0) hκ) (by norm_num)
  have h1' := norm_Theta_le_of_bound ha0 ha1 hC
    (fun v hv => norm_Gnl_zero_le ha0 ha1 hv) hu
  have hexp : (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
      * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3))
      = (2 / 3) * (eqLam a / (1 + (eqLam a) ^ 2)) := by
    rw [show (1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
          * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3))
        = ((1 / a) * ((eqLam a) ^ 2 / (1 - (eqLam a) ^ 4))
            * (a * ((eqLam a)⁻¹ - eqLam a))) * (2 / 3) by ring,
      div_lamSum_mul_kapC ha0 ha1]
    ring
  rw [hexp] at h1'
  exact le_trans h1' (two_thirds_mul_lam_div_le ha0 ha1)

/-- The affine maps `w ↦ λ^{2j+1} w` map the disc of radius `r` into the disc of radius `λr`. -/
lemma mapsTo_lamC_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    MapsTo (fun w : ℂ => (lamC a) ^ (2 * j + 1) * w) (ball 0 (germR a))
      (ball 0 (eqLam a * germR a)) := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  intro w hw
  rw [mem_ball_zero_iff] at hw ⊢
  rw [norm_mul, norm_lamC_pow]
  have h1' : |eqLam a| ^ (2 * j + 1) ≤ eqLam a := by
    rw [abs_of_nonneg h0']
    calc (eqLam a) ^ (2 * j + 1) ≤ (eqLam a) ^ 1 :=
          pow_le_pow_of_le_one h0' (le_of_lt h1) (by omega)
      _ = eqLam a := pow_one _
  calc |eqLam a| ^ (2 * j + 1) * ‖w‖ ≤ eqLam a * ‖w‖ :=
        mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
    _ < eqLam a * germR a := mul_lt_mul_of_pos_left hw h0

/-- The `j`-th summand of `Θ`. -/
noncomputable def thetaTerm (a : ℝ) (ρ : ℂ → ℂ) (j : ℕ) (u : ℂ) : ℂ :=
  (a : ℂ)⁻¹ * ((lamC a) ^ (4 * j + 2) * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u))

/-- A summable majorant for the summands of `Θ`. -/
noncomputable def thetaMaj (a : ℝ) (j : ℕ) : ℝ :=
  ‖(a : ℂ)⁻¹‖ * (((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j)
    * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
        + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a))

lemma ThetaOf_eq_tsum (a : ℝ) (ρ : ℂ → ℂ) :
    ThetaOf a ρ = fun u => ∑' j : ℕ, thetaTerm a ρ j u := by
  funext u
  simp only [ThetaOf, thetaTerm]
  rw [tsum_mul_left]

lemma summable_thetaMaj (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (thetaMaj a) := by
  have h0 := eqLam_pos ha0 ha1
  have h1 := eqLam_lt_one ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  have h4 : ‖(eqLam a) ^ 4‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ h0' h1 (by norm_num)
  change Summable (fun j : ℕ => ‖(a : ℂ)⁻¹‖ * (((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j)
    * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
        + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)))
  have h := (((summable_geometric_of_norm_lt_one h4).mul_left ((eqLam a) ^ 2)).mul_left
        (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
          + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)).mul_left ‖(a : ℂ)⁻¹‖
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

lemma norm_thetaTerm_le (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hb : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) {j : ℕ} {u : ℂ} (hu : ‖u‖ < germR a) :
    ‖thetaTerm a ρ j u‖ ≤ thetaMaj a j := by
  have hstep : ‖(lamC a) ^ (2 * j + 1) * u‖ ≤ eqLam a * germR a := by
    have h := mapsTo_lamC_pow (a := a) ha0 ha1 j (mem_ball_zero_iff.mpr hu)
    rw [mem_ball_zero_iff] at h
    exact le_of_lt h
  show ‖(a : ℂ)⁻¹ * ((lamC a) ^ (4 * j + 2) * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u))‖
    ≤ ‖(a : ℂ)⁻¹‖ * (((eqLam a) ^ 2 * ((eqLam a) ^ 4) ^ j)
        * (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
            + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a))
  rw [norm_mul, norm_mul, norm_lamC_pow_four ha0 ha1]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (norm_Gnl_le ha0 ha1 hb hstep) (by positivity)

lemma differentiable_thetaTerm (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : AnalyticOnNhd ℂ ρ (ball 0 (germR a)))
    (hb : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) (j : ℕ) :
    DifferentiableOn ℂ (thetaTerm a ρ j) (ball 0 (germR a)) := by
  have hG := Gnl_analytic (a := a) ha0 ha1 hρ hb
  have hlin : DifferentiableOn ℂ (fun w : ℂ => (lamC a) ^ (2 * j + 1) * w)
      (ball 0 (germR a)) := by fun_prop
  have hcomp := hG.differentiableOn.comp hlin (mapsTo_lamC_pow ha0 ha1 j)
  have h2 : DifferentiableOn ℂ (fun u : ℂ => (lamC a) ^ (4 * j + 2)
      * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u)) (ball 0 (germR a)) :=
    hcomp.const_mul _
  have h3 : DifferentiableOn ℂ (fun u : ℂ => (a : ℂ)⁻¹ * ((lamC a) ^ (4 * j + 2)
      * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u))) (ball 0 (germR a)) :=
    h2.const_mul _
  show DifferentiableOn ℂ (fun u : ℂ => (a : ℂ)⁻¹ * ((lamC a) ^ (4 * j + 2)
    * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u))) (ball 0 (germR a))
  exact h3

/-- Analyticity of `Θ(ρ)` for analytic `ρ` bounded by `1`. -/
lemma Theta_analytic (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : AnalyticOnNhd ℂ ρ (ball 0 (germR a)))
    (hb : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) :
    AnalyticOnNhd ℂ (ThetaOf a ρ) (ball 0 (germR a)) := by
  rw [ThetaOf_eq_tsum]
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (summable_thetaMaj (a := a) ha0 ha1)
    (fun j => differentiable_thetaTerm (a := a) ha0 ha1 hρ hb j) isOpen_ball
    (fun j w hw => norm_thetaTerm_le (a := a) ha0 ha1 hb (mem_ball_zero_iff.mp hw))).analyticOnNhd
    isOpen_ball

section FixedPoint

/-- The iterates of `Θ` starting from `0`. -/
noncomputable def rhoIter (a : ℝ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | (n + 1) => ThetaOf a (rhoIter a n)

@[simp] lemma rhoIter_zero (a : ℝ) : rhoIter a 0 = fun _ => (0 : ℂ) := rfl
@[simp] lemma rhoIter_succ (a : ℝ) (n : ℕ) : rhoIter a (n + 1) = ThetaOf a (rhoIter a n) := rfl

lemma rhoIter_bound (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ∀ z : ℂ, ‖z‖ ≤ germR a → ‖rhoIter a n z‖ ≤ 1 := by
  induction n with
  | zero => intro z hz; simp
  | succ n ih =>
      intro z hz
      rw [rhoIter_succ]
      exact norm_Theta_le_one ha0 ha1 (fun w hw => ih w hw) hz

lemma rhoIter_analytic (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    AnalyticOnNhd ℂ (rhoIter a n) (ball 0 (germR a)) := by
  induction n with
  | zero => rw [rhoIter_zero]; exact analyticOnNhd_const
  | succ n ih =>
      rw [rhoIter_succ]
      exact Theta_analytic ha0 ha1 ih (rhoIter_bound ha0 ha1 n)

lemma rhoIter_diff_bound (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ∀ z : ℂ, ‖z‖ ≤ germR a → ‖rhoIter a (n + 1) z - rhoIter a n z‖ ≤ (1 / 3) * (1 / 2) ^ n := by
  induction n with
  | zero =>
      intro z hz
      have h := norm_Theta_zero_le ha0 ha1 hz
      simpa only [rhoIter_succ, rhoIter_zero, Pi.zero_apply, sub_zero, pow_zero,
        mul_one] using h
  | succ n ih =>
      intro z hz
      have h := norm_Theta_sub_le (a := a) ha0 ha1 (rhoIter_bound ha0 ha1 (n + 1))
        (rhoIter_bound ha0 ha1 n) (M := (1 / 3) * (1 / 2) ^ n) (fun w hw => ih w hw) hz
      rw [show rhoIter a (n + 1 + 1) z - rhoIter a (n + 1) z
          = ThetaOf a (rhoIter a (n + 1)) z - ThetaOf a (rhoIter a n) z by
        rw [rhoIter_succ, rhoIter_succ]]
      calc ‖ThetaOf a (rhoIter a (n + 1)) z - ThetaOf a (rhoIter a n) z‖
          ≤ (1 / 2) * ((1 / 3) * (1 / 2) ^ n) := h
        _ = (1 / 3) * (1 / 2) ^ (n + 1) := by ring

/-- The limit of the iterates, as the telescoping series of the successive differences. -/
noncomputable def rhoLim (a : ℝ) (u : ℂ) : ℂ :=
  ∑' n : ℕ, (rhoIter a (n + 1) u - rhoIter a n u)

lemma summable_rhoDiff (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ ≤ germR a) :
    Summable (fun n : ℕ => rhoIter a (n + 1) z - rhoIter a n z) := by
  refine Summable.of_norm_bounded ?_ (fun n => rhoIter_diff_bound ha0 ha1 n z hz)
  have hgeo : Summable (fun n : ℕ => ((1:ℝ) / 2) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hgeo.mul_left ((1:ℝ) / 3)

lemma tsum_three_halves : (∑' n : ℕ, ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ n) = 2 / 3 := by
  have hgeo : (∑' n : ℕ, (((1:ℝ) / 2)) ^ n) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ) / 2)‖ < 1)]
    norm_num
  rw [tsum_mul_left, hgeo]
  norm_num

lemma rhoLim_bound (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ ≤ germR a) :
    ‖rhoLim a z‖ ≤ 2 / 3 := by
  have hsum := summable_rhoDiff ha0 ha1 hz
  have hgeo : Summable (fun n : ℕ => ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ)/2)‖ < 1)).mul_left ((1:ℝ)/3)
  have h1 : ‖rhoLim a z‖ ≤ ∑' n : ℕ, ‖rhoIter a (n + 1) z - rhoIter a n z‖ :=
    norm_tsum_le_tsum_norm hsum.norm
  have h2 : (∑' n : ℕ, ‖rhoIter a (n + 1) z - rhoIter a n z‖)
      ≤ ∑' n : ℕ, ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ n :=
    Summable.tsum_le_tsum (fun n => rhoIter_diff_bound ha0 ha1 n z hz) hsum.norm hgeo
  have h3 := tsum_three_halves
  linarith

lemma rhoLim_analytic (ha0 : 0 < a) (ha1 : a < 1) :
    AnalyticOnNhd ℂ (rhoLim a) (ball 0 (germR a)) := by
  have hgeo : Summable (fun n : ℕ => ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ)/2)‖ < 1)).mul_left ((1:ℝ)/3)
  have := Complex.differentiableOn_tsum_of_summable_norm hgeo
    (fun n => (rhoIter_analytic ha0 ha1 (n + 1)).differentiableOn.sub
      (rhoIter_analytic ha0 ha1 n).differentiableOn) isOpen_ball
    (fun n w hw => rhoIter_diff_bound ha0 ha1 n w (le_of_lt (mem_ball_zero_iff.mp hw)))
  exact this.analyticOnNhd isOpen_ball

lemma rhoIter_tsum_tail (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ ≤ germR a) (n : ℕ) :
    rhoLim a z - rhoIter a n z
      = ∑' k : ℕ, (rhoIter a (k + n + 1) z - rhoIter a (k + n) z) := by
  have hsum := summable_rhoDiff ha0 ha1 hz
  have htel : ∀ N : ℕ, (∑ k ∈ Finset.range N, (rhoIter a (k + 1) z - rhoIter a k z))
      = rhoIter a N z := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have h := hsum.sum_add_tsum_nat_add n
  rw [htel n] at h
  have h3' : (∑' i : ℕ, (rhoIter a (i + 1) z - rhoIter a i z))
      = rhoIter a n z + ∑' i : ℕ, (rhoIter a (i + n + 1) z - rhoIter a (i + n) z) := h.symm
  show rhoLim a z - rhoIter a n z = _
  rw [show rhoLim a z = ∑' i : ℕ, (rhoIter a (i + 1) z - rhoIter a i z) from rfl]
  rw [h3']
  ring

lemma rhoLim_tail (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ ≤ germR a) (n : ℕ) :
    ‖rhoIter a n z - rhoLim a z‖ ≤ (2 / 3) * (1 / 2) ^ n := by
  have hsum := summable_rhoDiff ha0 ha1 hz
  have hshift : Summable (fun k : ℕ => rhoIter a (k + n + 1) z - rhoIter a (k + n) z) :=
    (summable_nat_add_iff n).mpr hsum
  have hgeo : Summable (fun k : ℕ => ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ (k + n)) := by
    have h : Summable (fun k : ℕ => ((1:ℝ) / 2) ^ (k + n)) :=
      (summable_nat_add_iff n).mpr
        (summable_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ)/2)‖ < 1))
    exact h.mul_left _
  have h1 : ‖∑' k : ℕ, (rhoIter a (k + n + 1) z - rhoIter a (k + n) z)‖
      ≤ ∑' k : ℕ, ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ (k + n) :=
    le_trans (norm_tsum_le_tsum_norm hshift.norm)
      (Summable.tsum_le_tsum (fun k => rhoIter_diff_bound ha0 ha1 (k + n) z hz) hshift.norm hgeo)
  have h2 : (∑' k : ℕ, ((1:ℝ) / 3) * ((1:ℝ) / 2) ^ (k + n))
      = (2 / 3) * (1 / 2) ^ n := by
    have hsplit : (fun k : ℕ => ((1:ℝ)/3) * ((1:ℝ)/2)^(k+n))
        = fun k : ℕ => (((1:ℝ)/2)^n * ((1:ℝ)/3)) * ((1:ℝ)/2)^k := by
      funext k
      rw [pow_add]
      ring
    rw [hsplit, tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by norm_num : ‖((1:ℝ)/2)‖ < 1)]
    ring
  have h3 := rhoIter_tsum_tail ha0 ha1 hz n
  have hgoal : rhoIter a n z - rhoLim a z
      = -(∑' k : ℕ, (rhoIter a (k + n + 1) z - rhoIter a (k + n) z)) := by
    rw [← h3]; ring
  rw [hgoal, norm_neg]
  rw [h2] at h1
  exact h1

lemma rhoLim_fixed (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ ≤ germR a) :
    ThetaOf a (rhoLim a) z = rhoLim a z := by
  have hbL : ∀ w : ℂ, ‖w‖ ≤ germR a → ‖rhoLim a w‖ ≤ 1 :=
    fun w hw => le_trans (rhoLim_bound ha0 ha1 hw) (by norm_num)
  have hmain : ∀ n : ℕ, ‖ThetaOf a (rhoLim a) z - rhoLim a z‖
      ≤ (1 / 2) * ((2 / 3) * (1 / 2) ^ n) + (2 / 3) * (1 / 2) ^ (n + 1) := by
    intro n
    have h1 := norm_Theta_sub_le (a := a) ha0 ha1 (ρ₁ := rhoLim a) (ρ₂ := rhoIter a n)
      hbL (rhoIter_bound ha0 ha1 n) (M := (2 / 3) * (1 / 2) ^ n)
      (fun w hw => by
        rw [show rhoLim a w - rhoIter a n w = -(rhoIter a n w - rhoLim a w) by ring, norm_neg]
        exact rhoLim_tail ha0 ha1 hw n) hz
    have h2 : ‖ThetaOf a (rhoIter a n) z - rhoLim a z‖ ≤ (2 / 3) * (1 / 2) ^ (n + 1) := by
      have hn := rhoLim_tail (a := a) ha0 ha1 hz (n + 1)
      simpa only [rhoIter_succ] using hn
    calc ‖ThetaOf a (rhoLim a) z - rhoLim a z‖
        ≤ ‖ThetaOf a (rhoLim a) z - ThetaOf a (rhoIter a n) z‖
            + ‖ThetaOf a (rhoIter a n) z - rhoLim a z‖ := by
          have h := norm_add_le (ThetaOf a (rhoLim a) z - ThetaOf a (rhoIter a n) z)
            (ThetaOf a (rhoIter a n) z - rhoLim a z)
          rwa [sub_add_sub_cancel] at h
      _ ≤ (1 / 2) * ((2 / 3) * (1 / 2) ^ n) + (2 / 3) * (1 / 2) ^ (n + 1) :=
          add_le_add h1 h2
  have htend : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((2 / 3) * ((1:ℝ) / 2) ^ n)
      + (2 / 3) * ((1:ℝ) / 2) ^ (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1:ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (1:ℝ)/2 < 1 by norm_num)
    have h2 := (h1.const_mul ((1:ℝ) / 2 * (2 / 3))).add (h1.const_mul ((2 / 3) * (1 / 2)))
    simpa [pow_succ, mul_add, mul_comm, mul_left_comm, mul_assoc] using h2
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds htend (Eventually.of_forall hmain)
  have hzero : ‖ThetaOf a (rhoLim a) z - rhoLim a z‖ = 0 :=
    le_antisymm (by simpa using hlim) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

lemma rhoLim_Gnl_sum (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    (∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u))
      = (a : ℂ) * rhoLim a u := by
  have h := rhoLim_fixed (a := a) ha0 ha1 hu
  rw [ThetaOf] at h
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha0
  have h' : (a : ℂ) * ((a : ℂ)⁻¹ * (∑' j : ℕ, (lamC a) ^ (4 * j + 2)
      * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u))) = (a : ℂ) * rhoLim a u := by
    rw [h]
  have h'' : (a : ℂ) * ((a : ℂ)⁻¹ * (∑' j : ℕ, (lamC a) ^ (4 * j + 2)
      * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u)))
      = ∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u) := by
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [h''] at h'
  exact h'

lemma summable_lamC_mul_Gnl (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    Summable (fun j : ℕ =>
      (lamC a) ^ (4 * j + 2) * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u)) := by
  have hK0 := gLipK_nonneg ha0 ha1
  have hC : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
      + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a :=
    add_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha0) (kapC_nonneg ha0 ha1)) (by norm_num))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hK0)
  exact summable_lamC_mul_of_bound (a := a) ha0 ha1 hC
    (fun v hv => norm_Gnl_le ha0 ha1
      (fun z hz => le_trans (rhoLim_bound ha0 ha1 hz) (by norm_num)) hv) hu

lemma norm_lamC' (ha0 : 0 < a) (ha1 : a < 1) : ‖lamC a‖ = eqLam a := by
  rw [lamC, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (eqLam_pos ha0 ha1))]

lemma norm_lamC_sq (ha0 : 0 < a) (ha1 : a < 1) : ‖(lamC a) ^ 2‖ = (eqLam a) ^ 2 := by
  rw [norm_pow, norm_lamC' ha0 ha1]

lemma norm_inv_lamC_sq (ha0 : 0 < a) (ha1 : a < 1) :
    ‖(((lamC a) ^ 2)⁻¹)‖ = (((eqLam a) ^ 2)⁻¹) := by
  rw [norm_inv, norm_lamC_sq ha0 ha1]

lemma norm_Glin_le (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) {v : ℂ} (hv : ‖v‖ ≤ eqLam a * germR a) :
    ‖GlinOf a ρ v‖ ≤ a * ((eqLam a) ^ 2 + (((eqLam a) ^ 2)⁻¹)) := by
  have h0 := eqLam_pos ha0 ha1
  have h0' : 0 ≤ eqLam a := le_of_lt h0
  have h2a : ‖(lamC a) ^ 2 * ρ (lamC a * v)‖ ≤ (eqLam a) ^ 2 := by
    rw [norm_mul, norm_lamC_sq ha0 ha1]
    have hb : ‖lamC a * v‖ ≤ germR a := by
      rw [norm_mul, norm_lamC' ha0 ha1]
      calc eqLam a * ‖v‖ ≤ eqLam a * (eqLam a * germR a) :=
            mul_le_mul_of_nonneg_left hv h0'
        _ ≤ germR a := by
            have h1 := eqLam_lt_one ha0 ha1
            have hr : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
            rw [show eqLam a * (eqLam a * germR a) = (eqLam a) ^ 2 * germR a by ring]
            calc (eqLam a) ^ 2 * germR a ≤ 1 * germR a :=
                  mul_le_mul_of_nonneg_right (by nlinarith) hr
              _ = germR a := one_mul _
    calc (eqLam a) ^ 2 * ‖ρ (lamC a * v)‖ ≤ (eqLam a) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hρ _ hb) (by positivity)
      _ = (eqLam a) ^ 2 := by ring
  have h2b : ‖(((lamC a) ^ 2)⁻¹) * ρ (v / lamC a)‖ ≤ ((eqLam a) ^ 2)⁻¹ := by
    rw [norm_mul, norm_inv_lamC_sq ha0 ha1]
    have hb : ‖v / lamC a‖ ≤ germR a := by
      rw [norm_div, norm_lamC' ha0 ha1, div_le_iff₀ h0]
      linarith
    calc (((eqLam a) ^ 2)⁻¹) * ‖ρ (v / lamC a)‖ ≤ ((eqLam a) ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hρ _ hb) (by positivity)
      _ = ((eqLam a) ^ 2)⁻¹ := by ring
  show ‖(a : ℂ) * ((lamC a) ^ 2 * ρ (lamC a * v)
      - (((lamC a) ^ 2)⁻¹) * ρ (v / lamC a))‖ ≤ a * ((eqLam a) ^ 2 + ((eqLam a) ^ 2)⁻¹)
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt ha0)
  exact le_trans (norm_sub_le _ _) (by linarith)

section RealOn

lemma im_mul_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z * w).im = 0 := by
  simp [hz, hw]

lemma im_add_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z + w).im = 0 := by
  simp [hz, hw]

lemma im_sub_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z - w).im = 0 := by
  simp [hz, hw]

lemma im_neg_zero {z : ℂ} (hz : z.im = 0) : (-z).im = 0 := by simp [hz]

lemma im_pow_zero {z : ℂ} (hz : z.im = 0) (n : ℕ) : (z ^ n).im = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact im_mul_zero ih hz

lemma im_inv_zero {z : ℂ} (hz : z.im = 0) : (z⁻¹).im = 0 := by simp [hz]

lemma im_div_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z / w).im = 0 := by
  rw [div_eq_mul_inv]
  exact im_mul_zero hz (im_inv_zero hw)

lemma im_cpow_half {w : ℂ} (hw : w.im = 0) (hpos : 0 < w.re) : (w ^ (1/2:ℂ)).im = 0 := by
  set y := w ^ (1 / 2 : ℂ) with hy
  have hy2 : y ^ 2 = w := by
    have h := sqHalf_sq (w - 1)
    have h1 : sqHalf (w - 1) = y := by
      rw [hy]
      simp only [sqHalf]
      congr 1
      ring
    rw [h1] at h
    rw [h]
    ring
  by_contra hne
  have hre : y.re = 0 := by
    have h1 : (y ^ 2).im = 0 := by rw [hy2, hw]
    have h2 : (y ^ 2).im = 2 * y.re * y.im := by
      rw [pow_two]
      simp only [Complex.mul_im, Complex.add_re, Complex.add_im]
      ring
    rw [h2] at h1
    have h3 : y.re * y.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hne
  have h2 : (y ^ 2).re = y.re ^ 2 - y.im ^ 2 := by
    rw [pow_two]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  rw [hy2, hre] at h2
  nlinarith [hpos, sq_nonneg y.im]

lemma lamC_im_zero (a : ℝ) : (lamC a).im = 0 := by simp [lamC]

lemma kapC_im_zero (a : ℝ) : (kapC a).im = 0 := by simp [kapC]

lemma betaOf_im_zero {ρ : ℂ → ℂ} {z : ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a) : (betaOf ρ z).im = 0 := by
  simp only [betaOf]
  exact im_add_zero (by simp) (im_mul_zero (im_pow_zero hz 2) (hρ z hz hzn))

lemma SOf_im_zero {ρ : ℂ → ℂ} {z : ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a) : (SOf ρ z).im = 0 := by
  have hb := betaOf_im_zero hρ hz hzn
  have hz2 := im_pow_zero hz 2
  have hb2 := im_pow_zero hb 2
  simp only [SOf]
  refine im_cpow_half ?_ ?_
  · simp only [Complex.add_im, Complex.mul_im]
    rw [hz2, hb2]
    simp
  · have hzsq : (z ^ 2).re = (z.re) ^ 2 := by
      rw [pow_two, Complex.mul_re, hz]; ring
    have hbsq_re : ((betaOf ρ z) ^ 2).re = ((betaOf ρ z).re) ^ 2 := by
      rw [pow_two, Complex.mul_re, hb]; ring
    have hre : (1 + z ^ 2 * (betaOf ρ z) ^ 2).re
        = 1 + (z.re) ^ 2 * ((betaOf ρ z).re) ^ 2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.one_re]
      rw [hzsq, hz2, hbsq_re, hb2]
      ring
    rw [hre]
    positivity

lemma WOf_im_zero {ρ : ℂ → ℂ} {z : ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a) : (WOf ρ z).im = 0 := by
  have hb := betaOf_im_zero hρ hz hzn
  have hs := SOf_im_zero hρ hz hzn
  simp only [WOf]
  exact im_div_zero (im_pow_zero hb 2) (im_add_zero (by simp) hs)

lemma div_lamC_im_zero {z : ℂ} (hz : z.im = 0) : (z / lamC a).im = 0 :=
  im_div_zero hz (lamC_im_zero a)

lemma mul_lamC_im_zero {z : ℂ} (hz : z.im = 0) : (lamC a * z).im = 0 :=
  im_mul_zero (lamC_im_zero a) hz

lemma A1Of_im_zero (a : ℝ) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a)
    (hdivn : ‖z / lamC a‖ ≤ germR a) (hmuln : ‖lamC a * z‖ ≤ germR a) :
    (A1Of a ρ z).im = 0 := by
  have hla := lamC_im_zero a
  have hdiv := div_lamC_im_zero (a := a) hz
  simp only [A1Of]
  exact im_sub_zero (hρ z hz hzn)
    (im_mul_zero (im_inv_zero (im_pow_zero hla 3)) (hρ _ hdiv hdivn))

lemma A2Of_im_zero (a : ℝ) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a)
    (hdivn : ‖z / lamC a‖ ≤ germR a) (hmuln : ‖lamC a * z‖ ≤ germR a) :
    (A2Of a ρ z).im = 0 := by
  have hla := lamC_im_zero a
  have hmul := mul_lamC_im_zero (a := a) hz
  simp only [A2Of]
  exact im_sub_zero (im_mul_zero (im_pow_zero hla 3) (hρ _ hmul hmuln)) (hρ z hz hzn)

lemma A3Of_im_zero (a : ℝ) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a)
    (hdivn : ‖z / lamC a‖ ≤ germR a) (hmuln : ‖lamC a * z‖ ≤ germR a) :
    (A3Of a ρ z).im = 0 := by
  have hla := lamC_im_zero a
  have hmul := mul_lamC_im_zero (a := a) hz
  have hdiv := div_lamC_im_zero (a := a) hz
  simp only [A3Of]
  exact im_sub_zero (im_mul_zero (im_pow_zero hla 3) (hρ _ hmul hmuln))
    (im_mul_zero (im_inv_zero (im_pow_zero hla 3)) (hρ _ hdiv hdivn))

lemma GnlOf_im_zero (a : ℝ) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a)
    (hdivn : ‖z / lamC a‖ ≤ germR a) (hmuln : ‖lamC a * z‖ ≤ germR a) :
    (GnlOf a ρ z).im = 0 := by
  have haa : ((a : ℂ)).im = 0 := by simp
  have hk := kapC_im_zero a
  have hz2 := im_pow_zero hz 2
  have hz4 := im_pow_zero hz 4
  have hrho := hρ z hz hzn
  have hw := WOf_im_zero hρ hz hzn
  have ha1 := A1Of_im_zero a hρ hz hzn hdivn hmuln
  have ha2 := A2Of_im_zero a hρ hz hzn hdivn hmuln
  have ha3 := A3Of_im_zero a hρ hz hzn hdivn hmuln
  simp only [GnlOf]
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_im, haa, hk, hz2, hz4, hrho, hw,
    ha1, ha2, ha3]
  ring

lemma thetaTerm_im_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    (j : ℕ) {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a) :
    (thetaTerm a ρ j z).im = 0 := by
  have hla := lamC_im_zero a
  have harg1 : ((lamC a) ^ (2 * j + 1) * z).im = 0 :=
    im_mul_zero (im_pow_zero hla (2 * j + 1)) hz
  have hargn : ‖(lamC a) ^ (2 * j + 1) * z‖ ≤ germR a := by
    rw [norm_mul, norm_lamC_pow]
    have h0 := eqLam_pos ha0 ha1
    have h0' : 0 ≤ eqLam a := le_of_lt h0
    calc |eqLam a| ^ (2 * j + 1) * ‖z‖ ≤ eqLam a * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [abs_of_nonneg h0']
          calc (eqLam a) ^ (2 * j + 1) ≤ (eqLam a) ^ 1 :=
                pow_le_pow_of_le_one h0' (le_of_lt (eqLam_lt_one ha0 ha1)) (by omega)
            _ = eqLam a := pow_one _
      _ ≤ eqLam a * germR a := mul_le_mul_of_nonneg_left hzn h0'
      _ ≤ germR a := by
          have hr : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
          have h1 := eqLam_lt_one ha0 ha1
          nlinarith
  have hdivn : ‖(lamC a) ^ (2 * j + 1) * z / lamC a‖ ≤ germR a := by
    rw [norm_div, norm_lamC' ha0 ha1]
    have h0 := eqLam_pos ha0 ha1
    rw [div_le_iff₀ h0]
    have h2 : ‖(lamC a) ^ (2 * j + 1) * z‖ ≤ eqLam a * germR a := by
      rw [norm_mul, norm_lamC_pow]
      have h0' : 0 ≤ eqLam a := le_of_lt h0
      calc |eqLam a| ^ (2 * j + 1) * ‖z‖ ≤ eqLam a * ‖z‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [abs_of_nonneg h0']
            calc (eqLam a) ^ (2 * j + 1) ≤ (eqLam a) ^ 1 :=
                  pow_le_pow_of_le_one h0' (le_of_lt (eqLam_lt_one ha0 ha1)) (by omega)
              _ = eqLam a := pow_one _
        _ ≤ eqLam a * germR a := mul_le_mul_of_nonneg_left hzn h0'
    calc ‖(lamC a) ^ (2 * j + 1) * z‖ ≤ eqLam a * germR a := h2
      _ ≤ germR a * eqLam a := le_of_eq (by ring)
  have hGn := GnlOf_im_zero a hρ harg1 hargn hdivn
    (by
      rw [norm_mul, norm_lamC' ha0 ha1]
      calc eqLam a * ‖(lamC a) ^ (2 * j + 1) * z‖ ≤ eqLam a * germR a :=
            mul_le_mul_of_nonneg_left hargn (le_of_lt (eqLam_pos ha0 ha1))
        _ ≤ germR a := by
            have h0 := eqLam_pos ha0 ha1
            have h1 := eqLam_lt_one ha0 ha1
            have hr : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
            nlinarith)
  have haa : ((a : ℂ)).im = 0 := by simp
  have hainv : (((a : ℂ))⁻¹).im = 0 := im_inv_zero haa
  have hla4 := im_pow_zero hla (4 * j + 2)
  simp only [thetaTerm]
  simp only [Complex.mul_im, hGn, hainv, hla4]
  ring

lemma im_tsum_zero {f : ℕ → ℂ} (hf : Summable f) (h : ∀ j, (f j).im = 0) :
    ((∑' j, f j).im = 0) := by
  have hmap := Complex.imCLM.map_tsum (f := f) hf
  simp only [Complex.imCLM_apply] at hmap
  rw [hmap]
  simp [h]

lemma ThetaOf_im_zero (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℂ → ℂ}
    (hρ : ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → (ρ z).im = 0)
    (hb : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1)
    {z : ℂ} (hz : z.im = 0) (hzn : ‖z‖ ≤ germR a) : (ThetaOf a ρ z).im = 0 := by
  have hK0 := gLipK_nonneg ha0 ha1
  have hC : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3)
      + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a :=
    add_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha0) (kapC_nonneg ha0 ha1)) (by norm_num))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hK0)
  have hsum : Summable (fun j : ℕ => thetaTerm a ρ j z) := by
    have := (summable_lamC_mul_of_bound (a := a) ha0 ha1 hC
      (fun v hv => norm_Gnl_le ha0 ha1 hb hv) hzn).mul_left (((a : ℂ))⁻¹)
    simpa only [thetaTerm] using this
  rw [ThetaOf_eq_tsum]
  exact im_tsum_zero hsum (fun j => thetaTerm_im_zero ha0 ha1 hρ j hz hzn)

lemma rhoIter_im_zero (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ∀ z : ℂ, z.im = 0 → ‖z‖ ≤ germR a → ((rhoIter a n z).im = 0) := by
  induction n with
  | zero => intro z hz hzn; simp
  | succ n ih =>
      intro z hz hzn
      rw [rhoIter_succ]
      exact ThetaOf_im_zero ha0 ha1 ih (rhoIter_bound ha0 ha1 n) hz hzn

lemma rhoLim_im_zero (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ} (hz : z.im = 0)
    (hzn : ‖z‖ ≤ germR a) : (rhoLim a z).im = 0 := by
  have hsum := summable_rhoDiff ha0 ha1 hzn
  refine im_tsum_zero hsum (fun n => ?_)
  exact im_sub_zero (rhoIter_im_zero ha0 ha1 (n + 1) z hz hzn)
    (rhoIter_im_zero ha0 ha1 n z hz hzn)

lemma rhoLim_G_sum_zero (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ} (hu : ‖u‖ ≤ germR a) :
    (∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u)) = 0 := by
  have hb : ∀ z, ‖z‖ ≤ germR a → ‖rhoLim a z‖ ≤ 1 :=
    fun z hz => le_trans (rhoLim_bound ha0 ha1 hz) (by norm_num)
  have hCg : 0 ≤ a * ((eqLam a) ^ 2 + (((eqLam a) ^ 2)⁻¹)) :=
    mul_nonneg (le_of_lt ha0) (add_nonneg (by positivity) (by positivity))
  have hGlin := sum_Glin_mul (a := a) ha0 ha1 (C := 1) (fun z hz => hb z hz) u hu
  have hGnl := rhoLim_Gnl_sum ha0 ha1 hu
  have hs1 : Summable (fun j : ℕ =>
      (lamC a) ^ (4 * j + 2) * GlinOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u)) :=
    summable_lamC_mul_of_bound (a := a) ha0 ha1 hCg (fun v hv => norm_Glin_le ha0 ha1 hb hv) hu
  have hs2 := summable_lamC_mul_Gnl ha0 ha1 hu
  have hsplit : (∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u))
      = (∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GlinOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u))
        + (∑' j : ℕ, (lamC a) ^ (4 * j + 2) * GnlOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * u)) := by
    rw [← Summable.tsum_add hs1 hs2]
    refine tsum_congr (fun j => ?_)
    simp only [GOf]; ring
  rw [hsplit, hGlin, hGnl]
  ring

lemma LamInv_sum_eq_zero (ha0 : 0 < a) (ha1 : a < 1) {w : ℂ} (hw : ‖w‖ ≤ germR a) :
    (∑' j : ℕ, (((lamC a) ^ (2 * j + 1))⁻¹)
      * ((((lamC a) ^ (2 * j + 1)) * w) ^ 3 * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * w)
          / (a : ℂ))) = 0 := by
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha0
  have hlane : (lamC a) ≠ 0 := lamC_ne_zero_gs ha0 ha1
  have h1 : (∑' j : ℕ, (((lamC a) ^ (2 * j + 1))⁻¹)
      * ((((lamC a) ^ (2 * j + 1)) * w) ^ 3 * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * w)
          / (a : ℂ)))
      = (∑' j : ℕ, (w ^ 3 / (a : ℂ))
          * ((lamC a) ^ (4 * j + 2) * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * w))) :=
    tsum_congr (fun j => by
      rw [show ((lamC a) ^ (2 * j + 1))⁻¹
            * ((((lamC a) ^ (2 * j + 1)) * w) ^ 3 * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * w)
                / (a : ℂ))
          = (w ^ 3 / (a : ℂ))
            * ((lamC a) ^ (4 * j + 2) * GOf a (rhoLim a) ((lamC a) ^ (2 * j + 1) * w)) by
        field_simp
        ring])
  rw [h1, tsum_mul_left, rhoLim_G_sum_zero ha0 ha1 hw]
  ring

/-- On the disc of radius `λ r` the residual vanishes. -/
lemma GOf_rhoLim_eq_zero (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ}
    (hu : ‖u‖ < eqLam a * germR a) (hu0 : u ≠ 0) : GOf a (rhoLim a) u = 0 := by
  have h0 := eqLam_pos ha0 ha1
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha0
  have hb : ∀ z, ‖z‖ ≤ germR a → ‖rhoLim a z‖ ≤ 1 :=
    fun z hz => le_trans (rhoLim_bound ha0 ha1 hz) (by norm_num)
  have hK0 := gLipK_nonneg ha0 ha1
  set C0 : ℝ := a * ((eqLam a) ^ 2 + (((eqLam a) ^ 2)⁻¹))
      + (a * ((eqLam a)⁻¹ - eqLam a) * (2 / 3) + (eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a)
    with hC0def
  have hC0 : 0 ≤ C0 := by
    rw [hC0def]
    refine add_nonneg
      (mul_nonneg (le_of_lt ha0) (add_nonneg (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg _))))
      (add_nonneg (mul_nonneg (mul_nonneg (le_of_lt ha0) (kapC_nonneg ha0 ha1)) (by norm_num))
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hK0))
  have hCnst : ∀ v, ‖v‖ ≤ eqLam a * germR a → ‖GOf a (rhoLim a) v‖ ≤ C0 := by
    intro v hv
    refine le_trans (norm_add_le _ _) (add_le_add (norm_Glin_le ha0 ha1 hb hv)
      (norm_Gnl_le ha0 ha1 hb hv))
  have hR : 0 < eqLam a * germR a := mul_pos h0 (germR_pos ha0 ha1)
  have hF : ∀ z : ℂ, ‖z‖ < eqLam a * germR a →
      ‖z ^ 3 * GOf a (rhoLim a) z / (a : ℂ)‖ ≤ ((eqLam a * germR a) * C0 / a) * ‖z‖ ^ 2 := by
    intro z hz
    have hzn : ‖z‖ ≤ eqLam a * germR a := le_of_lt hz
    rw [norm_div, norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt ha0)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < a)]
    have h1 : ‖z‖ ^ 3 * ‖GOf a (rhoLim a) z‖ ≤ ‖z‖ ^ 2 * ((eqLam a * germR a) * C0) := by
      calc ‖z‖ ^ 3 * ‖GOf a (rhoLim a) z‖ = ‖z‖ ^ 2 * (‖z‖ * ‖GOf a (rhoLim a) z‖) := by ring
        _ ≤ ‖z‖ ^ 2 * ((eqLam a * germR a) * C0) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul hzn (hCnst z hzn) (norm_nonneg _) (by positivity)
    calc ‖z‖ ^ 3 * ‖GOf a (rhoLim a) z‖ ≤ ‖z‖ ^ 2 * ((eqLam a * germR a) * C0) := h1
      _ = ((eqLam a * germR a) * C0 / a) * ‖z‖ ^ 2 * a := by
          field_simp
  have hres := lam_resolvent (lam := eqLam a) (R := eqLam a * germR a)
    (C := ((eqLam a * germR a) * C0 / a)) h0 (eqLam_lt_one ha0 ha1) hR hF u hu
  have hw1 : ‖lamC a * u‖ ≤ germR a := by
    rw [lamC, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt h0)]
    calc eqLam a * ‖u‖ ≤ eqLam a * (eqLam a * germR a) :=
          mul_le_mul_of_nonneg_left (le_of_lt hu) (le_of_lt h0)
      _ ≤ germR a := by
          have h1 := eqLam_lt_one ha0 ha1
          have hr : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
          nlinarith
  have hw2 : ‖u / lamC a‖ ≤ germR a := by
    rw [lamC, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt h0), div_le_iff₀ h0]
    linarith [le_of_lt hu]
  rw [show ((eqLam a : ℝ) : ℂ) = lamC a from rfl] at hres
  rw [LamInv_sum_eq_zero (a := a) ha0 ha1 hw1,
      LamInv_sum_eq_zero (a := a) ha0 ha1 hw2] at hres
  simp only [neg_zero, mul_zero, sub_zero] at hres
  have hFu : u ^ 3 * GOf a (rhoLim a) u / (a : ℂ) = 0 := hres.symm
  have h1 : u ^ 3 * GOf a (rhoLim a) u = 0 := by
    have h := congrArg (fun z => z * (a : ℂ)) hFu
    rw [zero_mul] at h
    simpa only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hane, inv_mul_cancel₀ hane,
      mul_one] using h
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 3 hu0)

/-- The constructed germ is stable. -/
theorem isStableGerm_hOf {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsStableGerm a (hOf (rhoLim a)) (germR a) := by
  have h0 := eqLam_pos ha0 ha1
  refine ⟨germR_pos ha0 ha1, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : AnalyticOnNhd ℂ (fun u : ℂ => -u) (ball 0 (germR a)) := analyticOnNhd_id.neg
    have h2 : AnalyticOnNhd ℂ (fun u : ℂ => u ^ 3 * rhoLim a u) (ball 0 (germR a)) :=
      (analyticOnNhd_id.pow 3).mul (rhoLim_analytic ha0 ha1)
    have h3 := h1.add h2
    show AnalyticOnNhd ℂ (fun u : ℂ => -u + u ^ 3 * rhoLim a u) (ball 0 (germR a))
    exact h3
  · simp [hOf]
  · have hfun : hOf (rhoLim a) = fun u : ℂ => u * betaOf (rhoLim a) u := by
      funext u
      exact hOf_eq_mul_beta (rhoLim a) u
    rw [hfun]
    have hβ : AnalyticAt ℂ (fun u : ℂ => betaOf (rhoLim a) u) 0 := by
      have h1 : AnalyticAt ℂ (fun u : ℂ => -1 + u ^ 2 * rhoLim a u) 0 :=
        analyticAt_const.add ((analyticAt_id.pow 2).mul
          ((rhoLim_analytic ha0 ha1) 0 (mem_ball_self (germR_pos ha0 ha1))))
      simpa only [betaOf] using h1
    have hd : HasDerivAt (fun u : ℂ => u * betaOf (rhoLim a) u)
        (1 * betaOf (rhoLim a) 0 + 0 * deriv (fun u : ℂ => betaOf (rhoLim a) u) 0) 0 :=
      (hasDerivAt_id 0).mul hβ.differentiableAt.hasDerivAt
    rw [hd.deriv]
    have hb0 : betaOf (rhoLim a) 0 = -1 := by simp [betaOf]
    rw [hb0]
    ring
  · intro t ht
    have h := rhoLim_im_zero ha0 ha1 (z := ((t : ℝ) : ℂ)) (by simp)
      (by rw [norm_real, Real.norm_eq_abs]; exact le_of_lt ht)
    have ht_im : (((t : ℝ) : ℂ)).im = 0 := by simp
    have ht3 : ((((t : ℝ) : ℂ)) ^ 3).im = 0 := im_pow_zero ht_im 3
    simp only [hOf]
    simp only [Complex.add_im, Complex.neg_im, Complex.mul_im, ht_im, ht3, h]
    ring
  · intro u hu
    rw [mem_ball_zero_iff] at hu
    have hz : ‖u ^ 2 * (betaOf (rhoLim a) u) ^ 2‖ ≤ 1 / 64 := by
      rw [norm_mul, norm_pow, norm_pow]
      have hb : ‖betaOf (rhoLim a) u‖ ≤ 2 := by
        simp only [betaOf]
        calc ‖-1 + u ^ 2 * rhoLim a u‖ ≤ ‖(-1 : ℂ)‖ + ‖u ^ 2 * rhoLim a u‖ := norm_add_le _ _
          _ ≤ 1 + (eqLam a * germR a) ^ 2 * 1 := by
              refine add_le_add (by norm_num) ?_
              have h1 : ‖u‖ ^ 2 ≤ (eqLam a * germR a) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg u) (le_of_lt hu) 2
              have h2 : ‖rhoLim a u‖ ≤ 1 :=
                le_trans (rhoLim_bound ha0 ha1 (le_trans (le_of_lt hu)
                  (lam_mul_germR_le_germR ha0 ha1))) (by norm_num)
              rw [norm_mul, norm_pow]
              calc ‖u‖ ^ 2 * ‖rhoLim a u‖ ≤ (eqLam a * germR a) ^ 2 * 1 :=
                    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
                _ = (eqLam a * germR a) ^ 2 * 1 := by ring
          _ ≤ 2 := by
              have hgs := lam_sq_mul_germR_sq_le ha0 ha1
              linarith
      calc ‖u‖ ^ 2 * ‖betaOf (rhoLim a) u‖ ^ 2 ≤ (eqLam a * germR a) ^ 2 * 2 ^ 2 := by
            refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hu) 2)
              (pow_le_pow_left₀ (norm_nonneg _) hb 2) (by positivity) (by positivity)
        _ ≤ 1 / 64 := by
            have hgs := lam_sq_mul_germR_sq_le ha0 ha1
            nlinarith
    have hS : SOf (rhoLim a) u ≠ -1 := by
      intro hneg
      have h1 : ‖SOf (rhoLim a) u - 1‖ ≤ ‖u ^ 2 * (betaOf (rhoLim a) u) ^ 2‖ := by
        rw [SOf_eq_sqHalf]
        exact norm_sqHalf_sub_one_le (by linarith)
      rw [hneg] at h1
      have h2 : ‖((-1:ℂ) - 1)‖ = 2 := by norm_num
      rw [h2] at h1
      linarith
    simp only [GermFE]
    rw [show ((eqLam a : ℝ) : ℂ) = lamC a from rfl]
    rw [germFE_eq_u4_GOf ha0 ha1 (rhoLim a) u hS]
    by_cases hu0 : u = 0
    · subst hu0
      ring
    · rw [GOf_rhoLim_eq_zero ha0 ha1 hu hu0]
      ring

end RealOn

end FixedPoint

end ThetaEstimates

end Bounds

end Work.EQ
