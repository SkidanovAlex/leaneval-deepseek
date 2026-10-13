import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts
import Submission.Work.Coercivity.radial_bound
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Elementary facts about the weights -/

theorem Pss_hKer_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Work.Spaces.hKer r := by
  rw [Work.Spaces.hKer_apply]
  exact div_nonneg hr (by positivity)

theorem Pss_hKer_le_one {r : ℝ} (hr : 0 ≤ r) : Work.Spaces.hKer r ≤ 1 := by
  rw [Work.Spaces.hKer_apply, div_le_one (by positivity)]
  nlinarith

/-- `K(θ) = 3 sin θ cos²θ` is bounded by `3` on `Iθ`. -/
theorem Pss_K_abs_le {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [Work.Spaces.K, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2)]
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  rw [h3]
  have h4 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [h2, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have h5 : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 := by
    have h := mul_le_mul h1 h4 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  nlinarith [h5]

/-- `K(θ) ≥ 0` on `Iθ`. -/
theorem Pss_K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  obtain ⟨h1, h2⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨h1, by linarith [Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2⟩
  rw [Work.Spaces.K]
  positivity

theorem Pss_K_zero_left : Work.Spaces.K (0 : ℝ) = 0 := by simp [Work.Spaces.K]

theorem Pss_K_zero_right : Work.Spaces.K (Real.pi / 2) = 0 := by
  rw [Work.Spaces.K, Real.cos_pi_div_two]
  ring

theorem Pss_sin_two_zero_left {p : ℝ} (hp : p ≠ 0) : Real.sin (2 * (0 : ℝ)) ^ p = 0 := by
  rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero, Real.zero_rpow hp]

theorem Pss_sin_two_zero_right {p : ℝ} (hp : p ≠ 0) :
    Real.sin (2 * (Real.pi / 2)) ^ p = 0 := by
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, Real.zero_rpow hp]

/-- `|H(z)| ≤ 2 h(z)` on `z ≥ 0` for `H(z) = 2z(1-z)/(1+z)³` and `h(z) = z/(1+z)²`. -/
theorem Pss_HLz_le {r : ℝ} (hr : 0 ≤ r) :
    |Work.FTS.Nonlinear.FstarPkg.Hz r| ≤ 2 * Work.Spaces.hKer r := by
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, Work.Spaces.hKer_apply]
  rcases eq_or_lt_of_le hr with h | h
  · subst h; norm_num
  · have h1 : 0 < (1 + r) ^ 3 := by positivity
    have h2 : 0 < (1 + r) ^ 2 := by positivity
    rw [abs_div, abs_of_pos h1, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hr]
    have habs : |1 - r| ≤ 1 + r := abs_le.mpr ⟨by linarith, by linarith⟩
    have hfac : 0 ≤ 2 * r * (1 + r) ^ 2 := by positivity
    have key : 2 * r * |1 - r| * (1 + r) ^ 2 ≤ 2 * r * (1 + r) ^ 3 := by
      calc 2 * r * |1 - r| * (1 + r) ^ 2
          = (2 * r * (1 + r) ^ 2) * |1 - r| := by ring
        _ ≤ (2 * r * (1 + r) ^ 2) * (1 + r) := mul_le_mul_of_nonneg_left habs hfac
        _ = 2 * r * (1 + r) ^ 3 := by ring
    rw [show (2 * (r / (1 + r) ^ 2)) = 2 * r / (1 + r) ^ 2 from by ring]
    rw [div_le_div_iff₀ h1 h2]
    exact key

/-! ## The pointwise shape of `F_*`, `∂_θF_*` and `D_zF_*` -/

theorem Pss_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α r θ| ≤ 20 * α * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h1]; exact h2
  rw [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α]
  simp only
  rw [abs_mul, abs_mul, abs_of_nonneg hker0]
  have h2 : |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| ≤ (20 * α) * 1 :=
    calc |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        ≤ (20 * α) * |Work.Spaces.Gam α θ| :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ ≤ (20 * α) * 1 :=
          mul_le_mul_of_nonneg_left hGam (mul_nonneg (by norm_num) hα.le)
  have h3 : |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| * Work.Spaces.hKer r
      ≤ (20 * α) * 1 * (1 * Work.Spaces.hKer r) :=
    mul_le_mul h2 (by rw [one_mul]) hker0
      (mul_nonneg (mul_nonneg (by norm_num) hα.le) (by norm_num))
  calc |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| * Work.Spaces.hKer r
      ≤ (20 * α) * 1 * (1 * Work.Spaces.hKer r) := h3
    _ = 20 * α * Work.Spaces.hKer r := by ring

theorem Pss_pth_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r) :
    |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hfun : Work.Spaces.pth (Work.Construction.Fstar α) r θ
      = (2 * α / Work.Spaces.c α * Work.Spaces.hKer r)
          * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    have hc : (fun θ' : ℝ => Work.Construction.Fstar α r θ')
        = fun θ' : ℝ =>
            (2 * α / Work.Spaces.c α * Work.Spaces.hKer r) * Work.Spaces.Gam α θ' := by
      funext θ'
      rw [congrFun (congrFun (Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α) r) θ']
      ring
    rw [hc, Work.Spaces.deriv_const_mul']
  rw [hfun, abs_mul, abs_mul, abs_of_nonneg hker0]
  have h2 : |2 * α / Work.Spaces.c α| * Work.Spaces.hKer r ≤ 20 * α * Work.Spaces.hKer r :=
    mul_le_mul_of_nonneg_right hcoef hker0
  calc |2 * α / Work.Spaces.c α| * Work.Spaces.hKer r
        * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      = (|2 * α / Work.Spaces.c α| * Work.Spaces.hKer r)
          * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| := by ring
    _ ≤ (20 * α * Work.Spaces.hKer r) * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ = 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r := by ring

theorem Pss_Dz_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| ≤ 40 * α * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h1]; exact h2
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1 : ℝ) < r)]
  rw [abs_mul, abs_mul]
  have h2 : |Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz r|
      ≤ 2 * (2 * Work.Spaces.hKer r) :=
    mul_le_mul (le_trans hGam (by norm_num)) (Pss_HLz_le hr) (abs_nonneg _) (by norm_num)
  calc |α / Work.Spaces.c α| * (|Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz r|)
      ≤ (10 * α) * (2 * (2 * Work.Spaces.hKer r)) :=
        mul_le_mul hcoef h2 (by positivity) (by positivity)
    _ = 40 * α * Work.Spaces.hKer r := by ring

/-! ## The angular derivative of `Γ` -/

/-- On the open interval, `Γ' = α q Γ / sin(2θ)`. -/
theorem Pss_Gam_deriv_eq {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  rw [Work.Spaces.dthU] at h
  exact (eq_div_iff hsin2.ne').mpr (by rw [mul_comm]; exact h)

/-- `|q(θ)| = |cos 2θ - 1/3| ≤ 4/3`. -/
theorem Pss_qfun_abs_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun, abs_le]
  constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]

/-- On the open interval, `|Γ'| ≤ (4α/3)·Γ/sin(2θ)`. -/
theorem Pss_Gam_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ)) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hq := Pss_qfun_abs_le θ
  have hd := Pss_Gam_deriv_eq hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩).1
  rw [hd, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsin2, abs_of_nonneg hG0]
  have h3 : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
      ≤ (4 * α / 3) * Work.Spaces.Gam α θ := by
    nlinarith [hq, hG0, hα, mul_nonneg hα.le hG0]
  calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Real.sin (2 * θ)
      ≤ ((4 * α / 3) * Work.Spaces.Gam α θ) / Real.sin (2 * θ) :=
        div_le_div_of_nonneg_right h3 hsin2.le
    _ = (4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ)) := by ring

/-- `K(θ)·|Γ'(θ)| ≤ 2α` on the closed angular interval. -/
theorem Pss_K_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · subst h0
    rw [Pss_K_zero_left, zero_mul]
    linarith [hα]
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · have hsin2 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
    have hq := Pss_qfun_abs_le θ
    have hd := Pss_Gam_deriv_eq hα ⟨h0, h1⟩
    have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
      (Work.Spaces.Gam_bounds α θ hα ⟨hθ0, hθ1⟩).1
    have hG1 : Work.Spaces.Gam α θ ≤ 1 :=
      (Work.Spaces.Gam_bounds α θ hα ⟨hθ0, hθ1⟩).2
    rw [hd, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsin2, abs_of_nonneg hG0]
    have hratio : Work.Spaces.K θ * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
          / Real.sin (2 * θ))
        = (3 * Real.cos θ / 2) * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ) := by
      have hsne : Real.sin θ ≠ 0 := ne_of_gt hsinθ
      have hcne : Real.cos θ ≠ 0 := ne_of_gt hcosθ
      rw [Work.Spaces.K, Real.sin_two_mul]
      rw [show (3 * Real.sin θ * Real.cos θ ^ 2)
            * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
              / (2 * Real.sin θ * Real.cos θ))
          = (3 * Real.sin θ * Real.cos θ ^ 2 / (2 * Real.sin θ * Real.cos θ))
            * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ) from by ring]
      rw [show 3 * Real.sin θ * Real.cos θ ^ 2 / (2 * Real.sin θ * Real.cos θ)
          = 3 * Real.cos θ / 2 from by field_simp]
    rw [hratio]
    have h1' : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
        ≤ α * (4 / 3) * Work.Spaces.Gam α θ := by
      nlinarith [hq, hG0, hα, mul_nonneg hα.le hG0]
    have h2' : (3 * Real.cos θ / 2) * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ)
        ≤ (3 * Real.cos θ / 2) * (α * (4 / 3) * Work.Spaces.Gam α θ) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h4 : (3 * Real.cos θ / 2) * (α * (4 / 3) * Work.Spaces.Gam α θ)
        ≤ (3 * Real.cos θ / 2) * (α * (4 / 3) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG1 (by positivity)) (by positivity)
    have h5 : (3 * Real.cos θ / 2) * (α * (4 / 3) * 1) ≤ 2 * α := by
      nlinarith [Real.cos_le_one θ, hα, hcosθ.le]
    linarith [h2', h4, h5]
  · subst h1
    rw [Pss_K_zero_right, zero_mul]
    linarith [hα]

/-- On the open interval, `3 cos³θ·|Γ'| ≤ 4α·sin(2θ)^{α/5-1}`. -/
theorem Pss_K_Gam_deriv_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hGderiv := Pss_Gam_deriv_le hα hθ
  have hG := Work.FTS.Nonlinear.FstarPkg.Gam_le_sin_two_rpow hα ⟨hθ.1.le, hθ.2.le⟩
  have hsplit : (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (α / 5 - 1) * Real.sin (2 * θ) := by
    have h := Real.rpow_add hsin2 (α / 5 - 1) 1
    rw [Real.rpow_one] at h
    rw [show α / 5 - 1 + 1 = α / 5 by ring] at h
    exact h
  have hGam_le : Work.Spaces.Gam α θ / Real.sin (2 * θ)
      ≤ (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
    rw [div_le_iff₀ hsin2]
    calc Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := hG
      _ = (Real.sin (2 * θ)) ^ (α / 5 - 1) * Real.sin (2 * θ) := hsplit
  have hcos3 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ hcos.le (Real.cos_le_one θ)
  calc 3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 3 * 1 * ((4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ))) := by
        have h31 : 3 * Real.cos θ ^ 3 ≤ 3 * 1 := by nlinarith [hcos3]
        exact mul_le_mul h31 hGderiv (abs_nonneg _) (by positivity)
    _ ≤ 3 * 1 * ((4 * α / 3) * (Real.sin (2 * θ)) ^ (α / 5 - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hGam_le (by positivity)
    _ = 4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by ring

/-! ## The relation `V = R + tan θ · U` -/

theorem Pss_tan_Uop {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Real.tan θ * Work.Construction.Uop α Ψ z θ
      = Work.Construction.Vop Ψ z θ - Work.Construction.Rop α Ψ z θ := by
  simp only [Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The measure-theoretic reduction -/

/-- Reduction step: a pointwise bound of the shape `|K θ · N r θ| ≤ C·h(r)·A(θ)` gives the
required weighted estimate with constant `C·M·2`, where `M` bounds `∫⁻ A`. -/
theorem PssReduce {N : ℝ → ℝ → ℝ} {C M : ℝ} {A : ℝ → ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A θ)
    (hA : ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (A θ) ≤ ENNReal.ofReal M)
    (hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * N r θ| ≤ C * Work.Spaces.hKer r * A θ) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|)) ≤ ENNReal.ofReal (C * M * 2) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (C * Work.Spaces.hKer r * M) := by
    intro r hr
    have hker0 : 0 ≤ Work.Spaces.hKer r := by
      rw [Work.Spaces.hKer_apply]; exact div_nonneg (le_of_lt hr) (by positivity)
    have hCk : 0 ≤ C * Work.Spaces.hKer r := mul_nonneg hC hker0
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal (A θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hpt r hr, MeasureTheory.ae_restrict_mem hIθm] with θ h1 h2
          calc ENNReal.ofReal |Work.Spaces.K θ * N r θ|
              ≤ ENNReal.ofReal (C * Work.Spaces.hKer r * A θ) :=
                ENNReal.ofReal_le_ofReal h1
            _ = ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal (A θ) :=
                ENNReal.ofReal_mul hCk
      _ = ENNReal.ofReal (C * Work.Spaces.hKer r)
            * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (A θ) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal M :=
          mul_le_mul_right hA (ENNReal.ofReal (C * Work.Spaces.hKer r))
      _ = ENNReal.ofReal (C * Work.Spaces.hKer r * M) :=
          (ENNReal.ofReal_mul hCk).symm
  have houter : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * ENNReal.ofReal (C * Work.Spaces.hKer r * M) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_right (hinner r hr) (ENNReal.ofReal r⁻¹)
  have hcongr : (fun r : ℝ => ENNReal.ofReal r⁻¹
        * ENNReal.ofReal (C * Work.Spaces.hKer r * M))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => ENNReal.ofReal (C * M) * ENNReal.ofReal (1 / (1 + r) ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hker0 : 0 ≤ Work.Spaces.hKer r := by
      rw [Work.Spaces.hKer_apply]; exact div_nonneg hr0.le (by positivity)
    have hCk : 0 ≤ C * Work.Spaces.hKer r := mul_nonneg hC hker0
    have hCM : 0 ≤ C * M := mul_nonneg hC hM
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    have hkey : r⁻¹ * Work.Spaces.hKer r = 1 / (1 + r) ^ 2 := by
      rw [Work.Spaces.hKer_apply]
      field_simp
    calc ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * Work.Spaces.hKer r * M)
        = ENNReal.ofReal (r⁻¹ * (C * Work.Spaces.hKer r * M)) :=
            (ENNReal.ofReal_mul hinv).symm
      _ = ENNReal.ofReal (C * M * (r⁻¹ * Work.Spaces.hKer r)) := by
            rw [show r⁻¹ * (C * Work.Spaces.hKer r * M)
                = C * M * (r⁻¹ * Work.Spaces.hKer r) by ring]
      _ = ENNReal.ofReal (C * M * (1 / (1 + r) ^ 2)) := by rw [hkey]
      _ = ENNReal.ofReal (C * M) * ENNReal.ofReal (1 / (1 + r) ^ 2) :=
            ENNReal.ofReal_mul hCM
  rw [MeasureTheory.lintegral_congr_ae hcongr] at houter
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at houter
  refine le_trans houter ?_
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => 1 / (1 + r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.Coercivity.rb_integrableOn_inv_one_add_sq_Iz.mono_set Set.Ioi_subset_Ici_self
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => 1 / (1 + r) ^ 2) :=
    Filter.Eventually.of_forall fun r => by positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [← ENNReal.ofReal_mul (mul_nonneg hC hM)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hI : (∫ r in Set.Ioi (0 : ℝ), 1 / (1 + r) ^ 2) ≤ 2 := by
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact Work.Coercivity.rb_integral_Iz_inv_one_add_sq_le
  calc C * M * (∫ r in Set.Ioi (0 : ℝ), 1 / (1 + r) ^ 2) ≤ C * M * 2 :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hC hM)
    _ = C * M * 2 := rfl

/-! ## The angular integral for the `N₂` slot -/

theorem PssAngInt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Real.sin (2 * θ)) ^ (α / 5 - 1)))
      ≤ ENNReal.ofReal (500 / α) := by
  obtain ⟨hint, hle⟩ := Work.Spaces.sin_two_rpow (α / 5 - 1) (by linarith) (by linarith)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (α / 5 - 1)) :=
    (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ) _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans hle ?_
  rw [show α / 5 - 1 + 1 = α / 5 by ring]
  have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
  have heq : 100 / (α / 5) = 500 / α := by
    have hα5 : α / 5 ≠ 0 := div_ne_zero hαne (by norm_num)
    field_simp
    ring
  rw [heq]

/-! ## The five pointwise bounds -/

theorem Pss_N1ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hR := (Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs).1 r hr θ hθ
  have hF := Pss_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  show |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Construction.Fstar α r θ)| ≤ 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Construction.Fstar α r θ)|
      = |Work.Spaces.K θ| * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Construction.Fstar α r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hLHS]
  have h2 : 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
      ≤ 2 * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hR (by norm_num)
  calc |Work.Spaces.K θ| * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Construction.Fstar α r θ|
      ≤ 3 * (2 * (max Cs 0 * α)) * (20 * α * Work.Spaces.hKer r) := by
        refine mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hF
          (abs_nonneg _) (by positivity)
    _ = 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r := by ring

theorem Pss_N2ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|
        ≤ 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
  intro r hr θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hne : α / 5 - 1 ≠ 0 := by linarith
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · subst h0
    rw [Pss_K_zero_left, Pss_sin_two_zero_left hne]
    simp
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
    have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1
    have hKpos := Pss_K_nonneg ⟨hθ0, hθ1⟩
    obtain ⟨hRpt, hVpt, _⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
    have hR := hRpt r hr θ ⟨hθ0, hθ1⟩
    have hV := hVpt r hr0 θ ⟨hθ0, hθ1⟩
    have hUop : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * max Cs 0 * α / Real.tan θ := by
      have hid := Pss_tan_Uop (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) (z := r) (θ := θ)
        (ne_of_gt hcosθ)
      have h1' : Real.tan θ * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
          ≤ 2 * max Cs 0 * α := by
        calc Real.tan θ * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            = |Real.tan θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
              rw [abs_mul, abs_of_pos htan]
          _ = |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
                - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by rw [hid]
          _ ≤ |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
                + |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
              rw [sub_eq_add_neg]
              simpa [abs_neg] using abs_add_le
                (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
                (-(Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ))
          _ ≤ 2 * max Cs 0 * α := by linarith
      exact (le_div_iff₀ htan).mpr (by rw [mul_comm]; exact h1')
    have hpth := Pss_pth_Fstar_le α r θ hα hα1 hr0
    have hG := Pss_K_Gam_deriv_le hα hα1 ⟨h0, h1⟩
    have hKsplit : Work.Spaces.K θ / Real.tan θ = 3 * Real.cos θ ^ 3 := by
      have hsne : Real.sin θ ≠ 0 := ne_of_gt hsinθ
      have hcne : Real.cos θ ≠ 0 := ne_of_gt hcosθ
      rw [Work.Spaces.K, Real.tan_eq_sin_div_cos]
      field_simp
    show |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
        ≤ 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1)
    have hLHS : |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
          * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
        = Work.Spaces.K θ * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hKpos]
      ring
    rw [hLHS]
    have hmul : Work.Spaces.K θ
          * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
        ≤ Work.Spaces.K θ * (2 * (2 * max Cs 0 * α / Real.tan θ))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r) := by
      have h1 : 2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
          ≤ 2 * (2 * max Cs 0 * α / Real.tan θ) :=
        mul_le_mul_of_nonneg_left hUop (by norm_num)
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hKpos) hpth (abs_nonneg _) (by positivity)
    refine le_trans hmul ?_
    rw [show Work.Spaces.K θ * (2 * (2 * max Cs 0 * α / Real.tan θ))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r)
        = 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
          * (3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
        from by rw [← hKsplit]; ring]
    have hcoef : 0 ≤ 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_max_right Cs 0)) (sq_nonneg α))
        (Pss_hKer_nonneg hr0)
    calc 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
          * (3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
        ≤ 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
            * (4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1)) :=
          mul_le_mul_of_nonneg_left hG hcoef
      _ = 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by ring
  · subst h1
    rw [Pss_K_zero_right, Pss_sin_two_zero_right hne]
    simp

theorem Pss_N3ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|
        ≤ 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hV := (Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs).2.1 r hr0 θ hθ
  have hDz := Pss_Dz_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  show |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      ≤ 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      = |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hα.le]
    ring
  rw [hLHS]
  have h2 : 2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
      ≤ 2 * α * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hV (by positivity)
  calc |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ|
      ≤ 3 * (2 * α * (max Cs 0 * α)) * (40 * α * Work.Spaces.hKer r) := by
        refine mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hDz
          (abs_nonneg _) (by positivity)
    _ = 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r := by ring

theorem Pss_N4ss_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ| ≤ 40 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr0
  have hker1 : Work.Spaces.hKer r ≤ 1 := Pss_hKer_le_one hr0
  have hKgm := Pss_K_deriv_le hα hθ
  have hpth := Pss_pth_Fstar_le α r θ hα hα1 hr0
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (z := r) hα hα1
  have hK0 := Pss_K_nonneg hθ
  have hFKval : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * Work.Spaces.hKer r) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity)), Work.Spaces.hKer_apply]
    ring
  show |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)| ≤ 40 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
        * |Work.Construction.FK (Work.Construction.Fstar α) r|
        * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hK0]
    ring
  rw [hLHS, hFKval]
  have hs21 : |Work.Construction.s2 θ| ≤ 1 := by
    show |Real.sin (2 * θ)| ≤ 1
    exact abs_le.mpr ⟨Real.neg_one_le_sin (2 * θ), Real.sin_le_one (2 * θ)⟩
  have hstep : Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
        * (α * (2 * Work.Spaces.hKer r))
        * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r))
        * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r) := by
    have h2 : (1 / 2) * |Work.Construction.s2 θ| ≤ (1 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hs21 (by norm_num)
    have h3 : Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
          * (α * (2 * Work.Spaces.hKer r))
        ≤ Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK0) (by positivity)
    exact mul_le_mul h3 hpth (abs_nonneg _) (by positivity)
  refine le_trans hstep ?_
  rw [show Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r))
        * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r)
      = 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r
        * (Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
      from by ring]
  have hker2 : Work.Spaces.hKer r * Work.Spaces.hKer r ≤ Work.Spaces.hKer r := by
    have h := mul_le_mul_of_nonneg_left hker1 hker0
    simpa using h
  calc 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r
        * (Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
      ≤ 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r * (2 * α) :=
        mul_le_mul_of_nonneg_left hKgm (by positivity)
    _ = 40 * α ^ 3 * (Work.Spaces.hKer r * Work.Spaces.hKer r) := by ring
    _ ≤ 40 * α ^ 3 * Work.Spaces.hKer r :=
        mul_le_mul_of_nonneg_left hker2 (by positivity)
    _ ≤ 40 * α ^ 2 * Work.Spaces.hKer r :=
        mul_le_mul_of_nonneg_right (by nlinarith [hα, hα1]) hker0

theorem Pss_N5ss_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ| ≤ 120 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr0
  have hker1 : Work.Spaces.hKer r ≤ 1 := Pss_hKer_le_one hr0
  have hF := Pss_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (z := r) hα hα1
  have hsin1 : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one θ)
  show |Work.Spaces.K θ * (-(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Construction.Fstar α r θ)| ≤ 120 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Construction.Fstar α r θ)|
      = |Work.Spaces.K θ| * ((Real.sin θ) ^ 2
          * |Work.Construction.FK (Work.Construction.Fstar α) r|)
        * |Work.Construction.Fstar α r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    ring
  rw [hLHS]
  have hFKval : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * Work.Spaces.hKer r) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity)), Work.Spaces.hKer_apply]
    ring
  rw [hFKval]
  have h2 : (Real.sin θ) ^ 2 * (α * (2 * Work.Spaces.hKer r))
      ≤ 1 * (α * (2 * Work.Spaces.hKer r)) :=
    mul_le_mul_of_nonneg_right hsin1 (by positivity)
  calc |Work.Spaces.K θ| * ((Real.sin θ) ^ 2 * (α * (2 * Work.Spaces.hKer r)))
        * |Work.Construction.Fstar α r θ|
      ≤ 3 * (1 * (α * (2 * Work.Spaces.hKer r))) * (20 * α * Work.Spaces.hKer r) :=
        mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hF
          (abs_nonneg _) (by positivity)
    _ = 120 * α ^ 2 * (Work.Spaces.hKer r * Work.Spaces.hKer r) := by ring
    _ ≤ 120 * α ^ 2 * (Work.Spaces.hKer r * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hker1 hker0) (by positivity)
    _ = 120 * α ^ 2 * Work.Spaces.hKer r := by ring

theorem Pss {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) := by
  refine ⟨400000 * max Cs 0 + 1000, ?_, ?_⟩
  · have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
    linarith
  · intro α g Φs Φg hα hα1 hαα2 hN4 hGal hStar hEll
    have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
    have hπ := Real.pi_lt_four
    have hunit : ∀ θ : ℝ, (fun _ : ℝ => (1 : ℝ)) θ = 1 := fun θ => rfl
    have hA1 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) θ)) ≤ ENNReal.ofReal (Real.pi / 2) := by
      have h1 : (fun θ : ℝ => ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) θ))
          = fun _ : ℝ => (1 : ENNReal) := by funext x; simp
      rw [h1, MeasureTheory.lintegral_const, one_mul,
        MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      unfold Work.Spaces.Iθ
      rw [Real.volume_Icc]
      simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hred := PssReduce (N := Work.FTS.Nonlin.N1ss α Φs)
          (C := 120 * max Cs 0 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by nlinarith [hm, sq_nonneg α])
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N1ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (120 : ℝ) * Real.pi * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by
        nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N2ss α Φs)
          (C := 320 * max Cs 0 * α ^ 3) (M := 500 / α)
          (A := fun θ : ℝ => (Real.sin (2 * θ)) ^ (α / 5 - 1))
          (mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3))
          (div_nonneg (by norm_num) hα.le)
          (fun θ hθ => Real.rpow_nonneg
            (Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ) _)
          (PssAngInt hα hα1)
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            exact Pss_N2ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have hval : 320 * max Cs 0 * α ^ 3 * (500 / α) * 2 = 320000 * max Cs 0 * α ^ 2 := by
        have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [hval]
      have h1 : (320000 : ℝ) * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hm]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
    · have hred := PssReduce (N := Work.FTS.Nonlin.N3ss α Φs)
          (C := 240 * max Cs 0 * α ^ 3) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3))
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N3ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (240 : ℝ) * Real.pi * max Cs 0 * α ≤ 400000 * max Cs 0 + 1000 := by
        have hA : 240 * Real.pi * max Cs 0 * α ≤ 960 * max Cs 0 * α := by
          have hp : Real.pi * (max Cs 0 * α) ≤ 4 * (max Cs 0 * α) :=
            mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hm hα.le)
          nlinarith [hp]
        have hB : (960 : ℝ) * max Cs 0 * α ≤ 960 * max Cs 0 := by
          have hb : (960 * max Cs 0) * α ≤ (960 * max Cs 0) * 1 :=
            mul_le_mul_of_nonneg_left hα1 (mul_nonneg (by norm_num) hm)
          linarith [hb]
        have hC : (960 : ℝ) * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hm]
        linarith [hA, hB, hC]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N4ss α)
          (C := 40 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by positivity)
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N4ss_pt hα hα1 r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (40 : ℝ) * Real.pi ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N5ss α)
          (C := 120 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by positivity)
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N5ss_pt hα hα1 r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (120 : ℝ) * Real.pi ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]

end Work.FTS.Nonlinear.Pieces.rl1Pieces
