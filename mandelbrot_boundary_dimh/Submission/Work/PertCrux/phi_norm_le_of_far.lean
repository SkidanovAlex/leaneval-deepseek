import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup

namespace Work.PertCrux

/-!
# `phi_norm_le_of_far`

The Fatou coordinate `φ = φ₀` of §4.1 (`ParabData.φ`) tends to `0` at infinity inside
Shishikura's repelling sector `Q₀ = QLeft ξ₀ = {π/3 < |arg(w + ξ₀)|}`.  Concretely: for every
`c > 0` there is `R > 0` with `‖φ₀ u‖ ≤ c` for all `u ∈ Q₀`, `‖u‖ ≥ R`.

The content is exactly the asymptotic expansion field `ParabData.φ_asymp`:
`τ₀(φ w) = -1/φ w = w + a log(-w) + b + o(1)` on `Q₀`.  For `‖w‖` large the polynomial term `w`
dominates, so `‖τ₀(φ w)‖ ≥ ‖w‖/2 - 1` is eventually positive and
`‖φ w‖ = 1/‖τ₀(φ w)‖` is eventually smaller than every prescribed `c`.  The elementary estimates
used are `log r ≤ 2√r` (so the `a log(-w) + b` term is eventually `< ‖w‖/2`) and
`‖log z‖ ≤ log ‖z‖ + π` for `‖z‖ ≥ 1`.
-/

/-- `log r ≤ 2√r` for `r ≥ 0` (the logarithmic term grows slower than the linear one). -/
lemma log_le_two_sqrt_far {r : ℝ} (hr : 0 ≤ r) : Real.log r ≤ 2 * Real.sqrt r := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    simp
  · have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr h
    have h1 : Real.log (Real.sqrt r) ≤ Real.sqrt r - 1 := Real.log_le_sub_one_of_pos hsqrt
    rw [Real.log_sqrt hr] at h1
    linarith

/-- `‖log z‖ ≤ log ‖z‖ + π` for `‖z‖ ≥ 1` (principal branch). -/
lemma norm_log_le_far (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_nonneg (Real.log_nonneg hz)
  rw [h2] at h1
  have h3 : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
  linarith

/-- For fixed `A B : ℝ` the function `r ↦ |A| (log r + π) + B` is eventually `≤ r/2`. -/
lemma exists_log_half_le_far (A B : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r → |A| * (Real.log r + Real.pi) + B ≤ r / 2 := by
  refine ⟨max 1 (max (64 * |A| ^ 2) (4 * (|A| * Real.pi + B + 1))), le_max_left _ _, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hA2 : 64 * |A| ^ 2 ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr)
  have hB2 : 4 * (|A| * Real.pi + B + 1) ≤ r :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr)
  have hr0 : 0 ≤ r := by linarith
  have hroot : Real.sqrt (64 * |A| ^ 2) = 8 * |A| := by
    rw [show (64 : ℝ) * |A| ^ 2 = (8 * |A|) ^ 2 from by ring]
    exact Real.sqrt_sq (by positivity)
  have hsq : 8 * |A| ≤ Real.sqrt r := by
    calc 8 * |A| = Real.sqrt (64 * |A| ^ 2) := hroot.symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hA2
  have hA0 : 0 ≤ |A| := abs_nonneg A
  have hb1 : |A| * Real.log r ≤ r / 4 := by
    have h4 : |A| * (2 * Real.sqrt r) ≤ r / 4 := by
      nlinarith [hsq, hA0, Real.sqrt_nonneg r, Real.sq_sqrt hr0]
    nlinarith [log_le_two_sqrt_far hr0, hA0]
  have hb2 : |A| * Real.pi + B ≤ r / 4 - 1 := by linarith
  nlinarith [hb1, hb2]

theorem phi_norm_le_of_far {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ u ∈ MandelDim.QLeft d.ξ₀, R ≤ ‖u‖ → ‖d.φ u‖ ≤ c := by
  obtain ⟨a, b, hab⟩ := d.φ_asymp
  obtain ⟨Rφ, hRφ⟩ := hab 1 (by norm_num)
  obtain ⟨Rl, hRl1, hRl⟩ := exists_log_half_le_far ‖a‖ ‖b‖
  refine ⟨max (max (Rφ + 1) Rl) (2 / c + 2), ?_, ?_⟩
  · have h2 : Rl ≤ max (max (Rφ + 1) Rl) (2 / c + 2) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  · intro u hu hRu
    have huRφ : Rφ < ‖u‖ := by
      have h : Rφ + 1 ≤ max (max (Rφ + 1) Rl) (2 / c + 2) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have huRl : Rl ≤ ‖u‖ := by
      have h : Rl ≤ max (max (Rφ + 1) Rl) (2 / c + 2) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hu2 : 2 / c + 2 ≤ ‖u‖ := le_trans (le_max_right _ _) hRu
    have hu1 : 1 ≤ ‖u‖ := le_trans hRl1 huRl
    have hclose : ‖MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)‖ < 1 :=
      hRφ u hu huRφ
    have hlogn : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
      have h := norm_log_le_far (-u) (by simpa using hu1)
      simpa using h
    have hYb : ‖a * Complex.log (-u) + b‖ ≤ ‖u‖ / 2 := by
      have hstep : ‖a * Complex.log (-u) + b‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) + ‖b‖ := by
        have h1 : ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
        rw [norm_mul] at h1
        have h2 : ‖a‖ * ‖Complex.log (-u)‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) :=
          mul_le_mul_of_nonneg_left hlogn (norm_nonneg a)
        linarith
      refine le_trans hstep ?_
      have h := hRl ‖u‖ huRl
      simpa [abs_of_nonneg (norm_nonneg a)] using h
    have hY : ‖u‖ / 2 ≤ ‖u + a * Complex.log (-u) + b‖ := by
      have h : ‖u‖ ≤ ‖u + a * Complex.log (-u) + b‖ + ‖a * Complex.log (-u) + b‖ := by
        have hsub := norm_sub_le (u + a * Complex.log (-u) + b) (a * Complex.log (-u) + b)
        simpa using hsub
      linarith
    have hlt : 1 / c ≤ ‖MandelDim.tau0 (d.φ u)‖ := by
      have h : ‖u + a * Complex.log (-u) + b‖ ≤ ‖MandelDim.tau0 (d.φ u)‖ +
          ‖MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b)‖ := by
        have hsub := norm_sub_le (MandelDim.tau0 (d.φ u))
          (MandelDim.tau0 (d.φ u) - (u + a * Complex.log (-u) + b))
        simpa using hsub
      rw [div_eq_mul_inv] at hu2 ⊢
      linarith
    have hval : ‖MandelDim.tau0 (d.φ u)‖ = 1 / ‖d.φ u‖ := by
      rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
    have hnormφ : ‖d.φ u‖ = 1 / ‖MandelDim.tau0 (d.φ u)‖ := by
      rw [hval, one_div_one_div]
    calc ‖d.φ u‖ = 1 / ‖MandelDim.tau0 (d.φ u)‖ := hnormφ
      _ ≤ 1 / (1 / c) := one_div_le_one_div_of_le (by positivity) hlt
      _ = c := by rw [one_div_one_div]

end Work.PertCrux
