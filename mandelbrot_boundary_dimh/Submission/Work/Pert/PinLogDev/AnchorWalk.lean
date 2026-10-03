import Mathlib
import Submission.Work.Pert.PinLogDev.Setup
import Submission.Work.Parab.Setup
import Submission.Work.Pert.Ksub2.Setup

/-!
# `Work.Pert.PinLogDev.AnchorWalk`

Datum-level asymptotics of the curve `Xc d u = τ₀ (φ₀ u)` on the negative real axis, together with
the margin estimates that describe the "anchor walk" `w j = Xc d (-M + j)`
(cf. `NOTES_new_route.md`).

The two margins of the gate

* `margA Ξ α z = Re z - Ξ + Re(1/α) + |Im z + Im(1/α)|`  (condition at the apex `Ξ - 1/α`),
* `margB Ξ α z = |Im z| - Ξ - Re z`                      (condition at the apex `-Ξ`)

satisfy: `margB` of a walk point is at least `x - K log x - C` for datum-level `K, C`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-- **The datum's asymptotics on the negative real axis.**  There are `a b : ℂ` (the same as in
`ParabData.φ_asymp`) and a radius `R ≥ exp π` with `ξ₀ + 1 < R` such that for every `x ≥ R` the
point `-x` lies in the repelling sector and `‖Xc d (-x) - (-x + a log x + b)‖ ≤ 1/1024`. -/
theorem exists_Xc_axis_asym {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ (a b : ℂ) (R : ℝ), 0 < R ∧ d.ξ₀ + 1 < R ∧ Real.exp Real.pi ≤ R ∧
      ∀ x : ℝ, R ≤ x →
        ‖Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024 := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R₀, hR₀⟩ := hasym (1 / 1024) (by norm_num)
  set R : ℝ := max (max (max R₀ (d.ξ₀ + 1)) 1) (Real.exp Real.pi) + 1 with hRdef
  have hinner : (1 : ℝ) ≤ max (max R₀ (d.ξ₀ + 1)) 1 := le_max_right _ _
  have hexp1 : (1 : ℝ) ≤ Real.exp Real.pi := by
    rw [Real.one_le_exp_iff]; exact Real.pi_pos.le
  have hmaxle : (1 : ℝ) ≤ max (max (max R₀ (d.ξ₀ + 1)) 1) (Real.exp Real.pi) :=
    le_trans hinner (le_max_left _ _)
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hξR : d.ξ₀ + 1 < R := by
    have h1 : d.ξ₀ + 1 ≤ max R₀ (d.ξ₀ + 1) := le_max_right _ _
    have h2 : max R₀ (d.ξ₀ + 1) ≤ max (max R₀ (d.ξ₀ + 1)) 1 := le_max_left _ _
    have h3 : max (max R₀ (d.ξ₀ + 1)) 1 ≤ max (max (max R₀ (d.ξ₀ + 1)) 1) (Real.exp Real.pi) :=
      le_max_left _ _
    rw [hRdef]; linarith
  have hexpR : Real.exp Real.pi ≤ R := by
    have h3 : Real.exp Real.pi ≤ max (max (max R₀ (d.ξ₀ + 1)) 1) (Real.exp Real.pi) :=
      le_max_right _ _
    rw [hRdef]; linarith
  refine ⟨a, b, R, hRpos, hξR, hexpR, ?_⟩
  intro x hx
  have hxlt : max (max (max R₀ (d.ξ₀ + 1)) 1) (Real.exp Real.pi) < x := by rw [hRdef] at hx; linarith
  have hxA : max (max R₀ (d.ξ₀ + 1)) 1 < x :=
    lt_of_le_of_lt (le_max_left _ _) hxlt
  have hxB : max R₀ (d.ξ₀ + 1) < x := lt_of_le_of_lt (le_max_left _ _) hxA
  have hxR₀ : R₀ < x := lt_of_le_of_lt (le_max_left _ _) hxB
  have hxξR : d.ξ₀ + 1 < x := lt_of_le_of_lt (le_max_right _ _) hxB
  have hxone : (1 : ℝ) < x := lt_of_le_of_lt hinner hxA
  have hQ : -(x : ℂ) ∈ MandelDim.QLeft d.ξ₀ := by
    apply Work.Parab.halfplane_subset_QLeft d.ξ₀
    rw [Set.mem_ofPred_eq]
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  have hnorm : R₀ < ‖-(x : ℂ)‖ := by
    have h1 : ‖-(x : ℂ)‖ = |x| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, abs_of_nonneg (by linarith)]
    exact hxR₀
  have h := hR₀ (-(x : ℂ)) hQ hnorm
  have h' : ‖Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ < 1 / 1024 := by
    simpa only [Xc, MandelDim.tau0, neg_neg] using h
  exact h'.le

/-- **The `margB` margin along the walk.**  With `a, b, R` as in `exists_Xc_axis_asym`, for every
`x ≥ R` the `margB`-margin of `Xc d (-x)` is at least
`x - (|Re a| + |Im a|) log x - ((|Re a| + |Im a|) π + |Re b| + |Im b| + Ξ + 1)`. -/
theorem margB_Xc_axis_ge {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R Ξ : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {x : ℝ} (hR : R ≤ x) (hexp : Real.exp Real.pi ≤ x) :
    x - (|a.re| + |a.im|) * Real.log x
        - ((|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 1) ≤
      margB Ξ α (Xc d (-(x : ℂ))) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by rw [Real.one_le_exp_iff]; exact Real.pi_pos.le) hexp
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlogpi : Real.pi ≤ Real.log x := by
    rw [← Real.log_exp Real.pi]; exact Real.log_le_log (Real.exp_pos _) hexp
  have hlog0 : 0 ≤ Real.log x := le_trans Real.pi_pos.le hlogpi
  set w : ℂ := Xc d (-(x : ℂ)) with hwdef
  set y : ℂ := -(x : ℂ) + a * Complex.log (x : ℂ) + b with hydef
  have hclose : ‖w - y‖ ≤ 1 / 1024 := hasym x hR
  have hbre : -(1 / 1024) ≤ w.re - y.re := by
    have h1 : |(w - y).re| ≤ ‖w - y‖ := Complex.abs_re_le_norm _
    have h2 := (abs_le.mp (le_trans h1 hclose)).1
    rwa [Complex.sub_re] at h2
  have hbim : |w.im - y.im| ≤ 1 / 1024 := by
    have h1 : |(w - y).im| ≤ ‖w - y‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    linarith
  have hlogre : (Complex.log (x : ℂ)).re = Real.log x := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le]
  have hloglo : -Real.pi ≤ (Complex.log (x : ℂ)).im := (Complex.neg_pi_lt_log_im _).le
  have hloghi : (Complex.log (x : ℂ)).im ≤ Real.pi := Complex.log_im_le_pi _
  have hyre : y.re = -x + (a * Complex.log (x : ℂ)).re + b.re := by simp [hydef]
  have hyim : y.im = (a * Complex.log (x : ℂ)).im + b.im := by simp [hydef]
  -- ## 1. the real part of the logarithmic term
  have hpi' : |a.im| * Real.pi ≤ |a.im| * Real.log x :=
    mul_le_mul_of_nonneg_left hlogpi (abs_nonneg _)
  have hA_re_ub : (a * Complex.log (x : ℂ)).re ≤ |a.re| * Real.log x + |a.im| * Real.pi := by
    rw [Complex.mul_re, hlogre]
    have h1 : a.re * Real.log x ≤ |a.re| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self a.re) hlog0
    have h2 : -(a.im * (Complex.log (x : ℂ)).im) ≤ |a.im * (Complex.log (x : ℂ)).im| :=
      neg_le_abs _
    have h3 : |a.im * (Complex.log (x : ℂ)).im| ≤ |a.im| * Real.pi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hloglo, hloghi⟩) (abs_nonneg _)
    linarith
  have hA_re : -((|a.re| + |a.im|) * Real.log x) ≤ (a * Complex.log (x : ℂ)).re := by
    rw [Complex.mul_re, hlogre]
    have h1 : -(|a.re| * Real.log x) ≤ a.re * Real.log x := by
      have h := mul_le_mul_of_nonneg_right (neg_abs_le a.re) hlog0
      rwa [neg_mul] at h
    have h2 : a.im * (Complex.log (x : ℂ)).im ≤ |a.im| * Real.pi := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hloglo, hloghi⟩) (abs_nonneg _)
    have h3 : -( |a.im| * Real.pi) ≤ -(a.im * (Complex.log (x : ℂ)).im) := neg_le_neg h2
    linarith
  -- ## 2. the imaginary part of the logarithmic term
  have hA_im : |a.im| * Real.log x - |a.re| * Real.pi ≤
      |(a * Complex.log (x : ℂ)).im| := by
    have hform : (a * Complex.log (x : ℂ)).im
        = a.re * (Complex.log (x : ℂ)).im + a.im * Real.log x := by
      rw [Complex.mul_im, hlogre]
    rw [hform, show a.re * (Complex.log (x : ℂ)).im + a.im * Real.log x
      = a.im * Real.log x + a.re * (Complex.log (x : ℂ)).im by ring]
    have h1 : |a.im * Real.log x| - |a.re * (Complex.log (x : ℂ)).im|
        ≤ |a.im * Real.log x + a.re * (Complex.log (x : ℂ)).im| := by
      have h := abs_sub_abs_le_abs_sub (a.im * Real.log x) (-(a.re * (Complex.log (x : ℂ)).im))
      rw [abs_neg] at h
      have h4 : a.im * Real.log x - (-(a.re * (Complex.log (x : ℂ)).im))
          = a.im * Real.log x + a.re * (Complex.log (x : ℂ)).im := by ring
      rwa [h4] at h
    have h2 : |a.im * Real.log x| = |a.im| * Real.log x := by
      simp only [abs_mul, abs_of_nonneg hlog0]
    have h3 : |a.re * (Complex.log (x : ℂ)).im| ≤ |a.re| * Real.pi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hloglo, hloghi⟩) (abs_nonneg _)
    linarith
  -- ## 3. the resulting bounds on `y` and on `w`
  have hbre2 : w.re - y.re ≤ 1 / 1024 := by
    have h1 : |(w - y).re| ≤ ‖w - y‖ := Complex.abs_re_le_norm _
    have h2 := (abs_le.mp (le_trans h1 hclose)).2
    rwa [Complex.sub_re] at h2
  have hwre : y.re - 1 / 1024 ≤ w.re := by linarith [hbre]
  have hwre2 : w.re ≤ y.re + 1 / 1024 := by linarith [hbre2]
  have hwim : |y.im| - 1 / 1024 ≤ |w.im| := by
    have h := abs_sub_abs_le_abs_sub y.im w.im
    rw [abs_sub_comm] at h
    linarith [hbim]
  have hyre_ub : y.re ≤ -x + (|a.re| + |a.im|) * Real.log x + |b.re| := by
    rw [hyre]
    have h5 : (a * Complex.log (x : ℂ)).re ≤ (|a.re| + |a.im|) * Real.log x :=
      le_trans hA_re_ub (by linarith [hpi'])
    linarith [le_abs_self b.re]
  have hyim_lb : |a.im| * Real.log x - |a.re| * Real.pi - |b.im| ≤ |y.im| := by
    have h := abs_sub_abs_le_abs_sub ((a * Complex.log (x : ℂ)).im) (-b.im)
    rw [abs_neg] at h
    have h5 : (a * Complex.log (x : ℂ)).im - (-b.im)
        = (a * Complex.log (x : ℂ)).im + b.im := by ring
    rw [h5] at h
    rw [hyim]
    linarith [hA_im, h]
  -- ## 4. assembly
  have hnn1 : 0 ≤ |a.im| * Real.log x := mul_nonneg (abs_nonneg _) hlog0
  have hnn2 : 0 ≤ |a.im| * Real.pi := mul_nonneg (abs_nonneg _) Real.pi_pos.le
  rw [margB]
  linarith [hwre, hwre2, hwim, hyre_ub, hyim_lb, hlogpi, Real.pi_pos, hnn1, hnn2,
    abs_nonneg a.re, abs_nonneg a.im, abs_nonneg b.re, abs_nonneg b.im]

/-- **The `F0f`-step along the negative axis.**  For `x > ξ₀ + 1` the curve satisfies
`Xc d (-(x-1)) = F0f f₀ (Xc d (-x))` (i.e. it is an orbit of the limit model). -/
theorem Xc_F0f_step {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {x : ℝ} (hx : d.ξ₀ + 1 < x) :
    Work.Pert.F0f f₀ (Xc d (-(x : ℂ))) = Xc d (-((x - 1 : ℝ) : ℂ)) := by
  have hx1 : d.ξ₀ < x := by linarith
  have hQ : -(x : ℂ) ∈ d.Dφ :=
    d.Q_sub (Work.Parab.halfplane_subset_QLeft d.ξ₀ (by
      rw [Set.mem_ofPred_eq]; simp only [Complex.neg_re, Complex.ofReal_re]; linarith))
  have hQ1 : -(x : ℂ) + 1 ∈ d.Dφ :=
    d.Q_sub (Work.Parab.halfplane_subset_QLeft d.ξ₀ (by
      rw [Set.mem_ofPred_eq]
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
      linarith))
  have h := Work.Pert.Xc_add_one d hQ hQ1
  have heq : -(x : ℂ) + 1 = -((x - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [← h, heq]

/-- **The `F0f`-defect of the curve is at most `1/32` in the deep range.** -/
theorem F0f_defect_axis_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {x : ℝ} (hRpos : 0 < R) (hR1 : max R 1 + 1 ≤ x) (hξ : d.ξ₀ + 1 < x) (ha : 64 * ‖a‖ ≤ R) :
    ‖Work.Pert.F0f f₀ (Xc d (-(x : ℂ))) - (Xc d (-(x : ℂ)) + 1)‖ ≤ 1 / 32 := by
  rw [Xc_F0f_step d hξ]
  have hmR : R ≤ max R 1 := le_max_left R (1 : ℝ)
  have hm1 : (1 : ℝ) ≤ max R 1 := le_max_right R (1 : ℝ)
  have hxR : R ≤ x - 1 := by linarith
  have hxpos : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  have hcast : (((x - 1 : ℝ)) : ℂ) = (x : ℂ) - 1 := by push_cast; ring
  set u₁ : ℂ := -(((x - 1 : ℝ)) : ℂ) + a * Complex.log (((x - 1 : ℝ)) : ℂ) + b with hu1
  set L₂ : ℂ := Complex.log (x : ℂ) with hL2
  set u₂ : ℂ := -(x : ℂ) + a * L₂ + b with hu2
  have h₁ : ‖Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁‖ ≤ 1 / 1024 := hasym (x - 1) hxR
  have h₂ : ‖Xc d (-(x : ℂ)) - u₂‖ ≤ 1 / 1024 := hasym x (by linarith)
  have hkey : Xc d (-(((x - 1 : ℝ)) : ℂ)) - (Xc d (-(x : ℂ)) + 1)
      = (Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁) - (Xc d (-(x : ℂ)) - u₂)
        + a * (Complex.log (((x - 1 : ℝ)) : ℂ) - L₂) := by
    rw [hu1, hu2, hcast]; ring
  rw [hkey]
  have h3 : ‖(Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁) - (Xc d (-(x : ℂ)) - u₂)
      + a * (Complex.log (((x - 1 : ℝ)) : ℂ) - L₂)‖
      ≤ ‖Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁‖ + ‖Xc d (-(x : ℂ)) - u₂‖
        + ‖a * (Complex.log (((x - 1 : ℝ)) : ℂ) - L₂)‖ := by
    have h4 := norm_add_le ((Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁) - (Xc d (-(x : ℂ)) - u₂))
      (a * (Complex.log (((x - 1 : ℝ)) : ℂ) - L₂))
    have h5 := norm_sub_le (Xc d (-(((x - 1 : ℝ)) : ℂ)) - u₁) (Xc d (-(x : ℂ)) - u₂)
    linarith
  have hlog : ‖Complex.log (((x - 1 : ℝ)) : ℂ) - L₂‖ ≤ 1 / (x - 1) := by
    have h1 : Complex.log (((x - 1 : ℝ)) : ℂ) = ((Real.log (x - 1) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log (le_of_lt hxpos)]
    have h2 : L₂ = ((Real.log x : ℝ) : ℂ) := by
      rw [hL2, ← Complex.ofReal_log (le_of_lt hx0)]
    have h3 : Real.log x - Real.log (x - 1) = Real.log (x / (x - 1)) := by
      rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hxpos)]
    have h4 : x / (x - 1) = 1 + 1 / (x - 1) := by field_simp; ring
    have h5 : Real.log (1 + 1 / (x - 1)) ≤ 1 / (x - 1) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (x - 1) by positivity)
      simpa using this
    rw [h1, h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by
        have h6 := Real.log_le_log hxpos (by linarith : x - 1 ≤ x)
        linarith)]
    rw [neg_sub, h3, h4]
    exact h5
  have h6 : ‖a * (Complex.log (((x - 1 : ℝ)) : ℂ) - L₂)‖ ≤ ‖a‖ * (1 / (x - 1)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
  have h7 : ‖a‖ * (1 / (x - 1)) + 2 * (1 / 1024) ≤ 1 / 32 := by
    have h9 : ‖a‖ * (1 / (x - 1)) ≤ ‖a‖ * (1 / R) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
      exact one_div_le_one_div_of_le hRpos hxR
    have h10 : ‖a‖ * (1 / R) ≤ 1 / 64 := by
      rw [mul_one_div, div_le_iff₀ hRpos]
      linarith
    linarith
  linarith


/-- **The `margA` margin along the walk.**  With `a, b, R` as in `exists_Xc_axis_asym`, for
`x ≥ R` the `margA`-margin of `Xc d (-x)` is at least
`(1/α).re + |(1/α).im| - x - K log x - C` with datum-level `K, C`. -/
theorem margA_Xc_axis_ge {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {Ξ : ℝ} {x : ℝ} (hR : R ≤ x) (hexp : Real.exp Real.pi ≤ x) :
    (1 / α).re + |(1 / α).im| - x
        - (2 * (|a.re| + |a.im|) * Real.log x
            + (2 * (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 4)) ≤
      margA Ξ α (Xc d (-(x : ℂ))) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by rw [Real.one_le_exp_iff]; exact Real.pi_pos.le) hexp
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlogpi : Real.pi ≤ Real.log x := by
    rw [← Real.log_exp Real.pi]; exact Real.log_le_log (Real.exp_pos _) hexp
  have hlog0 : 0 ≤ Real.log x := le_trans Real.pi_pos.le hlogpi
  set w : ℂ := Xc d (-(x : ℂ)) with hwdef
  have hclose : ‖w - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024 := hasym x hR
  have hbre : -(1 / 1024) ≤ (w - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)).re :=
    (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hclose)).1
  have hbim : |(w - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)).im| ≤ 1 / 1024 :=
    le_trans (Complex.abs_im_le_norm _) hclose
  have hlogre : (Complex.log (x : ℂ)).re = Real.log x := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le]
  have hloglo : -Real.pi ≤ (Complex.log (x : ℂ)).im := (Complex.neg_pi_lt_log_im _).le
  have hloghi : (Complex.log (x : ℂ)).im ≤ Real.pi := Complex.log_im_le_pi _
  have hAre : -((|a.re| + |a.im|) * Real.log x) ≤ (a * Complex.log (x : ℂ)).re := by
    rw [Complex.mul_re, hlogre]
    have h1 : -(|a.re| * Real.log x) ≤ a.re * Real.log x := by
      have h := mul_le_mul_of_nonneg_right (neg_abs_le a.re) hlog0
      rwa [neg_mul] at h
    have h2 : a.im * (Complex.log (x : ℂ)).im ≤ |a.im| * Real.pi := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hloglo, hloghi⟩) (abs_nonneg _)
    nlinarith [h1, h2, hlogpi, Real.pi_pos, abs_nonneg a.re, abs_nonneg a.im]
  have hAim : |(a * Complex.log (x : ℂ)).im| ≤ |a.re| * Real.pi + |a.im| * Real.log x := by
    rw [Complex.mul_im, hlogre]
    have h1 : |a.re * (Complex.log (x : ℂ)).im| ≤ |a.re| * Real.pi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hloglo, hloghi⟩) (abs_nonneg _)
    have h2 : |a.im * Real.log x| = |a.im| * Real.log x := by
      simp only [abs_mul, abs_of_nonneg hlog0]
    have h3 : |a.re * (Complex.log (x : ℂ)).im + a.im * Real.log x|
        ≤ |a.re * (Complex.log (x : ℂ)).im| + |a.im * Real.log x| := abs_add_le _ _
    rw [h2] at h3; linarith
  -- the real part of `w`
  have hYre : (-(x : ℂ) + a * Complex.log (x : ℂ) + b).re
      = -x + (a * Complex.log (x : ℂ)).re + b.re := by simp
  have hwre : -x - (|a.re| + |a.im|) * Real.log x - |b.re| - 1 ≤ w.re := by
    have h2 : w.re - (-(x : ℂ) + a * Complex.log (x : ℂ) + b).re ≥ -(1 / 1024) := by
      simpa only [Complex.sub_re] using hbre
    rw [hYre] at h2
    have h4 : -|b.re| ≤ b.re := neg_abs_le b.re
    linarith [hAre]
  -- the imaginary part of `w`
  have hYim : (-(x : ℂ) + a * Complex.log (x : ℂ) + b).im
      = (a * Complex.log (x : ℂ)).im + b.im := by simp
  have hwim : |w.im| ≤ |a.re| * Real.pi + |a.im| * Real.log x + |b.im| + 1 := by
    have h2 : |w.im - (-(x : ℂ) + a * Complex.log (x : ℂ) + b).im| ≤ 1 / 1024 := by
      simpa only [Complex.sub_im] using hbim
    rw [hYim] at h2
    have h3 : |w.im| ≤ |w.im - ((a * Complex.log (x : ℂ)).im + b.im)|
        + |(a * Complex.log (x : ℂ)).im + b.im| := by
      have h := abs_add_le (w.im - ((a * Complex.log (x : ℂ)).im + b.im))
        ((a * Complex.log (x : ℂ)).im + b.im)
      have h4 : (w.im - ((a * Complex.log (x : ℂ)).im + b.im))
          + ((a * Complex.log (x : ℂ)).im + b.im) = w.im := by ring
      rwa [h4] at h
    have h5 : |(a * Complex.log (x : ℂ)).im + b.im|
        ≤ |(a * Complex.log (x : ℂ)).im| + |b.im| := abs_add_le _ _
    linarith [hAim]
  rw [margA]
  have h6 : |w.im + (1 / α).im| ≥ |(1 / α).im| - |w.im| := by
    have h := abs_sub_abs_le_abs_sub ((1 / α).im) (-w.im)
    rw [abs_neg] at h
    have h7 : (1 / α).im - (-w.im) = w.im + (1 / α).im := by ring
    rw [h7] at h; linarith
  have hA0 : (|a.re| + |a.im|) * Real.log x
      = |a.re| * Real.log x + |a.im| * Real.log x := by ring
  have hA1 : (|a.re| + |a.im|) * Real.pi
      = |a.re| * Real.pi + |a.im| * Real.pi := by ring
  nlinarith [hwre, hwim, h6, hA0, hA1, hlogpi, Real.pi_pos, abs_nonneg a.re, abs_nonneg a.im,
    abs_nonneg b.re, abs_nonneg b.im, abs_nonneg (1 / α).im,
    mul_nonneg (abs_nonneg a.re) hlog0, mul_nonneg (abs_nonneg a.im) hlog0,
    mul_nonneg (abs_nonneg a.re) Real.pi_pos.le, mul_nonneg (abs_nonneg a.im) Real.pi_pos.le]

end

end Work.Pert.PinLogDev
