/-
# The lattice-sum (Euler–Maclaurin) estimate for Area A6

Fix a pitch `h > 0` and a shift `a`.  Writing `x_m = (m + a) * h = m * h + a * h`, the intervals
`I_m = (x_m, x_m + h]` tile `ℝ`, and for a differentiable `g` with integrable derivative we prove

* `Summable (fun m : ℤ => g (x_m))`;
* `∑'_m ‖g x_m‖ ≤ h⁻¹ * ∫ ‖g‖ + ∫ ‖g'‖`  (a discrete `L¹` sampling bound);
* `|∑'_m g (x_m) * h - ∫ g| ≤ h * ∫ ‖g'‖` (the Riemann-sum error estimate).

The three auxiliary lemmas are the tiling of `ℝ` by the translates of `Ioc` at pitch `h`
(`latticeSum_tiling`), the interval mean-value bound for a differentiable function with
integrable derivative (`latticeSum_interval_pointwise`), and the per-cell Riemann-sum error
(`latticeSum_interval_error`); they are combined by summing over `m : ℤ`.
-/
import Mathlib

open scoped Function

namespace Work.KMTPlan.A6

open MeasureTheory

/-- **Tiling identity.** Registered as a `HasSum` (hence unconditionally convergent) tiling of
`ℝ` by the translates `(m * h + c, m * h + c + h]` of a half-open interval of length `h > 0`:
the integral of an integrable function is the sum of its integrals over the cells. -/
theorem latticeSum_tiling (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f)
    {c h : ℝ} (hh : 0 < h) :
    HasSum (fun m : ℤ => ∫ x in ((m : ℝ) * h + c)..((m : ℝ) * h + c + h), f x)
      (∫ x : ℝ, f x) := by
  have hfun : (fun m : ℤ => Set.Ioc ((m:ℝ)*h + c) ((m:ℝ)*h + c + h))
      = (fun m : ℤ => Set.Ioc (c + m • h) (c + (m + 1) • h)) := by
    funext m
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]
    congr 1 <;> ring
  have hcov : (⋃ m : ℤ, Set.Ioc ((m:ℝ)*h + c) ((m:ℝ)*h + c + h)) = Set.univ := by
    rw [hfun]; exact iUnion_Ioc_add_zsmul (p := h) hh c
  have hdisj : Pairwise (Disjoint on fun m : ℤ => Set.Ioc ((m:ℝ)*h + c) ((m:ℝ)*h + c + h)) := by
    rw [hfun]; exact Set.pairwise_disjoint_Ioc_add_zsmul c h
  rw [← MeasureTheory.setIntegral_univ]
  simp_rw [intervalIntegral.integral_of_le (f := f) (le_add_of_nonneg_right hh.le)]
  rw [← hcov]
  exact MeasureTheory.hasSum_integral_iUnion (fun m => measurableSet_Ioc) hdisj
    (by rw [hcov]; exact hf.integrableOn)

/-- **Interval mean-value bound.** For a differentiable `g` with integrable derivative and
`h > 0`: the oscillation of `g` over `[x, x+h]` is dominated by `∫_x^{x+h} ‖g'‖`, and the same
majorant bounds `h * ‖g x‖` against `∫_x^{x+h} ‖g‖`. -/
theorem latticeSum_interval_pointwise (g : ℝ → ℝ) (hd : Differentiable ℝ g)
    (hg' : MeasureTheory.Integrable (deriv g)) {x h : ℝ} (hh : 0 < h) :
    (∀ t ∈ Set.Icc x (x + h), ‖g x - g t‖ ≤ ∫ y in x..(x + h), ‖deriv g y‖) ∧
    h * ‖g x‖ ≤ (∫ y in x..(x + h), ‖g y‖) + h * ∫ y in x..(x + h), ‖deriv g y‖ := by
  have hxh : x ≤ x + h := by linarith
  have hnorm : IntervalIntegrable (fun y => ‖deriv g y‖) volume x (x + h) :=
    hg'.intervalIntegrable.norm
  have key : ∀ t ∈ Set.Icc x (x + h), ‖g x - g t‖ ≤ ∫ y in x..(x + h), ‖deriv g y‖ := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hxt | rfl
    · have hint : IntervalIntegrable (deriv g) volume x t := hg'.intervalIntegrable
      have hftc : ∫ y in x..t, deriv g y = g t - g x :=
        intervalIntegral.integral_deriv_eq_sub (fun y _ => hd y) hint
      have h1 : ‖g x - g t‖ ≤ ∫ y in x..t, ‖deriv g y‖ := by
        rw [norm_sub_rev, ← hftc]
        exact intervalIntegral.norm_integral_le_integral_norm hxt.le
      have h2 : ∫ y in x..t, ‖deriv g y‖ ≤ ∫ y in x..(x + h), ‖deriv g y‖ :=
        intervalIntegral.integral_mono_interval (le_refl x) hxt.le ht.2
          (Filter.Eventually.of_forall fun y => norm_nonneg _) hnorm
      exact h1.trans h2
    · simp only [sub_self, norm_zero]
      exact intervalIntegral.integral_nonneg hxh (fun u _ => norm_nonneg _)
  refine ⟨key, ?_⟩
  have hpt : ∀ u ∈ Set.Icc x (x + h), ‖g x‖ ≤ ‖g u‖ + ∫ y in x..(x + h), ‖deriv g y‖ := by
    intro u hu
    have := key u hu
    calc ‖g x‖ = ‖g u + (g x - g u)‖ := by congr 1; ring
      _ ≤ ‖g u‖ + ‖g x - g u‖ := norm_add_le _ _
      _ ≤ ‖g u‖ + ∫ y in x..(x + h), ‖deriv g y‖ := by linarith
  have hIg : IntervalIntegrable (fun u => ‖g u‖ + ∫ y in x..(x + h), ‖deriv g y‖)
      volume x (x + h) :=
    (hd.continuous.norm.intervalIntegrable x (x + h)).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hxh intervalIntegrable_const hIg hpt
  rw [intervalIntegral.integral_const,
      intervalIntegral.integral_add (hd.continuous.norm.intervalIntegrable x (x + h))
        intervalIntegrable_const,
      intervalIntegral.integral_const] at hmono
  rw [show x + h - x = h by ring] at hmono
  simpa only [smul_eq_mul] using hmono

/-- **Per-cell Riemann-sum error.** `h * g x` is the integral of the constant approximation `g x`
to `g` on `[x, x+h]`, and the error is at most `h * ∫_x^{x+h} ‖g'‖`. -/
theorem latticeSum_interval_error (g : ℝ → ℝ) (hd : Differentiable ℝ g)
    (hg' : MeasureTheory.Integrable (deriv g)) {x h : ℝ} (hh : 0 < h) :
    ‖h * g x - ∫ y in x..(x + h), g y‖ ≤ h * ∫ y in x..(x + h), ‖deriv g y‖ := by
  have hxh : x ≤ x + h := by linarith
  have hIg : IntervalIntegrable g volume x (x + h) := hd.continuous.intervalIntegrable x (x + h)
  have hE : h * g x - ∫ y in x..(x + h), g y = ∫ y in x..(x + h), (g x - g y) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIg,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  rw [hE]
  calc ‖∫ y in x..(x + h), (g x - g y)‖ ≤ ∫ y in x..(x + h), ‖g x - g y‖ :=
        intervalIntegral.norm_integral_le_integral_norm hxh
    _ ≤ ∫ y in x..(x + h), (∫ z in x..(x + h), ‖deriv g z‖) := by
        refine intervalIntegral.integral_mono_on hxh
          ((continuous_const.sub hd.continuous).norm.intervalIntegrable x (x + h))
          intervalIntegrable_const ?_
        intro y hy
        exact (latticeSum_interval_pointwise g hd hg' hh).1 y hy
    _ = h * ∫ z in x..(x + h), ‖deriv g z‖ := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show x + h - x = h by ring]

/-- **Lattice sum bound.** For a differentiable `g` with integrable derivative, the values of `g`
on the lattice `{(m + a) * h : m ∈ ℤ}` are summable, with the discrete `L¹` bound
`∑'_m ‖g ((m+a) * h)‖ ≤ h⁻¹ ∫ ‖g‖ + ∫ ‖g'‖`, and the rectangle rule
`∑'_m g ((m+a)*h) * h` differs from `∫ g` by at most `h ∫ ‖g'‖`. -/
theorem latticeSum_bound
    {g : ℝ → ℝ} (hd : Differentiable ℝ g) (hg : MeasureTheory.Integrable g)
    (hg' : MeasureTheory.Integrable (deriv g)) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    Summable (fun m : ℤ => g (((m : ℝ) + a) * h)) ∧
    (∑' m : ℤ, ‖g (((m : ℝ) + a) * h)‖) ≤ h⁻¹ * (∫ t : ℝ, ‖g t‖) + ∫ t : ℝ, ‖deriv g t‖ ∧
    |(∑' m : ℤ, g (((m : ℝ) + a) * h) * h) - ∫ t : ℝ, g t| ≤ h * ∫ t : ℝ, ‖deriv g t‖ := by
  have hxm : ∀ m : ℤ, ((m : ℝ) + a) * h = (m : ℝ) * h + a * h := fun m => by ring
  have hA := latticeSum_tiling (fun x => ‖g x‖) hg.norm (c := a * h) (h := h) hh
  have hB := latticeSum_tiling (fun x => ‖deriv g x‖) hg'.norm (c := a * h) (h := h) hh
  have hC := latticeSum_tiling g hg (c := a * h) (h := h) hh
  -- discrete sampling bound, cell by cell
  have hb : ∀ m : ℤ, ‖g (((m:ℝ)+a)*h)‖ ≤
      h⁻¹ * ((∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖g x‖)
        + h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖) := by
    intro m
    have h2 := (latticeSum_interval_pointwise g hd hg' (x := (m:ℝ)*h + a*h) (h := h) hh).2
    calc ‖g (((m:ℝ)+a)*h)‖ = h⁻¹ * (h * ‖g (((m:ℝ)+a)*h)‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh), one_mul]
      _ = h⁻¹ * (h * ‖g ((m:ℝ)*h + a*h)‖) := by rw [hxm m]
      _ ≤ h⁻¹ * ((∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖g x‖)
            + h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hh))
  have hRHSsum : Summable (fun m : ℤ => h⁻¹ *
      ((∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖g x‖)
        + h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖)) :=
    (hA.summable.add (hB.summable.mul_left h)).mul_left h⁻¹
  have hsum_norm : Summable (fun m : ℤ => ‖g (((m:ℝ)+a)*h)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb hRHSsum
  have htsum_bound :
      (∑' m : ℤ, ‖g (((m:ℝ)+a)*h)‖) ≤ h⁻¹ * (∫ t : ℝ, ‖g t‖) + ∫ t : ℝ, ‖deriv g t‖ := by
    have hts := Summable.tsum_le_tsum hb hsum_norm hRHSsum
    have heq : (∑' m : ℤ, h⁻¹ *
          ((∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖g x‖)
            + h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖))
        = h⁻¹ * (∫ t : ℝ, ‖g t‖) + ∫ t : ℝ, ‖deriv g t‖ := by
      rw [tsum_mul_left, Summable.tsum_add hA.summable (hB.summable.mul_left h),
        tsum_mul_left, hA.tsum_eq, hB.tsum_eq, mul_add, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hh), one_mul]
    rwa [heq] at hts
  have hsumm : Summable (fun m : ℤ => g (((m:ℝ)+a)*h)) :=
    hsum_norm.of_norm_bounded (fun m => le_refl _)
  -- Riemann-sum error
  have hE : HasSum (fun m : ℤ =>
        h * g (((m:ℝ)+a)*h) - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x)
      (h * (∑' m : ℤ, g (((m:ℝ)+a)*h)) - ∫ x : ℝ, g x) := by
    have h1 : HasSum (fun m : ℤ => h * g (((m:ℝ)+a)*h))
        (h * (∑' m : ℤ, g (((m:ℝ)+a)*h))) := hsumm.hasSum.mul_left h
    exact h1.sub hC
  have hEbound : ∀ m : ℤ,
      ‖h * g (((m:ℝ)+a)*h) - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x‖
      ≤ h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖ := by
    intro m
    rw [hxm m]
    exact latticeSum_interval_error g hd hg' (x := (m:ℝ)*h + a*h) (h := h) hh
  have hsumE : Summable (fun m : ℤ =>
      h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖) :=
    hB.summable.mul_left h
  have hsumEn : Summable (fun m : ℤ =>
      ‖h * g (((m:ℝ)+a)*h) - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hEbound hsumE
  have hfinal : ‖∑' m : ℤ,
        (h * g (((m:ℝ)+a)*h) - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x)‖
      ≤ h * ∫ t : ℝ, ‖deriv g t‖ := by
    calc ‖∑' m : ℤ,
          (h * g (((m:ℝ)+a)*h) - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x)‖
        ≤ ∑' m : ℤ, ‖h * g (((m:ℝ)+a)*h)
            - ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), g x‖ :=
          norm_tsum_le_tsum_norm hsumEn
      _ ≤ ∑' m : ℤ, h * ∫ x in ((m:ℝ)*h + a*h)..((m:ℝ)*h + a*h + h), ‖deriv g x‖ :=
          Summable.tsum_le_tsum hEbound hsumEn hsumE
      _ = h * ∫ t : ℝ, ‖deriv g t‖ := by rw [tsum_mul_left, hB.tsum_eq]
  have hfin : ‖(∑' m : ℤ, g (((m:ℝ)+a)*h) * h) - ∫ t : ℝ, g t‖
      ≤ h * ∫ t : ℝ, ‖deriv g t‖ := by
    rw [tsum_mul_right, mul_comm (∑' m : ℤ, g (((m:ℝ)+a)*h)) h, ← hE.tsum_eq]
    exact hfinal
  exact ⟨hsumm, htsum_bound, by simpa only [Real.norm_eq_abs] using hfin⟩

end Work.KMTPlan.A6
