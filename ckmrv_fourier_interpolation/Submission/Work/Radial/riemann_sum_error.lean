import Mathlib

namespace Work.Radial

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- Error of the left-endpoint rectangle rule on a single interval `[p, q]`:
if `g` has derivative `g'` with `‖g'‖ ≤ M` on `[p, q]`, then
`‖∫_p^q g - (q - p) * g p‖ ≤ M * (q - p)^2 / 2`. -/
private lemma rect_error (g g' : ℝ → ℂ) {p q M : ℝ} (hpq : p ≤ q)
    (hd : ∀ u ∈ Set.Icc p q, HasDerivAt g (g' u) u)
    (hb : ∀ u ∈ Set.Icc p q, ‖g' u‖ ≤ M) :
    ‖(∫ u in p..q, g u) - (q - p) * g p‖ ≤ M * (q - p) ^ 2 / 2 := by
  have hcont : ContinuousOn g (Set.Icc p q) :=
    fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hui : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hgi : IntervalIntegrable g volume p q := by
    have : ContinuousOn g (Set.uIcc p q) := by rwa [hui]
    exact this.intervalIntegrable
  -- `∫ (g - g p) = ∫ g - (q - p) * g p`
  have hkey : (∫ u in p..q, (g u - g p)) = (∫ u in p..q, g u) - (q - p) * g p := by
    rw [intervalIntegral.integral_sub hgi intervalIntegrable_const, intervalIntegral.integral_const]
    simp [Complex.real_smul]
  rw [← hkey]
  calc ‖∫ u in p..q, (g u - g p)‖
      ≤ ∫ u in p..q, ‖g u - g p‖ := intervalIntegral.norm_integral_le_integral_norm hpq
    _ ≤ ∫ u in p..q, M * (u - p) := by
        apply intervalIntegral.integral_mono_on hpq
        · have : ContinuousOn (fun u => ‖g u - g p‖) (Set.uIcc p q) := by
            rw [hui]; exact (hcont.sub continuousOn_const).norm
          exact this.intervalIntegrable
        · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable p q
        · intro u hu
          -- mean value bound: `‖g u - g p‖ ≤ M * (u - p)`
          have hdiff : ∀ v ∈ Set.Icc p q, DifferentiableAt ℝ g v :=
            fun v hv => (hd v hv).differentiableAt
          have hdb : ∀ v ∈ Set.Icc p q, ‖deriv g v‖ ≤ M := fun v hv => by
            rw [(hd v hv).deriv]; exact hb v hv
          have h2 := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hdb (convex_Icc p q)
            (⟨le_refl p, hpq⟩ : p ∈ Set.Icc p q) hu
          rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu.1)] at h2
          exact h2
    _ = M * (q - p) ^ 2 / 2 := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => M * x) p]
        rw [intervalIntegral.integral_const_mul]
        rw [integral_id]
        ring

/-- Riemann-sum (left rectangle rule) error estimate: for `a ≤ b`, `N > 0`, and `g` with
derivative `g'` bounded by `M` on `[a, b]`, the left-endpoint Riemann sum with `N` equal
subintervals approximates `∫_a^b g` with error at most `M * (b - a)^2 / (2 * N)`. -/
theorem riemann_sum_error (g g' : ℝ → ℂ) {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) {N : ℕ} (hN : 0 < N)
    (hd : ∀ u ∈ Set.Icc a b, HasDerivAt g (g' u) u)
    (hb : ∀ u ∈ Set.Icc a b, ‖g' u‖ ≤ M) :
    ‖(∫ u in a..b, g u) - ((b - a) / N) *
        ∑ k ∈ Finset.range N, g (a + k * ((b - a) / N))‖ ≤ M * (b - a) ^ 2 / (2 * N) := by
  have _hM := hM
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  set h : ℝ := (b - a) / N with hh
  have hnonneg : 0 ≤ h := by rw [hh]; exact div_nonneg (sub_nonneg.mpr hab) hNpos.le
  have hba : (N:ℝ) * h = b - a := by rw [hh]; field_simp
  let x : ℕ → ℝ := fun k => a + (k:ℝ) * h
  have hx0 : x 0 = a := by simp [x]
  have hxN : x N = b := by
    simp only [x]
    rw [hba]
    ring
  have hxmono : ∀ k < N, x k ≤ x (k+1) := by
    intro k hk
    have hk' : (k:ℝ) ≤ ((k:ℝ) + 1) := by linarith
    have hm : (k:ℝ) * h ≤ ((k:ℝ) + 1) * h := mul_le_mul_of_nonneg_right hk' hnonneg
    simp only [x]
    push_cast
    linarith
  have ha_le_x : ∀ k, a ≤ x k := by
    intro k
    have hm : (0:ℝ) ≤ (k:ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hnonneg
    simp only [x]
    linarith
  have hx_le_b : ∀ k ≤ N, x k ≤ b := by
    intro k hk
    have hk' : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk
    have hm : (k:ℝ) * h ≤ (N:ℝ) * h := mul_le_mul_of_nonneg_right hk' hnonneg
    simp only [x]
    linarith [hba]
  have hcont : ContinuousOn g (Set.Icc a b) :=
    fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hsub : ∀ k < N, Set.Icc (x k) (x (k+1)) ⊆ Set.Icc a b := by
    intro k hk u hu
    exact ⟨le_trans (ha_le_x k) hu.1, le_trans hu.2 (hx_le_b (k+1) (by omega))⟩
  -- split the integral over the `N` subintervals
  have hsplit : ∫ u in a..b, g u = ∑ k ∈ Finset.range N, ∫ u in x k..x (k+1), g u := by
    have hInt : ∀ k < N, IntervalIntegrable g volume (x k) (x (k+1)) := by
      intro k hk
      have hc : ContinuousOn g (Set.Icc (x k) (x (k+1))) := hcont.mono (hsub k hk)
      have : ContinuousOn g (Set.uIcc (x k) (x (k+1))) := by
        rwa [Set.uIcc_of_le (hxmono k hk)]
      exact this.intervalIntegrable
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g) (a := x)
      (n := N) hInt
    rw [hx0, hxN] at this
    exact this.symm
  -- per-subinterval error bound
  have hterm : ∀ k < N, ‖(∫ u in x k..x (k+1), g u) - h * g (x k)‖ ≤ M * h ^ 2 / 2 := by
    intro k hk
    have hd' : ∀ u ∈ Set.Icc (x k) (x (k+1)), HasDerivAt g (g' u) u :=
      fun u hu => hd u (hsub k hk hu)
    have hb' : ∀ u ∈ Set.Icc (x k) (x (k+1)), ‖g' u‖ ≤ M := fun u hu => hb u (hsub k hk hu)
    have hres := rect_error g g' (hxmono k hk) hd' hb'
    have hreal : x (k+1) - x k = h := by simp only [x]; push_cast; ring
    have hdiff : ((x (k+1) : ℂ) - (x k : ℂ)) = (h : ℂ) := by
      rw [← Complex.ofReal_sub, hreal]
    rw [hdiff, hreal] at hres
    exact hres
  have hkey : (∫ u in a..b, g u) - h * ∑ k ∈ Finset.range N, g (x k)
      = ∑ k ∈ Finset.range N, ((∫ u in x k..x (k+1), g u) - h * g (x k)) := by
    rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- rewrite the complex-valued factor `(b - a) / N` using `h`
  have hcast : (((b : ℂ) - (a : ℂ)) / (N : ℂ)) = (h : ℂ) := by
    rw [hh]; push_cast; ring
  rw [hcast]
  change ‖(∫ u in a..b, g u) - h * ∑ k ∈ Finset.range N, g (x k)‖
    ≤ M * (b - a) ^ 2 / (2 * ↑N)
  calc ‖(∫ u in a..b, g u) - h * ∑ k ∈ Finset.range N, g (x k)‖
      = ‖∑ k ∈ Finset.range N, ((∫ u in x k..x (k+1), g u) - h * g (x k))‖ := by rw [hkey]
    _ ≤ ∑ k ∈ Finset.range N, ‖(∫ u in x k..x (k+1), g u) - h * g (x k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, M * h ^ 2 / 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k (Finset.mem_range.mp hk)
    _ = M * (b - a) ^ 2 / (2 * ↑N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hba, eq_div_iff (by positivity)]
        ring

end Work.Radial
