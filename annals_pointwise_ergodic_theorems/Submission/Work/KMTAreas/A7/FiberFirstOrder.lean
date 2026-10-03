import Mathlib
import Submission.Work.A7.fiber_stepQ_trapezoid
import Submission.Work.A7.fiber_exists_mod_eq
import Submission.Work.KMTAreas.A7.unit_step_lipschitz_trapezoid
import Submission.Work.KMTAreas.A7.hull_integral_bound_c1

namespace Work.KMTAreas.A7

open MeasureTheory intervalIntegral


/-! ## The Lipschitz (mean value) bound implied by a bound on the derivative -/

/-- If `V` is of class `C¹` on `ℝ` and `‖deriv V‖ ≤ B₁` on `[K,N]`, then `V` is `B₁`-Lipschitz on
`[K,N]`. -/
lemma norm_sub_le_of_deriv_bound (V : ℝ → ℂ) (hV : ContDiff ℝ 1 V) {K N : ℕ} {B₁ : ℝ}
    (hB' : ∀ u ∈ Set.Icc (K : ℝ) (N : ℝ), ‖deriv V u‖ ≤ B₁) :
    ∀ x ∈ Set.Icc (K : ℝ) (N : ℝ), ∀ y ∈ Set.Icc (K : ℝ) (N : ℝ),
      ‖V y - V x‖ ≤ B₁ * |y - x| := by
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := V) (s := Set.Icc (K : ℝ) (N : ℝ)) (x := x) (y := y) (C := B₁)
    (fun z _ => hV.differentiable_one z) hB' (convex_Icc _ _) hx hy
  simpa [Real.norm_eq_abs] using h

/-- First-order (mean-value) comparison of the sum over one residue-class fibre with the integral
over the whole window: for `V : ℝ → ℂ` with `‖V‖ ≤ B` and `‖V'‖ ≤ B₁` on `[K,N]`, `q > 0`,
`a < q`, `K ≤ N`, the sum of `V` over the integers of `(K,N]` congruent to `a` mod `q` differs
from `q⁻¹∫_K^N V` by at most `3B + N·B₁`. -/
theorem FiberFirstOrder (V : ℝ → ℂ) {K N q a : ℕ} (hKN : K ≤ N) (hq : 0 < q) (ha : a < q)
    {B B₁ : ℝ} (hB0 : 0 ≤ B) (hB1 : 0 ≤ B₁)
    (hB : ∀ u ∈ Set.Icc (K : ℝ) (N : ℝ), ‖V u‖ ≤ B)
    (hV : ContDiff ℝ 1 V)
    (hB' : ∀ u ∈ Set.Icc (K : ℝ) (N : ℝ), ‖deriv V u‖ ≤ B₁) :
    ‖(∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ))
        - (q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u‖
      ≤ 3 * B + (N : ℝ) * B₁ := by
  classical
  have hKN' : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKN
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hcont : Continuous V := hV.continuous
  have hLipV := norm_sub_le_of_deriv_bound V hV hB'
  by_cases hFib : ((Finset.Ioc K N).filter (fun n => n % q = a)).Nonempty
  · -- ===================== nonempty fibre =====================
    obtain ⟨n₀, hn₀⟩ := hFib
    have hn₀' : K < n₀ ∧ n₀ ≤ N ∧ n₀ % q = a := by
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn₀
      exact ⟨hn₀.1.1, hn₀.1.2, hn₀.2⟩
    have haN : a ≤ N := by
      rw [← hn₀'.2.2]
      exact le_trans (Nat.mod_le n₀ q) hn₀'.2.1
    set m₁ : ℤ := Work.A7.mFirst q K a with hm₁
    set m₂ : ℤ := Work.A7.mLast q N a with hm₂
    set r₁ : ℝ := (a : ℝ) + (q : ℝ) * (m₁ : ℝ) with hr₁def
    set r₂ : ℝ := (a : ℝ) + (q : ℝ) * (m₂ : ℝ) with hr₂def
    have hm12 : m₁ ≤ m₂ :=
      le_trans (Work.A7.mFirst_le_div q hq ha hn₀'.2.2 hn₀'.1)
        (Work.A7.div_le_mLast q hq ha hn₀'.2.2 hn₀'.2.1)
    have hmb1 := Work.A7.mFirst_bounds q K a hq ha
    have hmb2 := Work.A7.mLast_bounds q N a hq haN
    have hKr1 : (K : ℝ) ≤ r₁ := le_of_lt hmb1.1
    have hr12 : r₁ ≤ r₂ := by
      have hmR : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm12
      have h := mul_le_mul_of_nonneg_left hmR hqnn
      linarith
    have hr2N : r₂ ≤ (N : ℝ) := hmb2.2
    have hr1q : r₁ ≤ (K : ℝ) + (q : ℝ) := hmb1.2
    have hr2q : (N : ℝ) - (q : ℝ) < r₂ := hmb2.1
    have hBr1 : ‖V r₁‖ ≤ B := hB r₁ ⟨hKr1, le_trans hr12 hr2N⟩
    have hBr2 : ‖V r₂‖ ≤ B := hB r₂ ⟨le_trans hKr1 hr12, hr2N⟩
    -- reindex the fibre sum as a sum over the progression `m ↦ a + q m`
    have hreindex : (∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ))
        = ∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)) := by
      have h1 := Work.A7.sum_filter_mod_eq_sum_Icc q hq a ha K N (fun z : ℤ => V (z : ℝ))
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h1
      exact h1
    -- first-order comparison on the progression
    have hkey := unit_step_lipschitz_trapezoid (fun t : ℝ => V ((a : ℝ) + (q : ℝ) * t))
      (hcont.comp (by fun_prop)) hm12 hB0 (mul_nonneg hqnn hB1) hBr1 hBr2 ?_
    · -- change of variables `t ↦ a + q t`
      have hI1 : (∫ t in (m₁ : ℝ)..(m₂ : ℝ), V ((a : ℝ) + (q : ℝ) * t))
          = (q : ℝ)⁻¹ * ∫ x in r₁..r₂, V x := by
        rw [Work.A7.integral_comp_affine V (q : ℝ) hqR (a : ℝ) (m₁ : ℝ) (m₂ : ℝ),
          Complex.real_smul]
      have hdelta : r₂ - r₁ = (q : ℝ) * ((m₂ : ℝ) - (m₁ : ℝ)) := by
        simp only [hr₁def, hr₂def]
        ring
      have hT : ‖(∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)))
            - (q : ℝ)⁻¹ * ∫ x in r₁..r₂, V x‖ ≤ B + B₁ * (r₂ - r₁) / 2 := by
        rw [hI1] at hkey
        have hlin : ((q : ℝ) * B₁) * ((m₂ : ℝ) - (m₁ : ℝ)) / 2 = B₁ * (r₂ - r₁) / 2 := by
          rw [hdelta]
          ring
        rwa [hlin] at hkey
      -- the hull comparison
      have hH := hull_integral_bound_c1 V hcont (B := B) q K N r₁ r₂ hB hKr1 hr12 hr2N hr1q hr2q
      have h2nd : ‖(q : ℝ)⁻¹ * ((∫ x in r₁..r₂, V x) - ∫ u in (K : ℝ)..(N : ℝ), V u)‖
          ≤ 2 * B := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc (q : ℝ)⁻¹ * ‖(∫ x in r₁..r₂, V x) - ∫ u in (K : ℝ)..(N : ℝ), V u‖
            ≤ (q : ℝ)⁻¹ * (2 * B * (q : ℝ)) :=
              mul_le_mul_of_nonneg_left hH (by positivity)
          _ = 2 * B := by field_simp
      rw [hreindex]
      have hdecomp : (∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)))
            - (q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u
          = ((∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)))
              - (q : ℝ)⁻¹ * ∫ x in r₁..r₂, V x)
            + (q : ℝ)⁻¹ * ((∫ x in r₁..r₂, V x) - ∫ u in (K : ℝ)..(N : ℝ), V u) := by
        ring
      rw [hdecomp]
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add hT h2nd) ?_
      have hr21N : r₂ - r₁ ≤ (N : ℝ) := by linarith
      have hfin : B₁ * (r₂ - r₁) / 2 ≤ (N : ℝ) * B₁ := by
        have h1 : B₁ * (r₂ - r₁) ≤ B₁ * (N : ℝ) := mul_le_mul_of_nonneg_left hr21N hB1
        have h2 : (0 : ℝ) ≤ (N : ℝ) * B₁ := mul_nonneg hNnn hB1
        linarith
      linarith
    · -- the Lipschitz hypothesis for `t ↦ V (a + q t)`
      intro x hx y hy
      have hpx : (a : ℝ) + (q : ℝ) * x ∈ Set.Icc (K : ℝ) (N : ℝ) := by
        refine ⟨?_, ?_⟩
        · have h1 : (m₁ : ℝ) ≤ x := hx.1
          have h2 : r₁ ≤ (a : ℝ) + (q : ℝ) * x := by
            have h := mul_le_mul_of_nonneg_left h1 hqnn
            linarith
          linarith
        · have h1 : x ≤ (m₂ : ℝ) := hx.2
          have h2 : (a : ℝ) + (q : ℝ) * x ≤ r₂ := by
            have h := mul_le_mul_of_nonneg_left h1 hqnn
            linarith
          linarith
      have hpy : (a : ℝ) + (q : ℝ) * y ∈ Set.Icc (K : ℝ) (N : ℝ) := by
        refine ⟨?_, ?_⟩
        · have h1 : (m₁ : ℝ) ≤ y := hy.1
          have h2 : r₁ ≤ (a : ℝ) + (q : ℝ) * y := by
            have h := mul_le_mul_of_nonneg_left h1 hqnn
            linarith
          linarith
        · have h1 : y ≤ (m₂ : ℝ) := hy.2
          have h2 : (a : ℝ) + (q : ℝ) * y ≤ r₂ := by
            have h := mul_le_mul_of_nonneg_left h1 hqnn
            linarith
          linarith
      have h1 := hLipV _ hpx _ hpy
      have h2 : |((a : ℝ) + (q : ℝ) * y) - ((a : ℝ) + (q : ℝ) * x)| = (q : ℝ) * |y - x| := by
        rw [show ((a : ℝ) + (q : ℝ) * y) - ((a : ℝ) + (q : ℝ) * x) = (q : ℝ) * (y - x) by ring,
          abs_mul, abs_of_nonneg hqnn]
      rw [h2] at h1
      calc ‖V ((a : ℝ) + (q : ℝ) * y) - V ((a : ℝ) + (q : ℝ) * x)‖ ≤ B₁ * ((q : ℝ) * |y - x|) := h1
        _ = ((q : ℝ) * B₁) * |y - x| := by ring
  · -- ===================== empty fibre =====================
    have hsum0 : (∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ)) = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hFib]
      simp
    rw [hsum0, zero_sub, norm_neg]
    have hlen : N - K < q := by
      by_contra hcon
      have hNK : K + q ≤ N := by omega
      obtain ⟨n, hnK, hnN, hna⟩ := Work.A7.fiber_exists_mod_eq q K N a hq ha hNK
      exact hFib ⟨n, by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hnK, hnN⟩, hna⟩⟩
    have hInt : ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ ≤ B * ((N : ℝ) - (K : ℝ)) := by
      have h1 : ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ ≤ B * |(N : ℝ) - (K : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (f := V) (a := (K : ℝ)) (b := (N : ℝ))
          (C := B) (fun x hx => by
            rw [Set.uIoc_of_le hKN'] at hx
            exact hB x ⟨le_of_lt hx.1, hx.2⟩)
      rwa [abs_of_nonneg (by linarith)] at h1
    have hNKle : (N : ℝ) - (K : ℝ) ≤ (q : ℝ) := by
      have hcast : (N : ℝ) - (K : ℝ) = ((N - K : ℕ) : ℝ) := by rw [Nat.cast_sub hKN]
      rw [hcast]
      exact_mod_cast le_of_lt hlen
    calc ‖(q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u‖
        = (q : ℝ)⁻¹ * ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ (q : ℝ)⁻¹ * (B * ((N : ℝ) - (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ ≤ (q : ℝ)⁻¹ * (B * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNKle hB0) (by positivity)
      _ = B := by field_simp
      _ ≤ 3 * B + (N : ℝ) * B₁ := by
          have h2 : (0 : ℝ) ≤ (N : ℝ) * B₁ := mul_nonneg hNnn hB1
          linarith

end Work.KMTAreas.A7
