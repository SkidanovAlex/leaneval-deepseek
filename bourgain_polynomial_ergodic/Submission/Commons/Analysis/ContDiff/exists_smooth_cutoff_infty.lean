import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open scoped ContDiff Topology

namespace Commons.Analysis.ContDiff

/-- If a function agrees with a constant near a point, then all its iterated derivatives of
positive order vanish at that point. -/
lemma iteratedDeriv_eq_zero_of_eventuallyEq_const {g : ℝ → ℝ} {x c : ℝ}
    (h : g =ᶠ[𝓝 x] fun _ => c) {j : ℕ} (hj : j ≠ 0) : iteratedDeriv j g x = 0 := by
  rw [Filter.EventuallyEq.iteratedDeriv_eq j h, iteratedDeriv_const]
  simp [hj]

/-- A `C^∞` function on `ℝ` which is constant on each of the two half-lines `(-∞, a]` and
`[b, ∞)` has bounded `j`-th derivative for every `j`. -/
theorem exists_bound_iteratedDeriv_of_const_outside (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {a b : ℝ} (hab : a ≤ b) (ha : ∀ t, t ≤ a → g t = g a) (hb : ∀ t, b ≤ t → g t = g b) :
    ∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ t, |iteratedDeriv j g t| ≤ A := by
  have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hmem_b : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  intro j
  obtain rfl | hj := Nat.eq_zero_or_pos j
  · obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b) hg.continuous.continuousOn
    have hC' : ∀ t ∈ Set.Icc a b, |g t| ≤ C := fun t ht => by simpa using hC t ht
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' a hmem_a)
    refine ⟨C + 1, by linarith, fun t => ?_⟩
    have : |g t| ≤ C := by
      rcases le_or_gt t a with ht | ht
      · rw [ha t ht]; exact hC' a hmem_a
      rcases le_or_gt t b with ht' | ht'
      · exact hC' t ⟨le_of_lt ht, ht'⟩
      · rw [hb t (le_of_lt ht')]; exact hC' b hmem_b
    rw [iteratedDeriv_zero]
    linarith
  · have hj0 : j ≠ 0 := hj.ne'
    have hcont : Continuous (iteratedDeriv j g) :=
      hg.continuous_iteratedDeriv j (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b) hcont.continuousOn
    have hC' : ∀ t ∈ Set.Icc a b, |iteratedDeriv j g t| ≤ C := fun t ht => by simpa using hC t ht
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' a hmem_a)
    refine ⟨C + 1, by linarith, fun t => ?_⟩
    have hzero_left : ∀ t, t < a → iteratedDeriv j g t = 0 := by
      intro t ht
      have hev : g =ᶠ[𝓝 t] (fun _ => g a) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
        exact ha y hy.le
      exact iteratedDeriv_eq_zero_of_eventuallyEq_const hev hj0
    have : |iteratedDeriv j g t| ≤ C := by
      rcases lt_or_ge t a with ht | ht
      · rw [hzero_left t ht, abs_zero]; exact hC0
      rcases le_or_gt t b with ht' | ht'
      · exact hC' t ⟨ht, ht'⟩
      · have hz : iteratedDeriv j g t = 0 := by
          have hev : g =ᶠ[𝓝 t] (fun _ => g b) := by
            filter_upwards [isOpen_Ioi.mem_nhds ht'] with y hy
            exact hb y hy.le
          exact iteratedDeriv_eq_zero_of_eventuallyEq_const hev hj0
        rw [hz, abs_zero]; exact hC0
    linarith

/-- The specific smooth step function `t ↦ 1 - Real.smoothTransition t` and its basic
properties: it is `1` on `(-∞, 0]`, `0` on `[1, ∞)`, takes values in `[0, 1]`, and each of its
iterated derivatives is bounded on `ℝ`. -/
lemma smoothTransition_cutoff_aux :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t, t ≤ 0 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧
      (∀ t, 0 ≤ φ t) ∧ (∀ t, φ t ≤ 1) ∧
      (∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ t, |iteratedDeriv j φ t| ≤ A) := by
  refine ⟨fun t => 1 - Real.smoothTransition t, by fun_prop, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    dsimp only
    rw [Real.smoothTransition.zero_of_nonpos ht, sub_zero]
  · intro t ht
    dsimp only
    rw [Real.smoothTransition.one_of_one_le ht, sub_self]
  · intro t
    have := Real.smoothTransition.le_one t
    linarith
  · intro t
    have := Real.smoothTransition.nonneg t
    linarith
  · intro j
    refine exists_bound_iteratedDeriv_of_const_outside (fun t => 1 - Real.smoothTransition t)
      (by fun_prop) (a := 0) (b := 1) (by norm_num) ?_ ?_ j
    · intro t ht
      simp [Real.smoothTransition.zero_of_nonpos ht]
    · intro t ht
      simp [Real.smoothTransition.one_of_one_le ht]

theorem exists_smooth_cutoff_infty (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ u, u ≤ x - y → f u = 1) ∧ (∀ u, x ≤ u → f u = 0) ∧
      (∀ u, 0 ≤ f u) ∧ (∀ u, f u ≤ 1) ∧
      (∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ A * (y ^ j)⁻¹) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  obtain ⟨φ, hφc, hφ1, hφ0, hφnonneg, hφle1, hφbound⟩ := smoothTransition_cutoff_aux
  have hfC : ContDiff ℝ ∞ (fun u : ℝ => φ ((u - (x - y)) / y)) := by fun_prop
  refine ⟨fun u => φ ((u - (x - y)) / y), hfC, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    refine hφ1 _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) hypos.le)
  · intro u hu
    refine hφ0 _ ?_
    rw [le_div_iff₀ hypos]
    linarith
  · intro u
    exact hφnonneg _
  · intro u
    exact hφle1 _
  · intro j
    obtain ⟨A, hApos, hAbound⟩ := hφbound j
    refine ⟨A, hApos, fun u _ => ?_⟩
    have hderiv : iteratedDeriv j (fun u : ℝ => φ ((u - (x - y)) / y)) u
        = (1 / y) ^ j * iteratedDeriv j φ ((u - (x - y)) / y) := by
      have h1 : (fun u : ℝ => φ ((u - (x - y)) / y))
          = fun u => (fun z : ℝ => φ (z * (1 / y))) (u - (x - y)) := by
        funext u
        simp only [div_eq_mul_inv, one_mul]
      rw [h1, iteratedDeriv_comp_sub_const j (fun z : ℝ => φ (z * (1 / y))) (x - y)]
      have h2 : (fun z : ℝ => φ (z * (1 / y))) = fun z : ℝ => φ ((1 / y) * z) := by
        funext z; rw [mul_comm]
      rw [h2, iteratedDeriv_comp_const_mul (hφc.of_le (by exact_mod_cast le_top)) (1 / y)]
      simp only [div_eq_mul_inv, one_mul]
      ring_nf
    have hcoef : |(1 / y : ℝ) ^ j| = (y ^ j)⁻¹ := by
      rw [abs_pow, abs_of_pos (one_div_pos.2 hypos), one_div, inv_pow]
    rw [hderiv, abs_mul, hcoef]
    calc (y ^ j)⁻¹ * |iteratedDeriv j φ ((u - (x - y)) / y)|
        ≤ (y ^ j)⁻¹ * A := mul_le_mul_of_nonneg_left (hAbound _) (by positivity)
      _ = A * (y ^ j)⁻¹ := by ring

end Commons.Analysis.ContDiff