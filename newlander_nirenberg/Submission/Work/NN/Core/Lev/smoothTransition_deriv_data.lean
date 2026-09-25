/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Derivative data for the smooth transition profile `Real.smoothTransition`

`σ = Real.smoothTransition` is the standard `C^∞` step: `σ t = 0` for `t ≤ 0`, `σ t = 1` for
`1 ≤ t` and `0 ≤ σ t ≤ 1`.  Here we record what is needed to control *derivatives* of the
rescaled profiles `t ↦ σ ((c - t)/δ)`, namely

* `σ' = deriv σ` and `σ'' = deriv (deriv σ)` are globally bounded (by constants `C₁`, `C₂`);
* `σ'` and `σ''` vanish on `(-∞,0]` and on `[1,∞)`.

Note that `σ` itself is *not* compactly supported (`σ = 1` on `[1,∞)`); it is `σ'` and `σ''`
which have compact support (`⊆ [0,1]`), and that is what makes them bounded.
-/
import Mathlib

noncomputable section

open scoped ContDiff Topology

namespace Work.NN.Core.Lev

lemma contDiff_smoothTransition : ContDiff ℝ ∞ Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

lemma continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  contDiff_smoothTransition.continuous_deriv (by simp)

lemma contDiff_deriv_smoothTransition : ContDiff ℝ ∞ (deriv Real.smoothTransition) := by
  simpa [Function.iterate_one] using ContDiff.iterate_deriv 1 contDiff_smoothTransition

lemma continuous_deriv_deriv_smoothTransition :
    Continuous (deriv (deriv Real.smoothTransition)) :=
  contDiff_deriv_smoothTransition.continuous_deriv (by simp)

/-- `σ'` vanishes on `(-∞,0)`: `σ` is constant `0` there. -/
lemma deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ'` vanishes on `(1,∞)`: `σ` is constant `1` there. -/
lemma deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ' = 0` on `(-∞,0]`: by continuity, since it vanishes on `(-∞,0)`. -/
lemma deriv_smoothTransition_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_lt_zero h
  · have h2 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[<] (0 : ℝ))
        (𝓝 (deriv Real.smoothTransition 0)) :=
      continuous_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv_smoothTransition_eq_zero_of_lt_zero hs).symm)
    exact tendsto_nhds_unique h2 h1

/-- `σ' = 0` on `[1,∞)`: by continuity, since it vanishes on `(1,∞)`. -/
lemma deriv_smoothTransition_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_one_lt h
  · have h2 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[>] (1 : ℝ))
        (𝓝 (deriv Real.smoothTransition 1)) :=
      continuous_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv_smoothTransition_eq_zero_of_one_lt hs).symm)
    exact tendsto_nhds_unique h2 h1

lemma hasCompactSupport_deriv_smoothTransition : HasCompactSupport (deriv Real.smoothTransition) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    rw [not_le] at h
    exact ht (deriv_smoothTransition_eq_zero_of_nonpos h.le)
  · by_contra h
    rw [not_le] at h
    exact ht (deriv_smoothTransition_eq_zero_of_one_le h.le)

/-- `σ''` vanishes on `(-∞,0)`: `σ'` is constant `0` there. -/
lemma deriv_deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact deriv_smoothTransition_eq_zero_of_nonpos hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ''` vanishes on `(1,∞)`: `σ'` is constant `0` there. -/
lemma deriv_deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact deriv_smoothTransition_eq_zero_of_one_le hs.le
  rw [hev.deriv_eq]
  simp

/-- `σ'' = 0` on `(-∞,0]`. -/
lemma deriv_deriv_smoothTransition_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv_deriv_smoothTransition_eq_zero_of_lt_zero h
  · have h2 : Filter.Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[<] (0 : ℝ))
        (𝓝 (deriv (deriv Real.smoothTransition) 0)) :=
      continuous_deriv_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv_deriv_smoothTransition_eq_zero_of_lt_zero hs).symm)
    exact tendsto_nhds_unique h2 h1

/-- `σ'' = 0` on `[1,∞)`. -/
lemma deriv_deriv_smoothTransition_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact deriv_deriv_smoothTransition_eq_zero_of_one_lt h
  · have h2 : Filter.Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[>] (1 : ℝ))
        (𝓝 (deriv (deriv Real.smoothTransition) 1)) :=
      continuous_deriv_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv_deriv_smoothTransition_eq_zero_of_one_lt hs).symm)
    exact tendsto_nhds_unique h2 h1

lemma hasCompactSupport_deriv_deriv_smoothTransition :
    HasCompactSupport (deriv (deriv Real.smoothTransition)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    rw [not_le] at h
    exact ht (deriv_deriv_smoothTransition_eq_zero_of_nonpos h.le)
  · by_contra h
    rw [not_le] at h
    exact ht (deriv_deriv_smoothTransition_eq_zero_of_one_le h.le)

/-- **Derivative data for the smooth transition profile.**

There are constants `C₁, C₂ ≥ 0` bounding `|σ'|` and `|σ''|`, and both `σ'` and `σ''` vanish
on `(-∞,0]` and on `[1,∞)`. -/
theorem smoothTransition_deriv_bounds :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C₁) ∧
      (∀ t : ℝ, |deriv (deriv Real.smoothTransition) t| ≤ C₂) ∧
      (∀ t : ℝ, t ≤ 0 → deriv Real.smoothTransition t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → deriv Real.smoothTransition t = 0) ∧
      (∀ t : ℝ, t ≤ 0 → deriv (deriv Real.smoothTransition) t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → deriv (deriv Real.smoothTransition) t = 0) := by
  obtain ⟨A₁, hA₁⟩ := continuous_deriv_smoothTransition.bounded_above_of_compact_support
    hasCompactSupport_deriv_smoothTransition
  obtain ⟨A₂, hA₂⟩ := continuous_deriv_deriv_smoothTransition.bounded_above_of_compact_support
    hasCompactSupport_deriv_deriv_smoothTransition
  refine ⟨max A₁ 0, max A₂ 0, le_max_right _ _, le_max_right _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have h := hA₁ t
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · intro t
    have h := hA₂ t
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · exact fun t ht => deriv_smoothTransition_eq_zero_of_nonpos ht
  · exact fun t ht => deriv_smoothTransition_eq_zero_of_one_le ht
  · exact fun t ht => deriv_deriv_smoothTransition_eq_zero_of_nonpos ht
  · exact fun t ht => deriv_deriv_smoothTransition_eq_zero_of_one_le ht

end Work.NN.Core.Lev
