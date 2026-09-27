import Mathlib
import Submission.Work.Drive.strip_offset
import Submission.Work.Drive.exists_embedded_configuration_strip

namespace Work.Drive

noncomputable section

/-- `Circle.exp π = -1`. -/
private lemma circle_exp_pi : Circle.exp Real.pi = -1 := by
  rw [← Circle.coe_inj, Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
  exact Complex.exp_pi_mul_I

/-- `Circle.exp (2 * π * (1/2)) = -1`. -/
private lemma circle_exp_half : Circle.exp (2 * Real.pi * (1 / 2)) = -1 := by
  have h : 2 * Real.pi * (1 / 2) = Real.pi := by ring
  rw [h, circle_exp_pi]

/-- On `[0, 1/2]` the map `s ↦ exp (2 π s)` is injective. -/
private lemma exp_two_pi_injOn_half :
    Set.InjOn (fun s : ℝ => Circle.exp (2 * Real.pi * s)) (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro s hs s' hs' heq
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), 2 * Real.pi * t ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro t ht
    refine ⟨by nlinarith [ht.1, h2π], ?_⟩
    have h1 : 2 * Real.pi * t ≤ 2 * Real.pi * (1 / 2) :=
      mul_le_mul_of_nonneg_left ht.2 (le_of_lt h2π)
    have h2 : 2 * Real.pi * (1 / 2) = Real.pi := by ring
    linarith
  have h : 2 * Real.pi * s = 2 * Real.pi * s' :=
    Circle.exp_injOn_Icc (a := 0) (b := Real.pi) (by linarith [Real.pi_pos])
      (hmem s hs) (hmem s' hs') heq
  exact mul_left_cancel₀ (ne_of_gt h2π) h

/-- Every element of the circle, or its inverse, is `exp (2 π s)` with `s ∈ [0, 1/2]`. -/
private lemma exists_exp_or_inv_exp (z : Circle) :
    (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ z = Circle.exp (2 * Real.pi * s)) ∨
    (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ z⁻¹ = Circle.exp (2 * Real.pi * s)) := by
  set θ : ℝ := (z : ℂ).arg with hθ
  have hz : z = Circle.exp θ := (Circle.exp_arg z).symm
  have hθle : θ ≤ Real.pi := Complex.arg_le_pi (z : ℂ)
  have hθgt : -Real.pi < θ := Complex.neg_pi_lt_arg (z : ℂ)
  by_cases h : (0 : ℝ) ≤ θ
  · left
    refine ⟨θ / (2 * Real.pi), ⟨div_nonneg h (by positivity), ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [hθle, Real.pi_pos]
    · rw [hz]
      congr 1
      field_simp
  · right
    have hlt : θ < 0 := lt_of_not_ge h
    refine ⟨(-θ) / (2 * Real.pi), ⟨div_nonneg (by linarith) (by positivity), ?_⟩, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [hθgt, Real.pi_pos]
    · rw [hz, ← Circle.exp_neg]
      congr 1
      field_simp

theorem stripOffset_param
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ)
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    (∀ x : Circle, Work.Drive.stripOffsetPt μ x (1 / 2) = Work.Drive.stripOffsetPt μ (-x) (1 / 2)) ∧
    (∀ x x' : Circle, ∀ s s' : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) → s' ∈ Set.Icc (0 : ℝ) (1 / 2) →
      Work.Drive.stripOffsetPt μ x s = Work.Drive.stripOffsetPt μ x' s' →
      (x = x' ∧ s = s') ∨ (s = 1 / 2 ∧ s' = 1 / 2 ∧ x' = -x)) ∧
    (∀ x y : Circle, ∃ x' : Circle, ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      μ (x, y) = Work.Drive.stripOffsetPt μ x' s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h1 : x * Circle.exp (2 * Real.pi * (1 / 2)) = -x := by
      rw [circle_exp_half]; simp
    have h2 : (-x) * Circle.exp (2 * Real.pi * (1 / 2)) = x := by
      rw [circle_exp_half]; simp
    simp only [stripOffsetPt, h1, h2]
    exact hsym (-x) x
  · intro x x' s s' hs hs' heq
    simp only [stripOffsetPt] at heq
    rcases hinj x (x * Circle.exp (2 * Real.pi * s)) x'
        (x' * Circle.exp (2 * Real.pi * s')) heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
    · refine Or.inl ⟨hxx, ?_⟩
      have hEs : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * s') := by
        rw [hxx] at hyy
        exact mul_left_cancel hyy
      exact exp_two_pi_injOn_half hs hs' hEs
    · have hcancel : Circle.exp (2 * Real.pi * s) * Circle.exp (2 * Real.pi * s') = 1 := by
        have h : x * (Circle.exp (2 * Real.pi * s) * Circle.exp (2 * Real.pi * s')) = x * 1 := by
          rw [mul_one, ← mul_assoc, hyx]
          exact hxy.symm
        exact mul_left_cancel h
      have hsum : Circle.exp (2 * Real.pi * (s + s')) = 1 := by
        have h : 2 * Real.pi * (s + s') = 2 * Real.pi * s + 2 * Real.pi * s' := by ring
        rw [h, Circle.exp_add]
        exact hcancel
      obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 hsum
      have hn' : s + s' = (n : ℝ) := by
        have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        refine mul_left_cancel₀ h2π ?_
        rw [hn]
        ring
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith [hs.1, hs'.1, hn']
      have hn1 : (n : ℝ) ≤ 1 := by linarith [hs.2, hs'.2, hn']
      have hn01 : n = 0 ∨ n = 1 := by
        have h0 : (0 : ℤ) ≤ n := by exact_mod_cast hn0
        have h1 : n ≤ 1 := by exact_mod_cast hn1
        omega
      rcases hn01 with hzero | hone
      · subst hzero
        simp only [Int.cast_zero] at hn'
        have hs0 : s = 0 := by linarith [hs.1, hs'.1, hn']
        have hs0' : s' = 0 := by linarith [hs.1, hs'.1, hn']
        refine Or.inl ⟨?_, by rw [hs0, hs0']⟩
        simp [hxy, hs0']
      · subst hone
        simp only [Int.cast_one] at hn'
        have hs_half : s = 1 / 2 := by linarith [hs.2, hs'.2, hn']
        have hs'_half : s' = 1 / 2 := by linarith [hs.2, hs'.2, hn']
        refine Or.inr ⟨hs_half, hs'_half, ?_⟩
        have hx_neg : x = -x' := by rw [hxy, hs'_half, circle_exp_half]; simp
        rw [hx_neg]; simp
  · intro x y
    rcases exists_exp_or_inv_exp (x⁻¹ * y) with ⟨s, hs, hzs⟩ | ⟨s, hs, hzs⟩
    · refine ⟨x, s, hs, ?_⟩
      simp only [stripOffsetPt]
      congr 1
      rw [← hzs]
      group
    · refine ⟨y, s, hs, ?_⟩
      simp only [stripOffsetPt]
      rw [hsym y x]
      congr 1
      rw [← hzs]
      group

end

end Work.Drive
