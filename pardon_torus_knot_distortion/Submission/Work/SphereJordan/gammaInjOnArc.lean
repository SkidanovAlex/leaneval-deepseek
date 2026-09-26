import Mathlib
import Submission.Work.Smooth.Jordan.All

/-!
# Parameters of equal points of a simple closed plane curve

For a simple closed plane curve (`Work.Smooth.Jordan.PlaneCurve.IsSimple`, i.e. injective on one
period `[0, 2π)`), two parameters giving the same point differ by an integer multiple of `2π`; as a
consequence `γ` is injective on every interval of length `< 2π`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The remainder of `x` modulo `2π`, lying in `[0, 2π)`. -/
def modTwoPi (x : ℝ) : ℝ := x - (⌊x / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi)

theorem modTwoPi_mem (x : ℝ) : modTwoPi x ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · have h := Int.floor_le (x / (2 * Real.pi))
    have := mul_le_mul_of_nonneg_right h (le_of_lt hp)
    rw [div_mul_cancel₀ x (ne_of_gt hp)] at this
    simp only [modTwoPi]
    linarith
  · have h := Int.lt_floor_add_one (x / (2 * Real.pi))
    have := mul_lt_mul_of_pos_right h hp
    rw [add_mul, one_mul, div_mul_cancel₀ x (ne_of_gt hp)] at this
    simp only [modTwoPi]
    linarith

theorem gamma_modTwoPi (x : ℝ) : γ.γ (modTwoPi x) = γ.γ x := by
  have hper : ∀ (y : ℝ) (n : ℤ),
      γ.γ (y - (n : ℝ) * (2 * Real.pi)) = γ.γ y := by
    intro y n
    have := (γ.periodic.int_mul n) (y - (n : ℝ) * (2 * Real.pi))
    simpa using this.symm
  exact hper x ⌊x / (2 * Real.pi)⌋

/-- **Equal points have parameters differing by a multiple of `2π`.** -/
theorem gamma_eq_imp_mod {s t : ℝ} (hs : γ.IsSimple) (h : γ.γ s = γ.γ t) :
    ∃ k : ℤ, s - t = (k : ℝ) * (2 * Real.pi) := by
  have h₁ : γ.γ (modTwoPi s) = γ.γ (modTwoPi t) := by
    rw [gamma_modTwoPi s, gamma_modTwoPi t]; exact h
  have heq : modTwoPi s = modTwoPi t :=
    hs (modTwoPi_mem s) (modTwoPi_mem t) h₁
  refine ⟨⌊s / (2 * Real.pi)⌋ - ⌊t / (2 * Real.pi)⌋, ?_⟩
  simp only [modTwoPi] at heq
  push_cast
  linarith

/-- **A simple closed plane curve is injective on every interval of length `< 2π`.** -/
theorem gammaInjOn_of_sub_lt (hs : γ.IsSimple) {a b s t : ℝ}
    (hs' : s ∈ Set.Icc a b) (ht' : t ∈ Set.Icc a b) (hlen : b - a < 2 * Real.pi)
    (h : γ.γ s = γ.γ t) : s = t := by
  obtain ⟨k, hk⟩ := gamma_eq_imp_mod hs h
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  have hbound : |s - t| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hs'.1, hs'.2, ht'.1, ht'.2, hlen]
  have h2 : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    have hb := hbound
    rw [hk, abs_mul, abs_of_pos hp] at hb
    exact hb
  have h3 : |(k : ℝ)| < 1 := by nlinarith [h2, hp]
  have h4 : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h3
  have h5 : |k| < 1 := by exact_mod_cast h4
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp h5
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- Injectivity on the two arcs cut out on `γ` by the two inner endpoints of the crosscuts. -/
theorem gammaInjOnArc (hs : γ.IsSimple)
    {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (h₂ : θ₂ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hlt : θ₁ < θ₂) :
    Set.InjOn γ.γ (Set.Icc θ₁ θ₂) ∧ Set.InjOn γ.γ (Set.Icc θ₂ (θ₁ + 2 * Real.pi)) := by
  constructor
  · intro s hs' t ht' h
    refine gammaInjOn_of_sub_lt hs hs' ht' ?_ h
    linarith [h₁.1, h₂.2]
  · intro s hs' t ht' h
    refine gammaInjOn_of_sub_lt hs hs' ht' ?_ h
    linarith [hlt]

end

end Work.SphereJordan
