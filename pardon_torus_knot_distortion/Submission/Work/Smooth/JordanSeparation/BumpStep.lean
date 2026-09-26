import Submission.Work.Smooth.JordanSeparation.BumpCylinder

/-!
# The bump-push step: simplicity of the pushed curve, and the constant-direction collar

This file adds the two remaining elementary facts about the bump push of `BumpCylinder.lean`:

* `translation_collar_injective` — the translation collar `(θ,u) ↦ γ θ + u • ν` of a `C¹` immersed
  simple closed curve in a **uniformly transverse** unit direction `ν` is injective on a strip
  (`offset_injective` applied to the constant field `fun _ ↦ ν`);
* `bumpPush_isSimple` — the pushed curve `θ ↦ γ θ + (φ θ) • ν` of a simple closed curve is again
  injective on one period whenever the profile's values lie inside the width of the translation
  collar.

Together with `bumpCylinder` / `bumpCylinder_of_chord` these are the per-step facts of the
exhaustion chain of `SCHOENFLIES.md` §6.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- A real number of the form `θ + k · 2π` with `θ` in a period cannot lie in the *same* period
unless `k = 0`. -/
theorem eq_of_int_mul_two_pi {θ θ' : ℝ} (hθ : θ ∈ Set.Ico 0 (2 * Real.pi))
    (hθ' : θ' ∈ Set.Ico 0 (2 * Real.pi)) {k : ℤ} (h : θ' = θ + (k : ℝ) * (2 * Real.pi)) :
    k = 0 := by
  have h1 : θ' - θ = (k : ℝ) * (2 * Real.pi) := by rw [h]; ring
  have h2 : |θ' - θ| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2, Real.pi_pos]
  have h3 : |(k : ℝ)| * (2 * Real.pi) = |θ' - θ| := by
    have h4 : |θ' - θ| = |(k : ℝ)| * (2 * Real.pi) := by
      rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact h4.symm
  have hklt : |(k : ℝ)| < 1 := by nlinarith [h2, h3, Real.pi_pos]
  rw [abs_lt] at hklt
  have hkI : -1 < k ∧ k < 1 := by exact_mod_cast hklt
  exact by omega

/-- **The translation collar in a fixed direction.**  For a `C¹` immersed simple closed curve `c`
and a unit direction `ν` which is *pointwise transverse* to the curve with a uniform constant `κ`
(`κ ‖γ'‖ ≤ |detV γ' ν|`), the collar `(θ,u) ↦ c.γ θ + u·ν` is injective on `S¹ × (-δ,δ)` modulo
the period.  This is `offset_injective` applied to the *constant* unit field `fun _ ↦ ν`. -/
theorem translation_collar_injective (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {ν : ℂ} {κ : ℝ} (hκ : 0 < κ) (hν : ‖ν‖ = 1)
    (htrans : ∀ t : ℝ, κ * ‖deriv c.γ t‖ ≤ |detV (deriv c.γ t) ν|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      c.γ t + u * ν = c.γ t' + u' * ν →
      u = u' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi) := by
  have h1 : IsTransverseUnitField c κ (fun _ => ν) := ⟨fun _ => hν, htrans⟩
  have h2 : IsLipschitzField 1 (fun _ => ν) := fun t t' => by
    simp only [sub_self, norm_zero]
    exact mul_nonneg zero_le_one (abs_nonneg _)
  have h3 : Function.Periodic (fun _ : ℝ => ν) (2 * Real.pi) := fun _ => rfl
  obtain ⟨δ, hδ, h⟩ := offset_injective c himm hs hκ one_pos h3 h1 h2
  exact ⟨δ, hδ, fun t t' u u' hu hu' heq =>
    h t t' u u' hu hu' (by simpa [offset] using heq)⟩

/-- The bump push of a simple closed curve along the direction `ν` (with a periodic nonnegative
profile whose values lie in the width `M` of the translation collar of `c` in the direction `ν`)
is again injective on one period: it is a simple closed curve. -/
theorem bumpPush_isSimple {γ : ℝ → ℂ} {ν : ℂ} {φ : ℝ → ℝ} {M : ℝ}
    (hφ0 : ∀ θ, 0 ≤ φ θ) (hφM : ∀ θ, φ θ < M)
    (hM : ∀ θ t θ' t', t ∈ Set.Icc 0 M → t' ∈ Set.Icc 0 M →
      γ θ + t * ν = γ θ' + t' * ν → t = t' ∧ ∃ k : ℤ, θ' = θ + k * (2 * Real.pi)) :
    Set.InjOn (bumpCurve γ φ ν) (Set.Ico 0 (2 * Real.pi)) := by
  intro θ hθ θ' hθ' h
  have hs : φ θ ∈ Set.Icc 0 M := ⟨hφ0 θ, le_of_lt (hφM θ)⟩
  have hs' : φ θ' ∈ Set.Icc 0 M := ⟨hφ0 θ', le_of_lt (hφM θ')⟩
  have h' : γ θ + (φ θ : ℝ) * ν = γ θ' + (φ θ' : ℝ) * ν := h
  obtain ⟨-, k, hk⟩ := hM θ (φ θ) θ' (φ θ') hs hs' h'
  have hk0 : k = 0 := eq_of_int_mul_two_pi hθ hθ' hk
  rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
  exact hk.symm

end

end Work.Smooth.JordanSeparation
