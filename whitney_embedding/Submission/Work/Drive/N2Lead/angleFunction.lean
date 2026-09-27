import Mathlib
import Submission.Work.Drive.N2.circleArcExtension

/-!
# The angle function of the saddle packet, in the `1`-periodic parameter

`Work.Drive.N2.circleArcExtension` produces a global angle function `Ψ` with `Ψ (x + 2π) = Ψ x + 2π`
agreeing with two prescribed monotone functions on two cyclically ordered intervals of the *angle*
parameter.  The packet needs the angle function of the level curve `γ i`, whose parameter is
`1`-periodic (the level circle is run once as `t` runs over `[0,1)`).

`angleFunction_periodOne` bridges the two: from the prescriptions on two intervals `[a,b]`, `[c,d]`
of the `1`-periodic parameter it produces `Θ` with `ContDiff ℝ ∞ Θ`, `deriv Θ > 0`,
`Θ (t + 1) = Θ t + 2 π` and the same two prescriptions.  The proof is the rescaling
`Θ t := Ψ (2 π t)`, i.e. `Work.Drive.N2.circleArcExtension` applied to the rescaled functions.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-- **The packet's angle function.**  Two `C^∞` increasing functions `ψ₁`, `ψ₂` prescribed on two
cyclically ordered intervals `[a,b]`, `[c,d]` of the `1`-periodic parameter, with the corresponding
cyclic order of their values, extend to a `C^∞` increasing `Θ` with `Θ (t + 1) = Θ t + 2 π`. -/
theorem angleFunction_periodOne {a b c d A B C D : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdA : d < a + 1)
    (hAB : A < B) (hBC : B < C) (hCD : C < D) (hDA : D < A + 2 * Real.pi)
    {ψ₁ ψ₂ : ℝ → ℝ} (h₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁)
    (h₁mono : ∀ x : ℝ, 0 < deriv ψ₁ x)
    (h₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₂)
    (h₂mono : ∀ x : ℝ, 0 < deriv ψ₂ x)
    (h₁a : ψ₁ a = A) (h₁b : ψ₁ b = B) (h₂c : ψ₂ c = C) (h₂d : ψ₂ d = D) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧ (∀ x : ℝ, 0 < deriv Θ x) ∧
      (∀ x : ℝ, Θ (x + 1) = Θ x + 2 * Real.pi) ∧
      (∀ x : ℝ, x ∈ Set.Icc a b → Θ x = ψ₁ x) ∧
      (∀ x : ℝ, x ∈ Set.Icc c d → Θ x = ψ₂ x) := by
  have hp_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hp_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hp_pos
  set ψ₁' : ℝ → ℝ := fun x => ψ₁ (x / (2 * Real.pi)) with h₁'
  set ψ₂' : ℝ → ℝ := fun x => ψ₂ (x / (2 * Real.pi)) with h₂'
  have h₁'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁' := by
    rw [h₁']; exact h₁sm.comp (by fun_prop)
  have h₂'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₂' := by
    rw [h₂']; exact h₂sm.comp (by fun_prop)
  have h₁'mono : ∀ x : ℝ, 0 < deriv ψ₁' x := by
    intro x
    have hd : HasDerivAt (fun y : ℝ => y / (2 * Real.pi)) (1 / (2 * Real.pi)) x := by
      simpa using (hasDerivAt_id x).div_const (2 * Real.pi)
    have h2 : HasDerivAt (fun y : ℝ => ψ₁ (y / (2 * Real.pi)))
        (deriv ψ₁ (x / (2 * Real.pi)) * (1 / (2 * Real.pi))) x :=
      (h₁sm.differentiable (by simp)).differentiableAt.hasDerivAt.comp x hd
    rw [h₁', h2.deriv]
    exact mul_pos (h₁mono (x / (2 * Real.pi))) (by positivity)
  have h₂'mono : ∀ x : ℝ, 0 < deriv ψ₂' x := by
    intro x
    have hd : HasDerivAt (fun y : ℝ => y / (2 * Real.pi)) (1 / (2 * Real.pi)) x := by
      simpa using (hasDerivAt_id x).div_const (2 * Real.pi)
    have h2 : HasDerivAt (fun y : ℝ => ψ₂ (y / (2 * Real.pi)))
        (deriv ψ₂ (x / (2 * Real.pi)) * (1 / (2 * Real.pi))) x :=
      (h₂sm.differentiable (by simp)).differentiableAt.hasDerivAt.comp x hd
    rw [h₂', h2.deriv]
    exact mul_pos (h₂mono (x / (2 * Real.pi))) (by positivity)
  obtain ⟨Ψ, hΨsm, hΨmono, hΨper, hΨ₁, hΨ₂⟩ :=
    Work.Drive.N2.circleArcExtension ((2 * Real.pi) * a) ((2 * Real.pi) * b)
      ((2 * Real.pi) * c) ((2 * Real.pi) * d) A B C D
      (by nlinarith [hp_pos]) (by nlinarith [hp_pos]) (by nlinarith [hp_pos])
      (by nlinarith [hp_pos, hdA, Real.pi_pos])
      hAB hBC hCD hDA ψ₁' ψ₂' h₁'sm h₁'mono h₂'sm h₂'mono
      (by change ψ₁ ((2 * Real.pi) * a / (2 * Real.pi)) = A
          rw [mul_div_cancel_left₀ a hp_ne]; exact h₁a)
      (by change ψ₁ ((2 * Real.pi) * b / (2 * Real.pi)) = B
          rw [mul_div_cancel_left₀ b hp_ne]; exact h₁b)
      (by change ψ₂ ((2 * Real.pi) * c / (2 * Real.pi)) = C
          rw [mul_div_cancel_left₀ c hp_ne]; exact h₂c)
      (by change ψ₂ ((2 * Real.pi) * d / (2 * Real.pi)) = D
          rw [mul_div_cancel_left₀ d hp_ne]; exact h₂d)
  refine ⟨fun t => Ψ ((2 * Real.pi) * t), ?_, ?_, ?_, ?_, ?_⟩
  · exact hΨsm.comp (by fun_prop)
  · intro x
    show 0 < deriv (fun t : ℝ => Ψ ((2 * Real.pi) * t)) x
    have hd : HasDerivAt (fun t : ℝ => (2 * Real.pi) * t) (2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
    have h2 : HasDerivAt (fun t : ℝ => Ψ ((2 * Real.pi) * t))
        (deriv Ψ ((2 * Real.pi) * x) * (2 * Real.pi)) x :=
      (hΨsm.differentiable (by simp)).differentiableAt.hasDerivAt.comp x hd
    rw [h2.deriv]
    exact mul_pos (hΨmono ((2 * Real.pi) * x)) hp_pos
  · intro x
    show Ψ ((2 * Real.pi) * (x + 1)) = Ψ ((2 * Real.pi) * x) + 2 * Real.pi
    rw [show (2 * Real.pi) * (x + 1) = (2 * Real.pi) * x + 2 * Real.pi by ring, hΨper]
  · intro x hx
    show Ψ ((2 * Real.pi) * x) = ψ₁ x
    have hmem : (2 * Real.pi) * x ∈ Set.Icc ((2 * Real.pi) * a) ((2 * Real.pi) * b) :=
      ⟨by nlinarith [hx.1, hp_pos], by nlinarith [hx.2, hp_pos]⟩
    have h1 := hΨ₁ _ hmem
    simp only [h₁'] at h1
    rw [mul_div_cancel_left₀ x hp_ne] at h1
    exact h1
  · intro x hx
    show Ψ ((2 * Real.pi) * x) = ψ₂ x
    have hmem : (2 * Real.pi) * x ∈ Set.Icc ((2 * Real.pi) * c) ((2 * Real.pi) * d) :=
      ⟨by nlinarith [hx.1, hp_pos], by nlinarith [hx.2, hp_pos]⟩
    have h1 := hΨ₂ _ hmem
    simp only [h₂'] at h1
    rw [mul_div_cancel_left₀ x hp_ne] at h1
    exact h1

end Work.Drive.N2Lead
