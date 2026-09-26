import Submission.Work.Smooth.JordanSeparation.Transfer
import Submission.Work.Smooth.JordanSeparation.offset_injective

/-!
# The bump-push cylinder (`SCHOENFLIES.md` §2(a)‴⁺)

The **exhaustion** route to (E) builds the filling of a simple closed plane curve `γ` by a nested
chain of curves `γ = γ₀, γ₁, γ₂, …` together with *explicit cylinders* `Φ k : S¹ × [0,1] → ℂ`
between consecutive ones (`Φ k (·,0) = γ k`, `Φ k (·,1) = γ (k+1)`), shrinking to a point; the
filling is then read off by "gluing" the cylinders along the dyadic annuli of the unit disc.

The *elementary* step of the chain is the **bump push**: choose a direction `ν` and a nonnegative
`2π`-periodic "profile" `φ` (supported on the arc where the curve is to be pushed), and move the
whole curve inward by `φ` in the direction `ν`:

`γ' θ = γ θ + φ θ • ν`,   `Φ θ s = γ θ + (s * φ θ) • ν`.

The cylinder property (`Φ` injective on `S¹ × [0,1]`, i.e. the level curves
`θ ↦ γ θ + t * ν` for `0 ≤ t ≤ sup φ` are pairwise disjoint and each simple) is exactly the
injectivity of the *translation collar* of `γ` in the direction `ν`, which is the hypothesis
`hinj` below.  Everything in this file is the purely algebraic content: the bump push inherits
injectivity from the translation collar, and is continuous/periodic.

## Main declarations

* `bumpCylinder` — the injectivity of the bump push;
* `bumpCurve`, `bumpCurve_apply`, `continuous_bumpCurve`, `bumpCurve_periodic`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The bump-push cylinder.**  If the translates `θ ↦ γ θ + t • ν` are pairwise disjoint for
`t ∈ [0,M]`, then the bump push `(θ,s) ↦ γ θ + (s * φ θ) • ν` is injective on
`S¹ × [0,1]` modulo the period (and the pushed-out depth is determined by the point). -/
theorem bumpCylinder {γ : ℝ → ℂ} {ν : ℂ} {φ : ℝ → ℝ} {M : ℝ}
    (hφ0 : ∀ θ, 0 ≤ φ θ) (hφM : ∀ θ, φ θ ≤ M)
    (hinj : ∀ θ t θ' t', t ∈ Set.Icc 0 M → t' ∈ Set.Icc 0 M →
      γ θ + t * ν = γ θ' + t' * ν → t = t' ∧ ∃ k : ℤ, θ' = θ + k * (2 * Real.pi))
    {θ : ℝ} {s : ℝ} {θ' : ℝ} {s' : ℝ} (hs : s ∈ Set.Icc 0 1) (hs' : s' ∈ Set.Icc 0 1)
    (h : γ θ + ((s * φ θ : ℝ) : ℂ) * ν = γ θ' + ((s' * φ θ' : ℝ) : ℂ) * ν) :
    s * φ θ = s' * φ θ' ∧ ∃ k : ℤ, θ' = θ + k * (2 * Real.pi) := by
  have ht : s * φ θ ∈ Set.Icc 0 M :=
    ⟨mul_nonneg hs.1 (hφ0 θ), by
      calc s * φ θ ≤ 1 * φ θ := mul_le_mul_of_nonneg_right hs.2 (hφ0 θ)
        _ = φ θ := one_mul _
        _ ≤ M := hφM θ⟩
  have ht' : s' * φ θ' ∈ Set.Icc 0 M :=
    ⟨mul_nonneg hs'.1 (hφ0 θ'), by
      calc s' * φ θ' ≤ 1 * φ θ' := mul_le_mul_of_nonneg_right hs'.2 (hφ0 θ')
        _ = φ θ' := one_mul _
        _ ≤ M := hφM θ'⟩
  exact hinj θ (s * φ θ) θ' (s' * φ θ') ht ht' h

/-- The injectivity of the bump push, in the "same level" form: two points of the same level curve
that coincide have the same parameter modulo the period (provided the profile is nonzero). -/
theorem bumpCylinder_same {γ : ℝ → ℂ} {ν : ℂ} {φ : ℝ → ℝ} {M : ℝ}
    (hφ0 : ∀ θ, 0 ≤ φ θ) (hφM : ∀ θ, φ θ ≤ M)
    (hinj : ∀ θ t θ' t', t ∈ Set.Icc 0 M → t' ∈ Set.Icc 0 M →
      γ θ + t * ν = γ θ' + t' * ν → t = t' ∧ ∃ k : ℤ, θ' = θ + k * (2 * Real.pi))
    {θ : ℝ} {s : ℝ} {θ' : ℝ} (hs : s ∈ Set.Icc 0 1) (hs' : s ∈ Set.Icc 0 1)
    (h : γ θ + ((s * φ θ : ℝ) : ℂ) * ν = γ θ' + ((s * φ θ' : ℝ) : ℂ) * ν) :
    ∃ k : ℤ, θ' = θ + k * (2 * Real.pi) :=
  (bumpCylinder hφ0 hφM hinj hs hs' h).2

/-- The **pushed curve** of a bump push. -/
def bumpCurve (γ : ℝ → ℂ) (φ : ℝ → ℝ) (ν : ℂ) : ℝ → ℂ := fun θ => γ θ + φ θ * ν

@[simp] theorem bumpCurve_apply (γ : ℝ → ℂ) (φ : ℝ → ℝ) (ν : ℂ) (θ : ℝ) :
    bumpCurve γ φ ν θ = γ θ + φ θ * ν := rfl

theorem continuous_bumpCurve {γ : ℝ → ℂ} {φ : ℝ → ℝ} (hγ : Continuous γ) (hφ : Continuous φ)
    (ν : ℂ) : Continuous (bumpCurve γ φ ν) :=
  hγ.add ((Complex.continuous_ofReal.comp hφ).mul continuous_const)

theorem bumpCurve_periodic {γ : ℝ → ℂ} {φ : ℝ → ℝ}
    (hγ : Function.Periodic γ (2 * Real.pi)) (hφ : Function.Periodic φ (2 * Real.pi)) (ν : ℂ) :
    Function.Periodic (bumpCurve γ φ ν) (2 * Real.pi) := fun θ => by
  simp only [bumpCurve_apply, hγ θ, hφ θ]

/-- The bump push at the bottom level is the curve itself. -/
theorem bumpCurve_zero (γ : ℝ → ℂ) (ν : ℂ) (θ : ℝ) :
    bumpCurve γ (fun _ => 0) ν θ = γ θ := by simp [bumpCurve]

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The sharpened legality of a bump push.**  The global translation collar of `γ` in the
direction `ν` need not exist (for a circle, *no* direction gives one: two congruent circles with
different centres always meet).  What is needed for the bump push `Φ (θ,s) = γ θ + (s * φ θ) • ν`
is only that no nonzero chord of `γ` in the direction `ℝν` with length at most `M` has an endpoint in
the *support* of the profile.  Under that hypothesis the push is injective. -/
theorem bumpCylinder_of_chord {γ : ℝ → ℂ} {ν : ℂ} {φ : ℝ → ℝ} {M : ℝ}
    (hφ0 : ∀ θ, 0 ≤ φ θ) (hφM : ∀ θ, φ θ ≤ M)
    (hchord : ∀ θ θ' t : ℝ, |t| ≤ M → (φ θ ≠ 0 ∨ φ θ' ≠ 0) →
      γ θ - γ θ' = t * ν → t = 0) :
    ∀ θ s θ' s' : ℝ, s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
      γ θ + ((s * φ θ : ℝ) : ℂ) * ν = γ θ' + ((s' * φ θ' : ℝ) : ℂ) * ν →
      s * φ θ = s' * φ θ' ∧ γ θ = γ θ' := by
  intro θ s θ' s' hs hs' h
  have hch : γ θ - γ θ' = ((s' * φ θ' - s * φ θ : ℝ) : ℂ) * ν := by
    have h2 : ((s' * φ θ' - s * φ θ : ℝ) : ℂ) * ν
        = ((s' * φ θ' : ℝ) : ℂ) * ν - ((s * φ θ : ℝ) : ℂ) * ν := by
      push_cast; ring
    rw [h2]
    linear_combination h
  have habs : |s' * φ θ' - s * φ θ| ≤ M := by
    have h1 : s * φ θ ∈ Set.Icc 0 M :=
      ⟨mul_nonneg hs.1 (hφ0 θ), by
        calc s * φ θ ≤ 1 * φ θ := mul_le_mul_of_nonneg_right hs.2 (hφ0 θ)
          _ = φ θ := one_mul _
          _ ≤ M := hφM θ⟩
    have h2 : s' * φ θ' ∈ Set.Icc 0 M :=
      ⟨mul_nonneg hs'.1 (hφ0 θ'), by
        calc s' * φ θ' ≤ 1 * φ θ' := mul_le_mul_of_nonneg_right hs'.2 (hφ0 θ')
          _ = φ θ' := one_mul _
          _ ≤ M := hφM θ'⟩
    rw [abs_sub_le_iff]; exact ⟨by linarith [h1.1, h2.2], by linarith [h2.1, h1.2]⟩
  rcases eq_or_ne (s' * φ θ' - s * φ θ) 0 with h0 | h0
  · have hsub : ((s' * φ θ' - s * φ θ : ℝ) : ℂ) = 0 := by simp [h0]
    rw [hsub, zero_mul] at hch
    exact ⟨by linarith, sub_eq_zero.mp hch⟩
  · exfalso
    have hne : φ θ ≠ 0 ∨ φ θ' ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact h0 (by rw [hcon.1, hcon.2, mul_zero, mul_zero, sub_zero])
    exact h0 (hchord θ θ' (s' * φ θ' - s * φ θ) habs hne hch)

end

end Work.Smooth.JordanSeparation
