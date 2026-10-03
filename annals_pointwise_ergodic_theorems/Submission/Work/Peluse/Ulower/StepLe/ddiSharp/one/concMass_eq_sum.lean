import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp.one

private theorem ThetaSet_one_sum' {D : ℕ} (H : Finset ((Fin 1 → ℤ) × (Fin 1 → ℤ)))
    {M : Type*} [AddCommMonoid M] (f : (Fin 1 → ℤ) → (Fin 1 → ℤ) → (Fin 1 → ℤ) → M) :
    (∑ k ∈ ThetaSet 1 D H, f k.1 k.2.1 k.2.2)
      = ∑ a ∈ thetaBox 1 D, ∑ u ∈ thetaFibre D H a, ∑ v ∈ thetaFibre D H a, f a u v := by
  classical
  have hTS : ThetaSet 1 D H = (thetaBox 1 D ×ˢ (thetaBox 1 D ×ˢ thetaBox 1 D)).filter
      (fun k => ∀ ω : Fin 1 → Bool, ((k.1, fun i => if ω i then k.2.1 i else k.2.2 i) ∈ H)) := rfl
  rw [hTS, Finset.sum_filter]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_product]
  have hcond : ∀ u v : Fin 1 → ℤ,
      (∀ ω : Fin 1 → Bool, ((a, fun i => if ω i then u i else v i)) ∈ H)
        ↔ ((a, u) ∈ H ∧ (a, v) ∈ H) := by
    intro u v
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have hω := h (fun _ => true)
        rwa [show (fun i : Fin 1 => if (fun _ : Fin 1 => true) i then u i else v i) = u from by
          funext i; simp] at hω
      · have hω := h (fun _ => false)
        rwa [show (fun i : Fin 1 => if (fun _ : Fin 1 => false) i then u i else v i) = v from by
          funext i; simp] at hω
    · rintro ⟨h1, h2⟩ ω
      have hω : ω = fun _ => ω 0 := by funext i; exact congrArg ω (Subsingleton.elim i 0)
      rw [hω]
      have hmix : (fun i : Fin 1 => if (fun _ : Fin 1 => ω 0) i then u i else v i)
          = (if ω 0 then u else v) := by
        cases h : ω 0 <;> simp
      rw [hmix]
      cases h : ω 0
      · exact h2
      · exact h1
  simp only [hcond]
  have hinner : ∀ u : Fin 1 → ℤ,
      (∑ v ∈ thetaBox 1 D, (if ((a, u) ∈ H ∧ (a, v) ∈ H) then f a u v else 0))
        = if ((a, u) ∈ H) then
            (∑ v ∈ thetaBox 1 D, (if (a, v) ∈ H then f a u v else 0)) else 0 := by
    intro u
    by_cases h : (a, u) ∈ H <;> simp [h]
  rw [Finset.sum_congr rfl (fun u _ => hinner u)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [← Finset.sum_filter]
  rw [show thetaFibre D H a = (thetaBox 1 D).filter (fun v => (a, v) ∈ H) from rfl]

theorem concMass_eq_sum {Z : Type} [Fintype Z] (D B : ℕ) (G : Z → ℤ → ℂ)
    (H : Finset ((Fin 1 → ℤ) × (Fin 1 → ℤ))) (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ)
    (hH : ∀ p ∈ H, p.1 ∈ thetaBox 1 D ∧ p.2 ∈ thetaBox 1 D) :
    concMass 1 D B G H φ
      = ∑ a ∈ thetaBox 1 D,
          ∑ u ∈ thetaFibre D H a,
            ∑ v ∈ thetaFibre D H a,
              ‖((B : ℂ))⁻¹ * gramD G φ a u v‖ ^ 2 := by
  simp only [concMass]
  rw [ThetaSet_one_sum' H (f := fun a u v => ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
      ((Fintype.card Z : ℂ))⁻¹ * ∑ z, Work.Peluse.cubeTerm u v (G z) x *
      Complex.exp (2 * Real.pi * Complex.I *
        (((mixedPhase φ (a, u, v) : ℝ)) : ℂ) * (x : ℂ))‖ ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun u _ =>
    Finset.sum_congr rfl (fun v _ => ?_)))
  have hφ : (((mixedPhase φ (a, u, v) : ℝ)) : ℂ) = (φ a v : ℂ) - (φ a u : ℂ) := by
    rw [mixedPhase_fin1 φ a u v]
    push_cast
    ring
  have htsum : (∑' x : ℤ, ((Fintype.card Z : ℂ))⁻¹ * ∑ z,
          Work.Peluse.cubeTerm u v (G z) x *
          Complex.exp (2 * Real.pi * Complex.I *
            (((mixedPhase φ (a, u, v) : ℝ)) : ℂ) * (x : ℂ)))
      = ∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I *
            ((φ a v : ℂ) - (φ a u : ℂ)) * (x : ℂ)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + v 0) * star (G z (x + u 0))) := by
    apply tsum_congr
    intro x
    rw [hφ]
    rw [show (∑ z, Work.Peluse.cubeTerm u v (G z) x *
          Complex.exp (2 * Real.pi * Complex.I * ((φ a v : ℂ) - (φ a u : ℂ)) * (x : ℂ)))
        = (∑ z, G z (x + v 0) * star (G z (x + u 0))) *
          Complex.exp (2 * Real.pi * Complex.I * ((φ a v : ℂ) - (φ a u : ℂ)) * (x : ℂ)) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [cubeTerm_fin1 u v (G z) x]]
    ring
  rw [htsum, gramD]

end Work.Peluse.Ulower.StepLe.ddiSharp.one
