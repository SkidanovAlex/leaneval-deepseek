import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp.one

private theorem sum_H_fibre' {σ D : ℕ} {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    (hH : ∀ p ∈ H, p.1 ∈ thetaBox σ D ∧ p.2 ∈ thetaBox σ D)
    {M : Type*} [AddCommMonoid M] (f : (Fin σ → ℤ) → (Fin σ → ℤ) → M) :
    (∑ p ∈ H, f p.1 p.2) = ∑ a ∈ thetaBox σ D, ∑ u ∈ thetaFibre D H a, f a u := by
  classical
  let P : (Fin σ → ℤ) × (Fin σ → ℤ) → Prop := fun p => p ∈ H
  have h1 : H = ((thetaBox σ D) ×ˢ (thetaBox σ D)).filter P := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => ⟨⟨(hH p h).1, (hH p h).2⟩, h⟩, fun h => h.2⟩
  have hsum : (∑ p ∈ H, f p.1 p.2)
      = ∑ p ∈ (thetaBox σ D) ×ˢ (thetaBox σ D), (if P p then f p.1 p.2 else 0) := by
    conv_lhs => rw [h1]
    rw [Finset.sum_filter]
  rw [hsum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have key : (∑ u ∈ thetaFibre D H a, f a u)
      = ∑ u ∈ thetaBox σ D, (if P (a, u) then f a u else 0) := by
    rw [show thetaFibre D H a = (thetaBox σ D).filter (fun u => (a, u) ∈ H) from rfl,
      Finset.sum_filter]
  rw [key]

theorem hypoMass_eq_sum {Z : Type} [Fintype Z] (B D : ℕ) (G : Z → ℤ → ℂ)
    (H : Finset ((Fin 1 → ℤ) × (Fin 1 → ℤ))) (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ)
    (hH : ∀ p ∈ H, p.1 ∈ thetaBox 1 D ∧ p.2 ∈ thetaBox 1 D) :
    hypoMass 1 B G H φ
      = ∑ a ∈ thetaBox 1 D, ∑ u ∈ thetaFibre D H a, ‖((B : ℂ))⁻¹ * rowC G φ a u‖ ^ 2 := by
  simp only [hypoMass]
  rw [sum_H_fibre' hH (f := fun a u => ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        Work.Peluse.cubeTerm a u (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x *
        Complex.exp (2 * Real.pi * Complex.I * (φ a u : ℂ) * (x : ℂ))‖ ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun u _ => ?_))
  have htsum : (∑' x : ℤ, Work.Peluse.cubeTerm a u
          (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x *
        Complex.exp (2 * Real.pi * Complex.I * (φ a u : ℂ) * (x : ℂ)))
      = ∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * (φ a u : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a 0)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + u 0)) := by
    apply tsum_congr
    intro x
    rw [cubeTerm_fin1 a u (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x]
    ring
  rw [htsum, rowC]
  rfl

end Work.Peluse.Ulower.StepLe.ddiSharp.one
