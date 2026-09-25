import Mathlib
import Submission.Work.Tower.Shafarevich.Cohomology.TwistedExt

namespace Work.Tower.Shafarevich.Cohomology

/-- Two maps `τ τ'` on a free group satisfying the same cocycle-multiplication law
`τ (u * v) = τ u + τ v + κ (φ u, φ v)`, both normalized by `τ 1 = 0`, and agreeing on the
generators, are equal: their difference is a genuine homomorphism out of the free group
vanishing on generators. -/
theorem tau_unique {p : ℕ} {G : Type*} [Group G] {d : ℕ} (κ : G × G → ZMod p)
    (φ : FreeGroup (Fin d) →* G) {τ τ' : FreeGroup (Fin d) → ZMod p} (h1 : τ 1 = 0)
    (hmul : ∀ u v, τ (u * v) = τ u + τ v + κ (φ u, φ v)) (h1' : τ' 1 = 0)
    (hmul' : ∀ u v, τ' (u * v) = τ' u + τ' v + κ (φ u, φ v))
    (hgen : ∀ i, τ (FreeGroup.of i) = τ' (FreeGroup.of i)) : τ = τ' := by
  -- Values on inverses are forced by the cocycle law applied to `u * u⁻¹ = 1`.
  have inv_eq : ∀ (σ : FreeGroup (Fin d) → ZMod p), σ 1 = 0 →
      (∀ u v, σ (u * v) = σ u + σ v + κ (φ u, φ v)) →
      ∀ u : FreeGroup (Fin d), σ u⁻¹ = -σ u - κ (φ u, φ u⁻¹) := by
    intro σ hs1 hsmul u
    have h2 := hsmul u u⁻¹
    rw [mul_inv_cancel, hs1] at h2
    linear_combination -h2
  have key : ∀ u : FreeGroup (Fin d), τ u = τ' u := by
    intro u
    refine FreeGroup.induction_on u ?_ ?_ ?_ ?_
    · rw [h1, h1']
    · intro i; exact hgen i
    · intro i hi
      rw [inv_eq τ h1 hmul (FreeGroup.of i), inv_eq τ' h1' hmul' (FreeGroup.of i), hi]
    · intro x y hx hy
      rw [hmul x y, hmul' x y, hx, hy]
  exact funext key

end Work.Tower.Shafarevich.Cohomology
