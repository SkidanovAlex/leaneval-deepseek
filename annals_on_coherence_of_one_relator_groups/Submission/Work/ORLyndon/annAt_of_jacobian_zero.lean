import Mathlib
import Submission.Work.ORLyndon.nielsenTransfer

/-!
# Componentwise Nielsen transfer of `annAt` under a Jacobian-vanishing hypothesis

`Work.ORLyndon.annAt K (u ^ l) u E` says that the componentwise annihilator of the Fox vector
`(∂u/∂x)_x` of the root `u` is trivial in `K[⟨X | u ^ l⟩]`.  The Nielsen transfer of `Vann` (the
triviality of the annihilator of the *whole* vector) under an automorphism `ψ` of the free group is
`Work.ORLyndon.vann_of_vann_psi`: the Fox vector of `ψ u` is the image of the Fox vector of `u`
along the isomorphism `⟨X | u ^ l⟩ ≅ ⟨X | (ψ u) ^ l⟩`, contracted with the Jacobian
`(∂(ψ x)/∂y)_{x,y}`.

For the *componentwise* statement at a single letter `x` the contraction is not harmless: a
component `(∂ψ u/∂x)` need not be the image of the component `(∂u/∂x)`.  The present file treats the
case in which the Jacobian is *zero off the diagonal at `x`*: if `∂(ψ q)/∂x = 0` for every generator
`q ≠ x`, then the Fox chain rule collapses to a single term,

`∂(ψ u)/∂x = Φ (∂u/∂x) · ∂(ψ x)/∂x`,  `Φ = MonoidAlgebra.mapDomainRingHom K ψ`,

so that the component `(∂ψ u/∂x)` of the transformed root is the image of the component
`(∂u/∂x)` of `u` *times an arbitrary right factor*.  Right multiplication by that factor does not
destroy vanishing, so the whole argument of `vann_of_vann_psi` goes through componentwise and gives

`annAt K ((ψ u) ^ l) (ψ u) {x} → annAt K (u ^ l) u {x}`.

## Main results

* `Work.ORLyndon.foxD_comp_of_jacobian_zero` -- the collapse of the Fox chain rule;
* `Work.ORLyndon.annAt_of_jacobian_zero` -- the componentwise Nielsen transfer.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **The Fox chain rule collapses onto the `x`-coordinate** when the Jacobian of `ψ` vanishes off
the diagonal at `x`: if `∂(ψ q)/∂x = 0` for every generator `q ≠ x`, then
`∂(ψ u)/∂x = Φ (∂u/∂x) · ∂(ψ x)/∂x`, where `Φ = MonoidAlgebra.mapDomainRingHom K ψ`. -/
theorem foxD_comp_of_jacobian_zero {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (ψ : FreeGroup α →* FreeGroup α) (u : FreeGroup α) (x : α)
    (hJ : ∀ q : α, q ≠ x → foxD (K := K) x (ψ (FreeGroup.of q)) = 0) :
    foxD (K := K) x (ψ u) =
      MonoidAlgebra.mapDomainRingHom K ψ (foxD (K := K) x u) *
        foxD (K := K) x (ψ (FreeGroup.of x)) := by
  rw [foxD_comp (K := K) ψ x u]
  have h : ∀ q : α, foxD (K := K) x (ψ (FreeGroup.of q)) =
      if q = x then foxD (K := K) x (ψ (FreeGroup.of x)) else 0 := by
    intro q
    by_cases hq : q = x
    · subst hq; simp
    · simp [hq, hJ q hq]
  rw [Finsupp.sum_congr
        (g2 := fun q c => if q = x then (MonoidAlgebra.mapDomainRingHom K ψ) c *
          foxD (K := K) x (ψ (FreeGroup.of x)) else 0) ?_,
      Finsupp.sum_ite_eq', foxFD_apply]
  · by_cases hx : x ∈ (foxFD (K := K) u).support
    · rw [if_pos hx]
    · rw [if_neg hx]
      have hx2 : foxD (K := K) x u = 0 := by
        rw [← foxFD_apply]
        by_contra hcon
        exact hx (Finsupp.mem_support_iff.mpr hcon)
      rw [hx2, map_zero, zero_mul]
  · intro q _
    rw [h q, mul_ite, mul_zero]

/-- **Componentwise Nielsen transfer of `annAt`.**  If the Jacobian `(∂(ψ q)/∂x)_q` vanishes for
every generator `q ≠ x`, then the triviality of the annihilator of the single component
`(∂(ψ u)/∂x)` in `K[⟨X | (ψ u) ^ l⟩]` implies the same for `(∂u/∂x)` in `K[⟨X | u ^ l⟩]`. -/
theorem annAt_of_jacobian_zero {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (ψ : FreeGroup α →* FreeGroup α) (hι : Function.Injective ψ) (hσ : Function.Surjective ψ)
    (u : FreeGroup α) (l : ℕ) (x : α)
    (hJ : ∀ q : α, q ≠ x → foxD (K := K) x (ψ (FreeGroup.of q)) = 0) :
    annAt K ((ψ u) ^ l) (ψ u) {x} → annAt K (u ^ l) u {x} := by
  intro h b hb
  set B := MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b with hB
  -- The image of `b` kills the `x`-component of the root `ψ u` in `K[⟨X | (ψ u) ^ l⟩]`.
  have hzero : B * rootVec K ((ψ u) ^ l) (ψ u) x = 0 := by
    rw [rootVec_apply, foxD_comp_of_jacobian_zero ψ u x hJ, map_mul,
      ← mapDomainRingHom_psiBar_presentAlg ψ u l (foxD (K := K) x u),
      ← mul_assoc, ← map_mul, ← rootVec_apply]
    rw [hb x (Set.mem_singleton x), map_zero, zero_mul]
  have hB0 : B = 0 := h B (fun y hy => by
    rw [Set.mem_singleton_iff] at hy; subst hy; exact hzero)
  have h0 : MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b = 0 := by
    rw [← hB]; exact hB0
  exact MonoidAlgebra.mapDomain_injective (psiBar_injective ψ hι hσ u l)
    (by rw [MonoidAlgebra.mapDomain_zero]
        simpa only [MonoidAlgebra.mapDomainRingHom_apply] using h0)

end Work.ORLyndon
