import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.SSGRoute.H1Dual.DegreeZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bijectivity of the degree-`0` evaluation pairing `(H₀(G,N))^∨ → H⁰(G, N^∨)`

The pairing `H0DualMap N` of `Submission.Work.SSGRoute.H1Dual.DegreeZero` is the composite

* `(H₀(G,N))^∨ → ((N_G))^∨`, the transpose of the isomorphism `H0Iso N : H₀(G,N) ≅ N_G`,
* `((N_G))^∨ → (N^∨)^G`, the auxiliary map `H0DualAux N` induced by the quotient map `N ↠ N_G`,
* `(N^∨)^G → H⁰(G,N^∨)`, the inverse of the isomorphism `H0Iso (N^∨)`.

The first and the third are linear equivalences, so everything rests on the classical fact that
evaluation `(n, ψ) ↦ ψ n` identifies the dual of the coinvariants `N_G` with the invariants of
the dual `(N^∨)^G`; this is `H0DualAux_bijective` below. Concretely, a `G`-invariant functional
on `N` kills every element `ρ g x - x`, hence descends to `N_G` (surjectivity), and a functional
vanishing on `N_G` vanishes on all of `N` because `N ↠ N_G` is surjective (injectivity).
-/

namespace Work.SSGRoute.H1Dual

open CategoryTheory

noncomputable section

universe u

/-- The auxiliary degree-`0` evaluation pairing `(N_G)^∨ →ₗ (N^∨)^G` is bijective: a linear
functional on the coinvariants is exactly a `G`-invariant linear functional on `N`. -/
theorem H0DualAux_bijective {k : Type u} [CommRing k] {G : Type u} [Group G]
    (N : Rep k G) :
    Function.Bijective (Work.SSGRoute.H0DualAux N) := by
  constructor
  · -- Injectivity: `H0DualAux N l = l ∘ mk` and `mk` is surjective.
    intro l l' h
    have hval : ∀ x : N.V, l (Representation.Coinvariants.mk N.ρ x)
        = l' (Representation.Coinvariants.mk N.ρ x) := by
      intro x
      have hx := congrArg
        (fun f : ↥((Work.SSGRoute.dualRep N).ρ.invariants) => (f : N.V →ₗ[k] k) x) h
      simpa [Work.SSGRoute.H0DualAux] using hx
    exact Representation.Coinvariants.hom_ext (LinearMap.ext hval)
  · -- Surjectivity: an invariant functional is constant on the coinvariants relation, hence
    -- descends to `N_G`.
    intro ψ
    have hinv : ∀ g : G, (ψ : N.V →ₗ[k] k) ∘ₗ N.ρ g = ψ := by
      intro g
      have h2 := ψ.2 g⁻¹
      simpa [Work.SSGRoute.dualRep, Representation.dual_apply, Module.Dual.transpose_apply]
        using h2
    refine ⟨Representation.Coinvariants.lift N.ρ ψ.1 hinv, ?_⟩
    ext x
    show (Representation.Coinvariants.lift N.ρ (ψ.1) hinv).comp
        (Representation.Coinvariants.mk N.ρ) x = ψ.1 x
    simp

/-- The degree-`0` evaluation pairing `(H₀(G,N))^∨ →ₗ H⁰(G, N^∨)` (defined in
`Submission.Work.SSGRoute.H1Dual.DegreeZero` as `H0DualMap`) is bijective. -/
theorem degreeZeroBijective {k : Type} [Field k] {G : Type} [Group G] (N : Rep k G) :
    Function.Bijective (Work.SSGRoute.H0DualMap N) := by
  have h1 : Function.Bijective
      ((LinearEquiv.dualMap (Iso.toLinearEquiv (groupHomology.H0Iso N)).symm).toLinearMap) :=
    (LinearEquiv.dualMap (Iso.toLinearEquiv (groupHomology.H0Iso N)).symm).bijective
  have h3 : Function.Bijective
      ((Iso.toLinearEquiv (groupCohomology.H0Iso (Work.SSGRoute.dualRep N))).symm) :=
    (Iso.toLinearEquiv (groupCohomology.H0Iso (Work.SSGRoute.dualRep N))).symm.bijective
  change Function.Bijective (fun x => Work.SSGRoute.H0DualMap N x)
  have hcomp : (fun x => Work.SSGRoute.H0DualMap N x)
      = fun x =>
          (Iso.toLinearEquiv (groupCohomology.H0Iso (Work.SSGRoute.dualRep N))).symm
            (Work.SSGRoute.H0DualAux N
              ((LinearEquiv.dualMap (Iso.toLinearEquiv (groupHomology.H0Iso N)).symm) x)) :=
    rfl
  rw [hcomp]
  exact h3.comp ((H0DualAux_bijective N).comp h1)

end

end Work.SSGRoute.H1Dual
