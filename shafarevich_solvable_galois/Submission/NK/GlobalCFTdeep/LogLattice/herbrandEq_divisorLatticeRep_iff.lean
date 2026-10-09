import Mathlib
import Submission.NK.GlobalCFTdeep.LogLattice.LogLatticeMain
import Submission.NK.GlobalCFTdeep.Herbrand.RepIso
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.LogLattice

/-- **The divisor lattice is the permutation module `Hom(T, ℤ)`.**  The `ℤ[Gal(L/K)]`-module
`NK.GlobalCFTdeep.divisorLatticeRep` (integer-valued functions on `T`, inside `∏_{w ∈ T} ℝ`)
is isomorphic to `NK.GlobalCFTdeep.placeFunRep` (`↥T → ℤ` with the permutation action), via
`NK.GlobalCFTdeep.divisorHom : (↥T → ℤ) →+ ↥(divisorLattice T)`,
`g ↦ (fun w => g w)`, which is bijective (`NK.GlobalCFTdeep.divisorHom_bijective`) and
`G`-equivariant.  Hence the two have the same Herbrand quotient
(`NK.GlobalCFTdeep.Herbrand.herbrandEq_of_repIso`, `Herbrand/RepIso.lean`).

Proof: build the `Rep ℤ G`-morphism from `Rep.ofHom` with `toFun := divisorHom T`, prove the
intertwining property by `Subtype.ext (funext fun w => rfl)`, get a `LinearEquiv` by
`LinearEquiv.ofBijective`, and package it as an isomorphism with
`Rep.mkIso (Representation.Equiv.mk e (fun γ => f.hom.isIntertwining' γ))` (the pattern of
`Herbrand/fiberIdelesRep_iso_coind.lean`).  The two permutation actions must be installed with
`letI := permAction T hT ℤ` / `letI := permAction T hT ℝ`. -/
theorem herbrandEq_divisorLatticeRep_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T) (m : ℕ) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.divisorLatticeRep (L := L) T hT) m ↔
      NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.placeFunRep (L := L) T hT) m := by
  have hbij : Function.Bijective (NK.GlobalCFTdeep.divisorHom (L := L) T) :=
    NK.GlobalCFTdeep.divisorHom_bijective T
  let e : (↥T → ℤ) ≃ₗ[ℤ] ↥(NK.GlobalCFTdeep.divisorLattice (L := L) T) :=
    LinearEquiv.ofBijective
      (NK.GlobalCFTdeep.divisorHom (L := L) T).toIntLinearMap hbij
  have he : ∀ σ : L ≃ₐ[K] L,
      e.toLinearMap ∘ₗ (NK.GlobalCFTdeep.placeFunRep (L := L) T hT).ρ σ =
        (NK.GlobalCFTdeep.divisorLatticeRep (L := L) T hT).ρ σ ∘ₗ e.toLinearMap := by
    intro σ
    apply LinearMap.ext
    intro f
    exact (show (NK.GlobalCFTdeep.divisorLatticeRep (L := L) T hT).ρ σ
          (NK.GlobalCFTdeep.divisorHom (L := L) T f)
        = NK.GlobalCFTdeep.divisorHom (L := L) T
            ((NK.GlobalCFTdeep.placeFunRep (L := L) T hT).ρ σ f) from rfl)
  exact (NK.GlobalCFTdeep.herbrandEq_of_repIso
    (Rep.mkIso (Representation.Equiv.mk e he)) m).symm

end NK.GlobalCFTdeep.LogLattice
