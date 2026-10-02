import Submission.Work.Cohomology.Endgame.shiftCap
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.relChainsProjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cap-map comparison square, and the element forms it needs

`Work.Cohomology.Endgame.exists_capTopCanon_relCapHalf` is the last mathematical step of the
transgression route (NOTES §16–§19): it identifies the homology map of the chain-level cap map
`capTopCanon` (`shiftCap.lean`) with the abstract relative cap product `relCapHalf` (`RelCap.lean`),
along the quasi-isomorphism `phi : relMVTopC X A U V ⟶ relChains X A` produced by
`relMV_quasiIso`.  Together with `transgression_capUvCanon` and `dshShort_cruxShort_delta` it gives
the transgression identity `U (a ⌢ c) = ± (r a) ⌢ (T c)` of the endgame.

## How it is proved (the technique is the point)

The four computation rules involved — `cokernelComponentIso_canon`, `relCapHalf_apply`,
`capTopCanon_spec`, `capSub_comp_incl` — have their ambient objects spelled through `abbrev`s
(`relChainsModule`, `relChains`, `relMVTopC`, `smallChains`, `inclChains`) which `rw`'s motive check
does **not** unfold once the goal has been reshaped, even though they are `abbrev`-equal.  The
proof therefore:

1. cancels the epimorphism `(cokernel.π (smallInToSmall U V A)).f (4+m)` and uses the compatibility
   `h2` degreewise (`hlevel`);
2. descends to elements (`ext y`, `ModuleCat.hom_comp`, `LinearMap.comp_apply`) and states every
   rule as an equation between elements, with the **projection the goal itself uses**
   (`ModuleCat.Hom.hom`);
3. where two `abbrev` spellings are needed *inside one term* — `relCapHalf`'s domain is
   `relChainsModule ℤ X A (4+m)` while its argument is an element of the bare
   `cokernel ((inclChains X A).f (4+m))` — inserts the **explicit cast**
   `eqToHom hcast.symm` (`hcast : relChainsModule ℤ X A (4+m) = cokernel ((inclChains X A).f
   (4+m))`, provable by `rfl`), which is definitionally the identity, so a leading `show` accepts it;
   `simp only [CategoryTheory.eqToHom_refl, …]` then reduces the cast, fires the three rules that
   match, and leaves the last rule to a final `show` (which removes the inserted identity
   application) followed by `exact`.

**The reusable rule**: `show` changes spelling (statement-level `isDefEq` unfolds `abbrev`s), `rw`
does not; and `show` cannot unfold a *local* definition, so the spelling must be a global
`abbrev`/`def` unfolding.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

noncomputable section

/-- Element form of the canonical comparison between `(cokernel.π f).f n` and `cokernel.π (f.f n)`.

The statement uses *verbatim* the type spellings Lean produces for the goal of the comparison
square: the element lives in `↑(cokernel (f.f n))`, and the morphisms are projected with
`ConcreteCategory.hom` (the projection the goal itself uses) — mixing in `ModuleCat.Hom.hom`, or
routing the codomain through the `abbrev` `relChainsModule`, makes the `rw` fail in the motive
check (see `Endgame/NOTES.md` §19). -/
theorem cokernelComponentIso_canon_apply (X : TopCat) (A : Set X) (m : ℕ)
    (y : ↑((singularChains ℤ X).X (4 + m))) :
    ModuleCat.Hom.hom (cokernelComponentIso (inclChains X A) (4 + m)).hom
        (ModuleCat.Hom.hom ((cokernel.π (inclChains X A)).f (4 + m)) y)
      = ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (4 + m))) y := by
  have h := congrArg (fun (g : (singularChains ℤ X).X (4 + m) ⟶
      cokernel ((inclChains X A).f (4 + m))) => g.hom y)
    (cokernelComponentIso_canon (inclChains X A) (4 + m))
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Element form of the computation rule for `relCapHalf`. -/
theorem relCapHalf_apply' (X : TopCat) (A : Set X) (α : relKern ℤ X A 4) (m : ℕ)
    (y : ↑((singularChains ℤ X).X (4 + m))) :
    ModuleCat.Hom.hom (relCapHalf ℤ X A α m) (ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (4 + m))) y)
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α.1 m) y := by
  show (ModuleCat.Hom.hom (relCapHalf ℤ X A α m))
      ((ModuleCat.Hom.hom (cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f (4 + m)))) y)
      = (ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α.1 m)) y
  rw [relCapHalf_apply ℤ X A α y]
  rfl

/-- Element form of `capTopCanon_spec`. -/
theorem capTopCanon_spec_apply (X : TopCat) (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ)
    (y : ↑((smallChains U V).X (4 + m))) :
    ModuleCat.Hom.hom (capTopCanon A U V α m) (ModuleCat.Hom.hom ((cokernel.π (smallInToSmall U V A)).f (4 + m)) y)
      = ModuleCat.Hom.hom (capSub (Y := TopCat.toSSet.obj X) (smallSubcomplex U V) 4 m α.1) y := by
  have h := congrArg (fun (g : (smallChains U V).X (4 + m) ⟶ (smallChains U V).X m) => ModuleCat.Hom.hom g y)
    (capTopCanon_spec A U V α m)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Element form of `capSub_comp_incl`. -/
theorem capSub_comp_incl_apply (X : TopCat) (U V : Set X) (m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) 4) (y : ↑((smallChains U V).X (4 + m))) :
    ModuleCat.Hom.hom ((smallToSing U V).f m) (ModuleCat.Hom.hom (capSub (Y := TopCat.toSSet.obj X) (smallSubcomplex U V) 4 m α) y)
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α m) (ModuleCat.Hom.hom ((smallToSing U V).f (4 + m)) y) := by
  have h := congrArg (fun (g : (smallChains U V).X (4 + m) ⟶ singChains ℤ X m) => ModuleCat.Hom.hom g y)
    (capSub_comp_incl (Y := TopCat.toSSet.obj X) (smallSubcomplex U V) 4 m α)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem exists_capTopCanon_relCapHalf (X : TopCat) (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (α : relKern ℤ X A 4) (m : ℕ) :
    ∃ phi : relMVTopC X A U V ⟶ relChains X A,
      (∀ n : ℕ, IsIso (HomologicalComplex.homologyMap phi n)) ∧
      cokernel.π (smallInToSmall U V A) ≫ phi = smallToSing U V ≫ cokernel.π (inclChains X A) ∧
      phi.f (4 + m) ≫ (cokernelComponentIso (inclChains X A) (4 + m)).hom ≫ relCapHalf ℤ X A α m
        = capTopCanon A U V α m ≫ (smallToSing U V).f m := by
  obtain ⟨phi, h1, h2⟩ := relMV_quasiIso X A U V hU hV hcov
  refine ⟨phi, h1, h2, ?_⟩
  haveI : Epi ((cokernel.π (smallInToSmall U V A)).f (4 + m)) := epi_cokernel_π_f _ (4 + m)
  have hlevel : (cokernel.π (smallInToSmall U V A)).f (4 + m) ≫ phi.f (4 + m)
      = (smallToSing U V).f (4 + m) ≫ (cokernel.π (inclChains X A)).f (4 + m) := by
    rw [← HomologicalComplex.comp_f, h2, HomologicalComplex.comp_f]
  rw [← cancel_epi ((cokernel.π (smallInToSmall U V A)).f (4 + m))]
  simp only [← Category.assoc]
  rw [hlevel]
  ext y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcast : relChainsModule ℤ X A (4 + m) = cokernel ((inclChains X A).f (4 + m)) := rfl
  show (ModuleCat.Hom.hom (relCapHalf ℤ X A α m))
      ((eqToHom hcast.symm).hom
        ((ModuleCat.Hom.hom (cokernelComponentIso (inclChains X A) (4 + m)).hom)
          ((ModuleCat.Hom.hom ((cokernel.π (inclChains X A)).f (4 + m)))
            ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y))))
      = (ModuleCat.Hom.hom ((smallToSing U V).f m))
          ((ModuleCat.Hom.hom (capTopCanon A U V α m))
            ((ModuleCat.Hom.hom ((cokernel.π (smallInToSmall U V A)).f (4 + m))) y))
  simp only [CategoryTheory.eqToHom_refl, cokernelComponentIso_canon_apply,
    relCapHalf_apply', capTopCanon_spec_apply, capSub_comp_incl_apply]
  show (ModuleCat.Hom.hom (relCapHalf ℤ X A α m))
      ((ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (4 + m))))
        ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y))
      = (ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α.1 m))
          ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y)
  exact relCapHalf_apply' X A α m ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y)

end

end Work.Cohomology
