import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relCohMVDefs
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.MVcapSquares

/-!
# The components of a cokernel of chain complexes

**The `n`-th component of the cokernel of a morphism of chain complexes is the cokernel of the
`n`-th component.**  The evaluation functor `HomologicalComplex.eval` preserves colimits, so the
colimiting cocone defining `(cokernel f).X n` is a colimiting cocone for the diagram
`parallelPair (f.f n) 0`; the two functors `parallelPair f 0 ⋙ eval` and `parallelPair (f.f n) 0`
are equal (same objects, same morphisms), which compares the two colimits.

This is the connective tissue needed to descend a construction on the small chains of a cover to
the relative complexes `C^{U,V}_*(X,A) = coker(C^{U,V}_*(A) → C^{U,V}_*(X))`; the pattern is the one
of `Work.Cohomology.relChains_cokernelIso` (`relChainsProjective.lean`).

## Main results

* `cokernelComponentIso f n : (cokernel f).X n ≅ cokernel (f.f n)`;
* `relSmallTopCokernelIso U V A n : (relSmallTop U V A).X n ≅ cokernel ((smallInToSmall U V A).f n)`;
* `relSmallChainsCokernelIso U V B C h n : (relSmallChains U V B C h).X n ≅ cokernel ((subInclChain U V h).f n)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The `n`-th component of the cokernel of a morphism of chain complexes is the cokernel of the
`n`-th component.** -/
def cokernelComponentIso {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    (cokernel f).X n ≅ cokernel (f.f n) := by
  let F : WalkingParallelPair ⥤ ModuleCat ℤ := (parallelPair f 0) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
  let G : WalkingParallelPair ⥤ ModuleCat ℤ := parallelPair (f.f n) 0
  have hFG : F = G := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j <;> rfl
    · rintro X' Y' g
      match g with
      | .left => cat_disch
      | .right => cat_disch
      | .id Z => cat_disch
  exact IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
        (colimit.isColimit (parallelPair f 0)))
      (colimit.isColimit F) ≪≫ HasColimit.isoOfNatIso (eqToIso hFG)

/-- **`cokernelComponentIso` is the canonical comparison**: composed with the projection
`cokernel.π f` it is the degreewise cokernel projection. -/
theorem cokernelComponentIso_canon {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    (cokernel.π f).f n ≫ (cokernelComponentIso f n).hom = cokernel.π (f.f n) := by
  simp only [cokernelComponentIso]
  have hs : ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0))).ι.app WalkingParallelPair.one
      = (cokernel.π f).f n := rfl
  rw [← hs]
  rw [coconePointUniqueUpToIso_comp_isoOfNatIso_ι
    ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0)))
    _ (eqToIso _) WalkingParallelPair.one]
  simp

variable {X : TopCat}

/-- The `n`-th component of the relative small chains `C^{U,V}_*(X,A)` is the cokernel of the
`n`-th component of `smallInToSmall`. -/
def relSmallTopCokernelIso (U V A : Set X) (n : ℕ) :
    (relSmallTop U V A).X n ≅ cokernel ((smallInToSmall U V A).f n) :=
  cokernelComponentIso (smallInToSmall U V A) n

/-- The `n`-th component of the relative small chains `C^{U,V}_*(B,C)` is the cokernel of the
`n`-th component of `subInclChain`. -/
def relSmallChainsCokernelIso (U V B C : Set X) (h : C ⊆ B) (n : ℕ) :
    (relSmallChains U V B C h).X n ≅ cokernel ((subInclChain U V h).f n) :=
  cokernelComponentIso (subInclChain U V h) n

/-- **The cap product descends to the relative small chains of the cover.**  By the descent lemma
`smallInToSmall_capSub_eq_zero` the cap map with a relative cocycle factors through the quotient
`C^{U,V}_*(X,A) = C^{U,V}_*(X)/C^{U,V}_*(A) = relMVTopC X A U V`. -/
theorem exists_cap_relMVTopC (X : TopCat) (U V A : Set X) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n) :
    ∃ ψ : (relMVTopC X A U V).X (n + m) ⟶ (smallChains U V).X m,
      (cokernel.π (smallInToSmall U V A)).f (n + m) ≫ ψ =
        capSub (smallSubcomplex U V) n m α := by
  refine ⟨(cokernelComponentIso (smallInToSmall U V A) (n + m)).hom ≫
    cokernel.desc _ _ (smallInToSmall_capSub_eq_zero X U V A n m α hα), ?_⟩
  rw [← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-- **The cap product descends to the relative small chains `C^{U,V}_*(B,C)` of the cover.**  This
covers the `U`-, `V`- and `U ∩ V`-terms of the relative Mayer–Vietoris sequence; the top term is
`exists_cap_relMVTopC`. -/
theorem exists_cap_relSmallChains (X : TopCat) (U V B C : Set X) (hCB : C ⊆ B) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X C n) :
    ∃ ψ : (relSmallChains U V B C hCB).X (n + m) ⟶ (smallInChains U V B).X m,
      (cokernel.π (subInclChain U V hCB)).f (n + m) ≫ ψ =
        capSub (smallInSubcomplex U V B) n m α := by
  refine ⟨(cokernelComponentIso (subInclChain U V hCB) (n + m)).hom ≫
    cokernel.desc _ _ (subInclChain_capSub_eq_zero X U V B C hCB n m α hα), ?_⟩
  rw [← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-! ## The descended cap maps, as definitions

The cap maps of the SES-morphism are fixed once and for all from the existence statements above
(the pattern of `Work.Cohomology.relCapPair` / `relCapPair_apply`). -/

/-- **The cap product with a relative cocycle, descended to the relative complex
`C^{U,V}_*(X,A)`** (the top term of the relative Mayer–Vietoris sequence). -/
noncomputable def capRelTop (X : TopCat) (A U V : Set X) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n) :
    (relMVTopC X A U V).X (n + m) ⟶ (smallChains U V).X m :=
  Classical.choose (exists_cap_relMVTopC X U V A n m α hα)

/-- **The computation rule of `capRelTop`**: composed with the projection it is the cap product. -/
theorem capRelTop_spec (X : TopCat) (A U V : Set X) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n) :
    (cokernel.π (smallInToSmall U V A)).f (n + m) ≫ capRelTop X A U V n m α hα =
      capSub (smallSubcomplex U V) n m α :=
  Classical.choose_spec (exists_cap_relMVTopC X U V A n m α hα)

/-- **The cap product with a relative cocycle, descended to the relative small chains
`C^{U,V}_*(B,C)`** (`B = U`, `V` or `U ∩ V` in the applications). -/
noncomputable def capRelSmall (X : TopCat) (U V B C : Set X) (hCB : C ⊆ B) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X C n) :
    (relSmallChains U V B C hCB).X (n + m) ⟶ (smallInChains U V B).X m :=
  Classical.choose (exists_cap_relSmallChains X U V B C hCB n m α hα)

/-- **The computation rule of `capRelSmall`**: composed with the projection it is the cap
product. -/
theorem capRelSmall_spec (X : TopCat) (U V B C : Set X) (hCB : C ⊆ B) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X C n) :
    (cokernel.π (subInclChain U V hCB)).f (n + m) ≫ capRelSmall X U V B C hCB n m α hα =
      capSub (smallInSubcomplex U V B) n m α :=
  Classical.choose_spec (exists_cap_relSmallChains X U V B C hCB n m α hα)

/-- **The naturality of the projection to a cokernel**: `cokernel.π f ≫ cokernel.map f f' p q w`
equals `q ≫ cokernel.π f'`.  (Reproduced here so that the capped-manifold world does not have to
import the modules that declare it; the proof is the one of `cokernel.π_desc`.) -/
theorem cokernel_π_cokernelMap {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B A' B' : C} (f : A ⟶ B) [HasCokernel f] (f' : A' ⟶ B') [HasCokernel f']
    (p : A ⟶ A') (q : B ⟶ B') (w : f ≫ q = p ≫ f') :
    cokernel.π f ≫ cokernel.map f f' p q w = q ≫ cokernel.π f' := by
  rw [cokernel.map]
  exact cokernel.π_desc _ _ _

/-- **The components of `cokernel.map`.**  Conjugated by the component isomorphisms
`cokernelComponentIso`, the `n`-th component of the cokernel-map of a morphism of chain complexes is
the cokernel-map of the `n`-th components. -/
theorem cokernelComponentIso_map {K L K' L' : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K ⟶ L) (f' : K' ⟶ L') (p : K ⟶ K') (q : L ⟶ L') (w : f ≫ q = p ≫ f') (n : ℕ) :
    (cokernelComponentIso f n).inv ≫ (cokernel.map f f' p q w).f n =
      cokernel.map (f.f n) (f'.f n) (p.f n) (q.f n)
        (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]) ≫
      (cokernelComponentIso f' n).inv := by
  have hcancel : (cokernel.π f').f n ≫ (cokernelComponentIso f' n).hom ≫
      (cokernelComponentIso f' n).inv = (cokernel.π f').f n := by
    rw [Iso.hom_inv_id, Category.comp_id]
  have hL : cokernel.π (f.f n) ≫
      ((cokernelComponentIso f n).inv ≫ (cokernel.map f f' p q w).f n) =
      (q.f n) ≫ (cokernel.π f').f n := by
    calc cokernel.π (f.f n) ≫
          ((cokernelComponentIso f n).inv ≫ (cokernel.map f f' p q w).f n)
        = ((cokernel.π f).f n ≫ (cokernelComponentIso f n).hom) ≫
            ((cokernelComponentIso f n).inv ≫ (cokernel.map f f' p q w).f n) := by
          rw [cokernelComponentIso_canon]
      _ = (cokernel.π f).f n ≫ ((cokernelComponentIso f n).hom ≫
            ((cokernelComponentIso f n).inv ≫ (cokernel.map f f' p q w).f n)) := by
          rw [Category.assoc]
      _ = (cokernel.π f).f n ≫ (cokernel.map f f' p q w).f n := by
          rw [Iso.hom_inv_id_assoc]
      _ = (cokernel.π f ≫ cokernel.map f f' p q w).f n := by
          rw [HomologicalComplex.comp_f]
      _ = (q ≫ cokernel.π f').f n := by rw [cokernel_π_cokernelMap]
      _ = (q.f n) ≫ (cokernel.π f').f n := by rw [HomologicalComplex.comp_f]
  have hR : cokernel.π (f.f n) ≫
      (cokernel.map (f.f n) (f'.f n) (p.f n) (q.f n)
          (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]) ≫
        (cokernelComponentIso f' n).inv) = (q.f n) ≫ (cokernel.π f').f n := by
    calc cokernel.π (f.f n) ≫ (cokernel.map (f.f n) (f'.f n) (p.f n) (q.f n)
            (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]) ≫
          (cokernelComponentIso f' n).inv)
        = (cokernel.π (f.f n) ≫ cokernel.map (f.f n) (f'.f n) (p.f n) (q.f n)
            (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f])) ≫
          (cokernelComponentIso f' n).inv := by rw [Category.assoc]
      _ = ((q.f n) ≫ cokernel.π (f'.f n)) ≫ (cokernelComponentIso f' n).inv := by
          rw [cokernel_π_cokernelMap]
      _ = (q.f n) ≫ (cokernel.π (f'.f n) ≫ (cokernelComponentIso f' n).inv) := by
          rw [Category.assoc]
      _ = (q.f n) ≫ (cokernel.π f').f n := by
          rw [← cokernelComponentIso_canon f' n, Category.assoc, hcancel]
  rw [← cancel_epi (cokernel.π (f.f n)), hL, hR]

end

end Work.Cohomology
