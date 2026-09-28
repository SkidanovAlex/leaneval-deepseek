import Mathlib
import Submission.Work.RatHurewicz.relHurewiczClass_eq_of_homotopic
import Submission.Work.Cohomology.cokernelComponent

/-!
# Homotopy descent of a chain map to the cokernels, over a general ring

This file proves `Work.Serre.DiscPair.cokernelMapHomologyEq`, the `ModuleCat R` form (for an
arbitrary commutative ring `R`) of `Work.RatHurewicz.cokernelMap_homologyMap_eq`.

**Descent of a chain homotopy to the relative complexes.**  Let `inC : P ⟶ C` and `inD : Q ⟶ D` be
the inclusions of the "subcomplexes" of a morphism of pairs of chain complexes, `h` a chain
homotopy between the induced maps `f₀, f₁` on the ambient complexes, and suppose that the
components of `h` in degrees `(i, i+1)` carry the subcomplex `P` into the subcomplex `Q`, i.e.
factor as `(inC.f i) ≫ (h.hom i (i+1)) = (g i) ≫ (inD.f (i+1))`.  Then the maps `a₀`, `a₁` induced
on the cokernels (characterised by `cokernel.π inC ≫ a = f ≫ cokernel.π inD`) are chain homotopic,
hence equal on homology in every degree.

The only ingredient that is not yet available over a general ring is the identification of the
components of a cokernel of chain complexes: `cokernelComponentIso` below is the `ModuleCat R` form
of `Work.Cohomology.cokernelComponentIso`, proved by the same argument (the evaluation functor
`HomologicalComplex.eval` preserves the colimit, and the two parallel-pair diagrams agree).

The proof of the theorem is the one of `Work.RatHurewicz.cokernelMap_homologyMap_eq`: the descended
homotopy `Ψ` has components `(cokernelComponentIso inC i).hom ≫ d ≫ (cokernelComponentIso inD j).inv`
with `d` the descent of `h.hom i (i+1)` to the cokernels of the components; the identity
`(cokernel.π inC).f i ≫ Ψ i j = h.hom i j ≫ (cokernel.π inD).f j` is the defining property of the
descent, and the homotopy identity follows from the naturality of `cokernel.π` as a chain map.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The `n`-th component of the cokernel of a morphism of chain complexes of `R`-modules is the
cokernel of the `n`-th component.**  The `ModuleCat R` form of
`Work.Cohomology.cokernelComponentIso`: the evaluation functor
`HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n` preserves the colimit defining
`cokernel f`, and the two parallel-pair diagrams `parallelPair f 0 ⋙ eval n` and
`parallelPair (f.f n) 0` are equal. -/
def cokernelComponentIso {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (n : ℕ) : (cokernel f).X n ≅ cokernel (f.f n) := by
  let F : WalkingParallelPair ⥤ ModuleCat R := (parallelPair f 0) ⋙
    HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n
  let G : WalkingParallelPair ⥤ ModuleCat R := parallelPair (f.f n) 0
  have hFG : F = G := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j <;> rfl
    · rintro X' Y' g
      match g with
      | .left => cat_disch
      | .right => cat_disch
      | .id Z => cat_disch
  exact IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)
        (colimit.isColimit (parallelPair f 0)))
      (colimit.isColimit F) ≪≫ HasColimit.isoOfNatIso (eqToIso hFG)

/-- **`cokernelComponentIso` is the canonical comparison**: composed with the projection
`cokernel.π f` it is the degreewise cokernel projection. -/
theorem cokernelComponentIso_canon {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    (cokernel.π f).f n ≫ (cokernelComponentIso f n).hom = cokernel.π (f.f n) := by
  simp only [cokernelComponentIso]
  have hs : ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0))).ι.app WalkingParallelPair.one
      = (cokernel.π f).f n := rfl
  rw [← hs]
  rw [Work.Cohomology.coconePointUniqueUpToIso_comp_isoOfNatIso_ι
    ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair f 0)))
    _ (eqToIso _) WalkingParallelPair.one]
  simp

/-- **Descent of a chain homotopy to the relative chain complexes.**  Let `inC : P ⟶ C` and
`inD : Q ⟶ D` be the inclusions of the subcomplexes of a morphism of pairs of chain complexes of
`R`-modules, `h` a chain homotopy between the induced maps `f₀, f₁` on the ambient complexes, and
suppose that the components of `h` in degrees `(i, i+1)` carry the subcomplex `P` into the
subcomplex `Q`, i.e. factor as `(inC.f i) ≫ (h.hom i (i+1)) = (g i) ≫ (inD.f (i+1))`.  Then the
maps `a₀`, `a₁` induced on the cokernels (characterised by
`cokernel.π inC ≫ a = f ≫ cokernel.π inD`) are chain homotopic, hence equal on homology in every
degree. -/
theorem cokernelMapHomologyEq {R : Type} [CommRing R] {P C Q D : ChainComplex (ModuleCat R) ℕ}
    (inC : P ⟶ C) (inD : Q ⟶ D) {f₀ f₁ : C ⟶ D} (h : Homotopy f₀ f₁)
    (g : ∀ i, P.X i ⟶ Q.X (i+1))
    (hg : ∀ i, (inC.f i) ≫ (h.hom i (i+1)) = (g i) ≫ (inD.f (i+1)))
    {a₀ a₁ : cokernel inC ⟶ cokernel inD}
    (ha₀ : cokernel.π inC ≫ a₀ = f₀ ≫ cokernel.π inD)
    (ha₁ : cokernel.π inC ≫ a₁ = f₁ ≫ cokernel.π inD) (k : ℕ) :
    HomologicalComplex.homologyMap a₀ k = HomologicalComplex.homologyMap a₁ k := by
  let Ψ : ∀ i j, (cokernel inC).X i ⟶ (cokernel inD).X j := fun i j =>
    if hj : j = i + 1 then hj.symm ▸
      ((cokernelComponentIso inC i).hom ≫
        cokernel.map (inC.f i) (inD.f (i+1)) (g i) (h.hom i (i+1)) (hg i) ≫
        (cokernelComponentIso inD (i+1)).inv)
    else 0
  have key : ∀ i, (cokernel.π inC).f i ≫ Ψ i (i+1) =
      h.hom i (i+1) ≫ (cokernel.π inD).f (i+1) := by
    intro i
    dsimp only [Ψ]
    rw [dif_pos rfl]
    rw [← Category.assoc, cokernelComponentIso_canon inC i, ← Category.assoc,
      Work.Cohomology.cokernel_π_cokernelMap (inC.f i) (inD.f (i+1)) (g i) (h.hom i (i+1)) (hg i),
      Category.assoc, ← cokernelComponentIso_canon inD (i+1)]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (show Homotopy a₀ a₁ from
    { hom := Ψ
      zero := fun i j hij => by
        dsimp only [Ψ]
        rw [dif_neg]
        intro hj
        exact hij (by rw [ComplexShape.down_Rel]; omega)
      comm := fun i => by
        haveI : Epi ((cokernel.π inC).f i) := by
          rw [show (cokernel.π inC).f i =
              cokernel.π (inC.f i) ≫ (cokernelComponentIso inC i).inv from by
            rw [← cokernelComponentIso_canon inC i]
            simp]
          infer_instance
        have e1 : (cokernel.π inC).f i ≫ a₀.f i = f₀.f i ≫ (cokernel.π inD).f i := by
          rw [← HomologicalComplex.comp_f, ha₀, HomologicalComplex.comp_f]
        have e2 : (cokernel.π inC).f i ≫ a₁.f i = f₁.f i ≫ (cokernel.π inD).f i := by
          rw [← HomologicalComplex.comp_f, ha₁, HomologicalComplex.comp_f]
        have e3 : ∀ i, (cokernel.π inC).f i ≫ dNext i Ψ =
            dNext i h.hom ≫ (cokernel.π inD).f i := by
          intro i
          cases i with
          | zero => rw [Homotopy.dNext_zero_chainComplex, Homotopy.dNext_zero_chainComplex,
              comp_zero, zero_comp]
          | succ k =>
            rw [Homotopy.dNext_succ_chainComplex Ψ k, Homotopy.dNext_succ_chainComplex h.hom k]
            rw [← Category.assoc, HomologicalComplex.Hom.comm (cokernel.π inC) (k+1) k,
              Category.assoc, key k]
            simp only [Category.assoc]
        have e4 : ∀ i, (cokernel.π inC).f i ≫ prevD i Ψ =
            prevD i h.hom ≫ (cokernel.π inD).f i := by
          intro i
          rw [Homotopy.prevD_chainComplex Ψ i, Homotopy.prevD_chainComplex h.hom i]
          rw [← Category.assoc, key i, Category.assoc]
          rw [HomologicalComplex.Hom.comm (cokernel.π inD) (i+1) i]
          simp only [Category.assoc]
        rw [← cancel_epi ((cokernel.π inC).f i)]
        rw [Preadditive.comp_add, Preadditive.comp_add, e1, e2, e3 i, e4 i]
        rw [h.comm i, Preadditive.add_comp, Preadditive.add_comp] }).homologyMap_eq k

end

end Work.Serre.DiscPair
