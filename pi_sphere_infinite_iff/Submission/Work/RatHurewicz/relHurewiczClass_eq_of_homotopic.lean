import Mathlib
import Submission.Work.RatHurewicz.RelHurewicz
import Submission.Work.Thom.PairPrism

/-!
# Homotopy invariance of the relative Hurewicz class

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  This file proves
`Work.RatHurewicz.relHurewiczClass_eq_of_homotopic`, the well-definedness input of the relative
Hurewicz homomorphism `π_{n+1}(X,A) → H_{n+1}(X,A;ℤ)`: two maps of pairs
`g₀, g₁ : (I^{n+1}, ∂I^{n+1}) → (X,A)` that are homotopic *through maps of pairs* have the same
relative Hurewicz class, i.e. the same image of the relative fundamental class of the cube.

The proof has two ingredients.

* `Work.RatHurewicz.cokernelMap_homologyMap_eq`: a general descent statement — a chain homotopy
  between the ambient maps of a morphism of pairs of chain complexes whose components carry the
  subcomplex of the source into the subcomplex of the target descends to a chain homotopy between
  the cokernel maps, hence induces the same map on homology.
* `Work.Thom.prism_preserves`: the prism operator of a homotopy of pairs does carry chains of the
  subspace into chains of the subspace (Mathlib's `TopCat.Homotopy.singularChainComplexFunctorObjMap`
  applied to `Work.Thom.restrHomotopyTop`).
-/

open CategoryTheory Limits MonoidalCategory

namespace Work.RatHurewicz

noncomputable section

/-- **Descent of a chain homotopy to the relative chain complexes.**  Let `inC : P ⟶ C` and
`inD : Q ⟶ D` be the inclusions `C_*(∂) ⟶ C_*(I)` and `C_*(A) ⟶ C_*(X)` coming from a morphism of
pairs of chain complexes, `h` a chain homotopy between the induced maps `f₀, f₁` on the ambient
complexes, and suppose that the components of `h` in degrees `(i, i+1)` carry the subcomplex `P`
into the subcomplex `Q`, i.e. factor as `(inC.f i) ≫ (h.hom i (i+1)) = (g i) ≫ (inD.f (i+1))`.
Then the maps `a₀`, `a₁` induced on the cokernels (characterised by
`cokernel.π inC ≫ a = f ≫ cokernel.π inD`) are chain homotopic, hence equal on homology in every
degree. -/
theorem cokernelMap_homologyMap_eq {P C Q D : ChainComplex (ModuleCat ℤ) ℕ}
    (inC : P ⟶ C) (inD : Q ⟶ D) {f₀ f₁ : C ⟶ D} (h : Homotopy f₀ f₁)
    (g : ∀ i, P.X i ⟶ Q.X (i+1))
    (hg : ∀ i, (inC.f i) ≫ (h.hom i (i+1)) = (g i) ≫ (inD.f (i+1)))
    {a₀ a₁ : cokernel inC ⟶ cokernel inD}
    (ha₀ : cokernel.π inC ≫ a₀ = f₀ ≫ cokernel.π inD)
    (ha₁ : cokernel.π inC ≫ a₁ = f₁ ≫ cokernel.π inD) (k : ℕ) :
    HomologicalComplex.homologyMap a₀ k = HomologicalComplex.homologyMap a₁ k := by
  let Ψ : ∀ i j, (cokernel inC).X i ⟶ (cokernel inD).X j := fun i j =>
    if hj : j = i + 1 then hj.symm ▸
      ((Work.Cohomology.cokernelComponentIso inC i).hom ≫
        cokernel.map (inC.f i) (inD.f (i+1)) (g i) (h.hom i (i+1)) (hg i) ≫
        (Work.Cohomology.cokernelComponentIso inD (i+1)).inv)
    else 0
  have key : ∀ i, (cokernel.π inC).f i ≫ Ψ i (i+1) =
      h.hom i (i+1) ≫ (cokernel.π inD).f (i+1) := by
    intro i
    dsimp only [Ψ]
    rw [dif_pos rfl]
    rw [← Category.assoc, Work.Cohomology.cokernelComponentIso_canon inC i, ← Category.assoc,
      Work.Cohomology.cokernel_π_cokernelMap (inC.f i) (inD.f (i+1)) (g i) (h.hom i (i+1)) (hg i),
      Category.assoc, ← Work.Cohomology.cokernelComponentIso_canon inD (i+1)]
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
              cokernel.π (inC.f i) ≫ (Work.Cohomology.cokernelComponentIso inC i).inv from by
            rw [← Work.Cohomology.cokernelComponentIso_canon inC i]
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

/-- **Homotopy invariance of the relative Hurewicz class.**  Two maps of pairs
`g₀, g₁ : (I^{n+1}, ∂I^{n+1}) → (X, A)` which are homotopic through maps of pairs (a homotopy
`H : I × I^{n+1} → X` carrying `I × ∂I^{n+1}` into `A`) have the same relative Hurewicz class
`Work.RatHurewicz.relHurewiczClass n · ·`, i.e. the same image of the relative fundamental class of
the cube under the induced maps of relative singular chain complexes.  This is the well-definedness
input of the relative Hurewicz homomorphism `π_{n+1}(X,A) → H_{n+1}(X,A;ℤ)`.

Here `ContinuousMap.Homotopy g₀ g₁` is Mathlib's homotopy, whose underlying map is
`H.toContinuousMap : C(I × I^{n+1}, X)` (time first).  The two pointwise hypotheses `hg₀`, `hg₁` are
instances of the homotopy hypothesis `hH` (at `t = 0` and `t = 1`); they are kept separate because
they are the arguments of the two instances of `relHurewiczClass` whose values are compared.  Proof
route: the homotopy `H` induces a chain homotopy between the two chain maps on `C_*(I^{n+1})`;
because `H` carries `I × ∂I^{n+1}` into `A`, this chain homotopy restricts to the subcomplex
`C_*(∂I^{n+1})` and therefore descends to a chain homotopy between the induced maps on the relative
chain complexes `C_*(X,A)`, so the induced maps on homology agree in every degree — in particular on
`relCubeGen n`.  Concretely: `H` restricts to a homotopy of the pair (as `Work.Thom.restrHomotopyTop`,
Mathlib's homotopy of the restricted maps of `TopCat`), whose prism operator carries chains of the
boundary into chains of `A` (`Work.Thom.prism_preserves`), and `cokernelMap_homologyMap_eq` descends
that prism to the relative chain complexes. -/
theorem relHurewiczClass_eq_of_homotopic (n : ℕ) {X : Type} [TopologicalSpace X] {A : Set X}
    {g₀ g₁ : C(cubeTop (n + 1), X)}
    (hg₀ : ∀ z : cubeTop (n + 1), z ∈ cubeBdrySet (n + 1) → g₀ z ∈ A)
    (hg₁ : ∀ z : cubeTop (n + 1), z ∈ cubeBdrySet (n + 1) → g₁ z ∈ A)
    (H : ContinuousMap.Homotopy g₀ g₁)
    (hH : ∀ (z : cubeTop (n + 1)) (t : unitInterval),
      z ∈ cubeBdrySet (n + 1) → H.toContinuousMap (t, z) ∈ A) :
    relHurewiczClass n g₀ hg₀ = relHurewiczClass n g₁ hg₁ := by
  let Hf : TopCat.Homotopy (TopCat.ofHom g₀) (TopCat.ofHom g₁) := H
  have hHtop : ∀ t x, x ∈ cubeBdrySet (n+1) → Hf (t, x) ∈ A := fun t x hx => hH x t hx
  let hh : Homotopy
      (Work.Cohomology.chainMap ℤ (cubeTop (n+1)) (TopCat.of X) (TopCat.ofHom g₀))
      (Work.Cohomology.chainMap ℤ (cubeTop (n+1)) (TopCat.of X) (TopCat.ofHom g₁)) :=
    Hf.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
  have ha₀ : cokernel.π (Work.Cohomology.inclChains (cubeTop (n+1)) (cubeBdrySet (n+1))) ≫
      (Work.Cohomology.relChainsMapOf (cubeTop (n+1)) (TopCat.of X) (cubeBdrySet (n+1)) A
        (TopCat.ofHom g₀) (TopCat.ofHom (bdryRestrict n g₀ hg₀)) (bdryRestrict_comm n g₀ hg₀))
      = (Work.Cohomology.chainMap ℤ (cubeTop (n+1)) (TopCat.of X) (TopCat.ofHom g₀)) ≫
        cokernel.π (Work.Cohomology.inclChains (TopCat.of X) A) := by
    rw [Work.Cohomology.relChainsMapOf]
    exact Work.Cohomology.cokernel_π_cokernelMap _ _ _ _ _
  have ha₁ : cokernel.π (Work.Cohomology.inclChains (cubeTop (n+1)) (cubeBdrySet (n+1))) ≫
      (Work.Cohomology.relChainsMapOf (cubeTop (n+1)) (TopCat.of X) (cubeBdrySet (n+1)) A
        (TopCat.ofHom g₁) (TopCat.ofHom (bdryRestrict n g₁ hg₁)) (bdryRestrict_comm n g₁ hg₁))
      = (Work.Cohomology.chainMap ℤ (cubeTop (n+1)) (TopCat.of X) (TopCat.ofHom g₁)) ≫
        cokernel.π (Work.Cohomology.inclChains (TopCat.of X) A) := by
    rw [Work.Cohomology.relChainsMapOf]
    exact Work.Cohomology.cokernel_π_cokernelMap _ _ _ _ _
  unfold relHurewiczClass
  have hmap : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (cubeTop (n+1)) (TopCat.of X) (cubeBdrySet (n+1)) A
          (TopCat.ofHom g₀) (TopCat.ofHom (bdryRestrict n g₀ hg₀))
          (bdryRestrict_comm n g₀ hg₀)) (n+1)
      = HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (cubeTop (n+1)) (TopCat.of X) (cubeBdrySet (n+1)) A
          (TopCat.ofHom g₁) (TopCat.ofHom (bdryRestrict n g₁ hg₁))
          (bdryRestrict_comm n g₁ hg₁)) (n+1) := by
    refine cokernelMap_homologyMap_eq
      (Work.Cohomology.inclChains (cubeTop (n+1)) (cubeBdrySet (n+1)))
      (Work.Cohomology.inclChains (TopCat.of X) A) hh
      (fun i => ((Work.Thom.restrHomotopyTop Hf hg₀ hg₁ hHtop).toSSet.chainComplexMap
        (ModuleCat.of ℤ ℤ)).hom i (i+1)) (fun i => ?_) ha₀ ha₁ (n+1)
    exact (Work.Thom.prism_preserves Hf hg₀ hg₁ hHtop ℤ i).symm
  rw [hmap]

end

end Work.RatHurewicz
