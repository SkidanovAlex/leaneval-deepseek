import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relChainsMapOf_comp

/-!
# Factorisation of a map of pairs through open subsets

A map of pairs `f : (X, A) → (Y, B)` (`A ⊆ X`, `B ⊆ Y`, with `Work.Cohomology.relChainsMapOf` the
induced map of relative chain complexes) is a quasi-isomorphism as soon as it *factors* through open
subsets `U ⊆ X`, `V ⊆ Y` which, together with `A` and `B`, cover `X` and `Y`:

* `(U, U ∩ A) → (X, A)` and `(V, V ∩ B) → (Y, B)` are the excision inclusions
  (`Work.Cohomology.excision_relChainsMap_isIso`), and
* the "middle" map `(U, U ∩ A) → (V, V ∩ B)` is induced by a pair of quasi-isomorphisms
  `U → V`, `U ∩ A → V ∩ B` (`Work.Cohomology.relChainsMapOf_homologyMap_isIso`).

The point of the lemma is the *identity* between `f` and this composite: it is the naturality of the
excision inclusion (`relChainsMap_natural` below) together with the well-definedness of
`relChainsMapOf` in the compatibility proof (`relChainsMapOf_congr`).

This is the abstract form of the argument that the inclusion of one copy of a manifold with boundary
into its double is an isomorphism on local homology at an *interior* point (see
`Submission/Work/ThomBordism/doubleFC/span_pairMap_M.lean`): there `X = M`, `Y = Double n M`,
`A = M ∖ {y}`, `B = D ∖ {ιM y}`, `U = int M` and `V = ιM '' int M`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.doubleFC

noncomputable section

/-! ## Well-definedness of `relChainsMapOf` -/

/-- `relChainsMapOf` depends only on the two maps, not on the compatibility proof. -/
theorem relChainsMapOf_proof_irrel (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w w' : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f g w' := by
  have h : w = w' := Subsingleton.elim _ _
  rw [h]

/-- **Well-definedness of `relChainsMapOf`**: it is determined by the pair of maps. -/
theorem relChainsMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y} {f f' : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  cases hf; cases hg
  exact relChainsMapOf_proof_irrel X Y A B f g w w'

/-- The inclusion `inclInterA X U A` followed by the inclusion of `A` in `X` is the composite of the
two inclusions of the relative subsets. -/
theorem inclInterA_comp_subtypeIncl (X : TopCat) (U A : Set X) :
    Work.Cohomology.inclInterA X U A ≫ Work.Cohomology.subtypeIncl X A
      = Work.Cohomology.subtypeIncl (TopCat.of U) {y : U | (y : X) ∈ A} ≫
        Work.Cohomology.subtypeIncl X U := by
  ext y
  rfl

/-! ## Naturality of the excision inclusion -/

/-- The compatibility datum for `Work.Cohomology.relChainsMapOf_comp` on the source side. -/
theorem compatC {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (U : Set X) :
    Work.Cohomology.subtypeIncl (TopCat.of U) {x : U | (x : X) ∈ A} ≫
        (Work.Cohomology.subtypeIncl X U ≫ f)
      = (Work.Cohomology.inclInterA X U A ≫ g) ≫ Work.Cohomology.subtypeIncl Y B := by
  simp only [Category.assoc]
  rw [← w]
  simp only [← Category.assoc]
  rw [inclInterA_comp_subtypeIncl]

/-- The compatibility datum for `Work.Cohomology.relChainsMapOf_comp` on the target side. -/
theorem compatD {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (U : Set X) (V : Set Y) (h : TopCat.of U ⟶ TopCat.of V)
    (hw : Work.Cohomology.subtypeIncl X U ≫ f = h ≫ Work.Cohomology.subtypeIncl Y V)
    (h' : TopCat.of {x : U | (x : X) ∈ A} ⟶ TopCat.of {y : V | (y : Y) ∈ B})
    (w'' : Work.Cohomology.subtypeIncl (TopCat.of U) {x : U | (x : X) ∈ A} ≫ h
      = h' ≫ Work.Cohomology.subtypeIncl (TopCat.of V) {y : V | (y : Y) ∈ B}) :
    Work.Cohomology.subtypeIncl (TopCat.of U) {x : U | (x : X) ∈ A} ≫
        (h ≫ Work.Cohomology.subtypeIncl Y V)
      = (h' ≫ Work.Cohomology.inclInterA Y V B) ≫ Work.Cohomology.subtypeIncl Y B := by
  simp only [Category.assoc]
  rw [← hw]
  rw [inclInterA_comp_subtypeIncl]
  simp only [← Category.assoc]
  rw [← w'']
  simp only [Category.assoc]
  rw [hw]

/-- **Naturality of the excision inclusion.**  If a map of pairs `(X, A) → (Y, B)` carries the open
set `U ⊆ X` onto `V ⊆ Y` (compatibly with the inclusions of `A`, `B`), then the induced map of
relative chain complexes factors through the two excision inclusions. -/
theorem relChainsMap_natural (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (U : Set X) (V : Set Y)
    (h : TopCat.of U ⟶ TopCat.of V)
    (hw : Work.Cohomology.subtypeIncl X U ≫ f = h ≫ Work.Cohomology.subtypeIncl Y V)
    (h' : TopCat.of {x : U | (x : X) ∈ A} ⟶ TopCat.of {y : V | (y : Y) ∈ B})
    (hw' : Work.Cohomology.inclInterA X U A ≫ g = h' ≫ Work.Cohomology.inclInterA Y V B)
    (w'' : Work.Cohomology.subtypeIncl (TopCat.of U) {x : U | (x : X) ∈ A} ≫ h
      = h' ≫ Work.Cohomology.subtypeIncl (TopCat.of V) {y : V | (y : Y) ∈ B}) :
    Work.Cohomology.relChainsMap X U A ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf (TopCat.of U) (TopCat.of V) {x : U | (x : X) ∈ A}
          {y : V | (y : Y) ∈ B} h h' w'' ≫ Work.Cohomology.relChainsMap Y V B := by
  rw [Work.Cohomology.relChainsMap, Work.Cohomology.relChainsMap,
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ (compatC A B f g w U),
    Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ (compatD A B f U V h hw h' w'')]
  exact relChainsMapOf_congr hw hw' _ _

/-! ## The factorisation criterion -/

/-- **A map of pairs which factors through open subsets is a quasi-isomorphism.**  If `U ⊆ X`,
`V ⊆ Y` are open, `U ∪ A = X`, `V ∪ B = Y`, and there are compatible maps
`h : U → V`, `h' : U ∩ A → V ∩ B` which are quasi-isomorphisms, then the map
`H_k(X, A) → H_k(Y, B)` induced by `f` is an isomorphism.

The hypotheses are the four compatibility equations:
`w` (that `g` lies over `f`), `hw` (that `h` lies over `f`), `hw'` (that `h'` lies over `g`) and
`w''` (that `h'` is the restriction of `h`). -/
theorem isIso_homologyMap_relChainsMapOf_of_factorization
    {X Y : TopCat} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (hA : IsOpen A) (hB : IsOpen B)
    (hcovU : U ∪ A = Set.univ) (hcovV : V ∪ B = Set.univ)
    (h : TopCat.of U ⟶ TopCat.of V)
    (hw : Work.Cohomology.subtypeIncl X U ≫ f = h ≫ Work.Cohomology.subtypeIncl Y V)
    (h' : TopCat.of {x : U | (x : X) ∈ A} ⟶ TopCat.of {y : V | (y : Y) ∈ B})
    (hw' : Work.Cohomology.inclInterA X U A ≫ g = h' ≫ Work.Cohomology.inclInterA Y V B)
    (w'' : Work.Cohomology.subtypeIncl (TopCat.of U) {x : U | (x : X) ∈ A} ≫ h
      = h' ≫ Work.Cohomology.subtypeIncl (TopCat.of V) {y : V | (y : Y) ∈ B})
    (k : ℕ)
    (hk : ∀ j, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of U) (TopCat.of V) h) j))
    (hk' : ∀ j, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of {x : U | (x : X) ∈ A})
        (TopCat.of {y : V | (y : Y) ∈ B}) h') j)) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) :=
    Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcovU k
  haveI h2 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap Y V B) k) :=
    Work.Cohomology.excision_relChainsMap_isIso Y V B hV hB hcovV k
  haveI h3 : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of U) (TopCat.of V) {x : U | (x : X) ∈ A}
        {y : V | (y : Y) ∈ B} h h' w'') k) :=
    Work.Cohomology.relChainsMapOf_homologyMap_isIso _ _ _ _ _ _ hk hk'
  have hfac := relChainsMap_natural X Y A B f g w U V h hw h' hw' w''
  have heq : HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k ≫
        HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k =
      HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf (TopCat.of U) (TopCat.of V) {x : U | (x : X) ∈ A}
            {y : V | (y : Y) ∈ B} h h' w'') k ≫
        HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap Y V B) k := by
    rw [← HomologicalComplex.homologyMap_comp, hfac, HomologicalComplex.homologyMap_comp]
  have hα : HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k =
      inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) ≫
        (HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf (TopCat.of U) (TopCat.of V) {x : U | (x : X) ∈ A}
              {y : V | (y : Y) ∈ B} h h' w'') k ≫
          HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap Y V B) k) := by
    calc HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k
        = 𝟙 _ ≫ HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k :=
          (Category.id_comp _).symm
      _ = (inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) ≫
            HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) ≫
            HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k := by
          rw [IsIso.inv_hom_id, Category.id_comp]
      _ = inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) ≫
            (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k ≫
              HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) k) :=
          Category.assoc _ _ _
      _ = inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) k) ≫
            (HomologicalComplex.homologyMap
                (Work.Cohomology.relChainsMapOf (TopCat.of U) (TopCat.of V)
                  {x : U | (x : X) ∈ A} {y : V | (y : Y) ∈ B} h h' w'') k ≫
              HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap Y V B) k) := by
          rw [heq]
  rw [hα]
  infer_instance

end

end Work.ThomBordism.doubleFC
