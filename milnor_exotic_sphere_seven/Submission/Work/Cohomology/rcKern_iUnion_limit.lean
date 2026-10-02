import Mathlib
import Submission.Work.Cohomology.wsfDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative `k`-cochains on a directed union of open sets

For a topological space `X`, a subset `A ⊆ X`, a linearly ordered index type `J` and a monotone
family `W : J → Set X` of open sets, the relative `k`-cochains on the union `⋃ j, W j` are the
*inverse limit* of the relative `k`-cochains on the pieces `W j`: a `k`-cochain on `⋃ j, W j` is
exactly a compatible family of `k`-cochains on the `W j`.

The mathematical content is that every singular `k`-simplex of `⋃ j, W j` has compact image, hence
(hopenness of the `W j`, directedness of `J`) lies in a *single* `W j`; consequently a cochain on
the union is determined by, and can be glued from, its restrictions.  The main lemma is
`Work.Cohomology.rcKern_iUnion_limit`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The singular simplicial set of a subset. -/
abbrev rcSST (Y : Set X) : SSet := TopCat.toSSet.obj (TopCat.of Y)

/-- The type of singular `k`-simplices of a subset. -/
abbrev rcSimp (Y : Set X) (k : ℕ) : Type _ :=
  (rcSST Y).obj (Opposite.op (SimplexCategory.mk k))

/-- The `k`-cochains of a subset, as linear functionals on its `k`-chains. -/
abbrev rcCochain (Y : Set X) (k : ℕ) : Type _ :=
  ((rcSST Y).chainComplex (ModuleCat.of ℤ ℤ)).X k →ₗ[ℤ] ℤ

/-- For `A ⊆ X` and `Y ⊆ X`, the relative subset `A ∩ Y`, as a subset of `Y`. -/
abbrev rcRelSub (A : Set X) (Y : Set X) : Set Y := {y : Y | (y : X) ∈ A}

/-! ## Elementary facts about the inclusions `pdIncl` -/

theorem rcPdIncl_injective {S T : Set X} (h : S ⊆ T) :
    Function.Injective (ConcreteCategory.hom (pdIncl (M := TopCat.of X) T S h)) := by
  intro a b hab
  have h2 : ((ConcreteCategory.hom (pdIncl (M := TopCat.of X) T S h)) a : X)
      = ((ConcreteCategory.hom (pdIncl (M := TopCat.of X) T S h)) b : X) := congrArg Subtype.val hab
  exact Subtype.ext (by simpa [pdIncl] using h2)

theorem rcPdIncl_proof_irrel {S T : Set X} (h h' : S ⊆ T) :
    pdIncl (M := TopCat.of X) T S h = pdIncl (M := TopCat.of X) T S h' := by
  apply TopCat.ext; intro y; rfl

/-- The map on simplices induced by `pdIncl` does not depend on the proof of the inclusion. -/
theorem rcMapPdIncl_congr {S T : Set X} (h h' : S ⊆ T) (k : ℕ) (τ : rcSimp S k) :
    (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h)).app (Opposite.op (SimplexCategory.mk k)) τ
      = (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h')).app
          (Opposite.op (SimplexCategory.mk k)) τ := by
  rw [rcPdIncl_proof_irrel h h']

/-- The inclusions of simplices are compatible with composing the inclusions of sets. -/
theorem rcMapPdIncl_trans {S S' T : Set X} (h : S ⊆ S') (h' : S' ⊆ T) (k : ℕ) (τ : rcSimp S k) :
    (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S' h')).app (Opposite.op (SimplexCategory.mk k))
        ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) S' S h)).app
          (Opposite.op (SimplexCategory.mk k)) τ)
      = (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S (h.trans h'))).app
          (Opposite.op (SimplexCategory.mk k)) τ := by
  conv_rhs => rw [← pdIncl_comp h h']
  rw [TopCat.toSSet.map_comp]
  rfl

/-! ## Evaluation of the restriction of relative cochains at a simplex -/

/-- Naturality of `genEval` under the pullback of cochains along a map of simplicial sets. -/
theorem rcGenEval_chainComplexMap {Xs Ys : SSet} (f : Xs ⟶ Ys) (k : ℕ)
    (φ : ((Ys.chainComplex (ModuleCat.of ℤ ℤ)).X k →ₗ[ℤ] ℤ))
    (σ : Xs.obj (Opposite.op (SimplexCategory.mk k))) :
    genEval ℤ Xs (((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f k).hom.dualMap φ) σ
      = genEval ℤ Ys φ ((ConcreteCategory.hom (f.app (Opposite.op (SimplexCategory.mk k)))) σ) := by
  simp only [genEval, LinearMap.dualMap_apply]
  have h4 := congrArg (fun g => g.hom 1)
    (SSet.ι_chainComplexMap_f (X := Xs) (Y := Ys) f (ModuleCat.of ℤ ℤ) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  rw [h4]

theorem rcGenEval_pullbackX (S T : Set X) (h : S ⊆ T) (k : ℕ) (φ : rcCochain T k)
    (σ : rcSimp S k) :
    genEval ℤ (rcSST S)
        (((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h))
            (ModuleCat.of ℤ ℤ)).f k).hom.dualMap φ) σ
      = genEval ℤ (rcSST T) φ ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h)).app _ σ) :=
  rcGenEval_chainComplexMap _ k φ σ

theorem rcResLM_coe_dualMap (A : Set X) {S T : Set X} (h : S ⊆ T) (k : ℕ)
    (φ : ↥(rcKern A T k)) :
    (rcResLM A h k φ).1
      = (((SSet.chainComplexMap (TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h))
            (ModuleCat.of ℤ ℤ)).f k).hom.dualMap) φ.1 := by
  rw [rcResLM_coe]
  rw [dualChainMap_f_hom, chainMap_f_eq]
  rfl

/-- The zero cochain evaluates to zero. -/
theorem rcGenEval_zero {Xs : SSet} (k : ℕ) (σ : Xs.obj (Opposite.op (SimplexCategory.mk k))) :
    genEval ℤ Xs (0 : ((Xs.chainComplex (ModuleCat.of ℤ ℤ)).X k →ₗ[ℤ] ℤ)) σ = 0 := by
  simp [genEval]

/-- Evaluation of the restriction of a relative cochain. -/
theorem rcGenEval_rcResLM (A : Set X) {S T : Set X} (h : S ⊆ T) (k : ℕ) (φ : ↥(rcKern A T k))
    (σ : rcSimp S k) :
    genEval ℤ (rcSST S) (rcResLM A h k φ).1 σ
      = genEval ℤ (rcSST T) φ.1 ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) T S h)).app _ σ) := by
  rw [rcResLM_coe_dualMap A h k φ]
  exact rcGenEval_pullbackX S T h k φ.1 σ

/-- A relative cochain vanishes on every simplex lying in `A`. -/
theorem rcGenEval_relKern_zero (A : Set X) {Y : Set X} (k : ℕ) (φ : ↥(rcKern A Y k))
    (τ : rcSimp (rcRelSub A Y) k) :
    genEval ℤ (rcSST Y) φ.1
      ((TopCat.toSSet.map (subtypeIncl (TopCat.of Y) (rcRelSub A Y))).app _ τ) = 0 :=
  genEval_eq_zero_of_mem_relKern ℤ (TopCat.of Y) (rcRelSub A Y) φ.1 φ.2 τ

/-- A simplex whose every point lies in `B ⊆ Y` corestricts to a simplex of `B`. -/
theorem rcCorestrict_simplex {Y : Set X} {B : Set Y} (k : ℕ) (τ : rcSimp Y k)
    (hτ : ∀ x, (((TopCat.toSSetObjEquiv (TopCat.of Y)
      (Opposite.op (SimplexCategory.mk k))) τ) x : Y) ∈ B) :
    ∃ τ' : rcSimp B k,
      (TopCat.toSSet.map (subtypeIncl (TopCat.of Y) B)).app
        (Opposite.op (SimplexCategory.mk k)) τ' = τ := by
  let g := (TopCat.toSSetObjEquiv (TopCat.of Y) (Opposite.op (SimplexCategory.mk k))) τ
  let g' : C(Convexity.StdSimplex ℝ (Fin (k+1)), TopCat.of B) :=
    ⟨fun x => ⟨g x, hτ x⟩, Continuous.subtype_mk g.continuous _⟩
  refine ⟨(TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op (SimplexCategory.mk k))).symm g', ?_⟩
  apply (TopCat.toSSetObjEquiv (TopCat.of Y) (Opposite.op (SimplexCategory.mk k))).injective
  rw [toSSetObjEquiv_naturality_space, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-! ## Every simplex of the union lies in one piece -/

/-- Every singular `k`-simplex of `⋃ j, W j` is the image of a singular `k`-simplex of some `W j`. -/
theorem rcExistsWitness {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ) (σ : rcSimp (⋃ j, W j) k) :
    ∃ (j : J) (τ : rcSimp (W j) k),
      (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W j)
        (Set.subset_iUnion W j))).app (Opposite.op (SimplexCategory.mk k)) τ = σ := by
  let g : C(Convexity.StdSimplex ℝ (Fin (k+1)), TopCat.of (⋃ j, W j)) :=
    (TopCat.toSSetObjEquiv (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk k))) σ
  have hcont : Continuous (fun x => ((g x : ⋃ j, W j) : X)) :=
    continuous_subtype_val.comp g.continuous
  have hcomp : IsCompact
      (Set.range (fun x : Convexity.StdSimplex ℝ (Fin (k+1)) => ((g x : ⋃ j, W j) : X))) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hcont
  have hsub : Set.range (fun x : Convexity.StdSimplex ℝ (Fin (k+1)) => ((g x : ⋃ j, W j) : X)) ⊆ ⋃ j, W j := by
    rintro y ⟨x, rfl⟩
    exact (g x).2
  classical
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover W (fun j => hopen j) hsub
  have hne : t.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    obtain ⟨x⟩ : Nonempty (Convexity.StdSimplex ℝ (Fin (k+1))) := inferInstance
    have hmem : ((g x : ⋃ j, W j) : X) ∈ (⋃ i ∈ t, W i) := ht ⟨x, rfl⟩
    rw [hc] at hmem
    simp at hmem
  set j0 := t.max' hne with hj0
  have hsub2 : Set.range (fun x : Convexity.StdSimplex ℝ (Fin (k+1)) => ((g x : ⋃ j, W j) : X)) ⊆ W j0 := by
    intro y hy
    rcases Set.mem_iUnion.mp (ht hy) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hit, hyi⟩
    exact hmono (Finset.le_max' _ _ hit) hyi
  let g' : C(Convexity.StdSimplex ℝ (Fin (k+1)), TopCat.of (W j0)) :=
    ⟨fun x => ⟨((g x : ⋃ j, W j) : X), hsub2 ⟨x, rfl⟩⟩, Continuous.subtype_mk hcont _⟩
  refine ⟨j0, (TopCat.toSSetObjEquiv (TopCat.of (W j0)) (Opposite.op (SimplexCategory.mk k))).symm g', ?_⟩
  apply (TopCat.toSSetObjEquiv (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk k))).injective
  rw [toSSetObjEquiv_naturality_space]
  rw [Equiv.apply_symm_apply]
  rw [show (TopCat.toSSetObjEquiv (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk k))) σ = g from rfl]
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The value of the compatible family does not depend on the choice of the piece. -/
theorem rcWitnessAgree (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hmono : Monotone W) (k : ℕ) (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i)
    {σ : rcSimp (⋃ j, W j) k} {j j' : J} {τ : rcSimp (W j) k} {τ' : rcSimp (W j') k}
    (hτ : (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W j)
        (Set.subset_iUnion W j))).app (Opposite.op (SimplexCategory.mk k)) τ = σ)
    (hτ' : (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W j')
        (Set.subset_iUnion W j'))).app (Opposite.op (SimplexCategory.mk k)) τ' = σ) :
    genEval ℤ (rcSST (W j)) (f j).1 τ = genEval ℤ (rcSST (W j')) (f j').1 τ' := by
  set m := max j j' with hm
  have hj : j ≤ m := le_max_left _ _
  have hj' : j' ≤ m := le_max_right _ _
  have hp : (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (W m) (W j) (hmono hj))).app _ τ
      = (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (W m) (W j') (hmono hj'))).app _ τ' := by
    apply (injective_toSSet_map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W m) (Set.subset_iUnion W m))
      (rcPdIncl_injective (Set.subset_iUnion W m)) k)
    rw [rcMapPdIncl_trans (hmono hj) (Set.subset_iUnion W m) k τ,
        rcMapPdIncl_trans (hmono hj') (Set.subset_iUnion W m) k τ',
        rcMapPdIncl_congr _ (Set.subset_iUnion W j) k τ, hτ,
        rcMapPdIncl_congr _ (Set.subset_iUnion W j') k τ', hτ']
  calc genEval ℤ (rcSST (W j)) (f j).1 τ
      = genEval ℤ (rcSST (W j)) (rcResLM A (hmono hj) k (f m)).1 τ := by rw [hf j m hj]
    _ = genEval ℤ (rcSST (W m)) (f m).1
          ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) (W m) (W j) (hmono hj))).app _ τ) :=
        rcGenEval_rcResLM A (hmono hj) k (f m) τ
    _ = genEval ℤ (rcSST (W m)) (f m).1
          ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) (W m) (W j') (hmono hj'))).app _ τ') := by
        rw [hp]
    _ = genEval ℤ (rcSST (W j')) (rcResLM A (hmono hj') k (f m)).1 τ' :=
        (rcGenEval_rcResLM A (hmono hj') k (f m) τ').symm
    _ = genEval ℤ (rcSST (W j')) (f j').1 τ' := by rw [hf j' m hj']

/-! ## The gluing of a compatible family -/

/-- A fixed piece containing a given simplex of the union. -/
noncomputable def rcGlueJ {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ) (σ : rcSimp (⋃ j, W j) k) : J :=
  Classical.choose (rcExistsWitness W hopen hmono k σ)

/-- A fixed simplex of that piece mapping to the given simplex. -/
noncomputable def rcGlueτ {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ) (σ : rcSimp (⋃ j, W j) k) :
    rcSimp (W (rcGlueJ W hopen hmono k σ)) k :=
  Classical.choose (Classical.choose_spec (rcExistsWitness W hopen hmono k σ))

theorem rcGlueτ_spec {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ) (σ : rcSimp (⋃ j, W j) k) :
    (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W (rcGlueJ W hopen hmono k σ))
        (Set.subset_iUnion W (rcGlueJ W hopen hmono k σ)))).app (Opposite.op (SimplexCategory.mk k))
        (rcGlueτ W hopen hmono k σ) = σ :=
  Classical.choose_spec (Classical.choose_spec (rcExistsWitness W hopen hmono k σ))

/-- The value of the glued cochain at a simplex: the value of the compatible family at any chosen
piece containing the simplex. -/
noncomputable def rcGlueVal (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k)) (σ : rcSimp (⋃ j, W j) k) : ℤ :=
  genEval ℤ (rcSST (W (rcGlueJ W hopen hmono k σ))) (f (rcGlueJ W hopen hmono k σ)).1
    (rcGlueτ W hopen hmono k σ)

/-- The value is independent of the chosen piece. -/
theorem rcGlueVal_spec (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i)
    {σ : rcSimp (⋃ j, W j) k} {j : J} {τ : rcSimp (W j) k}
    (h : (TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W j)
        (Set.subset_iUnion W j))).app (Opposite.op (SimplexCategory.mk k)) τ = σ) :
    rcGlueVal A W hopen hmono k f σ = genEval ℤ (rcSST (W j)) (f j).1 τ :=
  rcWitnessAgree A W hmono k f hf (rcGlueτ_spec W hopen hmono k σ) h

/-- The glued cochain, as a morphism of `ℤ`-modules. -/
noncomputable def rcGlueCochainHom (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) :
    ((rcSST (⋃ j, W j)).chainComplex (ModuleCat.of ℤ ℤ)).X k ⟶ ModuleCat.of ℤ ℤ :=
  Cofan.IsColimit.desc (SSet.isColimitChainComplexXCofan (rcSST (⋃ j, W j)) (ModuleCat.of ℤ ℤ) k)
    (fun σ => (rcGlueVal A W hopen hmono k f σ) • 𝟙 (ModuleCat.of ℤ ℤ))

/-- The glued cochain. -/
noncomputable def rcGlueCochain (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) :
    rcCochain (⋃ j, W j) k :=
  ModuleCat.Hom.hom (rcGlueCochainHom A W hopen hmono k f hf)

theorem rcGlueCochain_genEval (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i)
    (σ : rcSimp (⋃ j, W j) k) :
    genEval ℤ (rcSST (⋃ j, W j)) (rcGlueCochain A W hopen hmono k f hf) σ
      = rcGlueVal A W hopen hmono k f σ := by
  have hfac : ((rcSST (⋃ j, W j)).ιChainComplex σ) ≫ rcGlueCochainHom A W hopen hmono k f hf
      = (rcGlueVal A W hopen hmono k f σ) • 𝟙 (ModuleCat.of ℤ ℤ) :=
    Cofan.IsColimit.fac (SSet.isColimitChainComplexXCofan (rcSST (⋃ j, W j)) (ModuleCat.of ℤ ℤ) k)
      (fun σ => (rcGlueVal A W hopen hmono k f σ) • 𝟙 (ModuleCat.of ℤ ℤ)) σ
  have h2 := congrArg (fun (g : (ModuleCat.of ℤ ℤ) ⟶ ModuleCat.of ℤ ℤ) => g.hom 1) hfac
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  simp only [genEval, rcGlueCochain]
  rw [h2]
  simp

/-! ## The glued cochain is relative, and restricts correctly -/

theorem rcRestr_component (Y : Set X) (B : Set Y) (k : ℕ) :
    ((restr ℤ (TopCat.of Y) B).f k).hom
      = ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl (TopCat.of Y) B))
            (ModuleCat.of ℤ ℤ)).f k).hom.dualMap := by
  rw [restr, dualChainMap_f_hom, chainMap_f_eq]

/-- The glued cochain vanishes on chains lying in `A`. -/
theorem rcGlueVal_rel (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i)
    {σ : rcSimp (⋃ j, W j) k} {τ : rcSimp (rcRelSub A (⋃ j, W j)) k}
    (h : (TopCat.toSSet.map (subtypeIncl (TopCat.of (⋃ j, W j))
            (rcRelSub A (⋃ j, W j)))).app (Opposite.op (SimplexCategory.mk k)) τ = σ) :
    rcGlueVal A W hopen hmono k f σ = 0 := by
  rw [rcGlueVal_spec A W hopen hmono k f hf (rcGlueτ_spec W hopen hmono k σ)]
  let g0 : C(Convexity.StdSimplex ℝ (Fin (k+1)), TopCat.of (W (rcGlueJ W hopen hmono k σ))) :=
    (TopCat.toSSetObjEquiv (TopCat.of (W (rcGlueJ W hopen hmono k σ)))
      (Opposite.op (SimplexCategory.mk k))) (rcGlueτ W hopen hmono k σ)
  have himg : ∀ x, ((g0 x : W (rcGlueJ W hopen hmono k σ)) : X) ∈ A := by
    intro x
    have heq : (TopCat.toSSetObjEquiv (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk k)))
          ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j)
            (W (rcGlueJ W hopen hmono k σ)) (Set.subset_iUnion W (rcGlueJ W hopen hmono k σ)))).app
            (Opposite.op (SimplexCategory.mk k)) (rcGlueτ W hopen hmono k σ))
        = (TopCat.toSSetObjEquiv (TopCat.of (⋃ j, W j)) (Opposite.op (SimplexCategory.mk k)))
          ((TopCat.toSSet.map (subtypeIncl (TopCat.of (⋃ j, W j))
            (rcRelSub A (⋃ j, W j)))).app (Opposite.op (SimplexCategory.mk k)) τ) := by
      rw [rcGlueτ_spec W hopen hmono k σ, h]
    rw [toSSetObjEquiv_naturality_space, toSSetObjEquiv_naturality_space] at heq
    have hx : ((g0 x : W (rcGlueJ W hopen hmono k σ)) : X)
        = (((TopCat.toSSetObjEquiv (TopCat.of (rcRelSub A (⋃ j, W j)))
            (Opposite.op (SimplexCategory.mk k))) τ) x : X) := by
      have h2 := congrArg (fun (f : C(Convexity.StdSimplex ℝ (Fin (k+1)), TopCat.of (⋃ j, W j))) =>
        ((f x : (⋃ j, W j)) : X)) heq
      simp only [ContinuousMap.comp_apply] at h2
      simpa [pdIncl, subtypeIncl, g0] using h2
    rw [hx]
    exact (((TopCat.toSSetObjEquiv (TopCat.of (rcRelSub A (⋃ j, W j)))
      (Opposite.op (SimplexCategory.mk k))) τ) x).2
  obtain ⟨τ0', hτ0'⟩ := rcCorestrict_simplex (Y := W (rcGlueJ W hopen hmono k σ))
    (B := rcRelSub A (W (rcGlueJ W hopen hmono k σ))) k (rcGlueτ W hopen hmono k σ) himg
  have hval : genEval ℤ (rcSST (W (rcGlueJ W hopen hmono k σ)))
      (f (rcGlueJ W hopen hmono k σ)).1 (rcGlueτ W hopen hmono k σ)
      = genEval ℤ (rcSST (rcRelSub A (W (rcGlueJ W hopen hmono k σ))))
          (((restr ℤ (TopCat.of (W (rcGlueJ W hopen hmono k σ)))
            (rcRelSub A (W (rcGlueJ W hopen hmono k σ)))).f k).hom
          (f (rcGlueJ W hopen hmono k σ)).1) τ0' := by
    rw [← hτ0']
    rw [rcRestr_component]
    exact (rcGenEval_chainComplexMap (TopCat.toSSet.map (subtypeIncl
      (TopCat.of (W (rcGlueJ W hopen hmono k σ)))
      (rcRelSub A (W (rcGlueJ W hopen hmono k σ))))) k (f (rcGlueJ W hopen hmono k σ)).1 τ0').symm
  rw [hval]
  have hzero : ((restr ℤ (TopCat.of (W (rcGlueJ W hopen hmono k σ)))
      (rcRelSub A (W (rcGlueJ W hopen hmono k σ)))).f k).hom
      (f (rcGlueJ W hopen hmono k σ)).1 = 0 := (f (rcGlueJ W hopen hmono k σ)).2
  rw [hzero]
  simp [genEval]

/-- The glued cochain is relative. -/
theorem rcGlueCochain_mem (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) :
    rcGlueCochain A W hopen hmono k f hf ∈ rcKern A (⋃ j, W j) k := by
  rw [rcKern, relKern, LinearMap.mem_ker]
  rw [rcRestr_component]
  apply genEval_ext
  intro τ
  refine (rcGenEval_chainComplexMap (Xs := rcSST (rcRelSub A (⋃ j, W j)))
    (Ys := rcSST (⋃ j, W j))
    (TopCat.toSSet.map (subtypeIncl (TopCat.of (⋃ j, W j)) (rcRelSub A (⋃ j, W j)))) k
    (rcGlueCochain A W hopen hmono k f hf) τ).trans ?_
  rw [rcGlueCochain_genEval, rcGlueVal_rel A W hopen hmono k f hf rfl, rcGenEval_zero]

/-- The glued cochain restricts to `f j`. -/
theorem rcGlueCochain_restrict (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k))
    (hf : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) (j : J) :
    rcResLM A (Set.subset_iUnion W j) k
      ⟨rcGlueCochain A W hopen hmono k f hf, rcGlueCochain_mem A W hopen hmono k f hf⟩ = f j := by
  apply Subtype.ext
  apply genEval_ext
  intro σ
  rw [rcGenEval_rcResLM]
  change genEval ℤ (rcSST (⋃ j, W j)) (rcGlueCochain A W hopen hmono k f hf)
      ((TopCat.toSSet.map (pdIncl (M := TopCat.of X) (⋃ j, W j) (W j)
        (Set.subset_iUnion W j))).app _ σ) = genEval ℤ (rcSST (W j)) (f j).1 σ
  rw [rcGlueCochain_genEval]
  exact rcGlueVal_spec A W hopen hmono k f hf rfl

/-- The restriction to the pieces is injective. -/
theorem rcRestrict_injective (A : Set X) {J : Type} [LinearOrder J] (W : J → Set X)
    (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ) :
    ∀ y : ↥(rcKern A (⋃ j, W j) k),
      (∀ j, rcResLM A (Set.subset_iUnion W j) k y = 0) → y = 0 := by
  intro y hy
  apply Subtype.ext
  apply genEval_ext
  intro σ
  obtain ⟨j, τ, hτ⟩ := rcExistsWitness W hopen hmono k σ
  rw [← hτ, ← rcGenEval_rcResLM A (Set.subset_iUnion W j) k y τ, hy j]
  simp [genEval]

/-- The restriction map on the pieces does not depend on the proof of the inclusion. -/
theorem rcResLM_proof_irrel {A : Set X} {S T : Set X} (h h' : S ⊆ T) (k : ℕ) :
    rcResLM A h k = rcResLM A h' k :=
  congrArg (fun hh => rcResLM A hh k) (Subsingleton.elim h h')

/-! ## The limit statement -/

theorem rcKern_iUnion_limit {X : Type} [TopologicalSpace X] (A : Set X) {J : Type} [LinearOrder J] [WellFoundedLT J]
    (W : J → Set X) (hopen : ∀ j, IsOpen (W j)) (hmono : Monotone W) (k : ℕ)
    (f : (j : J) → ↥(rcKern A (W j) k)) :
    (∃! g : ↥(rcKern A (⋃ j, W j) k),
        ∀ j, rcResLM A (Set.subset_iUnion W j) k g = f j)
      ↔ (∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (f j) = f i) := by
  constructor
  · rintro ⟨g, hg, -⟩ i j hij
    have h1 : rcResLM A (hmono hij) k (f j)
        = rcResLM A ((hmono hij).trans (Set.subset_iUnion W j)) k g := by
      rw [← hg j, ← LinearMap.comp_apply,
        rcResLM_comp A (hmono hij) (Set.subset_iUnion W j) k]
    rw [h1, rcResLM_proof_irrel ((hmono hij).trans (Set.subset_iUnion W j))
      (Set.subset_iUnion W i) k]
    exact hg i
  · intro hf
    refine ⟨⟨rcGlueCochain A W hopen hmono k f hf, rcGlueCochain_mem A W hopen hmono k f hf⟩,
      ?_, ?_⟩
    · intro j
      exact rcGlueCochain_restrict A W hopen hmono k f hf j
    · intro y hy
      rw [← sub_eq_zero]
      apply rcRestrict_injective A W hopen hmono k
      intro j
      rw [map_sub, hy j, rcGlueCochain_restrict A W hopen hmono k f hf j, sub_self]

end

end Work.Cohomology
