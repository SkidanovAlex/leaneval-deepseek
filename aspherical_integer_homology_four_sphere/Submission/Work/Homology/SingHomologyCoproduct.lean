import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.HomologyBiprod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Homology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. The side of a point of a topological sum -/

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The indicator of which summand of a topological sum a point lies in. -/
def sumSide : α ⊕ β → Bool := Sum.elim (fun _ => true) (fun _ => false)

@[simp] theorem sumSide_inl (a : α) : sumSide (Sum.inl a : α ⊕ β) = true := rfl
@[simp] theorem sumSide_inr (b : β) : sumSide (Sum.inr b : α ⊕ β) = false := rfl

theorem continuous_sumSide : Continuous (sumSide : α ⊕ β → Bool) :=
  Continuous.sumElim continuous_const continuous_const

theorem exists_eq_inl_of_sumSide_eq_true (q : α ⊕ β) (h : sumSide q = true) :
    ∃ a, (Sum.inl a : α ⊕ β) = q := by
  cases q with
  | inl a => exact ⟨a, rfl⟩
  | inr b => exact absurd h (by simp)

theorem exists_eq_inr_of_sumSide_eq_false (q : α ⊕ β) (h : sumSide q = false) :
    ∃ b, (Sum.inr b : α ⊕ β) = q := by
  cases q with
  | inl a => exact absurd h (by simp)
  | inr b => exact ⟨b, rfl⟩

noncomputable def sumExtractLeft (q : α ⊕ β) (h : sumSide q = true) : α :=
  Classical.choose (exists_eq_inl_of_sumSide_eq_true q h)

theorem sumExtractLeft_spec (q : α ⊕ β) (h : sumSide q = true) :
    (Sum.inl (sumExtractLeft q h) : α ⊕ β) = q :=
  Classical.choose_spec (p := fun a => (Sum.inl a : α ⊕ β) = q)
    (exists_eq_inl_of_sumSide_eq_true q h)

noncomputable def sumExtractRight (q : α ⊕ β) (h : sumSide q = false) : β :=
  Classical.choose (exists_eq_inr_of_sumSide_eq_false q h)

theorem sumExtractRight_spec (q : α ⊕ β) (h : sumSide q = false) :
    (Sum.inr (sumExtractRight q h) : α ⊕ β) = q :=
  Classical.choose_spec (p := fun b => (Sum.inr b : α ⊕ β) = q)
    (exists_eq_inr_of_sumSide_eq_false q h)

end Topology

/-! ## 2. Splitting maps from a standard simplex into a sum -/

section Split

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The standard topological `n`-simplex. -/
abbrev stdSimplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- A continuous map into a sum which lands in the left summand, as a map to `α`. -/
noncomputable def sumToLeft {n : ℕ} (g : C(stdSimplex n, α ⊕ β))
    (h : ∀ t, sumSide (g t) = true) : C(stdSimplex n, α) where
  toFun t := sumExtractLeft (g t) (h t)
  continuous_toFun := by
    refine (Topology.IsEmbedding.inl (X := α) (Y := β)).continuous_iff.2 ?_
    have hg : ((Sum.inl : α → α ⊕ β) ∘ fun t => sumExtractLeft (g t) (h t)) = ⇑g := by
      funext t
      exact sumExtractLeft_spec (g t) (h t)
    rw [hg]
    exact g.continuous

/-- A continuous map into a sum which lands in the right summand, as a map to `β`. -/
noncomputable def sumToRight {n : ℕ} (g : C(stdSimplex n, α ⊕ β))
    (h : ∀ t, sumSide (g t) = false) : C(stdSimplex n, β) where
  toFun t := sumExtractRight (g t) (h t)
  continuous_toFun := by
    refine (Topology.IsEmbedding.inr (X := α) (Y := β)).continuous_iff.2 ?_
    have hg : ((Sum.inr : β → α ⊕ β) ∘ fun t => sumExtractRight (g t) (h t)) = ⇑g := by
      funext t
      exact sumExtractRight_spec (g t) (h t)
    rw [hg]
    exact g.continuous

/-- Postcomposition with `Sum.inl`, as a continuous map. -/
noncomputable def sumInlMap {n : ℕ} (a : C(stdSimplex n, α)) : C(stdSimplex n, α ⊕ β) where
  toFun t := Sum.inl (a t)
  continuous_toFun := continuous_inl.comp a.continuous

/-- Postcomposition with `Sum.inr`, as a continuous map. -/
noncomputable def sumInrMap {n : ℕ} (b : C(stdSimplex n, β)) : C(stdSimplex n, α ⊕ β) where
  toFun t := Sum.inr (b t)
  continuous_toFun := continuous_inr.comp b.continuous

@[simp] theorem sumInlMap_apply {n : ℕ} (a : C(stdSimplex n, α)) (t : stdSimplex n) :
    sumInlMap (β := β) a t = Sum.inl (a t) := rfl

@[simp] theorem sumInrMap_apply {n : ℕ} (b : C(stdSimplex n, β)) (t : stdSimplex n) :
    sumInrMap (α := α) b t = Sum.inr (b t) := rfl

/-- The side indicator of a continuous map from a simplex into a sum is constant. -/
theorem sumSide_const {n : ℕ} (g : C(stdSimplex n, α ⊕ β)) (t t' : stdSimplex n) :
    sumSide (g t) = sumSide (g t') :=
  TotallyDisconnectedSpace.eq_of_continuous (fun t => sumSide (g t))
    (continuous_sumSide.comp g.continuous) t t'

/-- If a continuous map from a simplex into a sum does not land in the left summand,
then it lands in the right one. -/
theorem exists_sum_right_of_not_exists_left {n : ℕ} (g : C(stdSimplex n, α ⊕ β))
    (h : ¬ ∃ a : C(stdSimplex n, α), ∀ t, Sum.inl (a t) = g t) :
    ∃ b : C(stdSimplex n, β), ∀ t, Sum.inr (b t) = g t := by
  have hc : ∀ t t' : stdSimplex n, sumSide (g t) = sumSide (g t') := sumSide_const g
  by_cases hv : sumSide (g (Classical.arbitrary (stdSimplex n))) = false
  · have hb : ∀ t, sumSide (g t) = false := by
      intro t
      rw [hc t (Classical.arbitrary (stdSimplex n)), hv]
    exact ⟨sumToRight g hb, fun t => sumExtractRight_spec (g t) (hb t)⟩
  · exfalso
    apply h
    have hv' : sumSide (g (Classical.arbitrary (stdSimplex n))) = true := by
      cases h' : sumSide (g (Classical.arbitrary (stdSimplex n))) <;> simp_all
    have ha : ∀ t, sumSide (g t) = true := by
      intro t
      rw [hc t (Classical.arbitrary (stdSimplex n)), hv']
    exact ⟨sumToLeft g ha, fun t => sumExtractLeft_spec (g t) (ha t)⟩

/-- Split a continuous map from a standard simplex into a topological sum according
to which summand its image lies in. -/
noncomputable def sumSplit {n : ℕ} (g : C(stdSimplex n, α ⊕ β)) :
    C(stdSimplex n, α) ⊕ C(stdSimplex n, β) :=
  if h : ∃ a : C(stdSimplex n, α), ∀ t, Sum.inl (a t) = g t then Sum.inl (Classical.choose h)
  else Sum.inr (Classical.choose (exists_sum_right_of_not_exists_left g h))

theorem sumSplit_eq_inl_iff {n : ℕ} (g : C(stdSimplex n, α ⊕ β))
    (h : ∃ a : C(stdSimplex n, α), ∀ t, Sum.inl (a t) = g t) :
    sumSplit g = Sum.inl (Classical.choose h) := by
  rw [sumSplit]
  exact dif_pos h

theorem sumSplit_eq_inr_iff {n : ℕ} (g : C(stdSimplex n, α ⊕ β))
    (h : ¬ ∃ a : C(stdSimplex n, α), ∀ t, Sum.inl (a t) = g t) :
    sumSplit g = Sum.inr (Classical.choose (exists_sum_right_of_not_exists_left g h)) := by
  rw [sumSplit]
  exact dif_neg h

theorem sumSplit_sumInlMap {n : ℕ} (a : C(stdSimplex n, α)) :
    sumSplit (sumInlMap (β := β) a) = Sum.inl a := by
  have h : ∃ a' : C(stdSimplex n, α), ∀ t, Sum.inl (a' t) = sumInlMap (β := β) a t :=
    ⟨a, fun t => rfl⟩
  rw [sumSplit_eq_inl_iff _ h]
  congr 1
  exact ContinuousMap.ext fun t => Sum.inl_injective (Classical.choose_spec h t)

theorem sumSplit_sumInrMap {n : ℕ} (b : C(stdSimplex n, β)) :
    sumSplit (sumInrMap (α := α) b) = Sum.inr b := by
  have h : ¬ ∃ a' : C(stdSimplex n, α), ∀ t, Sum.inl (a' t) = sumInrMap (α := α) b t := by
    rintro ⟨a', ha'⟩
    have h0 := ha' (Classical.arbitrary (stdSimplex n))
    rw [sumInrMap_apply] at h0
    exact Sum.inl_ne_inr h0
  rw [sumSplit_eq_inr_iff _ h]
  congr 1
  exact ContinuousMap.ext fun t => Sum.inr_injective
    (Classical.choose_spec (exists_sum_right_of_not_exists_left (sumInrMap (α := α) b) h) t)

/-- A continuous map from a simplex into a sum splits: it is either of the form
`Sum.inl ∘ a` or `Sum.inr ∘ b`. -/
theorem sumSplit_cases {n : ℕ} (g : C(stdSimplex n, α ⊕ β)) :
    (∃ a : C(stdSimplex n, α), sumSplit g = Sum.inl a ∧ ∀ t, Sum.inl (a t) = g t) ∨
      (∃ b : C(stdSimplex n, β), sumSplit g = Sum.inr b ∧ ∀ t, Sum.inr (b t) = g t) := by
  by_cases h : ∃ a : C(stdSimplex n, α), ∀ t, Sum.inl (a t) = g t
  · exact Or.inl ⟨_, sumSplit_eq_inl_iff g h, Classical.choose_spec h⟩
  · exact Or.inr ⟨_, sumSplit_eq_inr_iff g h,
      Classical.choose_spec (exists_sum_right_of_not_exists_left g h)⟩

end Split

/-! ## 3. The side of a singular simplex of a topological sum -/

section SSet

universe u

variable (α β : Type u) [TopologicalSpace α] [TopologicalSpace β]

/-- The inclusion of the first summand, as a morphism of `TopCat`. -/
def inlTop : TopCat.of α ⟶ TopCat.of (α ⊕ β) :=
  TopCat.ofHom ⟨Sum.inl, continuous_inl⟩

/-- The inclusion of the second summand, as a morphism of `TopCat`. -/
def inrTop : TopCat.of β ⟶ TopCat.of (α ⊕ β) :=
  TopCat.ofHom ⟨Sum.inr, continuous_inr⟩

theorem toSSetObjEquiv_inlTop (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of α)).obj (op ⦋n⦌)) :
    TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌)
        ((TopCat.toSSet.map (inlTop α β)).app (op ⦋n⦌) a)
      = sumInlMap (TopCat.toSSetObjEquiv (TopCat.of α) (op ⦋n⦌) a) := by
  ext t
  rfl

theorem toSSetObjEquiv_inrTop (n : ℕ)
    (b : (TopCat.toSSet.obj (TopCat.of β)).obj (op ⦋n⦌)) :
    TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌)
        ((TopCat.toSSet.map (inrTop α β)).app (op ⦋n⦌) b)
      = sumInrMap (TopCat.toSSetObjEquiv (TopCat.of β) (op ⦋n⦌) b) := by
  ext t
  rfl

/-- The side of a singular simplex of a topological sum. -/
noncomputable def sumSideTheta (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (α ⊕ β))).obj (op ⦋n⦌) →
      (TopCat.toSSet.obj (TopCat.of α)).obj (op ⦋n⦌) ⊕
        (TopCat.toSSet.obj (TopCat.of β)).obj (op ⦋n⦌) :=
  fun z => Sum.elim
    (fun a => Sum.inl ((TopCat.toSSetObjEquiv (TopCat.of α) (op ⦋n⦌)).symm a))
    (fun b => Sum.inr ((TopCat.toSSetObjEquiv (TopCat.of β) (op ⦋n⦌)).symm b))
    (sumSplit (TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌) z))

theorem sumSideTheta_inl (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of α)).obj (op ⦋n⦌)) :
    sumSideTheta α β n ((TopCat.toSSet.map (inlTop α β)).app (op ⦋n⦌) a) = Sum.inl a := by
  rw [sumSideTheta, toSSetObjEquiv_inlTop, sumSplit_sumInlMap]
  simp

theorem sumSideTheta_inr (n : ℕ)
    (b : (TopCat.toSSet.obj (TopCat.of β)).obj (op ⦋n⦌)) :
    sumSideTheta α β n ((TopCat.toSSet.map (inrTop α β)).app (op ⦋n⦌) b) = Sum.inr b := by
  rw [sumSideTheta, toSSetObjEquiv_inrTop, sumSplit_sumInrMap]
  simp

/-- Every singular simplex of a topological sum lies in one of the two summands. -/
theorem exists_eq_inlTop_or_eq_inrTop (n : ℕ)
    (z : (TopCat.toSSet.obj (TopCat.of (α ⊕ β))).obj (op ⦋n⦌)) :
    (∃ a, z = (TopCat.toSSet.map (inlTop α β)).app (op ⦋n⦌) a) ∨
      (∃ b, z = (TopCat.toSSet.map (inrTop α β)).app (op ⦋n⦌) b) := by
  rcases sumSplit_cases (TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌) z) with
    ⟨a, -, ha⟩ | ⟨b, -, hb⟩
  · left
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of α) (op ⦋n⦌)).symm a, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌)).injective
    rw [toSSetObjEquiv_inlTop, Equiv.apply_symm_apply]
    exact ContinuousMap.ext fun t => (ha t).symm
  · right
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of β) (op ⦋n⦌)).symm b, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of (α ⊕ β)) (op ⦋n⦌)).injective
    rw [toSSetObjEquiv_inrTop, Equiv.apply_symm_apply]
    exact ContinuousMap.ext fun t => (hb t).symm

end SSet

/-! ## 4. The splitting of the singular chain complex -/

/-- `C_*(X; R)`, the singular chain complex of `X`.  This is definitionally the
same as `singChain R X`, but its unfolding is transparent to `rw`. -/
abbrev singChainC (R : ModuleCat ℤ) (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex R

/-- The map of singular chain complexes induced by a continuous map, in the
form used below. -/
abbrev singChainMapC (R : ModuleCat ℤ) {X Y : TopCat} (f : X ⟶ Y) :
    singChainC R X ⟶ singChainC R Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) R

section Chain

variable {α β : Type} [TopologicalSpace α] [TopologicalSpace β] {R : ModuleCat ℤ}

/-- The chain map `C_*(α) ⊞ C_*(β) → C_*(α ⊔ β)` induced by the two inclusions. -/
noncomputable def coprodChainMap (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] :
    singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β) ⟶
      singChainC R (TopCat.of (α ⊕ β)) :=
  biprod.desc (singChainMapC R (inlTop α β)) (singChainMapC R (inrTop α β))

/-- The `n`-th component of the degreewise splitting `C_*(α ⊔ β) → C_*(α) ⊞ C_*(β)`. -/
noncomputable def splitChainApp (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] (n : ℕ) :
    (singChainC R (TopCat.of (α ⊕ β))).X n ⟶
      (singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).X n :=
  Limits.Sigma.desc fun z =>
    Sum.elim
      (fun a => (TopCat.toSSet.obj (TopCat.of α)).ιChainComplex a ≫
        (biprod.inl : singChainC R (TopCat.of α) ⟶
          singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n)
      (fun b => (TopCat.toSSet.obj (TopCat.of β)).ιChainComplex b ≫
        (biprod.inr : singChainC R (TopCat.of β) ⟶
          singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n)
      (sumSideTheta α β n z)

theorem iota_comp_splitChainApp (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] (n : ℕ)
    (z : (TopCat.toSSet.obj (TopCat.of (α ⊕ β))).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj (TopCat.of (α ⊕ β))).ιChainComplex z ≫ splitChainApp R α β n =
      Sum.elim
        (fun a => (TopCat.toSSet.obj (TopCat.of α)).ιChainComplex a ≫
          (biprod.inl : singChainC R (TopCat.of α) ⟶
            singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n)
        (fun b => (TopCat.toSSet.obj (TopCat.of β)).ιChainComplex b ≫
          (biprod.inr : singChainC R (TopCat.of β) ⟶
            singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n)
        (sumSideTheta α β n z) :=
  Limits.Sigma.ι_comp_desc _ z

theorem singChainMapC_iota (R : ModuleCat ℤ) {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫ (singChainMapC R f).f n =
      (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map f).app (op ⦋n⦌) x) :=
  SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map f) R x

theorem singChainMap_inlTop_comp_splitChainApp (R : ModuleCat ℤ) (α β : Type)
    [TopologicalSpace α] [TopologicalSpace β] (n : ℕ) :
    (singChainMapC R (inlTop α β)).f n ≫ splitChainApp R α β n =
      (biprod.inl : singChainC R (TopCat.of α) ⟶
        singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n := by
  refine SSet.chainComplex_hom_ext (fun a => ?_)
  simp only [← Category.assoc, singChainMapC_iota, iota_comp_splitChainApp,
    sumSideTheta_inl, Sum.elim_inl]

theorem singChainMap_inrTop_comp_splitChainApp (R : ModuleCat ℤ) (α β : Type)
    [TopologicalSpace α] [TopologicalSpace β] (n : ℕ) :
    (singChainMapC R (inrTop α β)).f n ≫ splitChainApp R α β n =
      (biprod.inr : singChainC R (TopCat.of β) ⟶
        singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)).f n := by
  refine SSet.chainComplex_hom_ext (fun b => ?_)
  simp only [← Category.assoc, singChainMapC_iota, iota_comp_splitChainApp,
    sumSideTheta_inr, Sum.elim_inr]

theorem coprodChainMap_f_comp_splitChainApp (R : ModuleCat ℤ) (α β : Type)
    [TopologicalSpace α] [TopologicalSpace β] (n : ℕ) :
    (coprodChainMap R α β).f n ≫ splitChainApp R α β n = 𝟙 _ := by
  rw [coprodChainMap]
  apply HomologicalComplex.biprodX_ext_from
  · simp only [← Category.assoc, HomologicalComplex.biprod_inl_desc_f, Category.comp_id,
      singChainMap_inlTop_comp_splitChainApp]
  · simp only [← Category.assoc, HomologicalComplex.biprod_inr_desc_f, Category.comp_id,
      singChainMap_inrTop_comp_splitChainApp]

theorem splitChainApp_comp_coprodChainMap_f (R : ModuleCat ℤ) (α β : Type)
    [TopologicalSpace α] [TopologicalSpace β] (n : ℕ) :
    splitChainApp R α β n ≫ (coprodChainMap R α β).f n = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext (fun z => ?_)
  rw [← Category.assoc, iota_comp_splitChainApp, coprodChainMap]
  rcases exists_eq_inlTop_or_eq_inrTop α β n z with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp only [sumSideTheta_inl, Sum.elim_inl, Category.assoc,
      HomologicalComplex.biprod_inl_desc_f, singChainMapC_iota, Category.comp_id,
      Category.id_comp]
  · simp only [sumSideTheta_inr, Sum.elim_inr, Category.assoc,
      HomologicalComplex.biprod_inr_desc_f, singChainMapC_iota, Category.comp_id,
      Category.id_comp]

theorem isIso_coprodChainMap_f (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] (n : ℕ) : IsIso ((coprodChainMap R α β).f n) :=
  IsIso.mk ⟨splitChainApp R α β n, coprodChainMap_f_comp_splitChainApp R α β n,
    splitChainApp_comp_coprodChainMap_f R α β n⟩

theorem isIso_coprodChainMap (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] : IsIso (coprodChainMap R α β) := by
  haveI (n : ℕ) : IsIso ((coprodChainMap R α β).f n) := isIso_coprodChainMap_f R α β n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The singular chain complex of a topological sum splits as a direct sum. -/
noncomputable def singChainCoproductIso (R : ModuleCat ℤ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] :
    singChainC R (TopCat.of (α ⊕ β)) ≅
      (singChainC R (TopCat.of α) ⊞ singChainC R (TopCat.of β)) := by
  haveI := isIso_coprodChainMap R α β
  exact (asIso (coprodChainMap R α β)).symm

end Chain

end

theorem SingHomologyCoproduct (R : ModuleCat ℤ) (k : ℕ) (α β : Type) [TopologicalSpace α]
    [TopologicalSpace β] :
    Nonempty (singHomology R k (TopCat.of (α ⊕ β)) ≅
      (singHomology R k (TopCat.of α) ⊞ singHomology R k (TopCat.of β))) := by
  refine ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
    (singChainCoproductIso R α β) ≪≫ ?_⟩
  exact (HomologyBiprod (singChain R (TopCat.of α)) (singChain R (TopCat.of β)) k).some

end Work.Homology
