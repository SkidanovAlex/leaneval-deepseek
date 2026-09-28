import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.isIso_biprod_desc_coprodMap
import Submission.Work.Cohomology.isIso_biprod_lift_dualMap
import Submission.Work.Cohomology.CoprodMVDefs
import Submission.Work.Cohomology.SphZeroBase
import Submission.Work.Cohomology.Pullback
import Submission.Work.StemsB.DualBiprodR

/-!
# The cohomology of `Y × S⁰`, over an arbitrary coefficient ring

`Submission/Work/Cohomology/cohProdSphZero.lean` proves, for `ℤ` coefficients and for `Y = Sᵖ`,

`H^k(Sᵖ × S⁰; ℤ) ≅ H^k(Sᵖ; ℤ) ⊞ H^k(Sᵖ; ℤ)`,

compatibly with the projection `Sᵖ × S⁰ → Sᵖ` (which corresponds to `biprod.inl` after the twist
`(a,b) ↦ (a, b−a)` of the biproduct).

This file is the *coefficient-general, arbitrary-base* version of that statement, with the two
generalisations that the rational model Thom class needs:

* the base is an **arbitrary topological space** `Y` rather than a sphere `Sᵖ`;
* the coefficients are an **arbitrary commutative ring** `R`.

The proof is the same: `S⁰` is discrete, the standard simplex `Δⁿ` is preconnected, so every
continuous map `Δⁿ → Y × S⁰` lands in exactly one of the two sheets `Y × {1}`, `Y × {−1}`; this
gives a bijection `sIdxSum` on `n`-simplices, hence an isomorphism
`C_*(Y;R) ⊞ C_*(Y;R) ≅ C_*(Y × S⁰;R)` on chains (built by the two sections), and dually
`C^*(Y × S⁰;R) ≅ C^*(Y;R) ⊞ C^*(Y;R)` on cochains.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial Topology

namespace Work.StemsB

noncomputable section

variable {R : Type} [CommRing R]
variable {Y : Type} [TopologicalSpace Y]

/-! ## Biproduct algebra over an arbitrary coefficient ring -/

/-- The `n`-th component of `biprod.desc a₁ a₂`, transported across the canonical isomorphism
`biprodXIso` between the components of a biproduct of chain complexes, is the `biprod.desc` of the
components.  (Coefficient-general form of `Work.Cohomology.biprod_desc_f`.) -/
theorem s0_biprod_desc_f {K M : ChainComplex (ModuleCat R) ℕ} (a₁ a₂ : K ⟶ M) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.biprodXIso K K n).inv
        ((CategoryTheory.Limits.biprod.desc a₁ a₂).f n)
      = CategoryTheory.Limits.biprod.desc (a₁.f n) (a₂.f n) := by
  apply CategoryTheory.Limits.biprod.hom_ext' <;> simp

/-- `coprodMap` of the identity map of index types is the identity. -/
theorem s0_coprodMap_id_eq {A : Type} :
    coprodMap (R:=R) (id : A → A) = 𝟙 (∐ (fun _ : A => ModuleCat.of R R)) := by
  rw [coprodMap, Sigma.map'_id, Sigma.map_id]

/-- `coprodMap` of an equivalence of index types is an isomorphism. -/
theorem s0_isIso_coprodMap_equiv {A S : Type} (e : A ≃ S) :
    IsIso (coprodMap (R:=R) (e : A → S)) := by
  refine IsIso.mk ⟨coprodMap (R:=R) (e.symm : S → A), ?_, ?_⟩
  · rw [coprodMap_comp,
      show ((e.symm : S → A) ∘ (e : A → S)) = id from funext (fun a => e.symm_apply_apply a),
      s0_coprodMap_id_eq]
  · rw [coprodMap_comp,
      show ((e : A → S) ∘ (e.symm : S → A)) = id from funext (fun s => e.apply_symm_apply s),
      s0_coprodMap_id_eq]

/-- `coprodMap` of a bijection of index types is an isomorphism. -/
theorem s0_isIso_coprodMap_of_bijective {A S : Type} (f : A → S)
    (hf : Function.Bijective f) : IsIso (coprodMap (R:=R) f) := by
  have h := s0_isIso_coprodMap_equiv (R:=R) (Equiv.ofBijective f hf)
  simpa [Equiv.coe_ofBijective] using h

/-- The canonical isomorphism `(∐_A R) ⊞ (∐_A R) ≅ ∐_{A ⊕ A} R`. -/
theorem s0_isIso_biprod_desc_inl_inr {A : Type} :
    IsIso (biprod.desc (coprodMap (R:=R) (Sum.inl : A → A ⊕ A))
                       (coprodMap (R:=R) (Sum.inr : A → A ⊕ A))) := by
  let eInv : (∐ (fun _ : A ⊕ A => ModuleCat.of R R)) ⟶
      ((∐ (fun _ : A => ModuleCat.of R R)) ⊞ (∐ (fun _ : A => ModuleCat.of R R))) :=
    Sigma.desc (Sum.elim
      (fun a => Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ biprod.inl)
      (fun a => Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ biprod.inr))
  refine IsIso.mk ⟨eInv, ?_, ?_⟩
  · apply biprod.hom_ext'
    · have h1 : coprodMap (R:=R) (Sum.inl : A → A ⊕ A) ≫ eInv = biprod.inl := by
        apply Sigma.hom_ext
        intro a
        rw [← Category.assoc, ι_coprodMap]
        simp only [eInv]
        rw [Sigma.ι_desc]
        rfl
      rw [← Category.assoc, biprod.inl_desc, h1, Category.comp_id]
    · have h2 : coprodMap (R:=R) (Sum.inr : A → A ⊕ A) ≫ eInv = biprod.inr := by
        apply Sigma.hom_ext
        intro a
        rw [← Category.assoc, ι_coprodMap]
        simp only [eInv]
        rw [Sigma.ι_desc]
        rfl
      rw [← Category.assoc, biprod.inr_desc, h2, Category.comp_id]
  · apply Sigma.hom_ext
    intro s
    rw [← Category.assoc]
    cases s with
    | inl a =>
      simp only [eInv, Sigma.ι_desc, Sum.elim_inl]
      rw [Category.assoc, biprod.inl_desc, ι_coprodMap, Category.comp_id]
    | inr a =>
      simp only [eInv, Sigma.ι_desc, Sum.elim_inr]
      rw [Category.assoc, biprod.inr_desc, ι_coprodMap, Category.comp_id]

/-- The factorisation of `biprod.desc` of two `coprodMap`s. -/
theorem s0_biprod_desc_coprodMap_factor {A B : Type} (u₁ u₂ : A → B) :
    biprod.desc (coprodMap (R:=R) u₁) (coprodMap (R:=R) u₂)
      = biprod.desc (coprodMap (R:=R) (Sum.inl : A → A ⊕ A))
                    (coprodMap (R:=R) (Sum.inr : A → A ⊕ A))
        ≫ coprodMap (R:=R) (Sum.elim u₁ u₂) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc]
    rw [biprod.inl_desc, biprod.inl_desc]
    rw [coprodMap_comp]
    congr 1
  · rw [← Category.assoc]
    rw [biprod.inr_desc, biprod.inr_desc]
    rw [coprodMap_comp]
    congr 1

/-- `biprod.desc` of two coproduct maps along a double cover of index types is an isomorphism. -/
theorem s0_isIso_biprod_desc_coprodMap {A B : Type} (u₁ u₂ : A → B)
    (hw : Function.Bijective (Sum.elim u₁ u₂)) :
    CategoryTheory.IsIso (CategoryTheory.Limits.biprod.desc
      (coprodMap (R:=R) u₁) (coprodMap (R:=R) u₂)) := by
  rw [s0_biprod_desc_coprodMap_factor u₁ u₂]
  haveI := s0_isIso_biprod_desc_inl_inr (R:=R) (A:=A)
  haveI := s0_isIso_coprodMap_of_bijective (R:=R) (Sum.elim u₁ u₂) hw
  infer_instance

/-- The homology of a biproduct of cochain complexes is the biproduct of the homologies,
compatibly with the biproduct structure maps.  (Coefficient-general form of
`Work.Cohomology.homology_biprod_iso`.) -/
theorem s0_homology_biprod_iso (C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ) :
    ∃ (e : (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k),
      (biprod.inl : C.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ∧
      (biprod.inr : D.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  refine ⟨F.mapBiprod C D, ?_, ?_⟩
  · erw [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  · erw [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl


/-! ## The two points of `S⁰`, the sections, and the decomposition of the simplices -/

/-- The space `Y × S⁰` of the decomposition. -/
abbrev YS0 (Y : Type) [TopologicalSpace Y] : TopCat := TopCat.of (Y × ↥(sphSet 1))

/-- The projection `Y × S⁰ ⟶ Y`. -/
def yProj : YS0 Y ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The section `y ↦ (y, 1)`. -/
def ySec₁ : TopCat.of Y ⟶ YS0 Y :=
  TopCat.ofHom ⟨fun y => (y, s0N), continuous_id.prodMk continuous_const⟩

/-- The section `y ↦ (y, -1)`. -/
def ySec₂ : TopCat.of Y ⟶ YS0 Y :=
  TopCat.ofHom ⟨fun y => (y, s0S), continuous_id.prodMk continuous_const⟩

@[simp] lemma ySec₁_comp_yProj : ySec₁ (Y := Y) ≫ yProj (Y := Y) = 𝟙 (TopCat.of Y) := by
  apply TopCat.hom_ext; ext y; rfl

@[simp] lemma ySec₂_comp_yProj : ySec₂ (Y := Y) ≫ yProj (Y := Y) = 𝟙 (TopCat.of Y) := by
  apply TopCat.hom_ext; ext y; rfl

/-- A continuous map from the standard simplex into `Y × S⁰` has constant second coordinate. -/
lemma contMap_snd_const_gen {n : ℕ}
    (σ : C(↥(stdSimplex ℝ (Fin (n+1))), Y × ↥(sphSet 1))) :
    ∃ c : ↥(sphSet 1), ∀ t, (σ t).2 = c := by
  haveI : DiscreteTopology ↥(sphSet 1) := s0_discrete
  have hcont : Continuous (fun t : ↥(stdSimplex ℝ (Fin (n+1))) => (σ t).2) :=
    continuous_snd.comp σ.continuous
  refine ⟨(σ (Classical.arbitrary _)).2, fun t => ?_⟩
  exact PreconnectedSpace.constant (Y := ↥(sphSet 1))
    (inferInstance : PreconnectedSpace ↥(stdSimplex ℝ (Fin (n+1)))) hcont
    (x := t) (y := Classical.arbitrary _)

/-- The map on `n`-simplices induced by the first section. -/
def yIdx₁ (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (YS0 Y)).obj (Opposite.op ⦋n⦌) :=
  fun a => (TopCat.toSSet.map (ySec₁ (Y := Y))).app (Opposite.op ⦋n⦌) a

/-- The map on `n`-simplices induced by the second section. -/
def yIdx₂ (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (YS0 Y)).obj (Opposite.op ⦋n⦌) :=
  fun a => (TopCat.toSSet.map (ySec₂ (Y := Y))).app (Opposite.op ⦋n⦌) a

/-- The map on `n`-simplices induced by the two sections, from the disjoint union of two copies of
the `n`-simplices of `Y`. -/
def yIdxSum (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) ⊕
        (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (YS0 Y)).obj (Opposite.op ⦋n⦌) :=
  Sum.elim (yIdx₁ (Y := Y) n) (yIdx₂ (Y := Y) n)

@[simp] lemma yIdxSum_inl (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌)) :
    yIdxSum (Y := Y) n (Sum.inl a) = yIdx₁ (Y := Y) n a := rfl

@[simp] lemma yIdxSum_inr (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌)) :
    yIdxSum (Y := Y) n (Sum.inr a) = yIdx₂ (Y := Y) n a := rfl

/-- The same decomposition, transported to the level of continuous maps `Δⁿ → Y`. -/
def yIdxSumCM (n : ℕ) :
    C(stdSimplex ℝ (Fin (n+1)), Y) ⊕ C(stdSimplex ℝ (Fin (n+1)), Y) →
      C(stdSimplex ℝ (Fin (n+1)), Y × ↥(sphSet 1)) :=
  Sum.elim (fun a => (ySec₁ (Y := Y)).hom.comp a) (fun a => (ySec₂ (Y := Y)).hom.comp a)

@[simp] lemma yIdxSumCM_inl (n : ℕ) (a : C(stdSimplex ℝ (Fin (n+1)), Y)) :
    yIdxSumCM (Y := Y) n (Sum.inl a) = (ySec₁ (Y := Y)).hom.comp a := rfl

@[simp] lemma yIdxSumCM_inr (n : ℕ) (a : C(stdSimplex ℝ (Fin (n+1)), Y)) :
    yIdxSumCM (Y := Y) n (Sum.inr a) = (ySec₂ (Y := Y)).hom.comp a := rfl

/-- `TopCat.toSSetObjEquivT` intertwines `yIdxSum` with `yIdxSumCM`. -/
lemma toSSetObjEquiv_yIdxSum (n : ℕ)
    (x : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) ⊕
      (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌)) :
    (YS0 Y).toSSetObjEquivT (Opposite.op ⦋n⦌) (yIdxSum (Y := Y) n x) =
      yIdxSumCM (Y := Y) n (Equiv.sumCongr
        ((TopCat.of Y).toSSetObjEquivT (Opposite.op ⦋n⦌))
        ((TopCat.of Y).toSSetObjEquivT (Opposite.op ⦋n⦌)) x) := by
  rcases x with a | a
  · apply ContinuousMap.ext; intro z; rfl
  · apply ContinuousMap.ext; intro z; rfl

/-- The decomposition is injective: the two sheets are disjoint. -/
lemma yIdxSumCM_bijective (n : ℕ) : Function.Bijective (yIdxSumCM (Y := Y) n) := by
  refine ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h
    · simp only [Sum.inl.injEq]
      apply ContinuousMap.ext; intro z
      exact congrArg Prod.fst (DFunLike.congr_fun h z)
    · exfalso
      exact s0N_ne_s0S (Prod.ext_iff.mp (DFunLike.congr_fun h (Classical.arbitrary _))).2
    · exfalso
      exact s0N_ne_s0S (Prod.ext_iff.mp (DFunLike.congr_fun h (Classical.arbitrary _))).2.symm
    · simp only [Sum.inr.injEq]
      apply ContinuousMap.ext; intro z
      exact congrArg Prod.fst (DFunLike.congr_fun h z)
  · intro σ
    obtain ⟨c, hc⟩ := contMap_snd_const_gen (Y := Y) σ
    rcases s0_cover c with h | h
    · refine ⟨Sum.inl ⟨fun t => (σ t).1, continuous_fst.comp σ.continuous⟩, ?_⟩
      apply ContinuousMap.ext
      intro t
      exact Prod.ext rfl (((hc t).trans h).symm)
    · refine ⟨Sum.inr ⟨fun t => (σ t).1, continuous_fst.comp σ.continuous⟩, ?_⟩
      apply ContinuousMap.ext
      intro t
      exact Prod.ext rfl (((hc t).trans h).symm)

/-- Every `n`-simplex of `Y × S⁰` factors uniquely through exactly one of the two sections of the
projection. -/
theorem yIdxSum_bijective (n : ℕ) : Function.Bijective (yIdxSum (Y := Y) n) := by
  set eY := (TopCat.of Y).toSSetObjEquivT (Opposite.op ⦋n⦌) with heY
  set e := (YS0 Y).toSSetObjEquivT (Opposite.op ⦋n⦌) with he
  set e₂ := Equiv.sumCongr eY eY with he₂
  have htr : ∀ x, e (yIdxSum (Y := Y) n x) = yIdxSumCM (Y := Y) n (e₂ x) :=
    fun x => toSSetObjEquiv_yIdxSum (Y := Y) n x
  have hCM := yIdxSumCM_bijective (Y := Y) n
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h1 : yIdxSumCM (Y := Y) n (e₂ x) = yIdxSumCM (Y := Y) n (e₂ y) := by
      rw [← htr x, ← htr y, h]
    exact e₂.injective (hCM.1 h1)
  · obtain ⟨z, hz⟩ := hCM.2 (e y)
    exact ⟨e₂.symm z, e.injective (by rw [htr, Equiv.apply_symm_apply, hz])⟩


/-! ## The chain map of the two sections is an isomorphism -/

/-- The `n`-th component of the chain map induced by the first section is `coprodMap` of the
induced map on simplices. -/
lemma chainMap_ySec₁_f (n : ℕ) :
    (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y))).f n
      = coprodMap (R:=R) (yIdx₁ (Y := Y) n) := by
  have h : chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y))
      = SSet.chainComplexMap (TopCat.toSSet.map (ySec₁ (Y := Y))) (ModuleCat.of R R) := rfl
  rw [h]
  apply SSet.chainComplex_hom_ext
  intro a
  rw [SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (YS0 Y)).ιChainComplex (yIdx₁ (Y := Y) n a)
      = (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex a ≫ coprodMap (R:=R) (yIdx₁ (Y := Y) n)
  rw [show (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex a
      = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) =>
          ModuleCat.of R R) a from rfl]
  rw [ι_coprodMap]
  rfl

/-- The `n`-th component of the chain map induced by the second section. -/
lemma chainMap_ySec₂_f (n : ℕ) :
    (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y))).f n
      = coprodMap (R:=R) (yIdx₂ (Y := Y) n) := by
  have h : chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y))
      = SSet.chainComplexMap (TopCat.toSSet.map (ySec₂ (Y := Y))) (ModuleCat.of R R) := rfl
  rw [h]
  apply SSet.chainComplex_hom_ext
  intro a
  rw [SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (YS0 Y)).ιChainComplex (yIdx₂ (Y := Y) n a)
      = (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex a ≫ coprodMap (R:=R) (yIdx₂ (Y := Y) n)
  rw [show (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex a
      = Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op ⦋n⦌) =>
          ModuleCat.of R R) a from rfl]
  rw [ι_coprodMap]
  rfl

/-- **The chain complex of `Y × S⁰` is the biproduct of two copies of the chain complex of `Y`**:
the map given by the two sections is an isomorphism. -/
theorem isIso_chainMap_desc :
    IsIso (biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
      (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))) := by
  haveI hcomp : ∀ n, IsIso ((biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
      (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))).f n) := by
    intro n
    haveI h1 : IsIso ((HomologicalComplex.biprodXIso (singularChains R (TopCat.of Y))
        (singularChains R (TopCat.of Y)) n).inv ≫
        (biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
          (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))).f n) := by
      rw [s0_biprod_desc_f, chainMap_ySec₁_f, chainMap_ySec₂_f]
      exact s0_isIso_biprod_desc_coprodMap (yIdx₁ (Y := Y) n) (yIdx₂ (Y := Y) n)
        (yIdxSum_bijective (Y := Y) n)
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.biprodXIso (singularChains R (TopCat.of Y))
        (singularChains R (TopCat.of Y)) n).inv _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The composite of the decomposition with the chain map of the projection is the *sum* of the two
components. -/
theorem chainMap_desc_comp_yProj :
    biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
        (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))
      ≫ chainMap R (YS0 Y) (TopCat.of Y) (yProj (Y := Y))
      = biprod.desc (𝟙 (singularChains R (TopCat.of Y)))
          (𝟙 (singularChains R (TopCat.of Y))) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, ← CategoryTheory.Functor.map_comp,
      ySec₁_comp_yProj, CategoryTheory.Functor.map_id, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_desc, ← CategoryTheory.Functor.map_comp,
      ySec₂_comp_yProj, CategoryTheory.Functor.map_id, biprod.inr_desc]

/-- **The chain complex of `Y × S⁰` is the biproduct of two copies of the chain complex of `Y`.** -/
noncomputable def chainS0Iso :
    singularChains R (TopCat.of Y) ⊞ singularChains R (TopCat.of Y) ≅
      singularChains R (YS0 Y) :=
  letI := isIso_chainMap_desc (R := R) (Y := Y)
  asIso (biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
      (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y))))


/-! ## Consequences on homology -/

/-- The homology of a biproduct of chain complexes is the biproduct of the homologies, compatibly
with the biproduct structure maps. -/
theorem s0_homology_biprod_iso_chain (C D : ChainComplex (ModuleCat R) ℕ) (k : ℕ) :
    ∃ (e : (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k),
      (biprod.inl : C.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k ∧
      (biprod.inr : D.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
        = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  refine ⟨F.mapBiprod C D, ?_, ?_⟩
  · erw [Functor.mapBiprod_inv, biprod.inl_desc]
    rfl
  · erw [Functor.mapBiprod_inv, biprod.inr_desc]
    rfl

/-- **The homology of `Y × S⁰` is the biproduct of two copies of the homology of `Y`**, over an
arbitrary coefficient ring. -/
noncomputable def homologyS0Iso (k : ℕ) :
    (singularChains R (YS0 Y)).homology k ≅
      (singularChains R (TopCat.of Y)).homology k ⊞
        (singularChains R (TopCat.of Y)).homology k :=
  (HomologicalComplex.homologyMapIso (chainS0Iso (R := R) (Y := Y)) k).symm ≪≫
    (Classical.choose (s0_homology_biprod_iso_chain (singularChains R (TopCat.of Y))
      (singularChains R (TopCat.of Y)) k))


/-! ## The cochain level -/

/-- The `n`-th component of `biprod.lift`, transported across `biprodXIso`. -/
lemma s0_biprod_lift_f_coch {K C D : CochainComplex (ModuleCat R) ℕ} (u : K ⟶ C) (v : K ⟶ D)
    (n : ℕ) :
    (biprod.lift u v).f n ≫ (HomologicalComplex.biprodXIso C D n).hom
      = biprod.lift (u.f n) (v.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst, ← HomologicalComplex.comp_f,
      biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f,
      biprod.lift_snd, biprod.lift_snd]

/-- The cochain complex of `Y`. -/
abbrev CohY (R : Type) [CommRing R] (Y : Type) [TopologicalSpace Y] :
    CochainComplex (ModuleCat R) ℕ := singularCochainComplex R (TopCat.of Y)

/-- **The cochain-level decomposition of `Y × S⁰`**: the two pullbacks along the two sections
present `C^*(Y × S⁰;R)` as the biproduct of two copies of `C^*(Y;R)`. -/
noncomputable def thetaY :
    singularCochainComplex R (YS0 Y) ⟶ CohY R Y ⊞ CohY R Y :=
  biprod.lift (dualChainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
    (dualChainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))

/-- `thetaY` is an isomorphism: it is the transpose of the chain-level decomposition, which is an
isomorphism by `yIdxSum_bijective`. -/
theorem isIso_thetaY : IsIso (thetaY (R := R) (Y := Y)) := by
  haveI hd : ∀ n, IsIso ((biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
      (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))).f n) := by
    intro n
    haveI h1 : IsIso ((HomologicalComplex.biprodXIso (singularChains R (TopCat.of Y))
        (singularChains R (TopCat.of Y)) n).inv ≫
        (biprod.desc (chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)))
          (chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)))).f n) := by
      rw [s0_biprod_desc_f, chainMap_ySec₁_f, chainMap_ySec₂_f]
      exact s0_isIso_biprod_desc_coprodMap (yIdx₁ (Y := Y) n) (yIdx₂ (Y := Y) n)
        (yIdxSum_bijective (Y := Y) n)
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.biprodXIso (singularChains R (TopCat.of Y))
        (singularChains R (TopCat.of Y)) n).inv _
  haveI hcomp : ∀ n, IsIso ((thetaY (R := R) (Y := Y)).f n) := by
    intro n
    have heq : (thetaY (R := R) (Y := Y)).f n
        ≫ (HomologicalComplex.biprodXIso (CohY R Y) (CohY R Y) n).hom
        = biprod.lift (ModuleCat.ofHom
              ((chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y))).f n).hom.dualMap)
            (ModuleCat.ofHom
              ((chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y))).f n).hom.dualMap) := by
      rw [thetaY, s0_biprod_lift_f_coch]
      rfl
    haveI hg : IsIso (biprod.desc ((chainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y))).f n)
        ((chainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y))).f n)) := by
      haveI := hd n
      rw [← s0_biprod_desc_f]
      infer_instance
    haveI h2 : IsIso ((thetaY (R := R) (Y := Y)).f n
        ≫ (HomologicalComplex.biprodXIso (CohY R Y) (CohY R Y) n).hom) := by
      rw [heq]
      exact isIso_biprod_lift_dualMap _ _
    exact IsIso.of_isIso_comp_right ((thetaY (R := R) (Y := Y)).f n)
      (HomologicalComplex.biprodXIso (CohY R Y) (CohY R Y) n).hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ## The compatibility with the projection -/

/-- The compatibility of the cochain-level decomposition with the projection: pulling back along
`Y × S⁰ → Y` corresponds to the *diagonal*. -/
theorem dualChainMap_yProj_thetaY :
    dualChainMap R (YS0 Y) (TopCat.of Y) (yProj (Y := Y)) ≫ thetaY (R := R) (Y := Y)
      = biprod.lift (𝟙 (CohY R Y)) (𝟙 (CohY R Y)) := by
  apply biprod.ext_to_iff.mpr
  constructor
  · rw [Category.assoc, thetaY, biprod.lift_fst, biprod.lift_fst,
      ← dualChainMap_comp R (ySec₁ (Y := Y)) (yProj (Y := Y)), ySec₁_comp_yProj, dualChainMap_id]
  · rw [Category.assoc, thetaY, biprod.lift_snd, biprod.lift_snd,
      ← dualChainMap_comp R (ySec₂ (Y := Y)) (yProj (Y := Y)), ySec₂_comp_yProj, dualChainMap_id]


/-- The first component of the cochain-level decomposition is the pullback along the first
section. -/
theorem thetaY_comp_fst :
    thetaY (R := R) (Y := Y) ≫ biprod.fst
      = dualChainMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)) :=
  biprod.lift_fst _ _

/-- The second component of the cochain-level decomposition is the pullback along the second
section. -/
theorem thetaY_comp_snd :
    thetaY (R := R) (Y := Y) ≫ biprod.snd
      = dualChainMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)) :=
  biprod.lift_snd _ _

/-! ## The cohomology of `Y × S⁰` -/

/-- The biproduct-compatibility of the homology of cochain complexes. -/
noncomputable def s0_homologyBiprodIsoCoch (C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ) :
    (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k :=
  haveI : PreservesBinaryBiproduct C D
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) k) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ C D
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) k).mapBiprod C D

lemma s0_homologyBiprodIsoCoch_hom (C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ) :
    (s0_homologyBiprodIsoCoch (R := R) C D k).hom
      = biprod.lift (HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k)
          (HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k) := by
  rw [s0_homologyBiprodIsoCoch, Functor.mapBiprod_hom]
  rfl

lemma s0_homologyBiprodIsoCoch_hom_fst (C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ) :
    (s0_homologyBiprodIsoCoch (R := R) C D k).hom ≫ biprod.fst
      = HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k := by
  rw [s0_homologyBiprodIsoCoch_hom]; exact biprod.lift_fst _ _

lemma s0_homologyBiprodIsoCoch_hom_snd (C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ) :
    (s0_homologyBiprodIsoCoch (R := R) C D k).hom ≫ biprod.snd
      = HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k := by
  rw [s0_homologyBiprodIsoCoch_hom]; exact biprod.lift_snd _ _

lemma s0_homologyMap_biprod_lift_coch (K C D : CochainComplex (ModuleCat R) ℕ) (k : ℕ)
    (u : K ⟶ C) (v : K ⟶ D) :
    HomologicalComplex.homologyMap (biprod.lift u v) k
        ≫ (s0_homologyBiprodIsoCoch (R := R) C D k).hom
      = biprod.lift (HomologicalComplex.homologyMap u k)
          (HomologicalComplex.homologyMap v k) := by
  apply biprod.hom_ext
  · rw [Category.assoc, s0_homologyBiprodIsoCoch_hom_fst, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, s0_homologyBiprodIsoCoch_hom_snd, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_snd, biprod.lift_snd]

/-- **The cohomology of `Y × S⁰` as the biproduct of two copies of the cohomology of `Y`**, given
explicitly (so that its components can be computed). -/
noncomputable def cohS0Iso (k : ℕ) :
    singularCohomology R k (YS0 Y) ≅
      singularCohomology R k (TopCat.of Y) ⊞ singularCohomology R k (TopCat.of Y) :=
  letI := isIso_thetaY (R := R) (Y := Y)
  asIso (HomologicalComplex.homologyMap (thetaY (R := R) (Y := Y)) k) ≪≫
    s0_homologyBiprodIsoCoch (R := R) (CohY R Y) (CohY R Y) k

/-- The first component of `cohS0Iso` is the pullback along the first section. -/
theorem cohS0Iso_hom_fst (k : ℕ) :
    (cohS0Iso (R := R) (Y := Y) k).hom ≫ biprod.fst
      = singularCohomologyMap R (TopCat.of Y) (YS0 Y) (ySec₁ (Y := Y)) k := by
  show (HomologicalComplex.homologyMap (thetaY (R := R) (Y := Y)) k
      ≫ (s0_homologyBiprodIsoCoch (R := R) (CohY R Y) (CohY R Y) k).hom) ≫ biprod.fst = _
  rw [Category.assoc, s0_homologyBiprodIsoCoch_hom_fst, ← HomologicalComplex.homologyMap_comp,
    thetaY_comp_fst]
  rfl

/-- The second component of `cohS0Iso` is the pullback along the second section. -/
theorem cohS0Iso_hom_snd (k : ℕ) :
    (cohS0Iso (R := R) (Y := Y) k).hom ≫ biprod.snd
      = singularCohomologyMap R (TopCat.of Y) (YS0 Y) (ySec₂ (Y := Y)) k := by
  show (HomologicalComplex.homologyMap (thetaY (R := R) (Y := Y)) k
      ≫ (s0_homologyBiprodIsoCoch (R := R) (CohY R Y) (CohY R Y) k).hom) ≫ biprod.snd = _
  rw [Category.assoc, s0_homologyBiprodIsoCoch_hom_snd, ← HomologicalComplex.homologyMap_comp,
    thetaY_comp_snd]
  rfl

/-- The pullback along the projection, composed with `cohS0Iso`, is the diagonal. -/
theorem cohS0Iso_yProj (k : ℕ) :
    singularCohomologyMap R (YS0 Y) (TopCat.of Y) (yProj (Y := Y)) k
        ≫ (cohS0Iso (R := R) (Y := Y) k).hom
      = biprod.lift (𝟙 (singularCohomology R k (TopCat.of Y)))
          (𝟙 (singularCohomology R k (TopCat.of Y))) := by
  show HomologicalComplex.homologyMap (dualChainMap R (YS0 Y) (TopCat.of Y) (yProj (Y := Y))) k
      ≫ (HomologicalComplex.homologyMap (thetaY (R := R) (Y := Y)) k
        ≫ (s0_homologyBiprodIsoCoch (R := R) (CohY R Y) (CohY R Y) k).hom)
      = biprod.lift (𝟙 (singularCohomology R k (TopCat.of Y)))
          (𝟙 (singularCohomology R k (TopCat.of Y)))
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, dualChainMap_yProj_thetaY,
    s0_homologyMap_biprod_lift_coch, HomologicalComplex.homologyMap_id]
  rfl

/-- **The cohomology of `Y × S⁰` is the biproduct of two copies of the cohomology of `Y`**, over an
arbitrary coefficient ring, compatibly with the projection (which corresponds to the *diagonal*). -/
theorem coh_S0_decomp (k : ℕ) :
    ∃ e : singularCohomology R k (YS0 Y) ≅
        singularCohomology R k (TopCat.of Y) ⊞ singularCohomology R k (TopCat.of Y),
      singularCohomologyMap R (YS0 Y) (TopCat.of Y) (yProj (Y := Y)) k ≫ e.hom
        = biprod.lift (𝟙 (singularCohomology R k (TopCat.of Y)))
            (𝟙 (singularCohomology R k (TopCat.of Y))) :=
  ⟨cohS0Iso (R := R) (Y := Y) k, cohS0Iso_yProj (R := R) (Y := Y) k⟩

end

end Work.StemsB
