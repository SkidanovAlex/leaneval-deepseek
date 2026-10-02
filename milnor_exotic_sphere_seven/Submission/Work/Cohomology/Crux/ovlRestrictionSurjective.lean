import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.relComplexMapHomologyIsoCompat
import Submission.Work.Cohomology.relChainsMap_quasiIso
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.Endgame.tripleLESSurj
import Submission.Work.Cohomology.Endgame.ovlCohomologyGroups
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Milnor.cohomology_Mk_minus_two
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.CollarHomotopy
import Submission.Work.Milnor.collar_homotopyEquiv_Mk
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.collarInclCohomologyIsIso
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.Ovl.OvlDefs
import Submission.Work.Cohomology.Ovl.ovlUnionVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## 1.  The relative cochains of a pair include compatibly with a pair map -/

/-- The map of pairs on relative cochains is compatible with the inclusion of the relative
cochains into the absolute (singular) cochains. -/
theorem relComplexMap_comp_relIncl_local {R : Type} [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap R A₁ A₂ f h ≫ relIncl R X₁ A₁ =
      relIncl R X₂ A₂ ≫ dualChainMap R X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relComplexMap_f, relIncl_f, relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact relMapLM_coe R A₁ A₂ f h n x

/-! ## 2.  The abstract five lemma: an inclusion of subspaces inducing a cohomology
isomorphism can be replaced by the identity of the ambient space -/

/-- If `A₁ ⊆ A₂ ⊆ X` and the inclusion `A₁ ↪ A₂` induces an isomorphism on singular cohomology,
then the map of pairs `(X, A₁) → (X, A₂)` given by the identity of `X` is an isomorphism on
relative cohomology.  (Five lemma applied to the morphism of short exact sequences of the pairs.) -/
theorem relComplexMap_pairId_isIso {X : TopCat} (A₁ A₂ : Set X)
    (h : ∀ x ∈ A₁, (𝟙 X) x ∈ A₂)
    (hiso : ∀ k, IsIso (singularCohomologyMap ℤ (TopCat.of A₁) (TopCat.of A₂)
      (relMapSub A₁ A₂ (𝟙 X) h) k))
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ (𝟙 X) h) n) := by
  classical
  have h' : ∀ x ∈ A₁, (𝟙 X) x ∈ A₂ := h
  let φ : pairShort ℤ X A₂ ⟶ pairShort ℤ X A₁ :=
    ShortComplex.homMk (relComplexMap ℤ A₁ A₂ (𝟙 X) h')
      (𝟙 (singularCochainComplex ℤ X))
      (dualChainMap ℤ (TopCat.of A₁) (TopCat.of A₂) (relMapSub A₁ A₂ (𝟙 X) h'))
      (by
        have hh := relComplexMap_comp_relIncl_local (R := ℤ) A₁ A₂ (𝟙 X) h'
        rwa [dualChainMap_id] at hh)
      (by
        show (𝟙 (singularCochainComplex ℤ X)) ≫ restr ℤ X A₁
          = restr ℤ X A₂ ≫ dualChainMap ℤ (TopCat.of A₁) (TopCat.of A₂)
              (relMapSub A₁ A₂ (𝟙 X) h')
        rw [Category.id_comp]
        have hh := dualChainMap_restr_comp ℤ A₁ A₂ (𝟙 X) h'
        rwa [dualChainMap_id] at hh)
  have h₂ : ∀ k, IsIso (HomologicalComplex.homologyMap φ.τ₂ k) := by
    intro k
    have hh : IsIso (HomologicalComplex.homologyMap
        (𝟙 (singularCochainComplex ℤ X)) k) := by
      rw [HomologicalComplex.homologyMap_id]
      infer_instance
    exact hh
  have h₃ : ∀ k, IsIso (HomologicalComplex.homologyMap φ.τ₃ k) := fun k => hiso k
  exact isIso_homologyMap_tau1 ℤ φ (pairShort_shortExact ℤ X A₂)
    (pairShort_shortExact ℤ X A₁) h₂ h₃ n

/-! ## 2b.  The pair map on relative chains is the excision map -/

/-- The map of relative chain complexes does not depend on the spelling of the subspace map, as
long as the underlying functions agree. -/
lemma relChainsMapOf_congr_sub_local {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) {g : TopCat.of A₁ ⟶ TopCat.of A₂}
    (w : subtypeIncl X₁ A₁ ≫ f = g ≫ subtypeIncl X₂ A₂)
    (hg : g = relMapSub A₁ A₂ f h) :
    relChainsMapOf X₁ X₂ A₁ A₂ f g w
      = relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h) := by
  subst hg
  rfl

/-- The canonical inclusion of the trace `U ∩ A` is the map of subspaces attached to the
inclusion `U ⊆ X`. -/
lemma inclInterA_eq_relMapSub (X : TopCat) (U A : Set X)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    inclInterA X U A = relMapSub {y : U | (y : X) ∈ A} A (subtypeIncl X U) h := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  exact Subtype.ext rfl

/-- The pair map on relative chains of the inclusion of a subspace is the map `relChainsMap`. -/
lemma relPairsChainsMapCompat_eq_relChainsMap (X : TopCat) (U A : Set X)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    Crux.relPairsChainsMapCompat (X₁ := TopCat.of ↥U) (X₂ := X)
        {y : U | (y : X) ∈ A} A (subtypeIncl X U) h = relChainsMap X U A := by
  rw [Crux.relPairsChainsMapCompat, relChainsMap]
  congr 1

/-! ## 2c.  Excision for an open cover -/

/-- **Excision.**  If `U, A ⊆ X` are open and cover `X`, the inclusion of pairs
`(U, U ∩ A) → (X, A)` induces an isomorphism on relative cohomology. -/
theorem openCover_excision_isIso (X : TopCat) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ {y : U | (y : X) ∈ A} A (subtypeIncl X U) h) n) := by
  rw [Crux.relComplexMap_dual (TopCat.of ↥U) X {y : U | (y : X) ∈ A} A (subtypeIncl X U) h]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have h2 : IsIso (HomologicalComplex.homologyMap (Crux.relCochainDualIso X A).inv n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      (Crux.relCochainDualIso X A).inv
  have h1 : IsIso (HomologicalComplex.homologyMap
      (Crux.relCochainDualIso (TopCat.of ↥U) {y : U | (y : X) ∈ A}).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      (Crux.relCochainDualIso (TopCat.of ↥U) {y : U | (y : X) ∈ A}).hom
  have hqc : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Crux.relPairsChainsMapCompat (X₁ := TopCat.of ↥U) (X₂ := X)
        {y : U | (y : X) ∈ A} A (subtypeIncl X U) h) k) := by
    intro k
    rw [relPairsChainsMapCompat_eq_relChainsMap X U A h]
    exact relChainsMap_quasiIso X U A hU hA hcov k
  have h3 : IsIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relChains (TopCat.of ↥U) {y : U | (y : X) ∈ A}) (relChains X A)
        (Crux.relPairsChainsMapCompat (X₁ := TopCat.of ↥U) (X₂ := X)
          {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)) n) :=
    dualComplexMap_quasiIso _ (fun k => relChainsProjective _ _ k)
      (fun k => relChainsProjective _ _ k) hqc n
  haveI := h2
  haveI := h3
  haveI := h1
  infer_instance

/-! ## 3.  The collar isomorphisms (the sphere bundle can be replaced by the collar) -/

/-- The inclusion of the sphere bundle `Mk(-2)` into the collar induces an isomorphism on
relative cohomology of the pair `(Vk(-2), ·)`. -/
theorem collarIsoX (n : ℕ)
    (h : ∀ x ∈ (Set.range (Work.Milnor.mkToVkFun (-2)) : Set (Submission.Milnor.Vk (-2))),
      (𝟙 (TopCat.of (Submission.Milnor.Vk (-2)))) x ∈ Work.Milnor.collar (-2)) :
    IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (Set.range (Work.Milnor.mkToVkFun (-2))) (Work.Milnor.collar (-2))
        (𝟙 (TopCat.of (Submission.Milnor.Vk (-2)))) h) n) := by
  have hh : ∀ k, IsIso (singularCohomologyMap ℤ
      (TopCat.of (Set.range (Work.Milnor.mkToVkFun (-2))))
      (TopCat.of (Work.Milnor.collar (-2)))
      (relMapSub (Set.range (Work.Milnor.mkToVkFun (-2))) (Work.Milnor.collar (-2))
        (𝟙 (TopCat.of (Submission.Milnor.Vk (-2)))) h) k) :=
    fun k => collarInclCohomologyIsIso h k
  exact relComplexMap_pairId_isIso
    (X := TopCat.of (Submission.Milnor.Vk (-2)))
    (A₁ := Set.range (Work.Milnor.mkToVkFun (-2))) (A₂ := Work.Milnor.collar (-2)) h hh n

/-! ## 3b.  Fibrewise scaling preserves the charts (hence the overlap) -/

/-- Fibrewise scaling preserves the first chart image. -/
lemma vScale_mem_range_ιX (k : ℤ) (c : ℝ) {p : Submission.Milnor.Vk k}
    (hp : p ∈ Set.range (Submission.Milnor.vData k).ιX) :
    Work.Milnor.vScale k c p ∈ Set.range (Submission.Milnor.vData k).ιX := by
  obtain ⟨a, rfl⟩ := hp
  rw [Work.Milnor.vScale_ιX]
  exact ⟨(a.1, c • a.2), rfl⟩

/-- Fibrewise scaling preserves the second chart image. -/
lemma vScale_mem_range_ιY (k : ℤ) (c : ℝ) {p : Submission.Milnor.Vk k}
    (hp : p ∈ Set.range (Submission.Milnor.vData k).ιY) :
    Work.Milnor.vScale k c p ∈ Set.range (Submission.Milnor.vData k).ιY := by
  obtain ⟨a, rfl⟩ := hp
  rw [Work.Milnor.vScale_ιY]
  exact ⟨(a.1, c • a.2), rfl⟩

/-- Normalising a point of the collar lands in the sphere bundle. -/
lemma vScale_inv_mem_range_mkToVkFun (k : ℤ) (p : Submission.Milnor.Vk k)
    (hp : p ∈ Work.Milnor.collar k) :
    Work.Milnor.vScale k (Work.Milnor.fibreNormFun k p)⁻¹ p
      ∈ Set.range (Work.Milnor.mkToVkFun k) := by
  refine ⟨Work.Milnor.unitInv k
    ⟨Work.Milnor.vScale k (Work.Milnor.fibreNormFun k p)⁻¹ p, ?_⟩, ?_⟩
  · exact Work.Milnor.fibreNormFun_vScale_inv k ⟨p, hp⟩
  · rw [Work.Milnor.mkToVkFun_unitInv]

/-- The overlap of the two charts, as a topological space. -/
abbrev ovlTopX : TopCat := TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV)

/-- The trace of the collar on the overlap. -/
abbrev ovlA2 : Set ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV) :=
  (Subtype.val :
      ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV) → Work.Cohomology.vkPairX) ⁻¹'
    Work.Milnor.collar (-2)

theorem continuous_ovlNorm_inner :
    Continuous (fun p : ↥ovlA2 =>
      Work.Milnor.vScale (-2) (Work.Milnor.fibreNormFun (-2) p.1.1)⁻¹ p.1.1) := by
  have hx : Continuous (fun p : ↥ovlA2 => p.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnu : Continuous (fun p : ↥ovlA2 => (Work.Milnor.fibreNormFun (-2) p.1.1)⁻¹) :=
    ((Work.Milnor.continuous_fibreNormFun (-2)).comp hx).inv₀ (fun p => by
      simp only [Function.comp_apply]
      exact ne_of_gt (by have := Work.Milnor.mem_collar.mp p.2; linarith))
  exact (Work.Milnor.continuous_vScale_uncurry (-2)).comp (hnu.prodMk hx)

/-- The normalisation `O ∩ collar → O ∩ Mk`. -/
def ovlG : TopCat.of ovlA2 ⟶ TopCat.of Work.Cohomology.Crux.vkOvlA :=
  TopCat.ofHom
  { toFun := fun p =>
      ⟨⟨Work.Milnor.vScale (-2) (Work.Milnor.fibreNormFun (-2) p.1.1)⁻¹ p.1.1,
          ⟨vScale_mem_range_ιX (-2) _ p.1.2.1, vScale_mem_range_ιY (-2) _ p.1.2.2⟩⟩,
        vScale_inv_mem_range_mkToVkFun (-2) p.1.1 p.2⟩
    continuous_toFun := Continuous.subtype_mk
      (Continuous.subtype_mk continuous_ovlNorm_inner
        (fun p => ⟨vScale_mem_range_ιX (-2) _ p.1.2.1, vScale_mem_range_ιY (-2) _ p.1.2.2⟩))
      (fun p => vScale_inv_mem_range_mkToVkFun (-2) p.1.1 p.2) }

/-- The inclusion of the trace of the sphere bundle into the trace of the collar. -/
def ovlF (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) :
    TopCat.of Work.Cohomology.Crux.vkOvlA ⟶ TopCat.of ovlA2 :=
  TopCat.ofHom
  { toFun := fun a => ⟨(𝟙 ovlTopX) a, h a a.2⟩
    continuous_toFun := Continuous.subtype_mk
      ((TopCat.Hom.hom (𝟙 ovlTopX)).continuous_toFun.comp continuous_subtype_val)
      (fun a => h a a.2) }

theorem continuous_ovlH2_toFun : Continuous (fun z : unitInterval × ↥ovlA2 =>
    (⟨⟨Work.Milnor.vScale (-2)
          (Work.Milnor.collarParam (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)) z.2.1.1,
        ⟨vScale_mem_range_ιX (-2) _ z.2.1.2.1, vScale_mem_range_ιY (-2) _ z.2.1.2.2⟩⟩,
      Work.Milnor.collarParam_mem (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)⟩ : ↥ovlA2)) := by
  have hvc : Continuous (fun z : unitInterval × ↥ovlA2 =>
      Work.Milnor.vScale (-2)
        (Work.Milnor.collarParam (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)) z.2.1.1) := by
    have hz' : Continuous (fun z : unitInterval × ↥ovlA2 => z.2.1.1) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have hcparam : Continuous (fun z : unitInterval × ↥ovlA2 =>
        Work.Milnor.collarParam (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)) := by
      have ht : Continuous (fun z : unitInterval × ↥ovlA2 => ((z.1 : unitInterval) : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hnu : Continuous (fun z : unitInterval × ↥ovlA2 =>
          (Work.Milnor.fibreNormFun (-2) z.2.1.1)⁻¹) :=
        ((Work.Milnor.continuous_fibreNormFun (-2)).comp hz').inv₀ (fun z => by
          simp only [Function.comp_apply]
          exact ne_of_gt (by have := Work.Milnor.mem_collar.mp z.2.2; linarith))
      have hmain : Continuous (fun z : unitInterval × ↥ovlA2 =>
          (1 - ((z.1 : unitInterval) : ℝ)) * (Work.Milnor.fibreNormFun (-2) z.2.1.1)⁻¹
            + ((z.1 : unitInterval) : ℝ)) := ((continuous_const.sub ht).mul hnu).add ht
      convert hmain using 1
      ext z
      simp only [Work.Milnor.collarParam]
    exact (Work.Milnor.continuous_vScale_uncurry (-2)).comp (hcparam.prodMk hz')
  exact Continuous.subtype_mk
    (Continuous.subtype_mk hvc
      (fun z => ⟨vScale_mem_range_ιX (-2) _ z.2.1.2.1, vScale_mem_range_ιY (-2) _ z.2.1.2.2⟩))
    (fun z => Work.Milnor.collarParam_mem (-2) (z.1, ⟨z.2.1.1, z.2.2⟩))

/-- The restriction of the collar homotopy to the overlap. -/
def ovlH2 (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) :
    TopCat.Homotopy (ovlG ≫ ovlF h) (𝟙 (TopCat.of ovlA2)) :=
  { toFun := fun z =>
      ⟨⟨Work.Milnor.vScale (-2)
            (Work.Milnor.collarParam (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)) z.2.1.1,
          ⟨vScale_mem_range_ιX (-2) _ z.2.1.2.1, vScale_mem_range_ιY (-2) _ z.2.1.2.2⟩⟩,
        Work.Milnor.collarParam_mem (-2) (z.1, ⟨z.2.1.1, z.2.2⟩)⟩
    continuous_toFun := continuous_ovlH2_toFun
    map_zero_left := by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      show Work.Milnor.vScale (-2)
            (Work.Milnor.collarParam (-2)
              (0, (⟨(p : ↥ovlA2).1.1, (p : ↥ovlA2).2⟩ : ↥(Work.Milnor.collar (-2)))))
            (p : ↥ovlA2).1.1
          = Work.Milnor.vScale (-2) (Work.Milnor.fibreNormFun (-2) (p : ↥ovlA2).1.1)⁻¹
              (p : ↥ovlA2).1.1
      rw [show Work.Milnor.collarParam (-2)
            (0, (⟨(p : ↥ovlA2).1.1, (p : ↥ovlA2).2⟩ : ↥(Work.Milnor.collar (-2))))
          = (Work.Milnor.fibreNormFun (-2) (p : ↥ovlA2).1.1)⁻¹ from by
        simp [Work.Milnor.collarParam]]
    map_one_left := by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      show Work.Milnor.vScale (-2)
            (Work.Milnor.collarParam (-2)
              (1, (⟨(p : ↥ovlA2).1.1, (p : ↥ovlA2).2⟩ : ↥(Work.Milnor.collar (-2)))))
            (p : ↥ovlA2).1.1
          = (p : ↥ovlA2).1.1
      rw [show Work.Milnor.collarParam (-2)
            (1, (⟨(p : ↥ovlA2).1.1, (p : ↥ovlA2).2⟩ : ↥(Work.Milnor.collar (-2))))
          = 1 from by simp [Work.Milnor.collarParam]]
      rw [Work.Milnor.vScale_one]
      rfl }

theorem ovlFG (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) :
    ovlF h ≫ ovlG = 𝟙 (TopCat.of Work.Cohomology.Crux.vkOvlA) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  show Work.Milnor.vScale (-2) (Work.Milnor.fibreNormFun (-2) (x : ↥Work.Cohomology.Crux.vkOvlA).1.1)⁻¹
        (x : ↥Work.Cohomology.Crux.vkOvlA).1.1
      = (x : ↥Work.Cohomology.Crux.vkOvlA).1.1
  have hnu : Work.Milnor.fibreNormFun (-2) ((x : ↥Work.Cohomology.Crux.vkOvlA).1.1) = 1 :=
    (Work.Milnor.mem_range_mkToVkFun_iff (-2) ((x : ↥Work.Cohomology.Crux.vkOvlA).1.1)).mp
      ((x : ↥Work.Cohomology.Crux.vkOvlA).2)
  rw [hnu, inv_one, Work.Milnor.vScale_one]
  rfl

/-- The (constant) homotopy `ovlF h ≫ ovlG ~ id`. -/
def ovlH1 (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) :
    TopCat.Homotopy (ovlF h ≫ ovlG) (𝟙 (TopCat.of Work.Cohomology.Crux.vkOvlA)) :=
  (ovlFG h) ▸ TopCat.Homotopy.refl (𝟙 (TopCat.of Work.Cohomology.Crux.vkOvlA))

/-- **The inclusion `O ∩ Mk → O ∩ collar` is a cohomology isomorphism.** -/
theorem ovlHiso (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) (k : ℕ) :
    IsIso (singularCohomologyMap ℤ (TopCat.of Work.Cohomology.Crux.vkOvlA) (TopCat.of ovlA2)
      (relMapSub Work.Cohomology.Crux.vkOvlA ovlA2 (𝟙 ovlTopX) h) k) :=
  homotopyEquiv ℤ (TopCat.of Work.Cohomology.Crux.vkOvlA) (TopCat.of ovlA2)
    (ovlF h) ovlG (ovlH1 h) (ovlH2 h) k

/-- The collar over the overlap does not change the relative cohomology. -/
theorem collarIsoW (n : ℕ) (h : ∀ x ∈ Work.Cohomology.Crux.vkOvlA, (𝟙 ovlTopX) x ∈ ovlA2) :
    IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ Work.Cohomology.Crux.vkOvlA ovlA2 (𝟙 ovlTopX) h) n) := by
  have hh : ∀ k, IsIso (singularCohomologyMap ℤ (TopCat.of Work.Cohomology.Crux.vkOvlA)
      (TopCat.of ovlA2) (relMapSub Work.Cohomology.Crux.vkOvlA ovlA2 (𝟙 ovlTopX) h) k) :=
    fun k => ovlHiso h k
  exact relComplexMap_pairId_isIso (X := ovlTopX) (A₁ := Work.Cohomology.Crux.vkOvlA)
    (A₂ := ovlA2) h hh n

/-! ## 4.  The cohomology computations used to collapse the triple sequence -/

/-- `H^n(↥(collar k))` vanishes for `n ∉ {0, 7}`. -/
lemma isZero_cohomology_collar (n : ℕ) (hn0 : n ≠ 0) (hn7 : n ≠ 7) :
    IsZero (singularCohomology ℤ n (TopCat.of ↥(Work.Milnor.collar (-2)))) := by
  obtain ⟨he⟩ := Work.Milnor.collar_homotopyEquiv_Mk (-2)
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv he n
  obtain ⟨e2⟩ := Work.Milnor.cohomology_Mk_minus_two n
  have hN : IsZero (ModuleCat.of ℤ
      (Fin ((if n = 0 then 1 else 0) + if n = 7 then 1 else 0) → ℤ)) := by
    rw [show ((if n = 0 then 1 else 0) + if n = 7 then 1 else 0) = 0 from by
      rw [if_neg hn0, if_neg hn7, Nat.add_zero]]
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso (IsZero.of_iso hN e2) e

/-- `H^n(Vk(-2))` vanishes for `n ∉ {0, 4}`. -/
lemma isZero_cohomology_vk (n : ℕ) (hn0 : n ≠ 0) (hn4 : n ≠ 4) :
    IsZero (singularCohomology ℤ n Work.Cohomology.vkPairX) := by
  obtain ⟨e⟩ := Work.Milnor.cohomology_Vk (-2) n
  have hN : IsZero (ModuleCat.of ℤ
      (Fin ((if n = 0 then 1 else 0) + if n = 4 then 1 else 0) → ℤ)) := by
    rw [show ((if n = 0 then 1 else 0) + if n = 4 then 1 else 0) = 0 from by
      rw [if_neg hn0, if_neg hn4, Nat.add_zero]]
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hN e

/-- `H^6` of the overlap pair `(U ∩ V, (U ∩ V) ∩ Mk)` vanishes. -/
lemma isZero_ovl_cohomology_six :
    IsZero (relCohomology ℤ Work.Cohomology.Crux.vkOvl Work.Cohomology.Crux.vkOvlA 6) := by
  obtain ⟨e⟩ := Endgame.ovlCohomologyGroups 6
  have hN : IsZero (ModuleCat.of ℤ
      (Fin ((if (6 : ℕ) = 4 then 1 else 0) + if (6 : ℕ) = 7 then 1 else 0) → ℤ)) := by
    rw [show ((if (6 : ℕ) = 4 then 1 else 0) + if (6 : ℕ) = 7 then 1 else 0) = 0 from by
      norm_num]
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hN e

end

/-! ## 5.  The collared restriction and its transport to the sphere bundle

The restriction `ρ : H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` is factored through the
collar pair `(Vk(-2), collar(-2))` and the union `W = (U ∩ V) ∪ collar(-2)`, following the
proof of `Submission/Work/Cohomology/ovlRestrCollarSurjective.lean` (whose module cannot be
imported here because it depends on this very module), and the sphere bundle is then replaced by
the collar using `Work.Cohomology.collarIsoW`. -/

noncomputable section

/-- The sphere bundle `Mk(-2)` is contained in the collar `{1/2 < ν}`. -/
theorem vkPairA_subset_collar : vkPairA ⊆ (Work.Milnor.collar (-2) : Set vkPairX) := by
  rintro x ⟨q, rfl⟩
  rw [Work.Milnor.mem_collar, Work.Milnor.fibreNormFun_mkToVkFun]
  norm_num

/-- The trace of the sphere bundle on the overlap lies in the trace of the collar. -/
theorem vkOvlA_subset_ovlA2 : Crux.vkOvlA ⊆ ovlA2 := by
  rintro x hx
  exact vkPairA_subset_collar hx

namespace OvlCollar

abbrev O : Set vkPairX := Crux.vkU ∩ Crux.vkV
abbrev Coll : Set vkPairX := Work.Milnor.collar (-2)
abbrev W : Set vkPairX := O ∪ Coll
abbrev ovlSpace : TopCat := TopCat.of ↥O
abbrev Xw : TopCat := TopCat.of ↥W
abbrev UO : Set ↥W := (Subtype.val : ↥W → vkPairX) ⁻¹' O
abbrev CW : Set ↥W := (Subtype.val : ↥W → vkPairX) ⁻¹' Coll
abbrev CO' : Set ↥UO := (Subtype.val : ↥UO → ↥W) ⁻¹' CW
abbrev CO : Set ↥O := (Subtype.val : ↥O → vkPairX) ⁻¹' Coll

/-- The canonical homeomorphism `O ≅ UO = O ∩ W`. -/
def eIso : ovlSpace ≅ TopCat.of ↥UO := Endgame.subPreImageHomeo W O (fun _ hx => Or.inl hx)

/-- `relComplexMap` of the identity is the identity. -/
theorem relComplexMap_id_local {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap ℤ A A (𝟙 X) h = 𝟙 (relComplex ℤ X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

theorem surjective_hom_comp {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f.hom) (hg : Function.Surjective g.hom) :
    Function.Surjective (f ≫ g).hom := by
  rw [ModuleCat.hom_comp]
  intro y
  obtain ⟨z, hz⟩ := hg y
  obtain ⟨w, hw⟩ := hf z
  exact ⟨w, by simp only [LinearMap.comp_apply]; rw [hw, hz]⟩

theorem surjective_of_split {A B : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ A)
    (h : g ≫ f = 𝟙 B) : Function.Surjective f.hom := by
  intro y
  refine ⟨g.hom y, ?_⟩
  have h2 := congrArg (fun (k : B ⟶ B) => (ModuleCat.Hom.hom k) y) h
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  simpa using h2

/-- `H⁵(Vk(-2), W) = 0` for `W = (U ∩ V) ∪ collar(-2)`. -/
theorem subsingleton_H5_W_local : Subsingleton (relCohomology ℤ vkPairX W 5) :=
  Ovl.ovlUnionCollar_vanishing

/-- The factorization of the collared restriction through the excised space. -/
theorem target_eq_composite :
    relComplexMap (X₁ := TopCat.of ↥O) (X₂ := vkPairX) ℤ CO Coll
        (subtypeIncl vkPairX O) (fun _ hx => hx)
      = (relComplexMap (X₁ := Xw) (X₂ := vkPairX) ℤ CW Coll
            (subtypeIncl vkPairX W) (fun _ hx => hx))
        ≫ (relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := Xw) ℤ CO' CW
            (subtypeIncl Xw UO) (fun _ hx => hx))
        ≫ (relComplexMap (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥UO) ℤ CO CO'
            eIso.hom (fun _ hx => hx)) := by
  have hcomp : eIso.hom ≫ subtypeIncl Xw UO ≫ subtypeIncl vkPairX W
      = subtypeIncl vkPairX O := Endgame.subPreImageHomeo_comp W O (fun _ hx => Or.inl hx)
  rw [← Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥O) (X₂ := vkPairX) CO Coll hcomp
      (fun _ hx => hx) (fun _ hx => hx)]
  rw [Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥UO)
    (X₃ := vkPairX) CO CO' Coll eIso.hom (subtypeIncl Xw UO ≫ subtypeIncl vkPairX W)
    (fun _ hx => hx) (fun _ hx => hx)]
  rw [Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥UO) (X₂ := Xw) (X₃ := vkPairX)
    CO' CW Coll (subtypeIncl Xw UO) (subtypeIncl vkPairX W) (fun _ hx => hx) (fun _ hx => hx)]
  rw [Category.assoc]

theorem chi_retract :
    relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := TopCat.of ↥O) ℤ CO' CO eIso.inv
        (fun _ hx => hx)
      ≫ relComplexMap (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥UO) ℤ CO CO' eIso.hom
          (fun _ hx => hx)
    = 𝟙 (relComplex ℤ (TopCat.of ↥O) CO) := by
  rw [← Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥UO)
    (X₃ := TopCat.of ↥O) CO CO' CO eIso.hom eIso.inv (fun _ hx => hx) (fun _ hx => hx)]
  rw [Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥O) CO CO
    eIso.hom_inv_id (fun _ hx => hx) (fun _ hx => hx)]
  exact relComplexMap_id_local (X := TopCat.of ↥O) CO (fun _ hx => hx)

theorem main_aux :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥O) (X₂ := vkPairX) ℤ CO Coll
        (subtypeIncl vkPairX O) (fun _ hx => hx)) 4)) := by
  have hphi : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := Xw) (X₂ := vkPairX) ℤ CW Coll
        (subtypeIncl vkPairX W) (fun _ hx => hx)) 4)) :=
    Endgame.tripleLESSurj vkPairX Coll W (fun _ hx => Or.inr hx) 4 subsingleton_H5_W_local
  have hpsiIso : IsIso (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := Xw) ℤ CO' CW
        (subtypeIncl Xw UO) (fun _ hx => hx)) 4) :=
    openCover_excision_isIso Xw UO CW
      ((Crux.vkU_isOpen.inter Crux.vkV_isOpen).preimage continuous_subtype_val)
      ((Work.Milnor.isOpen_collar (-2)).preimage continuous_subtype_val)
      (Set.eq_univ_of_forall (fun x => x.2)) 4 (fun _ hx => hx)
  have hpsi : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := Xw) ℤ CO' CW
        (subtypeIncl Xw UO) (fun _ hx => hx)) 4)) := by
    haveI := hpsiIso
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hchi : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥O) (X₂ := TopCat.of ↥UO) ℤ CO CO'
        eIso.hom (fun _ hx => hx)) 4)) :=
    surjective_of_split _
      (HomologicalComplex.homologyMap
        (relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := TopCat.of ↥O) ℤ CO' CO eIso.inv
          (fun _ hx => hx)) 4)
      (by rw [← HomologicalComplex.homologyMap_comp, chi_retract,
        HomologicalComplex.homologyMap_id])
  rw [target_eq_composite, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  exact surjective_hom_comp
    (f := HomologicalComplex.homologyMap (relComplexMap (X₁ := Xw) (X₂ := vkPairX) ℤ CW Coll
      (subtypeIncl vkPairX W) (fun _ hx => hx)) 4
      ≫ HomologicalComplex.homologyMap (relComplexMap (X₁ := TopCat.of ↥UO) (X₂ := Xw)
        ℤ CO' CW (subtypeIncl Xw UO) (fun _ hx => hx)) 4)
    (g := HomologicalComplex.homologyMap (relComplexMap (X₁ := TopCat.of ↥O)
      (X₂ := TopCat.of ↥UO) ℤ CO CO' eIso.hom (fun _ hx => hx)) 4)
    (surjective_hom_comp _ _ hphi hpsi) hchi

end OvlCollar

namespace OvlRestr

/-- The collared restriction `H⁴(Vk, collar) → H⁴(U ∩ V, (U ∩ V) ∩ Mk)` is surjective
(`Work.Cohomology.OvlCollar.main_aux`). -/
theorem gxT_surjective :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ ((Subtype.val : ↥(Crux.vkU ∩ Crux.vkV) → vkPairX) ⁻¹' (Work.Milnor.collar (-2))) (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => hx)) 4)) :=
  OvlCollar.main_aux

/-- The collar enlargement over the overlap is an isomorphism on `H⁴`. -/
theorem fT_isIso : IsIso (HomologicalComplex.homologyMap
    (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) ℤ Crux.vkOvlA ((Subtype.val : ↥(Crux.vkU ∩ Crux.vkV) → vkPairX) ⁻¹' (Work.Milnor.collar (-2))) (𝟙 (TopCat.of ↥(Crux.vkU ∩ Crux.vkV))) (fun _ hx => vkOvlA_subset_ovlA2 hx)) 4) :=
  collarIsoW 4 (fun _ hx => vkOvlA_subset_ovlA2 hx)

/-- The collared restriction with the sphere bundle as the sub-pair is surjective on `H⁴`. -/
theorem xiT_surjective :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => vkPairA_subset_collar hx)) 4)) := by
  haveI := fT_isIso
  have h : (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => vkPairA_subset_collar hx))
      = (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ ((Subtype.val : ↥(Crux.vkU ∩ Crux.vkV) → vkPairX) ⁻¹' (Work.Milnor.collar (-2))) (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => hx))
        ≫ (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) ℤ Crux.vkOvlA ((Subtype.val : ↥(Crux.vkU ∩ Crux.vkV) → vkPairX) ⁻¹' (Work.Milnor.collar (-2))) (𝟙 (TopCat.of ↥(Crux.vkU ∩ Crux.vkV))) (fun _ hx => vkOvlA_subset_ovlA2 hx)) := by
    have h0 := Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₃ := vkPairX)
      Crux.vkOvlA ((Subtype.val : ↥(Crux.vkU ∩ Crux.vkV) → vkPairX) ⁻¹' (Work.Milnor.collar (-2))) (Work.Milnor.collar (-2)) (𝟙 (TopCat.of ↥(Crux.vkU ∩ Crux.vkV))) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => vkOvlA_subset_ovlA2 hx) (fun _ hx => hx)
    rw [← h0]
    refine (Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) (A₁ := Crux.vkOvlA)
      (A₂ := (Work.Milnor.collar (-2))) (Category.id_comp (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV))) (fun _ hx => vkOvlA_subset_ovlA2 hx) (fun _ hx => vkPairA_subset_collar hx)).trans ?_
    exact Ovl.relComplexMap_hcongr _ _ _ _ _
  rw [h, HomologicalComplex.homologyMap_comp]
  exact OvlCollar.surjective_hom_comp _ _ gxT_surjective
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- The restriction of the collared pair to the overlap factors as `ψ ≫ ρ`. -/
theorem psiT_comp_rhoT :
    (relComplexMap (X₁ := vkPairX) (X₂ := vkPairX) ℤ vkPairA (Work.Milnor.collar (-2)) (𝟙 vkPairX) (fun _ hx => vkPairA_subset_collar hx))
      ≫ (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA vkPairA (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => hx))
    = (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => vkPairA_subset_collar hx)) := by
  have h0 := Ovl.relComplexMap_comp_ovl (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) (X₃ := vkPairX)
    Crux.vkOvlA vkPairA (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (𝟙 vkPairX) (fun _ hx => hx) (fun _ hx => vkPairA_subset_collar hx)
  rw [← h0]
  refine (Ovl.relComplexMap_congr_map (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) (A₁ := Crux.vkOvlA)
    (A₂ := (Work.Milnor.collar (-2))) (Category.comp_id (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV))) (fun _ hx => vkPairA_subset_collar hx) (fun _ hx => vkPairA_subset_collar hx)).trans ?_
  exact Ovl.relComplexMap_hcongr _ _ _ _ _

/-- **The restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` is surjective.** -/
theorem rhoT_surjective :
    Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA vkPairA (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => hx)) 4)) := by
  have hfac : HomologicalComplex.homologyMap
        (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA (Work.Milnor.collar (-2)) (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => vkPairA_subset_collar hx)) 4
      = HomologicalComplex.homologyMap
          (relComplexMap (X₁ := vkPairX) (X₂ := vkPairX) ℤ vkPairA (Work.Milnor.collar (-2)) (𝟙 vkPairX) (fun _ hx => vkPairA_subset_collar hx)) 4
        ≫ HomologicalComplex.homologyMap
          (relComplexMap (X₁ := TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) (X₂ := vkPairX) ℤ Crux.vkOvlA vkPairA (subtypeIncl vkPairX (Crux.vkU ∩ Crux.vkV)) (fun _ hx => hx)) 4 := by
    have h := congrArg (fun (φ : relComplex ℤ vkPairX (Work.Milnor.collar (-2)) ⟶ relComplex ℤ (TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) Crux.vkOvlA) =>
      HomologicalComplex.homologyMap φ 4) psiT_comp_rhoT
    rw [HomologicalComplex.homologyMap_comp] at h
    exact h.symm
  intro y
  obtain ⟨x, hx⟩ := xiT_surjective y
  refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    (relComplexMap (X₁ := vkPairX) (X₂ := vkPairX) ℤ vkPairA (Work.Milnor.collar (-2)) (𝟙 vkPairX) (fun _ hx => vkPairA_subset_collar hx)) 4)) x, ?_⟩
  have h := congrArg (fun (φ : (relComplex ℤ vkPairX (Work.Milnor.collar (-2))).homology 4 →ₗ[ℤ]
      (relComplex ℤ (TopCat.of ↥(Crux.vkU ∩ Crux.vkV)) Crux.vkOvlA).homology 4) => φ x)
    (congrArg ModuleCat.Hom.hom hfac)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm.trans hx

end OvlRestr

end


end Work.Cohomology

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

noncomputable section

theorem ovlRestrictionSurjective :
    Function.Surjective (HomologicalComplex.homologyMap
      (relComplexMap ℤ Work.Cohomology.Crux.vkOvlA Work.Cohomology.vkPairA
        (subtypeIncl Work.Cohomology.vkPairX (Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
        (fun _ hx => hx)) 4) := by
  exact Work.Cohomology.OvlRestr.rhoT_surjective

end
end Work.Cohomology.Crux
