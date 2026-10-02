import Mathlib
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.hasCollar_normalDiscSub
import Submission.Work.Orient.Boundary
import Submission.Work.Cohomology.pd_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology
open CategoryTheory CategoryTheory.Limits
open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- The open ε-disc bundle of the normal bundle, as a subset of the closed disc bundle. -/
def openDiscSub {E : EmbeddingData V (8 + k)} (ε : ℝ) : Set (NormalDiscSub E ε) :=
  {p | normalNorm E (p : NormalTotal E) < ε}

theorem mem_openDiscSub {E : EmbeddingData V (8 + k)} {ε : ℝ} {p : NormalDiscSub E ε} :
    p ∈ openDiscSub (E := E) ε ↔ normalNorm E (p : NormalTotal E) < ε := Iff.rfl

theorem isOpen_openDiscSub {E : EmbeddingData V (8 + k)} (ε : ℝ) :
    IsOpen (openDiscSub (E := E) ε) := by
  have hcont : Continuous (fun p : NormalDiscSub E ε => normalNorm E (p : NormalTotal E)) :=
    (continuous_normalNorm E).comp continuous_subtype_val
  have hset : openDiscSub (E := E) ε =
      {p : NormalDiscSub E ε | normalNorm E (p : NormalTotal E) < ε} := rfl
  rw [hset]
  exact isOpen_lt hcont continuous_const

theorem mem_openTubeSet_iff {E : EmbeddingData V (8 + k)} {y : Euc (8 + k)} :
    y ∈ openTubeSet E ε ↔ ∃ q : NormalDiscSub E ε,
      normalNorm E (q : NormalTotal E) < ε ∧ tubeMap E (q : NormalTotal E) = y := by
  constructor
  · intro hy
    rw [openTubeSet] at hy
    obtain ⟨q, hq, hqe⟩ := hy
    exact ⟨⟨q, mem_normalClosedDiscSet.mpr (le_of_lt hq)⟩, hq, hqe⟩
  · rintro ⟨q, hq, hqe⟩
    rw [openTubeSet]
    exact ⟨(q : NormalTotal E), hq, hqe⟩

theorem openTubeSet_subset_U {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    openTubeSet E ε ⊆ C.U := by
  intro y hy
  obtain ⟨q, hq, hqe⟩ := mem_openTubeSet_iff.mp hy
  exact hqe ▸ C.mem_U (q : NormalTotal E) (le_of_lt hq)

theorem normalNorm_inv_lt {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {y : Euc (8 + k)} (hy : y ∈ openTubeSet E ε) : normalNorm E (C.inv y) < ε := by
  obtain ⟨q, hq, hqe⟩ := mem_openTubeSet_iff.mp hy
  rw [← hqe, C.inv_tubeMap (q : NormalTotal E) (le_of_lt hq)]
  exact hq

theorem tubeMap_inv_openTube {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {y : Euc (8 + k)} (hy : y ∈ openTubeSet E ε) : tubeMap E (C.inv y) = y :=
  C.tubeMap_inv y (openTubeSet_subset_U C hy)

/-- **The inverse of the tubular map as a map from the open tube into the disc bundle.** -/
noncomputable def invOpenTube {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    C(↥(openTubeSet E ε), NormalDiscSub E ε) where
  toFun y := ⟨C.inv y.1, mem_normalClosedDiscSet.mpr (le_of_lt (normalNorm_inv_lt C y.2))⟩
  continuous_toFun := by
    have h : Continuous fun y : ↥(openTubeSet E ε) => C.inv y.1 :=
      C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => openTubeSet_subset_U C y.2)
    exact Continuous.subtype_mk h fun y =>
      mem_normalClosedDiscSet.mpr (le_of_lt (normalNorm_inv_lt C y.2))

@[simp] theorem invOpenTube_apply {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (y : ↥(openTubeSet E ε)) :
    ((invOpenTube C y : NormalDiscSub E ε) : NormalTotal E) = C.inv y.1 := rfl

theorem tubeMap_invOpenTube {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (y : ↥(openTubeSet E ε)) :
    tubeMap E ((invOpenTube C y : NormalDiscSub E ε) : NormalTotal E) = y.1 :=
  tubeMap_inv_openTube C y.2

/-- **The image of a subset of the disc bundle in the ambient space**, under the tubular map. -/
def tubeImage {E : EmbeddingData V (8 + k)} (K : Set (NormalDiscSub E ε)) : Set (Euc (8 + k)) :=
  {y | ∃ q ∈ K, tubeMap E (q : NormalTotal E) = y}

theorem mem_tubeImage {E : EmbeddingData V (8 + k)} {K : Set (NormalDiscSub E ε)}
    {y : Euc (8 + k)} :
    y ∈ tubeImage (E := E) K ↔ ∃ q ∈ K, tubeMap E (q : NormalTotal E) = y := Iff.rfl

theorem tubeImage_subset_openTube {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {K : Set (NormalDiscSub E ε)} (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε) :
    tubeImage (E := E) K ⊆ openTubeSet E ε := by
  rintro y ⟨q, hq, rfl⟩
  exact mem_openTubeSet_iff.mpr ⟨q, hK q hq, rfl⟩

/-- The subset of the open tube whose image in the disc bundle avoids `K` (the relative set of the
pair `(U_ε, U_ε ∖ K')`). -/
def tubeRelSub {E : EmbeddingData V (8 + k)} (K : Set (NormalDiscSub E ε)) :
    Set ↥(openTubeSet E ε) :=
  {y | (y : Euc (8 + k)) ∉ tubeImage (E := E) K}

theorem mem_tubeRelSub {E : EmbeddingData V (8 + k)} {K : Set (NormalDiscSub E ε)}
    {y : ↥(openTubeSet E ε)} : y ∈ tubeRelSub (E := E) K ↔ (y : Euc (8 + k)) ∉ tubeImage K :=
  Iff.rfl

/-- The complement of `K` inside the disc bundle (the relative set of the pair
`(D_ε(ν), D_ε(ν) ∖ K)`). -/
def discRelSub {E : EmbeddingData V (8 + k)} (K : Set (NormalDiscSub E ε)) :
    Set (NormalDiscSub E ε) :=
  {y | y ∉ K}

theorem mem_discRelSub {E : EmbeddingData V (8 + k)} {K : Set (NormalDiscSub E ε)}
    {y : NormalDiscSub E ε} : y ∈ discRelSub K ↔ y ∉ K := Iff.rfl

/-- The tubular map is injective on the disc bundle. -/
theorem tubeMap_injective {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) :
    Function.Injective fun q : NormalDiscSub E ε => tubeMap E (q : NormalTotal E) := by
  intro q q' h
  have h1 : C.inv (tubeMap E (q : NormalTotal E)) = (q : NormalTotal E) :=
    C.inv_tubeMap (q : NormalTotal E) q.2
  have h2 : C.inv (tubeMap E (q' : NormalTotal E)) = (q' : NormalTotal E) :=
    C.inv_tubeMap (q' : NormalTotal E) q'.2
  have hh : tubeMap E (q : NormalTotal E) = tubeMap E (q' : NormalTotal E) := by simpa using h
  exact Subtype.ext (h1.symm.trans ((congrArg (fun v => C.inv v) hh).trans h2))

/-- A point of the tube whose image in the disc bundle is outside `K` is outside `tubeImage K`. -/
theorem inv_mem_discRelSub {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    {K : Set (NormalDiscSub E ε)} {y : ↥(openTubeSet E ε)}
    (hy : (y : Euc (8 + k)) ∉ tubeImage (E := E) K) :
    invOpenTube C y ∈ discRelSub (E := E) K := by
  intro hmem
  refine hy ⟨invOpenTube C y, hmem, ?_⟩
  exact tubeMap_invOpenTube C y

/-- **The chain map on relative chain complexes induced by the inverse tubular map**: the map
`C_*(U_ε, U_ε∖K') ⟶ C_*(D_ε(ν), D_ε(ν)∖K)` given by the (continuous) map `inv`, where
`K' = tubeImage K`. -/
noncomputable def invChainMap {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (K : Set (NormalDiscSub E ε)) :
    Work.Cohomology.relChains (TopCat.of ↥(openTubeSet E ε)) (tubeRelSub (E := E) K)
      ⟶ Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε)) (discRelSub (E := E) K) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε)) (TopCat.of (NormalDiscSub E ε))
    (tubeRelSub (E := E) K) (discRelSub (E := E) K) (TopCat.ofHom (invOpenTube C))
    (TopCat.ofHom ⟨fun y => ⟨invOpenTube C y.1, inv_mem_discRelSub C y.2⟩,
      Continuous.subtype_mk ((invOpenTube C).continuous.comp continuous_subtype_val)
        (fun y => inv_mem_discRelSub C y.2)⟩)
    (by ext y <;> rfl)

/-- **The chain map on relative chain complexes induced by the tubular map**: the map
`C_*(D_ε(ν), D_ε(ν)∖K) ⟶ C_*(ℝ^N, ℝ^N∖K')` given by the tubular map, where `K' = tubeImage K`. -/
noncomputable def tubeChainMap {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (K : Set (NormalDiscSub E ε)) :
    Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε)) (discRelSub (E := E) K)
      ⟶ Work.Cohomology.relChains (TopCat.of (Euc (8 + k))) (tubeImage (E := E) K)ᶜ :=
  Work.Cohomology.relChainsMapOf (TopCat.of (NormalDiscSub E ε)) (TopCat.of (Euc (8 + k)))
    (discRelSub (E := E) K) (tubeImage (E := E) K)ᶜ
    (TopCat.ofHom ⟨fun q => tubeMap E (q : NormalTotal E),
      (continuous_tubeMap E).comp continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun q => ⟨tubeMap E (q.1 : NormalTotal E), by
        intro hmem
        obtain ⟨q', hq', hq'e⟩ := mem_tubeImage.mp hmem
        exact q.2 ((tubeMap_injective C hq'e) ▸ hq')⟩,
      Continuous.subtype_mk ((continuous_tubeMap E).comp
        (continuous_subtype_val.comp continuous_subtype_val)) (fun q => by
        intro hmem
        obtain ⟨q', hq', hq'e⟩ := mem_tubeImage.mp hmem
        exact q.2 ((tubeMap_injective C hq'e) ▸ hq'))⟩)
    (by ext y; rfl)

/-- **The excision map** on the ambient side: the inclusion of pairs
`(U_ε, U_ε∖K') ↪ (ℝ^N, ℝ^N∖K')`.  It is an isomorphism on homology by excision. -/
noncomputable def excisionMap {E : EmbeddingData V (8 + k)} (K : Set (NormalDiscSub E ε)) :
    Work.Cohomology.relChains (TopCat.of ↥(openTubeSet E ε)) (tubeRelSub (E := E) K)
      ⟶ Work.Cohomology.relChains (TopCat.of (Euc (8 + k))) (tubeImage (E := E) K)ᶜ :=
  Work.Cohomology.relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
    (tubeImage (E := E) K)ᶜ


/-- The point of the open tube corresponding to an interior point of the disc bundle. -/
def tubePt {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (x : NormalDiscSub E ε)
    (hx : normalNorm E (x : NormalTotal E) < ε) : ↥(openTubeSet E ε) :=
  ⟨tubeMap E (x : NormalTotal E), mem_openTubeSet_iff.mpr ⟨x, hx, rfl⟩⟩

@[simp] theorem tubePt_val {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    (tubePt C x hx : Euc (8 + k)) = tubeMap E (x : NormalTotal E) := rfl

/-- **The image of a singleton** is the corresponding point of the open tube. -/
theorem tubeImage_singleton {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)) = {(tubePt C x hx : Euc (8 + k))} := by
  ext y
  constructor
  · rintro ⟨q, hq, hqe⟩
    rw [Set.mem_singleton_iff] at hq
    rw [Set.mem_singleton_iff, ← hqe, hq]
    rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨x, rfl, by rw [hy]; rfl⟩

/-- Transport of a relative homology group along an equality of the excluded sets. -/
theorem relH_congr {M : TopCat} {N : ℕ} {S T : Set M} (h : S = T) :
    Work.Orient.RelH M N S = Work.Orient.RelH M N T := by
  rw [h]

/-- **Enlargement maps are compatible with an equality of the excluded sets.**  If `A = A'` and
`B = B'` then the two enlargements `C(X,X∖A) → C(X,X∖B)` and `C(X,X∖A') → C(X,X∖B')` agree up to the
canonical transports of the two relative chain complexes. -/
theorem relCokerMap_set_eq {X : TopCat} {A A' B B' : Set X} (hA : A = A') (hB : B = B')
    (h : A ⊆ B) (h' : A' ⊆ B') :
    CategoryTheory.eqToHom (congrArg (fun S => Work.Cohomology.relChains X S) hA)
        ≫ Work.Cohomology.relCokerMap X A' B' h'
      = Work.Cohomology.relCokerMap X A B h
        ≫ CategoryTheory.eqToHom (congrArg (fun S => Work.Cohomology.relChains X S) hB) := by
  subst hA
  subst hB
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- The enlargement map between a set and itself is the identity. -/
theorem relCokerMap_self {X : TopCat} (A : Set X) (h : A ⊆ A) :
    Work.Cohomology.relCokerMap X A A h = 𝟙 (Work.Cohomology.relChains X A) := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [Work.Cohomology.relCokerMap_comp_π X A A h]
  exact (Category.comp_id _).symm

/-- **The enlargement map between two *equal* sets is an isomorphism.** -/
theorem isIso_relCokerMap_of_eq_sets {X : TopCat} {A B : Set X} (h : A = B) (hAB : A ⊆ B) :
    CategoryTheory.IsIso (Work.Cohomology.relCokerMap X A B hAB) := by
  subst h
  rw [relCokerMap_self A hAB]
  exact CategoryTheory.IsIso.id _

/-- The same, on homology. -/
theorem isIso_homologyMap_relCokerMap_of_eq_sets {X : TopCat} {A B : Set X} (h : A = B)
    (hAB : A ⊆ B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A B hAB) n) := by
  subst h
  rw [relCokerMap_self A hAB, HomologicalComplex.homologyMap_id (Work.Cohomology.relChains X A) n]
  exact CategoryTheory.IsIso.id _

/-! ## The identification of the singleton image with the point -/

/-- The canonical identification of the relative chain complexes of the complement of a point with
those of the complement of the (equal) singleton image `tubeImage {x}`. -/
noncomputable def identMap {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    Work.Cohomology.relChains (TopCat.of (Euc (8 + k))) ({(tubePt C x hx : Euc (8 + k))}ᶜ)
      ⟶ Work.Cohomology.relChains (TopCat.of (Euc (8 + k)))
          ((tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)))ᶜ) :=
  Work.Cohomology.relCokerMap (TopCat.of (Euc (8 + k))) ({(tubePt C x hx : Euc (8 + k))}ᶜ)
    ((tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)))ᶜ)
    (fun y hy hmem => hy ((tubeImage_singleton C x hx) ▸ hmem))

theorem identMap_iso {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (identMap C x hx) (8 + k)) := by
  have hEq : ({(tubePt C x hx : Euc (8 + k))}ᶜ)
      = ((tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)))ᶜ) :=
    congrArg (fun S : Set (Euc (8 + k)) => Sᶜ) (tubeImage_singleton C x hx).symm
  exact isIso_homologyMap_relCokerMap_of_eq_sets hEq _ (8 + k)

/-- The image of a generator under a surjective `ℤ`-linear map generates. -/
theorem span_of_surjective_eq_top {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A →ₗ[ℤ] B) (hf : Function.Surjective f) {v : A}
    (hv : Submodule.span ℤ ({v} : Set A) = ⊤) : Submodule.span ℤ ({f v} : Set B) = ⊤ := by
  calc Submodule.span ℤ ({f v} : Set B)
      = Submodule.map f (Submodule.span ℤ ({v} : Set A)) := by
        rw [Submodule.map_span, Set.image_singleton]
    _ = Submodule.map f ⊤ := by rw [hv]
    _ = ⊤ := by rw [Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- **The ambient local class at the tube point**, read in the group
`H(ℝ^N, ℝ^N ∖ tubeImage {x})` (the target of the excision map `excisionMap {x}`). -/
noncomputable def tubePtClass {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (γ₀ : ∀ y : Euc (8 + k), Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    (Work.Cohomology.relChains (TopCat.of (Euc (8 + k)))
      ((tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)))ᶜ)).homology (8 + k) :=
  (HomologicalComplex.homologyMap (identMap C x hx) (8 + k)).hom (γ₀ (tubePt C x hx))

/-- `tubePtClass` is a generator whenever the ambient class `γ₀` is one. -/
theorem span_tubePtClass {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (γ₀ : ∀ y : Euc (8 + k), Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)
    (hgen : ∀ y, Submodule.span ℤ
      ({γ₀ y} : Set (Work.Orient.LocH (TopCat.of (Euc (8 + k))) (8 + k) y)) = ⊤)
    (x : NormalDiscSub E ε) (hx : normalNorm E (x : NormalTotal E) < ε) :
    Submodule.span ℤ ({tubePtClass C γ₀ x hx} : Set
      ((Work.Cohomology.relChains (TopCat.of (Euc (8 + k)))
        ((tubeImage (E := E) ({x} : Set (NormalDiscSub E ε)))ᶜ)).homology (8 + k))) = ⊤ := by
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (identMap C x hx) (8 + k)) :=
    identMap_iso C x hx
  have hbij : Function.Bijective
      (HomologicalComplex.homologyMap (identMap C x hx) (8 + k)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  rw [tubePtClass]
  exact span_of_surjective_eq_top _ hbij.2 (hgen (tubePt C x hx))

/-! ## Transport lemmas for the degree bookkeeping -/

/-- Transport of the span statement along an equality of degrees. -/
theorem span_relH_cast {M : TopCat} {S : Set M} {N N' : ℕ} (h : N = N')
    (v : (Work.Cohomology.relChains M S).homology N) :
    Submodule.span ℤ ({(h ▸ v)} : Set ((Work.Cohomology.relChains M S).homology N')) = ⊤
      ↔ Submodule.span ℤ ({v} : Set ((Work.Cohomology.relChains M S).homology N)) = ⊤ := by
  cases h
  rfl

/-- Transport of a restriction equation along an equality of degrees. -/
theorem resRelH_cast {M : TopCat} {A B : Set M} (hAB : A ⊆ B) {N N' : ℕ} (h : N = N')
    (v : Work.Orient.RelH M N B) :
    Work.Orient.resRelH M N' hAB (h ▸ v) = h ▸ (Work.Orient.resRelH M N hAB v) := by
  cases h
  rfl

/-- Cancellation of a type transport in an equation between transported elements. -/
theorem cast_inj' {N N' : ℕ} (h : N = N') {F : ℕ → Type*} {u v : F N} :
    ((h ▸ u : F N') = (h ▸ v : F N')) ↔ (u = v) := by
  cases h
  rfl

/-- An injective `ℤ`-linear map reflects "the span of `v` is everything". -/
theorem span_of_map_eq_top {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A →ₗ[ℤ] B) (hf : Function.Injective f) {v : A}
    (hv : Submodule.span ℤ ({f v} : Set B) = ⊤) : Submodule.span ℤ ({v} : Set A) = ⊤ := by
  have hmap : Submodule.map f (Submodule.span ℤ ({v} : Set A)) = ⊤ := by
    rw [Submodule.map_span, Set.image_singleton, hv]
  have hcom : Submodule.comap f (Submodule.map f (Submodule.span ℤ ({v} : Set A)))
      = Submodule.span ℤ ({v} : Set A) :=
    Submodule.comap_map_eq_of_injective hf _
  rw [hmap, Submodule.comap_top] at hcom
  exact hcom.symm

end

end Work.Tubular
