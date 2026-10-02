import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Serre.boundedFiveLemmaLES
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.cylRestrictHomeo
import Submission.Work.Serre.DiscPair.thomRVDefs
import Submission.Work.Serre.DiscPair.cupMapTransferRange
import Submission.Work.Serre.DiscPair.subsingleton_relCoh_cylBot_pair
import Submission.Work.Serre.relCohTripleIsoOfVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.Serre.DiscPair.thomCylAt_of_relVanishing`

The transport step of the CW-model Thom case: for `S ⊆ V ⊆ B` with `S` closed and `V` open, if the
pairs `(V,S)` and `(cylPre q V, cylBot q ∪ cylPre q S)` have vanishing rational relative cohomology
in degrees `≤ N+2`, and the Thom cup property holds over `S`, then it holds over `V`, in the range
`m + r + 1 ≤ N + 1`.

The proof works in the *subspace world* `↥(cylPre q V)` (see
`Submission/Work/Serre/DiscPair/thomRVDefs.lean`):

* `thomSubAt_iff_thomCylAt` transfers the hypothesis over `S` (and the conclusion over `V`) between
  the mapping-cylinder world and the subspace world, along the homeomorphisms
  `cylPreimageHomeo` (for closed `S`) and `cylPreimageHomeoOpen` (for open `V`);
* `bijective_relCohMap_cylPreSubRV` shows that the honest restriction of relative cohomology from
  the part over `V` to the part over `S` is *bijective in degrees `≤ N+1`*, which is the input of
  the range-limited transfer `cupMap_transfer_bwdR_range` of the cup-map property.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## Auxiliary lemmas -/

/-- The pullback along a homeomorphism is an isomorphism on cohomology. -/
theorem isIso_CohMap_homeo_of_homeomorph {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (R : Type) [CommRing R] (n : ℕ) :
    IsIso (Work.Thom.CohMap (e : C(Y, Z)) R n) := by
  refine IsIso.mk ⟨Work.Thom.CohMap (e.symm : C(Z, Y)) R n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp (e.symm : C(Z, Y)) (e : C(Y, Z)) R n]
    rw [show (e : C(Y, Z)).comp (e.symm : C(Z, Y)) = ContinuousMap.id Z from
      ContinuousMap.ext (fun z => e.apply_symm_apply z)]
    exact Work.Thom.CohMap_id R n
  · rw [← Work.Thom.CohMap_comp (e : C(Y, Z)) (e.symm : C(Z, Y)) R n]
    rw [show (e.symm : C(Z, Y)).comp (e : C(Y, Z)) = ContinuousMap.id Y from
      ContinuousMap.ext (fun y => e.symm_apply_apply y)]
    exact Work.Thom.CohMap_id R n

/-- The subtype inclusion `↥S → ↥V` for `S ⊆ V`. -/
def inclSV' (S V : Set B) (hSV : S ⊆ V) : C(↥S, ↥V) where
  toFun s := ⟨(s : B), hSV s.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem inclSV'_coe (S V : Set B) (hSV : S ⊆ V) (s : ↥S) :
    ((inclSV' S V hSV s : ↥V) : B) = (s : B) := rfl

/-- **The restriction `H^n(V) → H^n(S)` for `S ⊆ V` is an isomorphism** as soon as
`H^n(V,S) = H^{n+1}(V,S) = 0` (the transport of
`Work.Serre.DiscPair.isIso_restrCoh_of_relCoh_isZero` to the subtype `↥S = ↥{x : ↥V | ↑x ∈ S}`). -/
theorem isIso_CohMap_inclSV' (S V : Set B) (hSV : S ⊆ V) (n : ℕ)
    (h₁ : IsZero (Work.Thom.RelCoh ℚ n ↥V {x : ↥V | ((x : ↥V) : B) ∈ S}))
    (h₂ : IsZero (Work.Thom.RelCoh ℚ (n + 1) ↥V {x : ↥V | ((x : ↥V) : B) ∈ S})) :
    IsIso (Work.Thom.CohMap (inclSV' S V hSV) ℚ n) := by
  set A : Set ↥V := {x : ↥V | ((x : ↥V) : B) ∈ S} with hA
  have h1 : IsIso (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, ↥V)) ℚ n) :=
    isIso_restrCoh_of_relCoh_isZero A n h₁ h₂
  let eA : ↥S ≃ₜ ↥A :=
    { toFun := fun s => ⟨⟨(s : B), hSV s.2⟩, s.2⟩
      invFun := fun a => ⟨(a : ↥V).1, a.2⟩
      left_inv := fun s => Subtype.ext rfl
      right_inv := fun a => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hcomp : (inclSV' S V hSV : C(↥S, ↥V))
      = (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, ↥V)).comp (eA : C(↥S, ↥A)) := by
    ext s
    rfl
  rw [hcomp, Work.Thom.CohMap_comp]
  haveI := h1
  haveI := isIso_CohMap_homeo_of_homeomorph eA ℚ n
  infer_instance

/-- **The mapping cylinder of `q|_V` is the part of the mapping cylinder of `q` over an open `V`.**
The open companion of `Work.Serre.DiscPair.cylPreimageHomeo` (which is stated for *closed* `S`): the
map `cylPreimageLift q V` is a bijective quotient map because the restriction of the quotient map
`cylMk q` to the saturated *open* set `cylPreSet q V` is a quotient map
(`Topology.IsQuotientMap.restrictPreimage_isOpen`), so `isQuotientMap_cylPreimageLift` applies. -/
theorem cylPreimageHomeoOpenRV {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (V : Set B) (hV : IsOpen V) :
    ∃ e : Work.Serre.cyl (Work.Serre.restrictFibre q V) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' V),
      (∀ y, y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)) ↔
        e y ∈ cylPreBot q V) ∧
      (∀ y, cylPreRetract q V (e y) =
        Work.Serre.cylRetract (Work.Serre.restrictFibre q V) y) := by
  have hquot : Topology.IsQuotientMap (cylPreSetRestrict q V) :=
    Topology.IsQuotientMap.restrictPreimage_isOpen (f := Work.Serre.cylMk q)
      isQuotientMap_quotient_mk' (hV.preimage (Work.Serre.cylRetract q).continuous)
  have hq : Topology.IsQuotientMap (cylPreimageLift q V) :=
    isQuotientMap_cylPreimageLift q V hquot
  have hinj : Function.Injective (cylPreimageLift q V) := cylPreimageLift_injective q V
  let e : Work.Serre.cyl (Work.Serre.restrictFibre q V) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' V) :=
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hinj⟩).homeomorph (cylPreimageLift q V)
  refine ⟨e, ?_, ?_⟩
  · intro y
    have hy : (e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) = cylPreimageLift q V y := rfl
    show y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)) ↔
      ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q) ∈ Work.Serre.cylBot q
    rw [hy]
    exact (cylPreimageLift_range q V y).symm
  · intro y
    refine Subtype.ext ?_
    show Work.Serre.cylRetract q ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
      = ((Work.Serre.cylRetract (Work.Serre.restrictFibre q V) y : ↥V) : B)
    rw [show ((e y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
        = (cylPreimageLift q V y : Work.Serre.cyl q) from rfl]
    exact cylRetract_cylPreimageLift_qS q V y

/-- **The inclusion of the part of the mapping cylinder over `S` into the part over `V`**,
realised as the composite of the reindexing homeomorphism `cylPreSubHomeo` with the subtype
inclusion. -/
abbrev cylPreIncl' (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) :
    C(↥(Work.Serre.cylPre q S), ↥(Work.Serre.cylPre q V)) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V))).comp
    ((cylPreSubHomeo q V S hSV : ↥(Work.Serre.cylPre q S) ≃ₜ ↥(cylPreSub q V S)) :
      C(↥(Work.Serre.cylPre q S), ↥(cylPreSub q V S)))

/-- The homology of the inclusion of the triple `S ⊆ T ⊆ X` (which enlarges the relative set) is
the pullback `relCohMap` along the identity.  (A local copy of
`Work.Serre.homologyMap_tripleIncl_eq`, to avoid the import island of `CellImageEqUpper`.) -/
lemma homologyMap_tripleIncl_eqRV (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ X S T hST) n
      = Work.Thom.relCohMap (ContinuousMap.id (↥X)) S T hST ℚ n := by
  have hchain : Work.Serre.tripleIncl ℚ X S T hST
      = Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) ℚ S T (𝟙 X)
          (fun x hx => hST hx) := by
    apply HomologicalComplex.hom_ext
    intro m
    show ModuleCat.ofHom (Work.Serre.tripleInclLM ℚ X S T hST m)
        = ModuleCat.ofHom (Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) S T (𝟙 X)
            (fun x hx => hST hx) m)
    congr 1
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [Work.Serre.tripleInclLM_coe, Work.Cohomology.relMapLM_coe]
    show (x : (Work.Cohomology.singularCochainComplex ℚ X).X m)
      = ((Work.Cohomology.dualChainMap ℚ X X (𝟙 X)).f m).hom x.1
    rw [Work.Cohomology.dualChainMap_id]
    rfl
  rw [hchain]
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) ℚ S T
      (𝟙 X) (fun x hx => hST hx)) n
    = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) ℚ S T
      (𝟙 X) (fun x hx => hST hx)) n
  rfl

/-- **The map `H^n(Y,A') → H^n(Y,A)` that shrinks the relative set** (for `A ⊆ A'`) is an
isomorphism as soon as the relative cohomology of the pair `(A',A)` vanishes in degrees `≤ n`.

This is the first column of the long exact sequence of the triple `A ⊆ A' ⊆ Y`: exactness at
`H^n(Y,A')` gives injectivity from the vanishing of `H^{n-1}(A',A)`, and exactness at `H^n(Y,A)`
gives surjectivity from the vanishing of `H^n(A',A)`.  The identification of the homology of the
triple inclusion with `relCohMap (ContinuousMap.id Y)` is `homologyMap_tripleIncl_eq`. -/
theorem isIso_relCohMap_id_of_vanishingRV {Y : Type} [TopologicalSpace Y]
    (A A' : Set Y) (h : A ⊆ A') (n : ℕ)
    (hvan : ∀ k ≤ n,
      Subsingleton (Work.Thom.RelCoh ℚ k (TopCat.of ↥A') {x : ↥A' | (x : Y) ∈ A})) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id Y) A A' h ℚ n) := by
  have hmain : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.tripleIncl ℚ (TopCat.of Y) A A' h) n) := by
    have hex := Work.Serre.tripleShortCoh_shortExact ℚ (TopCat.of Y) A A' h
    have hepi : Epi (HomologicalComplex.homologyMap
        (Work.Serre.tripleIncl ℚ (TopCat.of Y) A A' h) n) := by
      have he := hex.homology_exact₂ n
      haveI : Subsingleton ↑((Work.Serre.tripleShortCoh ℚ (TopCat.of Y) A A' h).X₃.homology n) :=
        hvan n le_rfl
      have hzero : HomologicalComplex.homologyMap
          (Work.Serre.tripleShortCoh ℚ (TopCat.of Y) A A' h).g n = 0 :=
        IsZero.eq_zero_of_tgt (ModuleCat.isZero_of_subsingleton _) _
      exact (ShortComplex.exact_iff_epi _ hzero).mp he
    have hmono : Mono (HomologicalComplex.homologyMap
        (Work.Serre.tripleIncl ℚ (TopCat.of Y) A A' h) n) := by
      rcases n with _ | m
      · haveI : Mono (Work.Serre.tripleIncl ℚ (TopCat.of Y) A A' h) := hex.mono_f
        exact Work.Serre.mono_homologyMap_zero_of_mono _ inferInstance
      · have hrel : (ComplexShape.up ℕ).Rel m (m + 1) := by simp [ComplexShape.up]
        have he := hex.homology_exact₁ m (m + 1) hrel
        haveI : Subsingleton ↑((Work.Serre.tripleShortCoh ℚ (TopCat.of Y) A A' h).X₃.homology m) :=
          hvan m (by omega)
        have hzero : hex.δ m (m + 1) hrel = 0 :=
          IsZero.eq_zero_of_src (ModuleCat.isZero_of_subsingleton _) _
        exact (ShortComplex.exact_iff_mono _ hzero).mp he
    haveI := hmono
    haveI := hepi
    exact isIso_of_mono_of_epi _
  rwa [homologyMap_tripleIncl_eqRV (TopCat.of Y) A A' h n] at hmain

/-- **The honest restriction `H^m(cylPre q V, cylBot) → H^m(cylPre q S, cylBot)` is bijective in
degrees `≤ N+1`.**  (The relative sets are `cylPreBot q V` and `cylPreBot q S`.)

Decompose the map as `φ ≫ ψ` with `ψ` the restriction to `↥(cylPreSub q V S)` and
`φ : H^m(W, A_V) → H^m(W, A_S)` the shrinking of the relative set, `A_S = A_V ∩ cylPreSub q V S`:

* `ψ` is `isIso_relCohMap_incl_of_isZero` (with `X = ↥(cylPre q V)`, `A = A_S`,
  `B = cylPreSub q V S`), an isomorphism for `m ≤ N + 1` because `H^m(W, cylPreSub) =
  H^{m+1}(W, cylPreSub) = 0` by `subsingleton_relCoh_cylPre`;
* `φ` is an isomorphism for `m ≤ N + 1` by `relCohTripleIsoOfVanishing` and the vanishing of
  `H^k(A_V, A_S)` for `k ≤ N+1`, which is `subsingleton_relCoh_cylBot_pair`. -/
theorem bijective_relCohMap_cylPreSubRV (q : C(X, B)) (N : ℕ) (S V : Set B) (hSV : S ⊆ V)
    (hvanV : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}))
    (hvanX : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
        {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}))
    (m : ℕ) (hm : m ≤ N + 1) :
    Function.Bijective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
      (cylPreSubBot q V S) (cylPreBot q V)
      (fun x hx => Set.inter_subset_left hx) ℚ m).hom := by
  classical
  -- the pair `(cylPre q V, cylPre q S)` has vanishing relative cohomology in degrees `≤ N+2`
  have hQ : ∀ j : ℕ, j ≤ N + 2 → IsZero (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
      (cylPreSub q V S)) := fun j hj =>
    ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_relCoh_cylPre q S V hSV N hvanV j hj)
  -- the vanishing of `H^k(A_V, A_S)`
  have hvanAS : ∀ k : ℕ, k ≤ N + 1 → Subsingleton (Work.Thom.RelCoh ℚ k
      ↥(cylPreBot q V) {y : ↥(cylPreBot q V) |
        (y : ↥(Work.Serre.cylPre q V)) ∈ cylPreBot q V ∩ cylPreSub q V S}) := by
    intro k hk
    have hset : {y : ↥(cylPreBot q V) |
          (y : ↥(Work.Serre.cylPre q V)) ∈ cylPreBot q V ∩ cylPreSub q V S}
        = {y : ↥(cylPreBot q V) |
          ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} := by
      ext y
      exact ⟨fun hy => Set.inter_subset_right hy, fun hy => Set.mem_inter y.2 hy⟩
    rw [hset]
    exact subsingleton_relCoh_cylBot_pair q S V hSV N hvanV hvanX k hk
  -- the two isomorphisms
  have hψ : IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
      {x : ↥(cylPreSub q V S) | (x : ↥(Work.Serre.cylPre q V)) ∈
        (cylPreBot q V ∩ cylPreSub q V S)}
      (cylPreBot q V ∩ cylPreSub q V S)
      (fun x hx => hx) ℚ m) :=
    isIso_relCohMap_incl_of_isZero (TopCat.of ↥(Work.Serre.cylPre q V))
      (cylPreBot q V ∩ cylPreSub q V S) (cylPreSub q V S) Set.inter_subset_right m
      (hQ m (by omega)) (hQ (m + 1) (by omega))
  have hφ : IsIso (Work.Thom.relCohMap (ContinuousMap.id ↥(Work.Serre.cylPre q V))
      (cylPreBot q V ∩ cylPreSub q V S) (cylPreBot q V) (fun x hx => Set.inter_subset_left hx)
      ℚ m) :=
    isIso_relCohMap_id_of_vanishingRV (cylPreBot q V ∩ cylPreSub q V S) (cylPreBot q V)
      (fun x hx => Set.inter_subset_left hx) m (fun k hk => hvanAS k (le_trans hk hm))
  have hbijψ := (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hψ
  have hbijφ := (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hφ
  -- the composite is the honest restriction
  have hcomp : Work.Thom.relCohMap
        (ContinuousMap.id ↥(Work.Serre.cylPre q V))
        (cylPreBot q V ∩ cylPreSub q V S) (cylPreBot q V)
        (fun x hx => Set.inter_subset_left hx) ℚ m
      ≫ Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
          {x : ↥(cylPreSub q V S) | (x : ↥(Work.Serre.cylPre q V)) ∈
            (cylPreBot q V ∩ cylPreSub q V S)}
          (cylPreBot q V ∩ cylPreSub q V S) (fun x hx => hx) ℚ m
      = Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
          (cylPreSubBot q V S) (cylPreBot q V) (fun x hx => Set.inter_subset_left hx) ℚ m :=
    Work.Thom.relCohMap_compA
      {x : ↥(cylPreSub q V S) | (x : ↥(Work.Serre.cylPre q V)) ∈
        (cylPreBot q V ∩ cylPreSub q V S)}
      (cylPreBot q V ∩ cylPreSub q V S) (cylPreBot q V)
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
      (ContinuousMap.id ↥(Work.Serre.cylPre q V))
      (fun x hx => hx) (fun x hx => Set.inter_subset_left hx)
      (fun x hx => Set.inter_subset_left hx) ℚ m
  rw [← hcomp]
  change Function.Bijective
    ((⇑(Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
        {x : ↥(cylPreSub q V S) | (x : ↥(Work.Serre.cylPre q V)) ∈
          (cylPreBot q V ∩ cylPreSub q V S)}
        (cylPreBot q V ∩ cylPreSub q V S) (fun x hx => hx) ℚ m).hom)
      ∘ (⇑(Work.Thom.relCohMap (ContinuousMap.id ↥(Work.Serre.cylPre q V))
        (cylPreBot q V ∩ cylPreSub q V S) (cylPreBot q V)
        (fun x hx => Set.inter_subset_left hx) ℚ m).hom))
  exact hbijψ.comp hbijφ

end

/-! ## The base-change step -/

theorem thomCylAt_of_relVanishing {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (r N : ℕ) (S V : Set B) (hSV : S ⊆ V) (hScl : IsClosed S) (hVop : IsOpen V)
    (hvanV : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}))
    (hvanX : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥((Work.Serre.cylRetract q) ⁻¹' V)
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q) ∨
            Work.Serre.cylRetract q (x : Work.Serre.cyl q) ∈ S}))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S)) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q V) := by
  by_cases hrN : r + 1 ≤ N + 1
  swap
  · -- the range `m + r + 1 ≤ N + 1` is empty
    refine ⟨0, fun m hm => ?_⟩
    exfalso
    omega
  -- (1) transport the hypothesis over `S` to the subspace world
  have hbotS : ∀ y : Work.Serre.cyl (Work.Serre.restrictFibre q S),
      y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)) ↔
        (cylPreimageHomeo q S hScl) y ∈ cylPreBot q S := fun y =>
    (cylPreimageHomeo_range q S hScl y).symm
  have hretS : ∀ y : Work.Serre.cyl (Work.Serre.restrictFibre q S),
      cylPreRetract q S ((cylPreimageHomeo q S hScl) y) =
        Work.Serre.cylRetract (Work.Serre.restrictFibre q S) y := by
    intro y
    refine Subtype.ext ?_
    show (Work.Serre.cylRetract q) (((cylPreimageHomeo q S hScl) y :
        ↥(Work.Serre.cylPre q S)) : Work.Serre.cyl q)
      = ((Work.Serre.cylRetract (Work.Serre.restrictFibre q S) y : ↥S) : B)
    rw [show (cylPreimageHomeo q S hScl) y = cylPreimageLift q S y from rfl]
    exact cylRetract_cylPreimageLift_qS q S y
  have hsubS : ThomSubAt r N (cylPreBot q S) (cylPreRetract q S) :=
    (thomSubAt_iff_thomCylAt q S r N (cylPreBot q S) (cylPreRetract q S)
      (cylPreimageHomeo q S hScl) hbotS hretS).mp IH
  obtain ⟨U_S, hU_S⟩ := hsubS
  -- (2) the `S`-side cup map, in the `Bijective` form
  have hUSbij : ∀ k, k + r + 1 ≤ N + 1 → Function.Bijective (fun y : Work.Thom.Coh ℚ k ↥S =>
      (Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))
        ((Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom y) U_S) := by
    intro k hk
    have h := (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))).flip U_S ∘ₗ
        (Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom))).mp (hU_S k hk)
    have hfun : (⇑(ModuleCat.Hom.hom (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))).flip U_S ∘ₗ
          (Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom))))
        = (fun y : Work.Thom.Coh ℚ k ↥S =>
            (Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))
              ((Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom y) U_S) := by
      funext y
      simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.flip_apply]
    rwa [hfun] at h
  -- the restriction `H^*(V) → H^*(S)` is an isomorphism
  have hresbij : ∀ k, k + 1 ≤ N + 2 →
      Function.Bijective (Work.Thom.CohMap (inclSV' S V hSV) ℚ k).hom := by
    intro k hk
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (isIso_CohMap_inclSV' S V hSV k (hvanV k (by omega)) (hvanV (k + 1) (by omega)))
  -- the `S`-side cup property with the base `V`
  have hτ : ∀ k, k + (r + 1) ≤ N + 1 → Function.Bijective (fun x : Work.Thom.Coh ℚ k ↥V =>
      (Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))
        ((Work.Thom.CohMap ((inclSV' S V hSV).comp (cylPreRetract q S)) ℚ k).hom x) U_S) := by
    intro k hk
    have hcm : (Work.Thom.CohMap ((inclSV' S V hSV).comp (cylPreRetract q S)) ℚ k).hom
        = (Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom
          ∘ (Work.Thom.CohMap (inclSV' S V hSV) ℚ k).hom := by
      rw [Work.Thom.CohMap_comp, ModuleCat.hom_comp]
      rfl
    have hfun : (fun x : Work.Thom.Coh ℚ k ↥V =>
          (Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))
            ((Work.Thom.CohMap ((inclSV' S V hSV).comp (cylPreRetract q S)) ℚ k).hom x) U_S)
        = (fun y : Work.Thom.Coh ℚ k ↥S =>
            (Work.Thom.mixedCupC ℚ (cylPreBot q S) k (r + 1))
              ((Work.Thom.CohMap (cylPreRetract q S) ℚ k).hom y) U_S)
          ∘ (Work.Thom.CohMap (inclSV' S V hSV) ℚ k).hom := by
      funext x
      rw [hcm]
      rfl
    rw [hfun]
    exact (hUSbij k (by omega)).comp (hresbij k (by omega))
  -- (3) the honest inclusion of the parts of the mapping cylinder is bijective up to `N+1`
  have hfbij : ∀ m, m ≤ N + 1 → Function.Bijective (Work.Thom.relCohMap (cylPreIncl' q S V hSV)
      (cylPreBot q S) (cylPreBot q V) (fun y hy => hy) ℚ m).hom := by
    intro m hm
    have hmem : ∀ x : ↥(Work.Serre.cylPre q S), x ∈ cylPreBot q S ↔
        (cylPreSubHomeo q V S hSV) x ∈ cylPreSubBot q V S := by
      intro x
      constructor
      · intro hx
        exact ⟨hx, ((cylPreSubHomeo q V S hSV) x).2⟩
      · intro hx
        exact hx.1
    have hbij1 : Function.Bijective (Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V))) (cylPreSubBot q V S)
        (cylPreBot q V) (fun x hx => Set.inter_subset_left hx) ℚ m).hom :=
      bijective_relCohMap_cylPreSubRV q N S V hSV hvanV hvanX m hm
    have hbij2 : Function.Bijective (Work.Thom.relCohMap ((cylPreSubHomeo q V S hSV) :
        C(↥(Work.Serre.cylPre q S), ↥(cylPreSub q V S))) (cylPreBot q S)
        (cylPreSubBot q V S) (fun x hx => (hmem x).mp hx) ℚ m).hom :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
        (Work.Thom.CapGlue.isIso_relComplexMap_homeomorph (cylPreBot q S) (cylPreSubBot q V S)
          (cylPreSubHomeo q V S hSV) (fun x => (hmem x)) ℚ m)
    have hc : Work.Thom.relCohMap (cylPreIncl' q S V hSV) (cylPreBot q S) (cylPreBot q V)
        (fun y hy => hy) ℚ m
        = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V))) (cylPreSubBot q V S)
            (cylPreBot q V) (fun x hx => Set.inter_subset_left hx) ℚ m
          ≫ Work.Thom.relCohMap ((cylPreSubHomeo q V S hSV) :
              C(↥(Work.Serre.cylPre q S), ↥(cylPreSub q V S))) (cylPreBot q S)
              (cylPreSubBot q V S) (fun x hx => (hmem x).mp hx) ℚ m :=
      (Work.Thom.relCohMap_compA (cylPreBot q S) (cylPreSubBot q V S) (cylPreBot q V)
        ((cylPreSubHomeo q V S hSV) : C(↥(Work.Serre.cylPre q S), ↥(cylPreSub q V S)))
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V)))
        (fun x hx => (hmem x).mp hx) (fun x hx => Set.inter_subset_left hx)
        (fun y hy => hy) ℚ m).symm
    have hfun : (Work.Thom.relCohMap (cylPreIncl' q S V hSV) (cylPreBot q S) (cylPreBot q V)
          (fun y hy => hy) ℚ m).hom
        = (Work.Thom.relCohMap ((cylPreSubHomeo q V S hSV) :
              C(↥(Work.Serre.cylPre q S), ↥(cylPreSub q V S))) (cylPreBot q S)
              (cylPreSubBot q V S) (fun x hx => (hmem x).mp hx) ℚ m).hom
          ∘ (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(cylPreSub q V S), ↥(Work.Serre.cylPre q V))) (cylPreSubBot q V S)
              (cylPreBot q V) (fun x hx => Set.inter_subset_left hx) ℚ m).hom := by
      rw [hc, ModuleCat.hom_comp]
      rfl
    rw [hfun]
    exact hbij2.comp hbij1
  -- (4) the range-limited transfer of the cup-map property
  obtain ⟨U_V, -, hU_V⟩ := cupMap_transfer_bwdR_range ℚ (cylPreIncl' q S V hSV) (cylPreBot q V)
    (cylPreBot q S) (fun y hy => hy) (N + 1) hfbij (cylPreRetract q V)
    ((inclSV' S V hSV).comp (cylPreRetract q S)) (by ext y; rfl) (r + 1) U_S (by omega) hτ
  -- (5) the subspace-world conclusion over `V`
  have hsubV : ThomSubAt r N (cylPreBot q V) (cylPreRetract q V) := by
    refine ⟨U_V, fun m hm => ?_⟩
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (cylPreBot q V) m (r + 1))).flip U_V ∘ₗ
        (Work.Thom.CohMap (cylPreRetract q V) ℚ m).hom))).mpr (by
      have hfun : (⇑(ModuleCat.Hom.hom (ModuleCat.ofHom
          (((Work.Thom.mixedCupC ℚ (cylPreBot q V) m (r + 1))).flip U_V ∘ₗ
            (Work.Thom.CohMap (cylPreRetract q V) ℚ m).hom))))
          = (fun x : Work.Thom.Coh ℚ m ↥V =>
              (Work.Thom.mixedCupC ℚ (cylPreBot q V) m (r + 1))
                ((Work.Thom.CohMap (cylPreRetract q V) ℚ m).hom x) U_V) := by
        funext y
        simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.flip_apply]
      rw [hfun]
      exact hU_V m hm)
  -- (6) back to the mapping-cylinder world
  obtain ⟨e, hbot, hret⟩ := cylPreimageHomeoOpenRV q V hVop
  exact (thomSubAt_iff_thomCylAt q V r N (cylPreBot q V) (cylPreRetract q V) e hbot hret).mpr
    hsubV

end Work.Serre.DiscPair
