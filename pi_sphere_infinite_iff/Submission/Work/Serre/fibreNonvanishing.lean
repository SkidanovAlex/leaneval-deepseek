import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Serre.cylMidHomologyOnto
import Submission.Work.Serre.cylMidHomologyInj

/-!
# Fibre non-vanishing: injectivity of the restriction to a fibre pair

Target: `Work.Serre.fibreNonvanishing`.  Write `M = cyl p`, `A = range (cylIncl p)`,
`Mb = (cylRetract p)⁻¹{b}`, `Ab = {x : Mb | (x : M) ∈ A}` and `C = A ∪ Mb`.  The target map
factors as the composite of the restriction `H^{r+1}(M,A) → H^{r+1}(C,A)` (the `tripleRestr` of the
triple `A ⊆ C ⊆ M`) with the map `H^{r+1}(C,A) → H^{r+1}(Mb,Ab)` induced by the inclusion
`Mb ⊆ C`:

* the first map is injective as soon as `H^{r+1}(M,C) = 0`: exactness of the triple sequence
  `A ⊆ C ⊆ M` at the middle term (`Work.Serre.tripleCoh_exact₂_range`) identifies the kernel of
  `H^{r+1}(M,A) → H^{r+1}(C,A)` with the range of `H^{r+1}(M,C) → H^{r+1}(M,A)`;
* the second map is injective once it is an isomorphism, i.e. by excision for the union
  `C = A ∪ Mb`.

Both inputs are delegated; the assembly is `fibreNonvanishing_of_pieces` below, which is
`sorry`-free.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]

/-- The inclusion of `Mb = (cylRetract p)⁻¹{b}` into `C = A ∪ Mb`, where `A = range (cylIncl p)`. -/
def cIncl (p : C(E, B)) (b : B) :
    C(↥((cylRetract p) ⁻¹' {b}),
      ↥((Set.range (cylIncl p) ∪ (cylRetract p) ⁻¹' {b}) : Set (cyl p))) where
  toFun x := ⟨(x : cyl p), Or.inr x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- The inclusion of `C = A ∪ Mb` into `M = cyl p`. -/
def cInclM (p : C(E, B)) (b : B) :
    C(↥((Set.range (cylIncl p) ∪ (cylRetract p) ⁻¹' {b}) : Set (cyl p)), cyl p) where
  toFun x := (x : cyl p)
  continuous_toFun := continuous_subtype_val

/-- The inclusion of `Mb = (cylRetract p)⁻¹{b}` into `M = cyl p`. -/
def mInclM (p : C(E, B)) (b : B) : C(↥((cylRetract p) ⁻¹' {b}), cyl p) where
  toFun x := (x : cyl p)
  continuous_toFun := continuous_subtype_val

/-- The middle set `C = A ∪ Mb` of the triple `A ⊆ C ⊆ M`. -/
abbrev CMid (p : C(E, B)) (b : B) : Set (cyl p) :=
  (Set.range (cylIncl p) ∪ (cylRetract p) ⁻¹' {b} : Set (cyl p))

lemma CMid_subset (p : C(E, B)) (b : B) :
    (Set.range (cylIncl p) : Set (cyl p)) ⊆ CMid p b := Set.subset_union_left

/-- The "base" of the cone `Mb` inside `C`. -/
abbrev CBase (p : C(E, B)) (b : B) : Set ↥(CMid p b) :=
  {x | (x : cyl p) ∈ Set.range (cylIncl p)}

/-- The "base" of the cone `Mb` inside itself, i.e. the fibre of `p` over `b`. -/
abbrev MBase (p : C(E, B)) (b : B) : Set ↥((cylRetract p) ⁻¹' {b}) :=
  {x | (x : cyl p) ∈ Set.range (cylIncl p)}

lemma cInclM_comp_cIncl (p : C(E, B)) (b : B) :
    (cInclM p b).comp (cIncl p b) = mInclM p b := ContinuousMap.ext fun _ => rfl

@[simp] lemma cIncl_apply (p : C(E, B)) (b : B) (x : ↥((cylRetract p) ⁻¹' {b})) :
    ((cIncl p b x : ↥(CMid p b)) : cyl p) = (x : cyl p) := rfl

@[simp] lemma cInclM_apply (p : C(E, B)) (b : B) (x : ↥(CMid p b)) :
    cInclM p b x = (x : cyl p) := rfl

@[simp] lemma mInclM_apply (p : C(E, B)) (b : B) (x : ↥((cylRetract p) ⁻¹' {b})) :
    mInclM p b x = (x : cyl p) := rfl

/-- **The first half of the reduction.**  If `H^{r+1}(M, A ∪ Mb) = 0` then the restriction
`H^{r+1}(M,A) → H^{r+1}(C,A)` (with `C = A ∪ Mb`) is injective: its kernel is the range of
`H^{r+1}(M,C) → H^{r+1}(M,A)` by exactness of the triple `A ⊆ C ⊆ M`. -/
theorem injective_restrict_of_isZero (p : C(E, B)) (b : B) (r : ℕ)
    (hC : IsZero (Work.Thom.RelCoh ℚ (r + 1) (cyl p) (CMid p b))) :
    Function.Injective (Work.Thom.relCohMap (cInclM p b) (CBase p b)
      (Set.range (cylIncl p)) (fun _ hx => hx) ℚ (r + 1)).hom := by
  have h := Work.Serre.tripleCoh_exact₂_range ℚ (TopCat.of (cyl p)) (Set.range (cylIncl p))
    (CMid p b) (CMid_subset p b) (r + 1)
  have hzero : HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ (TopCat.of (cyl p))
      (Set.range (cylIncl p)) (CMid p b) (CMid_subset p b)) (r + 1) = 0 :=
    IsZero.eq_zero_of_src hC _
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Serre.tripleIncl ℚ (TopCat.of (cyl p)) (Set.range (cylIncl p)) (CMid p b)
        (CMid_subset p b)) (r + 1))) = ⊥ := by
    rw [hzero]; simp
  rw [hrange] at h
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Serre.tripleRestr ℚ (TopCat.of (cyl p)) (Set.range (cylIncl p)) (CMid p b)
        (CMid_subset p b)) (r + 1))) = ⊥ := h.symm
  have hid : HomologicalComplex.homologyMap
      (Work.Serre.tripleRestr ℚ (TopCat.of (cyl p)) (Set.range (cylIncl p)) (CMid p b)
        (CMid_subset p b)) (r + 1)
      = Work.Thom.relCohMap (cInclM p b) (CBase p b) (Set.range (cylIncl p))
          (fun _ hx => hx) ℚ (r + 1) := rfl
  rw [hid] at hker
  exact LinearMap.ker_eq_bot.mp hker

/-- The bundled inclusion `⟨Subtype.val, continuous_subtype_val⟩` of `C = CMid p b` into `cyl p`
used in the delegated transports is the map `cInclM p b` of this file. -/
theorem cInclM_eq (p : C(E, B)) (b : B) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(CMid p b), cyl p)) = cInclM p b := by
  ext x; rfl

/-- The bundled inclusion `⟨Subtype.val, continuous_subtype_val⟩` of `Mb = (cylRetract p)⁻¹{b}`
into `cyl p` is the map `mInclM p b` of this file. -/
theorem mInclM_eq (p : C(E, B)) (b : B) :
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥((cylRetract p) ⁻¹' {b}), cyl p)) = mInclM p b := by
  ext x; rfl

/-- **The exactness step**: if the inclusion `C ⊆ M` is an epimorphism on rational homology in
degree `r+1` and a monomorphism in degree `r`, then `H_{r+1}(M,C;ℚ) = 0`.  This is the exactness
chase in the long exact sequence of the pair (`Work.StemsB.isZero_relChainsR_homology_succ_of_epi_mono`),
with the two hypotheses read as surjectivity/injectivity of the map on rational homology induced by
the inclusion `C ⊆ M`. -/
theorem isZero_relChainsR_cylCMid_of_transports (p : C(E, B)) (b : B) (r : ℕ)
    (honto : Function.Surjective (Work.Serre.ratHomologyMap (cInclM p b) (r + 1)).hom)
    (hinj : Function.Injective (Work.Serre.ratHomologyMap (cInclM p b) r).hom) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (cyl p)) (CMid p b)).homology (r + 1)) := by
  have hmap : Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl p)) (CMid p b)
      = Work.Cohomology.chainMap ℚ (TopCat.of ↥(CMid p b)) (TopCat.of (cyl p))
          (TopCat.ofHom (cInclM p b)) := rfl
  refine Work.StemsB.isZero_relChainsR_homology_succ_of_epi_mono ℚ (TopCat.of (cyl p))
    (CMid p b) r ?_ ?_
  · rw [hmap]
    exact (ModuleCat.epi_iff_surjective _).mpr honto
  · rw [hmap]
    exact (ModuleCat.mono_iff_injective _).mpr hinj

/-- The same vanishing in cohomology, by the field universal coefficient theorem. -/
theorem isZero_relCoh_cylCMid_of_transports (p : C(E, B)) (b : B) (r : ℕ)
    (honto : Function.Surjective (Work.Serre.ratHomologyMap (cInclM p b) (r + 1)).hom)
    (hinj : Function.Injective (Work.Serre.ratHomologyMap (cInclM p b) r).hom) :
    IsZero (Work.Thom.RelCoh ℚ (r + 1) (cyl p) (CMid p b)) :=
  Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH (CMid p b) (r + 1)
    (isZero_relChainsR_cylCMid_of_transports p b r honto hinj)

/-- **The reduction.**  The target statement follows from the two pieces: the vanishing
`H^{r+1}(M, A ∪ Mb) = 0` (a Serre-type input) and the injectivity of the excision map
`H^{r+1}(C,A) → H^{r+1}(Mb,Ab)`. -/
theorem fibreNonvanishing_of_pieces (p : C(E, B)) (b : B) (r : ℕ)
    (hC : IsZero (Work.Thom.RelCoh ℚ (r + 1) (cyl p) (CMid p b)))
    (hexc : Function.Injective (Work.Thom.relCohMap (cIncl p b) (MBase p b) (CBase p b)
      (fun _ hx => hx) ℚ (r + 1)).hom) :
    Function.Injective (Work.Thom.relCohMap (mInclM p b) (MBase p b)
      (Set.range (cylIncl p)) (fun _ hx => hx) ℚ (r + 1)).hom := by
  have h1 := injective_restrict_of_isZero p b r hC
  have hcomp := Work.Thom.relCohMap_comp' (MBase p b) (CBase p b) (Set.range (cylIncl p))
    (cIncl p b) (cInclM p b) (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ (r + 1)
  have hcongr := Work.Thom.relCohMap_congr'
    (f := (cInclM p b).comp (cIncl p b)) (f' := mInclM p b)
    (MBase p b) (Set.range (cylIncl p)) (cInclM_comp_cIncl p b)
    (fun _ hx => hx) (fun _ hx => hx) ℚ (r + 1)
  rw [← hcongr, ← hcomp]
  intro a b hab
  exact h1 (hexc hab)

/-- The excision input of the assembly, in the vocabulary of this file: the delivered
`Work.Serre.fibreExcisionIso` says that the restriction `H^{r+1}(C,A) → H^{r+1}(Mb,Ab)` is
injective, with `C = excC p b` and `Mb = excM p b`; these are definitionally the sets `CMid p b`
and `(cylRetract p)⁻¹{b}` used here, and the map is `cIncl p b`. -/
theorem fibreExcisionInjective (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap (cIncl p b) (MBase p b) (CBase p b)
      (fun _ hx => hx) ℚ (r + 1)).hom := by
  have h := Work.Serre.fibreExcisionIso (r := r) (N := N) (hr := hr) (hrN := hrN) (hB := hB)
    (p := p) (hp := hp) (hvan := hvan) (hpc := hpc) (hgen := hgen) (b := b)
  simpa [cIncl, CBase, MBase, Work.Serre.excC, Work.Serre.excM, Work.Serre.excAc, Work.Serre.excMc,
    Work.Serre.cylBot, CMid] using h

/-- **The final assembly.**  The target follows from the two transported homology statements for
the inclusion `C ⊆ M` (delegated as `Work.Serre.cylMidHomologyOnto` and `Work.Serre.cylMidHomologyInj`)
together with the excision injectivity (delegated as `Work.Serre.fibreExcisionIso`). -/
theorem fibreNonvanishing_of_transports (p : C(E, B)) (b : B) (r : ℕ)
    (honto : Function.Surjective (Work.Serre.ratHomologyMap (cInclM p b) (r + 1)).hom)
    (hinj : Function.Injective (Work.Serre.ratHomologyMap (cInclM p b) r).hom)
    (hexc : Function.Injective (Work.Thom.relCohMap (cIncl p b) (MBase p b) (CBase p b)
      (fun _ hx => hx) ℚ (r + 1)).hom) :
    Function.Injective (Work.Thom.relCohMap (mInclM p b) (MBase p b)
      (Set.range (cylIncl p)) (fun _ hx => hx) ℚ (r + 1)).hom :=
  fibreNonvanishing_of_pieces p b r
    (isZero_relCoh_cylCMid_of_transports p b r honto hinj) hexc

/-- **Shape check for the final step**: with the two transported homology statements (stated in
the vocabulary of this file) supplied as hypotheses, the target's conclusion follows.  Once the
delegated `Work.Serre.cylMidHomologyOnto` / `Work.Serre.cylMidHomologyInj` are available (they state
the same facts with the inclusion written as `⟨Subtype.val, continuous_subtype_val⟩`, definitionally
the same map as `cInclM p b`), `Work.Serre.fibreNonvanishing` is the instance with those two lemmas
supplied. -/
theorem fibreNonvanishing_of_cylMid (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B)
    (honto : Function.Surjective (Work.Serre.ratHomologyMap (cInclM p b) (r + 1)).hom)
    (hinj : Function.Injective (Work.Serre.ratHomologyMap (cInclM p b) r).hom) :
    Function.Injective (Work.Thom.relCohMap (mInclM p b) (MBase p b) (Set.range (cylIncl p))
      (fun _ hx => hx) ℚ (r + 1)).hom :=
  fibreNonvanishing_of_transports p b r honto hinj
    (fibreExcisionInjective r N hr hrN hB p hp hvan hpc hgen b)

/-- **The requested statement.**  See the module docstring: it is assembled from
`injective_restrict_of_isZero` (the triple-sequence step) and the two delegated inputs
(the vanishing of `H^{r+1}(cyl p, A ∪ Mb)` and the excision isomorphism for the union
`A ∪ Mb = A ∪ (cylRetract p)⁻¹{b}`).  All the inputs are proved: the two transported homology
statements are `Work.Serre.cylMidHomologyOnto` and `Work.Serre.cylMidHomologyInj` (themselves
reduced to the Serre pair comparison `Work.Serre.ratPairComparisonOneBoundary` and to
`Work.Serre.fibrePairMapSurj`), and the excision input is `Work.Serre.fibreExcisionIso`. -/
theorem fibreNonvanishing (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract p) ⁻¹' {b}), Work.Serre.cyl p))
      {x : ↥((Work.Serre.cylRetract p) ⁻¹' {b}) |
        (x : Work.Serre.cyl p) ∈ Set.range (Work.Serre.cylIncl p)}
      (Set.range (Work.Serre.cylIncl p))
      (fun x hx => hx) ℚ (r + 1)).hom := by
  -- the two transported homology statements for the inclusion `C ⊆ M` (delegated)
  have honto : Function.Surjective (Work.Serre.ratHomologyMap (cInclM p b) (r + 1)).hom := by
    have h := Work.Serre.cylMidHomologyOnto r N hr hrN hB p hp hvan hpc hgen b
    rwa [cInclM_eq] at h
  have hinj : Function.Injective (Work.Serre.ratHomologyMap (cInclM p b) r).hom := by
    have h := Work.Serre.cylMidHomologyInj r N hr hrN hB p hp hvan hpc hgen b
    rwa [cInclM_eq] at h
  -- assemble: the vanishing of `H^{r+1}(M,C;ℚ)`, the triple sequence, and excision
  have h := fibreNonvanishing_of_cylMid r N hr hrN hB p hp hvan hpc hgen b honto hinj
  simpa [mInclM_eq] using h

end

end Work.Serre
