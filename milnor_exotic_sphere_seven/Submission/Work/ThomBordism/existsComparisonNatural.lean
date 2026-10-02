import Mathlib
import Submission.Work.ThomBordism.contractibleZeroComplement
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.Iso
import Submission.Work.Thom.ThomClass
import Submission.Work.Tubular.TotalMapProper
import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.ThomBordism.absExcisionHomeoIso
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.contractible
import Submission.Work.ThomBordism.isCompact_fibreNorm_le

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism

open Work.TangentClasses
open CategoryTheory
open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
variable {B' : Type} [TopologicalSpace B'] [CompactSpace B'] [T2Space B'] {ι' : Type}

/-! ## A norm-like function from a continuous fibrewise norm -/

/-- **A real bundle over a compact Hausdorff base whose fibrewise norm is continuous is
norm-like.**  The fibrewise norm itself is the witness: continuity is the hypothesis, homogeneity
is `Work.Thom.fibreNorm_smul`, vanishing on the zero section is `norm_eq_zero`, and the closed unit
ball is compact by `Work.ThomBordism.isCompact_fibreNorm_le`. -/
def normLikeOfContinuous (Z : RealBundle B F ι) (hZ : Continuous (Work.Thom.fibreNorm Z)) :
    NormLike Z where
  f := Work.Thom.fibreNorm Z
  continuous_f := hZ
  nonneg := fun p => norm_nonneg _
  smul := fun c hc p => by
    refine (Work.Thom.fibreNorm_smul (Z := Z) p.1 c (show F from p.2)).trans ?_
    rw [abs_of_nonneg hc]
  eq_zero := fun p => by
    obtain ⟨x, v⟩ := p
    rw [Work.Thom.fibreNorm]
    exact norm_eq_zero
  isCompact_le_one := Work.ThomBordism.isCompact_fibreNorm_le Z hZ 1

/-! ## The zeroth cohomology of a contractible space -/

/-- **The positive-degree cohomology of a contractible space vanishes.** -/
theorem isZero_singularCohomology_of_contractible {X : Type} [TopologicalSpace X]
    [ContractibleSpace X] {d : ℕ} (hd : 1 ≤ d) :
    CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology ℤ d (TopCat.of X)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact Work.Cohomology.contractible ℤ (TopCat.of X) k

/-- **`H^0(X) → H^0(A)` is surjective for a contractible `A ⊆ X`.**  If `a` is a contracting point,
the constant map `c : X → A` at `a` satisfies `(c ∘ incl) ≃ id_A`, so on `H^0` the pullback of `c`
is a right inverse of the pullback of `incl`. -/
theorem surjective_CohMap_zero_of_contractible {X : Type} [TopologicalSpace X] (A : Set X)
    [ContractibleSpace ↥A] :
    Function.Surjective
      ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) ℤ 0).hom) := by
  obtain ⟨a, ha⟩ :=
    (contractible_iff_id_nullhomotopic ↥A).mp (inferInstance : ContractibleSpace ↥A)
  have hc : (ContinuousMap.const X a).comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X))
      = ContinuousMap.const ↥A a := by
    ext x; rfl
  have hkey : CategoryTheory.CategoryStruct.comp (Work.Thom.CohMap (ContinuousMap.const X a) ℤ 0)
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) ℤ 0)
      = 𝟙 (Work.Thom.Coh ℤ 0 ↥A) := by
    rw [← Work.Thom.CohMap_comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) (ContinuousMap.const X a) ℤ 0, hc,
      Work.Thom.CohMap_homotopic ha.symm ℤ 0, Work.Thom.CohMap_id]
  have hlin : ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) ℤ 0).hom).comp
      ((Work.Thom.CohMap (ContinuousMap.const X a) ℤ 0).hom) = LinearMap.id := by
    have h := congrArg (fun φ : Work.Thom.Coh ℤ 0 ↥A ⟶ Work.Thom.Coh ℤ 0 ↥A => φ.hom) hkey
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  intro y
  refine ⟨(Work.Thom.CohMap (ContinuousMap.const X a) ℤ 0).hom y, ?_⟩
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hlin y

/-- The same statement for the restriction map of the pair long exact sequence. -/
theorem surjective_restr_zero_of_contractible {X : Type} [TopologicalSpace X] (A : Set X)
    [ContractibleSpace ↥A] :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of X) A) 0).hom := by
  have h : HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of X) A) 0
      = Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) ℤ 0 := rfl
  rw [h]
  exact surjective_CohMap_zero_of_contractible A

/-! ## The comparison `H^n(Z⁺) ≅ H^n(Z, Z∖0)` -/

/-- **The membership description of `A = (Z∖0) ∪ {∞}`.** -/
theorem mem_absNZ_iff {Z : RealBundle B F ι} {p : OnePoint Z.TotalSpace} :
    p ∈ absNZ Z ↔ p = OnePoint.infty ∨
      ∃ q : Z.TotalSpace, q ∈ Work.Thom.zeroComplement Z ∧ OnePoint.some q = p := by
  rw [absNZ, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨w, hw, hw'⟩ | h)
    · exact Or.inr ⟨w, hw, hw'⟩
    · exact Or.inl h
  · rintro (h | ⟨w, hw, hw'⟩)
    · exact Or.inr h
    · exact Or.inl ⟨w, hw, hw'⟩

/-- **The inclusion of the total space in its one-point compactification**, as a continuous map. -/
def someZ (Z : RealBundle B F ι) : C(Z.TotalSpace, OnePoint Z.TotalSpace) :=
  (infZIncl Z).comp (someHomeoZ Z)

theorem someZ_apply (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    someZ Z p = OnePoint.some p := by
  show ((Work.ThomBordism.someHomeoZ Z p : ↥(infZ Z)) : OnePoint Z.TotalSpace) = OnePoint.some p
  exact Work.ThomBordism.someHomeoZ_apply Z p

/-- **The comparison map `H^n(Z⁺) → H^n(Z, Z∖0)`**: the pullback along the inclusion of the total
space in its one-point compactification, i.e. the composite of the excision of `{∞}` and the
homeomorphism `Z ≅ {∞}ᶜ`. -/
def psiMor (Z : RealBundle B F ι) (n : ℕ) :
    Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z) ⟶
      Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z) :=
  Work.Thom.relCohMap (someZ Z) (Work.Thom.zeroComplement Z) (absNZ Z)
    (fun p hp => (some_mem_absNZ Z p).mpr hp) ℤ n

/-- The comparison as the composite of the excision of `{∞}` with the homeomorphism
`Z ≅ {∞}ᶜ`. -/
theorem psiMor_eq (Z : RealBundle B F ι) (n : ℕ) :
    psiMor Z n = CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ n)
      (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
        (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n) := by
  rw [psiMor,
    Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z) (excSubZ Z) (absNZ Z)
      (someHomeoZ Z) (infZIncl Z) _ _ (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n]
  exact Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement Z) (absNZ Z) rfl _ _ ℤ n

/-- **The comparison map is bijective**: excision (for the open cover `{∞}ᶜ ∪ A`) composed with
the homeomorphism `Z ≅ {∞}ᶜ`. -/
theorem psiMor_bijective (Z : RealBundle B F ι)
    (hZ : Continuous (Work.Thom.fibreNorm Z)) (n : ℕ) :
    Function.Bijective (psiMor Z n).hom := by
  haveI hiso : CategoryTheory.IsIso
      (Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ n) :=
    Work.Cohomology.capRel_excision_isIso (TopCat.of (OnePoint Z.TotalSpace)) (infZ Z) (absNZ Z)
      OnePoint.isClosed_infty.isOpen_compl
      (isOpen_absNZ (normLikeOfContinuous Z hZ)) (infZ_union_absNZ Z) n (fun x hx => hx)
  have hb1 : Function.Bijective
      (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
        (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n).hom :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.zeroComplement Z) (excSubZ Z)
      (someHomeoZ Z) (some_mem_excSubZ Z) ℤ n
  have hb2 : Function.Bijective
      (Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun y hy => hy) ℤ n).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have hsplit := congrArg (fun φ => φ.hom) (psiMor_eq Z n)
  rw [ModuleCat.hom_comp] at hsplit
  rw [hsplit]
  exact hb1.comp hb2

/-! ## Naturality of the comparison -/

/-- **`J` maps `A ⊆ Z⁺` into `A' ⊆ Z'⁺`** whenever it extends `j` (which preserves the complement
of the zero section) and fixes the point at infinity. -/
theorem absNZ_map {Z : RealBundle B F ι} {Z' : RealBundle B' F ι'}
    (j : C(Z.TotalSpace, Z'.TotalSpace))
    (hjmem : ∀ p ∈ Work.Thom.zeroComplement Z, j p ∈ Work.Thom.zeroComplement Z')
    (J : C(OnePoint Z.TotalSpace, OnePoint Z'.TotalSpace))
    (hJ : ∀ p : Z.TotalSpace, J (OnePoint.some p) = OnePoint.some (j p))
    (hJinf : J OnePoint.infty = OnePoint.infty) :
    ∀ p ∈ absNZ Z, J p ∈ absNZ Z' := by
  intro p hp
  rcases (mem_absNZ_iff.mp hp) with rfl | ⟨w, hw, hwp⟩
  · rw [hJinf]; exact infty_mem_absNZ Z'
  · rw [← hwp, hJ, some_mem_absNZ]; exact hjmem w hw

/-- **Naturality of the comparison map** along a bundle map.  Both composites are the pullback of
`H^n(Z'⁺, A')` along the map `Z → Z'⁺`, `p ↦ some (j p)`; the content is `hJ`, which says that
`J` extends `j` on the total spaces. -/
theorem psiMor_natural {Z : RealBundle B F ι} {Z' : RealBundle B' F ι'}
    (j : C(Z.TotalSpace, Z'.TotalSpace))
    (hjmem : ∀ p ∈ Work.Thom.zeroComplement Z, j p ∈ Work.Thom.zeroComplement Z')
    (J : C(OnePoint Z.TotalSpace, OnePoint Z'.TotalSpace))
    (hJ : ∀ p : Z.TotalSpace, J (OnePoint.some p) = OnePoint.some (j p))
    (hJinf : J OnePoint.infty = OnePoint.infty) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (Work.Thom.relCohMap J (absNZ Z) (absNZ Z')
          (absNZ_map j hjmem J hJ hJinf) ℤ n)
        (psiMor Z n)
      = CategoryTheory.CategoryStruct.comp (psiMor Z' n)
        (Work.Thom.relCohMap j (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z')
          hjmem ℤ n) := by
  have hmap : J.comp (someZ Z) = (someZ Z').comp j := by
    ext p
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, someZ_apply, someZ_apply, hJ]
  rw [psiMor, psiMor,
    Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z) (absNZ Z) (absNZ Z')
      (someZ Z) J _ _
      (fun x hx => by
        rw [someZ_apply Z x, hJ]
        exact (some_mem_absNZ Z' (j x)).mpr (hjmem x hx)) ℤ n,
    Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z')
      (absNZ Z') j (someZ Z') _ _
      (fun x hx => (some_mem_absNZ Z' (j x)).mpr (hjmem x hx)) ℤ n]
  exact Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement Z) (absNZ Z') hmap _ _ ℤ n

/-- **Naturality of the inverse of `relToAbs`.**  If two forgetful maps are bijective and commute
with the pullback along a map `f` on one side and `CohMap f` on the other, then so do their
inverses. -/
theorem relToAbs_symm_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (hφ : Function.Bijective ((Work.Thom.relToAbs ℤ A n).hom))
    (hψ : Function.Bijective ((Work.Thom.relToAbs ℤ B n).hom)) (u : Work.Thom.Coh ℤ n Y) :
    (LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ A n).hom) hφ).symm
        ((Work.Thom.CohMap f ℤ n).hom u)
      = (Work.Thom.relCohMap f A B hf ℤ n).hom
          ((LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ B n).hom) hψ).symm u) := by
  have hnat : ((Work.Thom.relToAbs ℤ A n).hom).comp ((Work.Thom.relCohMap f A B hf ℤ n).hom)
      = ((Work.Thom.CohMap f ℤ n).hom).comp ((Work.Thom.relToAbs ℤ B n).hom) := by
    have h := congrArg (fun (k : Work.Thom.RelCoh ℤ n Y B ⟶ Work.Thom.Coh ℤ n X) =>
        ModuleCat.Hom.hom k) (Work.Thom.relCohMap_relToAbs f A B hf ℤ n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  apply hφ.1
  rw [← LinearEquiv.ofBijective_apply (f := (Work.Thom.relToAbs ℤ A n).hom) (hf := hφ),
    LinearEquiv.apply_symm_apply]
  rw [← LinearMap.comp_apply, hnat, LinearMap.comp_apply,
    ← LinearEquiv.ofBijective_apply (f := (Work.Thom.relToAbs ℤ B n).hom) (hf := hψ),
    LinearEquiv.apply_symm_apply]

/-! ## `relToAbs : H^n(Z⁺, A) → H^n(Z⁺)` is an isomorphism for `n ≥ 1` -/

/-- **Forgetting the relative set of the pair `(Z⁺, A)` is an isomorphism in every positive
degree**, because `A = (Z∖0) ∪ {∞}` is contractible: the long exact sequence of the pair has
`H^n(A) = 0` (`n ≥ 1`) and `H^{n-1}(A) = 0` (`n ≥ 2`), while the degree-one case needs only that
`H^0(Z⁺) → H^0(A)` is surjective, which holds for a contractible `A`. -/
theorem bijective_relToAbs_absNZ (Z : RealBundle B F ι)
    (hZ : Continuous (Work.Thom.fibreNorm Z)) (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective ((Work.Thom.relToAbs ℤ (absNZ Z) n).hom) := by
  classical
  haveI hcA : ContractibleSpace ↥(absNZ Z) := contractibleZeroComplement Z hZ
  let X : TopCat := TopCat.of (OnePoint Z.TotalSpace)
  have hsurj : Function.Surjective ((Work.Thom.relToAbs ℤ (absNZ Z) n).hom) := by
    have hzero : HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X (absNZ Z)) n = 0 :=
      CategoryTheory.Limits.IsZero.eq_of_tgt
        (isZero_singularCohomology_of_contractible (X := ↥(absNZ Z)) hn) _ 0
    have h1 : ((HomologicalComplex.homologyMap
          (Work.Cohomology.relIncl ℤ X (absNZ Z)) n).hom).range
        = ((HomologicalComplex.homologyMap
          (Work.Cohomology.restr ℤ X (absNZ Z)) n).hom).ker :=
      CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
        (Work.Cohomology.pair_exact₂ ℤ X (absNZ Z) n)
    have hz : ((HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℤ X (absNZ Z)) n).hom) = 0 := by
      rw [hzero, ModuleCat.hom_zero]
    have h2 : ((HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℤ X (absNZ Z)) n).hom).range = ⊤ := by
      rw [h1, hz, LinearMap.ker_zero]
    exact LinearMap.range_eq_top.mp h2
  have hinj : Function.Injective ((Work.Thom.relToAbs ℤ (absNZ Z) n).hom) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have key : ((Work.Cohomology.pairδ ℤ X (absNZ Z) k).hom).range
        = ((HomologicalComplex.homologyMap
            (Work.Cohomology.relIncl ℤ X (absNZ Z)) (k + 1)).hom).ker :=
      CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
        (Work.Cohomology.pair_exact₁ ℤ X (absNZ Z) k)
    have hz : (Work.Cohomology.pairδ ℤ X (absNZ Z) k).hom = 0 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · subst hk0
        have h3 : ((Work.Cohomology.pairδ ℤ X (absNZ Z) 0).hom).ker = ⊤ := by
          have h4 : ((HomologicalComplex.homologyMap
              (Work.Cohomology.restr ℤ X (absNZ Z)) 0).hom).range
              = ((Work.Cohomology.pairδ ℤ X (absNZ Z) 0).hom).ker :=
            CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
              (Work.Cohomology.pair_exact₃ ℤ X (absNZ Z) 0)
          rw [← h4]
          exact LinearMap.range_eq_top.mpr
            (surjective_restr_zero_of_contractible (absNZ Z))
        exact LinearMap.ker_eq_top.mp h3
      · have hsrc := CategoryTheory.Limits.IsZero.eq_of_src
          (isZero_singularCohomology_of_contractible (X := ↥(absNZ Z)) hk)
          (Work.Cohomology.pairδ ℤ X (absNZ Z) k) 0
        rw [hsrc, ModuleCat.hom_zero]
    have h2 : ((HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℤ X (absNZ Z)) (k + 1)).hom).ker = ⊥ := by
      rw [← key, hz, LinearMap.range_zero]
    exact LinearMap.ker_eq_bot.mp h2
  exact ⟨hinj, hsurj⟩

end

theorem existsComparisonNatural :
    ∃ (Theta : ∀ {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
        {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
        (Z : Work.TangentClasses.RealBundle B F ι), Continuous (Work.Thom.fibreNorm Z) → (n : ℕ) →
        1 ≤ n →
        Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace) ≃ₗ[ℤ]
          Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z)),
      ∀ {B B' : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
        [TopologicalSpace B'] [CompactSpace B'] [T2Space B']
        {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        {ι ι' : Type} (Z : Work.TangentClasses.RealBundle B F ι)
        (Z' : Work.TangentClasses.RealBundle B' F ι')
        (hZ : Continuous (Work.Thom.fibreNorm Z)) (hZ' : Continuous (Work.Thom.fibreNorm Z'))
        (f : C(B, B')) (e : Work.Thom.BundleIso (Work.Thom.bundleComap Z' f) Z)
        (j : C(Z.TotalSpace, Z'.TotalSpace))
        (hj : j = fun p => Work.Thom.totalMap Z' f (e.invTotalSpace p))
        (hjmem : ∀ p ∈ Work.Thom.zeroComplement Z, j p ∈ Work.Thom.zeroComplement Z')
        (J : C(OnePoint Z.TotalSpace, OnePoint Z'.TotalSpace))
        (hJ : ∀ p : Z.TotalSpace, J (OnePoint.some p) = OnePoint.some (j p))
        (hJinf : J OnePoint.infty = OnePoint.infty)
        (n : ℕ) (hn : 1 ≤ n) (u : Work.Thom.Coh ℤ n (OnePoint Z'.TotalSpace)),
        (Theta Z hZ n hn) ((Work.Thom.CohMap J ℤ n).hom u)
          = (Work.Thom.relCohMap j (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z')
              hjmem ℤ n).hom ((Theta Z' hZ' n hn) u) := by
  refine ⟨?_, ?_⟩
  · intro B _ _ _ F _ _ _ ι Z hZ n hn
    exact (LinearEquiv.ofBijective ((Work.Thom.relToAbs ℤ (absNZ Z) n).hom)
        (bijective_relToAbs_absNZ Z hZ n hn)).symm.trans
      (LinearEquiv.ofBijective ((psiMor Z n).hom) (psiMor_bijective Z hZ n))
  · intro B _ _ _ B' _ _ _ F _ _ _ ι ι' Z Z' hZ hZ' f e j hj hjmem J hJ hJinf n hn u
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    rw [relToAbs_symm_natural (absNZ Z) (absNZ Z') J (absNZ_map j hjmem J hJ hJinf) n
      (bijective_relToAbs_absNZ Z hZ n hn) (bijective_relToAbs_absNZ Z' hZ' n hn) u]
    rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
    have hnat := congrArg (fun (k : Work.Thom.RelCoh ℤ n (OnePoint Z'.TotalSpace) (absNZ Z') ⟶
        Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z)) => ModuleCat.Hom.hom k)
      (psiMor_natural (Z := Z) (Z' := Z') j hjmem J hJ hJinf n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnat
    rw [← LinearMap.comp_apply, hnat, LinearMap.comp_apply]

end Work.ThomBordism
