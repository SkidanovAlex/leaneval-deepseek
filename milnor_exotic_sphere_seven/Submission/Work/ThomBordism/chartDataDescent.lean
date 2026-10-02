import Mathlib
import Submission.Work.ThomBordism.chartDescentEngine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Descent of local classes over a chart cover

`Work.ThomBordism.chartDataDescent`: a family of pairwise compatible local classes over the chart
pieces `Z.baseSet i` of a real bundle `Z` glues to a global class of the Thom pair.
-/

open Work.TangentClasses
open Work.Thom
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {X : Type} [TopologicalSpace X]

theorem chartDataDescent {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (c : (i : ι) → Work.Thom.PieceCoh Z (Z.baseSet i) n)
    (hc : ∀ (i : ι) (k : ℕ), Function.Bijective (Work.Thom.localThomMap Z n (Z.baseSet i) (c i) k))
    (hcompat : ∀ i j : ι,
      (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet i)) (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j))
        (Set.preimage_mono Set.inter_subset_left) n)) (c i)
      = (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet j)) (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j))
        (Set.preimage_mono Set.inter_subset_right) n)) (c j))
    (hlow : ∀ (W : Set B), Subsingleton (Work.Thom.PieceCoh Z W (n - 1))) :
    ∃ τ : Work.Thom.OpenThom Z n,
      ∀ i : ι, (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i) n)) τ = c i := by
  classical
  obtain ⟨loInst, hwf⟩ := exists_wellFoundedLT ι
  letI : LinearOrder ι := loInst
  haveI : WellFoundedLT ι := hwf
  let Q : ι → Set B := cumul Z.baseSet
  have hQopen : ∀ γ, IsOpen (Q γ) := fun γ =>
    isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ γ => Z.isOpen_baseSet β
  have hQmono : Monotone Q := by
    intro a b hab z hz
    obtain ⟨β, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hβ, hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨le_trans hβ hab, hz⟩⟩
  have hbaseQ : ∀ (i γ : ι), i ≤ γ → Z.baseSet i ⊆ Q γ := fun i γ h z hz => by
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact Set.mem_iUnion.mpr ⟨h, hz⟩
  have huniv : (⋃ γ : ι, Q γ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have h1 : z ∈ Q (Z.indexAt z) :=
      Set.mem_iUnion.mpr ⟨Z.indexAt z, Set.mem_iUnion.mpr ⟨le_rfl, Z.mem_baseSet_at z⟩⟩
    exact Set.mem_iUnion.mpr ⟨Z.indexAt z, h1⟩
  have uniqC : ∀ (γ : ι) (x₁ x₂ : PieceCoh Z (Q γ) n),
      (∀ (i : ι) (h : i ≤ γ), (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i))
        (Set.preimage_mono (hbaseQ i γ h)) n)) x₁ = c i) →
      (∀ (i : ι) (h : i ≤ γ), (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i))
        (Set.preimage_mono (hbaseQ i γ h)) n)) x₂ = c i) → x₁ = x₂ := by
    intro γ x₁ x₂ h₁ h₂
    have hzero : x₁ - x₂ = 0 := by
      refine sep_of_cover_sub Z n hn hlow (fun δ : ↥(Set.Iic γ) => Z.baseSet (δ : ι))
        (fun δ => Z.isOpen_baseSet (δ : ι)) (hQopen γ) (fun δ => hbaseQ (δ : ι) γ δ.2)
        ?_ (x₁ - x₂) ?_
      · intro z hz
        obtain ⟨β, hz⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hβ, hz⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨⟨β, hβ⟩, hz⟩
      · intro δ
        rw [map_sub, h₁ (δ : ι) δ.2, h₂ (δ : ι) δ.2, sub_self]
    exact sub_eq_zero.mp hzero
  have existsC : ∀ γ : ι, ∃ x : PieceCoh Z (Q γ) n,
      (∀ (i : ι) (h : i ≤ γ), (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i))
        (Set.preimage_mono (hbaseQ i γ h)) n)) x = c i) := by
    intro γ
    refine WellFoundedLT.induction (motive := fun γ : ι => ∃ x : PieceCoh Z (Q γ) n,
      (∀ (i : ι) (h : i ≤ γ), (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i))
        (Set.preimage_mono (hbaseQ i γ h)) n)) x = c i)) γ ?_
    intro γ ih
    let xv : (δ : ↥(Set.Iio γ)) → PieceCoh Z (Q (δ : ι)) n :=
      fun δ => Classical.choose (ih (δ : ι) δ.2)
    have hxv : ∀ δ : ↥(Set.Iio γ), (∀ (i : ι) (h : i ≤ (δ : ι)),
        (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet i))
          (Set.preimage_mono (hbaseQ i (δ : ι) h)) n)) (xv δ) = c i) :=
      fun δ => Classical.choose_spec (ih (δ : ι) δ.2)
    have hxvcompat : ∀ ⦃δ δ' : ↥(Set.Iio γ)⦄ (h : δ' ≤ δ),
        (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Q (δ' : ι)))
          (Set.preimage_mono (hQmono h)) n)) (xv δ) = xv δ' := by
      intro δ δ' h
      refine uniqC (δ' : ι) _ _ ?_ (hxv δ')
      intro i hi
      rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Set.preimage_mono (hbaseQ i (δ' : ι) hi)) (Set.preimage_mono (hQmono h)) n (xv δ)]
      rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) _
        (Set.preimage_mono (hbaseQ i (δ : ι) (le_trans hi h))) n (xv δ)]
      exact hxv δ i (le_trans hi h)
    have hpiece : ∀ δ : ↥(Set.Iio γ), Subsingleton (pdCohSub (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q (δ : ι))) (n - 1)) := fun δ => hlow _
    have hopen : ∀ δ : ↥(Set.Iio γ), IsOpen (Z.proj ⁻¹' (Q (δ : ι))) :=
      fun δ => (hQopen (δ : ι)).preimage Z.continuous_proj
    have hmono : Monotone (fun δ : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ : ι))) :=
      fun a b hab => Set.preimage_mono (hQmono hab)
    have hunionC : ∀ δ : ↥(Set.Iio γ), (∃ ε : ↥(Set.Iio γ), ε < δ) →
        Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (⋃ ε : ↥(Set.Iio γ), ⋃ (_ : ε < δ), Z.proj ⁻¹' (Q (ε : ι))) (n - 1)) := by
      intro δ _
      rw [iUnion_Iio_collapse (fun ε : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (ε : ι))) δ,
        iUnion_preimage Z (fun ε : ↥(Set.Iio δ) => Q ((ε : ↥(Set.Iio γ)) : ι))]
      exact hlow _
    obtain ⟨xmax, hxmax, -⟩ := coherentExtend (Work.Thom.zeroComplement Z) n hn
      (fun δ : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ : ι))) hopen hmono hpiece hunionC xv hxvcompat
    set W₀ : Set B := (⋃ δ : ↥(Set.Iio γ), Q (δ : ι)) ∩ Z.baseSet γ with hW0def
    have hW0open : IsOpen W₀ :=
      (isOpen_iUnion fun δ : ↥(Set.Iio γ) => hQopen (δ : ι)).inter (Z.isOpen_baseSet γ)
    have hQeq : (⋃ δ : ↥(Set.Iio γ), Q (δ : ι)) ∪ Z.baseSet γ = Q γ := by
      rw [show (⋃ δ : ↥(Set.Iio γ), Q (δ : ι)) = ⋃ δ, ⋃ (_ : δ < γ), Z.baseSet δ from
        (cumulative_iUnion_Iio Z.baseSet γ).trans (iUnion_Iio_eq Z.baseSet γ),
        ← cumulative_eq_union Z.baseSet γ]
      exact (cumul_eq Z.baseSet γ).symm
    have hglue : (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∪ (Z.proj ⁻¹' (Z.baseSet γ)) = Z.proj ⁻¹' (Q γ) := by
      rw [iUnion_preimage Z (fun δ : ↥(Set.Iio γ) => Q (δ : ι)),
        ← Set.preimage_union, hQeq]
    have hWU : ∀ (δ : ↥(Set.Iio γ)), Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ) ⊆ (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)) := by
      intro δ z hz
      obtain ⟨h1, h2⟩ := (Set.mem_inter_iff (Z.proj z) _ _).mp (Set.mem_preimage.mp hz)
      exact ⟨Set.mem_iUnion.mpr ⟨δ, hbaseQ (δ : ι) (δ : ι) le_rfl h1⟩, Set.mem_preimage.mpr h2⟩
    set yw : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) n :=
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_left n)) xmax
      - (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet γ)) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_right n)) (c γ) with hywdef
    have hsubQ : ∀ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)
        ⊆ Z.proj ⁻¹' (Q (δ : ι)) :=
      fun δ => Set.preimage_mono (fun z hz => hbaseQ (δ : ι) (δ : ι) le_rfl hz.1)
    have hsubQ' : ∀ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)) ⊆ (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) :=
      fun δ z hz => Set.mem_iUnion.mpr ⟨δ, hz⟩
    have hsubB : ∀ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)
        ⊆ Z.proj ⁻¹' (Z.baseSet (δ : ι)) :=
      fun δ => Set.preimage_mono (fun z hz => hz.1)
    have hsmall : ∀ δ : ↥(Set.Iio γ),
        (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)) (hWU δ) n)) yw = 0 := by
      intro δ
      have hx1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)) (hWU δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_left n)) xmax)
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            ((hWU δ).trans Set.inter_subset_left) n)) xmax :=
        pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (hWU δ) Set.inter_subset_left n xmax
      have hx2 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            ((hWU δ).trans Set.inter_subset_left) n)) xmax
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubQ δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Q (δ : ι))) (hsubQ' δ) n)) xmax) :=
        pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (hsubQ δ) (hsubQ' δ) _ n xmax
      have hx3 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Q (δ : ι))) (hsubQ' δ) n)) xmax = xv δ :=
        (pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (hsubQ' δ)
          (Set.subset_iUnion (fun δ' : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ' : ι))) δ) n xmax).trans
          (hxmax δ)
      have hx4 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubQ δ) n)) (xv δ)
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubB δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι)))
                (Set.preimage_mono (hbaseQ (δ : ι) (δ : ι) le_rfl)) n)) (xv δ)) :=
        pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (hsubB δ) (Set.preimage_mono (hbaseQ (δ : ι) (δ : ι) le_rfl)) _ n (xv δ)
      have hx5 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Q (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι)))
            (Set.preimage_mono (hbaseQ (δ : ι) (δ : ι) le_rfl)) n)) (xv δ) = c (δ : ι) :=
        hxv δ (δ : ι) le_rfl
      have hx1' : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)) (hWU δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (Z.proj ⁻¹' (Z.baseSet γ)) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_right n)) (c γ))
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet γ)) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            ((hWU δ).trans Set.inter_subset_right) n)) (c γ) :=
        pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (hWU δ) Set.inter_subset_right n (c γ)
      have hx2' : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet γ)) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            ((hWU δ).trans Set.inter_subset_right) n)) (c γ)
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet γ)) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (Set.preimage_mono Set.inter_subset_right) n)) (c γ) :=
        pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          ((hWU δ).trans Set.inter_subset_right) (Set.preimage_mono Set.inter_subset_right) n (c γ)
      have hx3' : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet γ)) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (Set.preimage_mono Set.inter_subset_right) n)) (c γ)
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubB δ) n)) (c (δ : ι)) :=
        (hcompat (δ : ι) γ).symm
      have hX1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)) (hWU δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_left n)) xmax)
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubB δ) n)) (c (δ : ι)) := by
        rw [hx1, hx2, hx3, hx4, hx5]
      have hX2 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ)) (hWU δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                (Z.proj ⁻¹' (Z.baseSet γ)) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_right n)) (c γ))
          = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Z.baseSet (δ : ι))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ Z.baseSet γ))
            (hsubB δ) n)) (c (δ : ι)) := by
        rw [hx1', hx2', hx3']
      rw [hywdef, map_sub, hX1, hX2, sub_self]
    have hW0eq : Z.proj ⁻¹' W₀ = (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)) := by
      rw [hW0def, iUnion_preimage Z (fun δ : ↥(Set.Iio γ) => Q (δ : ι))]
      rfl
    have hinc0 : Z.proj ⁻¹' W₀ ⊆ (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)) := fun z hz => hW0eq ▸ hz
    set yc : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' W₀) n :=
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' W₀) hinc0 n)) yw with hycdef
    have hyc : yc = 0 := by
      refine sep_of_cover Z n hn hlow (fun δ : ↥(Set.Iio γ) => Z.baseSet (δ : ι))
        (fun δ => Z.isOpen_baseSet (δ : ι)) hW0open ?_ yc ?_
      · intro z hz
        obtain ⟨hz1, -⟩ := (Set.mem_inter_iff z _ _).mp hz
        obtain ⟨δ, hz3⟩ := Set.mem_iUnion.mp hz1
        obtain ⟨β, hz4⟩ := Set.mem_iUnion.mp hz3
        obtain ⟨hβδ, hz5⟩ := Set.mem_iUnion.mp hz4
        exact Set.mem_iUnion.mpr ⟨⟨β, lt_of_le_of_lt hβδ δ.2⟩, hz5⟩
      · intro δ
        have hW0' : Z.baseSet (δ : ι) ∩ W₀ = Z.baseSet (δ : ι) ∩ Z.baseSet γ := by
          rw [hW0def]
          ext z
          constructor
          · rintro ⟨h1, -, h3⟩
            exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            have hq : z ∈ Q (δ : ι) := hbaseQ (δ : ι) (δ : ι) le_rfl h1
            have h2 : z ∈ ⋃ δ' : ↥(Set.Iio γ), Q (δ' : ι) := Set.mem_iUnion.mpr ⟨δ, hq⟩
            exact ⟨h1, h2, h3⟩
        have hsub1 : Z.baseSet (δ : ι) ∩ W₀ ⊆ Z.baseSet (δ : ι) ∩ Z.baseSet γ :=
          fun z hz => hW0' ▸ hz
        have hincδ : Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ W₀) ⊆ (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)) :=
          (Set.preimage_mono hsub1).trans (hWU δ)
        have hstep : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)))
            (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ W₀)) hincδ n)) yw = 0 :=
          pdCohMap_target_eq_zero (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (congrArg (Z.proj ⁻¹' ·) hW0'.symm) (hWU δ) hincδ n yw (hsmall δ)
        have h1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ W₀))
            (Set.preimage_mono Set.inter_subset_right) n)) yc
            = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) (Z.proj ⁻¹' (Z.baseSet (δ : ι) ∩ W₀)) hincδ n)) yw := by
          rw [hycdef,
            pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
              (Set.preimage_mono Set.inter_subset_right) hinc0 _ n yw]
        rw [h1]
        exact hstep
    have hsub0 : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        ((Z.proj ⁻¹' W₀) ∩ (Z.proj ⁻¹' W₀)) (n - 1)) :=
      subsingleton_pdCohSub_cast (Set.inter_self _).symm (hlow W₀)
    have hcov0 : (Z.proj ⁻¹' W₀) ∪ (Z.proj ⁻¹' W₀) = (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)) := by
      rw [Set.union_self]
      exact hW0eq
    have hWo : IsOpen (Z.proj ⁻¹' W₀) := hW0open.preimage Z.continuous_proj
    have hinj0 := Work.Thom.pdCohSub_pdCohMap_biprod_injective
      (X := TopCat.of Z.TotalSpace) (A := Work.Thom.zeroComplement Z)
      (W := (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ)))
      (U := Z.proj ⁻¹' W₀) (V := Z.proj ⁻¹' W₀)
      hWo hWo hinc0 hinc0 hcov0 n hsub0
    have hyw : yw = 0 := by
      refine hinj0 ?_
      rw [hycdef] at hyc
      simp only [hyc, map_zero]
    have hseam : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_left n)) xmax
        = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet γ)) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) ∩ (Z.proj ⁻¹' (Z.baseSet γ))) Set.inter_subset_right n)) (c γ) := by
      rw [hywdef] at hyw
      exact sub_eq_zero.mp hyw
    obtain ⟨x₀, hx₀W, hx₀U⟩ := subGlue (X := TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) n
      (W := ⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))
      (U := Z.proj ⁻¹' (Z.baseSet γ))
      (isOpen_iUnion fun δ : ↥(Set.Iio γ) => (hQopen (δ : ι)).preimage Z.continuous_proj)
      ((Z.isOpen_baseSet γ).preimage Z.continuous_proj) xmax (c γ) hseam
    refine ⟨(hglue ▸ x₀ : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' (Q γ)) n), ?_⟩
    intro i hi
    have hXi : Z.proj ⁻¹' (Z.baseSet i) ⊆ ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) ∪ ((Z.proj ⁻¹' (Z.baseSet γ))) := by
      by_cases hiγ : i = γ
      · subst hiγ
        exact fun z hz => Set.mem_union_right _ hz
      · have hlt : i < γ := lt_of_le_of_ne hi hiγ
        exact fun z hz => Set.mem_union_left _
          (Set.mem_iUnion.mpr ⟨⟨i, hlt⟩, hbaseQ i i le_rfl hz⟩)
    have e1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i)) (Set.preimage_mono (hbaseQ i γ hi)) n))
          (hglue ▸ x₀ : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' (Q γ)) n)
        = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) ∪ ((Z.proj ⁻¹' (Z.baseSet γ)))) (Z.proj ⁻¹' (Z.baseSet i)) hXi n)) x₀ := by
      rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Set.preimage_mono (hbaseQ i γ hi)) (hglue ▸ hXi) n
        (hglue ▸ x₀ : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (Q γ)) n)]
      have esc := pdCohMap_dcast_source_cast (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) hglue hXi n (hglue ▸ x₀ : pdCohSub
          (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ)) n)
      rw [esc, dcast_dcast hglue x₀]
    have e2 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) ∪ ((Z.proj ⁻¹' (Z.baseSet γ)))) (Z.proj ⁻¹' (Z.baseSet i)) hXi n)) x₀ = c i := by
      by_cases hiγ : i = γ
      · subst hiγ
        rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) hXi
          Set.subset_union_right n x₀]
        exact hx₀U
      · have hlt : i < γ := lt_of_le_of_ne hi hiγ
        have hVW : Z.proj ⁻¹' (Z.baseSet i) ⊆
            (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι))) :=
          (Set.preimage_mono (hbaseQ i i le_rfl)).trans (Set.subset_iUnion
            (fun δ' : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ' : ι))) ⟨i, hlt⟩)
        have h1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) ∪ ((Z.proj ⁻¹' (Z.baseSet γ)))) (Z.proj ⁻¹' (Z.baseSet i)) hXi n)) x₀
            = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
              (Work.Thom.zeroComplement Z) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) (Z.proj ⁻¹' (Z.baseSet i))
              hVW n)) ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
              (Work.Thom.zeroComplement Z) (((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) ∪ ((Z.proj ⁻¹' (Z.baseSet γ))))
              ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) Set.subset_union_left n)) x₀) :=
          pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (hVU := hVW) (hUW := Set.subset_union_left) (hVW := hXi) n x₀
        rw [h1, hx₀W]
        have h2 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : ι)))) (Z.proj ⁻¹' (Z.baseSet i))
            hVW n)) xmax
            = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
              (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q i)) (Z.proj ⁻¹' (Z.baseSet i))
              (Set.preimage_mono (hbaseQ i i le_rfl)) n)) (xv ⟨i, hlt⟩) := by
          have hstep2 := pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (hVU := Set.preimage_mono (hbaseQ i i le_rfl))
            (hUW := Set.subset_iUnion (fun δ' : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ' : ι))) ⟨i, hlt⟩)
            (hVW := hVW) n xmax
          rw [hstep2]
          congr 1
          exact hxmax ⟨i, hlt⟩
        rw [h2]
        exact hxv ⟨i, hlt⟩ i le_rfl
    exact e1.trans e2
  let xf : (γ : ι) → PieceCoh Z (Q γ) n := fun γ => Classical.choose (existsC γ)
  have hxf : ∀ γ : ι, (∀ (i : ι) (h : i ≤ γ),
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Z.baseSet i))
        (Set.preimage_mono (hbaseQ i γ h)) n)) (xf γ) = c i) :=
    fun γ => Classical.choose_spec (existsC γ)
  have hxfcompat : ∀ ⦃γ γ' : ι⦄ (h : γ' ≤ γ),
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Q γ)) (Z.proj ⁻¹' (Q γ')) (Set.preimage_mono (hQmono h)) n)) (xf γ)
      = xf γ' := by
    intro γ γ' h
    refine uniqC γ' _ _ ?_ (hxf γ')
    intro i hi
    rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Set.preimage_mono (hbaseQ i γ' hi)) (Set.preimage_mono (hQmono h)) n (xf γ)]
    rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) _
      (Set.preimage_mono (hbaseQ i γ (le_trans hi h))) n (xf γ)]
    exact hxf γ i (le_trans hi h)
  obtain ⟨xall, hxall, -⟩ := coherentExtend (Work.Thom.zeroComplement Z) n hn
    (fun γ : ι => Z.proj ⁻¹' (Q γ)) (fun γ => (hQopen γ).preimage Z.continuous_proj)
    (fun a b hab => Set.preimage_mono (hQmono hab)) (fun γ => hlow _)
    (fun γ _ => (iUnion_Iio_collapse (fun δ : ι => Z.proj ⁻¹' (Q δ)) γ).trans
      (iUnion_preimage Z (fun δ : ↥(Set.Iio γ) => Q (δ : ι))) ▸ hlow _)
    xf hxfcompat
  set BigU : Set B := ⋃ γ : ι, Q γ with hBigUdef
  have hBigUopen : IsOpen BigU := isOpen_iUnion fun γ => hQopen γ
  have hBigUuniv : BigU = Set.univ := huniv
  have hbaseBigU : ∀ i : ι, Q i ⊆ BigU := fun i => by
    rw [hBigUdef]
    exact Set.subset_iUnion Q i
  have hbaseSetBigU : ∀ i : ι, Z.baseSet i ⊆ BigU :=
    fun i => (hbaseQ i i le_rfl).trans (hbaseBigU i)
  have hpi2 : (⋃ γ : ι, Z.proj ⁻¹' (Q γ)) = Z.proj ⁻¹' BigU := iUnion_preimage Z Q
  set xu : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' BigU) n := hpi2 ▸ xall with hxudef
  have hxu : ∀ γ : ι, (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' (Q γ))
      (Set.preimage_mono (hbaseBigU γ)) n)) xu = xf γ := by
    intro γ
    rw [hxudef]
    have e : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' (Q γ))
        (Set.preimage_mono (hbaseBigU γ)) n))
          (hpi2 ▸ xall : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) n)
        = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' (Q γ))
          (hpi2 ▸ (Set.subset_iUnion (fun γ' : ι => Z.proj ⁻¹' (Q γ')) γ)) n))
          (hpi2 ▸ xall : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) n) :=
      pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Set.preimage_mono (hbaseBigU γ))
        (hpi2 ▸ (Set.subset_iUnion (fun γ' : ι => Z.proj ⁻¹' (Q γ')) γ)) n
        (hpi2 ▸ xall : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' BigU) n)
    rw [e]
    have esc := pdCohMap_dcast_source_cast (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) hpi2
      (Set.subset_iUnion (fun γ' : ι => Z.proj ⁻¹' (Q γ')) γ) n
      (hpi2 ▸ xall : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' BigU) n)
    rw [esc, dcast_dcast hpi2 xall]
    exact hxall γ
  set w : pdCohBiprod (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU) n :=
    (biprod.lift (𝟙 (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' BigU) n))
      (𝟙 (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' BigU) n))).hom xu with hwdef
  have hG : (Work.Cohomology.honestG (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU) n).hom w = 0 := by
    rw [hwdef]
    show (ModuleCat.Hom.hom (biprod.lift (𝟙 (pdCohSub (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) n))
        (𝟙 (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' BigU) n)) ≫
      biprod.desc (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_left n)
        (-(pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_right n)))) xu = 0
    rw [biprod.lift_desc,
      show (𝟙 (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) n) ≫ pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_left n)
          + (𝟙 (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) n) ≫ (-(pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU)
            (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_right n)))
          = (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_left n)
          - (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU ∩ Z.proj ⁻¹' BigU) Set.inter_subset_right n) from by
        simp only [Category.id_comp, Preadditive.comp_neg]
        abel,
      ModuleCat.hom_sub, LinearMap.sub_apply,
      pdCohMap_proof_irrel (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        Set.inter_subset_left Set.inter_subset_right n, sub_self]
  have hcU : BigU ∪ BigU = Set.univ := by rw [Set.union_self, hBigUuniv]
  obtain ⟨τ, hτ⟩ := Work.Thom.exists_glue Z n hBigUopen hBigUopen hcU w hG
  refine ⟨τ, ?_⟩
  intro i
  have hres : (ModuleCat.Hom.hom (pdCohRes (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' BigU) n)) τ = xu := by
    have h := Work.Cohomology.honestF_fst' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' BigU) n
    rw [← h]
    rw [ModuleCat.comp_apply, hτ, hwdef]
    rw [← ModuleCat.comp_apply, biprod.lift_fst]
    rfl
  have hfinal : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) (Z.proj ⁻¹' (Z.baseSet i))
      (Set.preimage_mono (hbaseSetBigU i)) n)) xu = c i := by
    rw [pdCohMap_step (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (hVU := Set.preimage_mono (hbaseQ i i le_rfl))
      (hUW := Set.preimage_mono (hbaseBigU i))
      (hVW := Set.preimage_mono (hbaseSetBigU i)) n xu]
    rw [hxu i]
    exact (pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Set.preimage_mono (hbaseQ i i le_rfl)) (Set.preimage_mono (hbaseQ i i le_rfl)) n
      (xf i)).trans (hxf i i le_rfl)
  rw [Work.Thom.PieceRes_eq_pdCohMap Z n (hbaseSetBigU i) τ]
  rw [show (ModuleCat.Hom.hom (pdCohRes (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' BigU) n)) τ = xu from hres]
  exact hfinal

end

end Work.ThomBordism
