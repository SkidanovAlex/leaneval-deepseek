import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.homologyMV
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.chartConvexPair_relHomology_iso
import Submission.Work.Cohomology.isZero_relChains_kcompact_high
import Submission.Work.Cohomology.chart_relCohomology_vanishing_of_compact
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.mv_subsingleton_homology_inter
import Submission.Work.Cohomology.cokerSmallLemmas
import Submission.Work.Cohomology.Endgame.shiftCap
import Submission.Work.Cohomology.CompactSupport
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.Crux33.WitnessEZ
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem exists_piece_cover_disjoint {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M)
    (Q : Set (EuclideanSpace ℝ (Fin N))) (hQ : IsOpen Q)
    (hQt : Q ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).target)
    (C S : Set M)
    (hCW : C ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹' Q ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source)
    (hSW : S ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹' Q ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source)
    (hCc : IsCompact C) (hSc : IsCompact S) (hCS : Disjoint C S) :
    ∃ (t : Finset M) (r : ℝ), 0 < r ∧ (∀ x ∈ t, x ∈ C) ∧
      C ⊆ ⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹'
            Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin N)) cc) x) r
          ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source) ∧
      Disjoint S (⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹'
            Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin N)) cc) x) r
          ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source)) ∧
      (∀ x ∈ t, Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin N)) cc) x) r ⊆ Q) := by
  classical
  set e := chartAt (EuclideanSpace ℝ (Fin N)) cc with he
  have hCs : C ⊆ e.source := fun x hx => (hCW hx).2
  have hSs : S ⊆ e.source := fun x hx => (hSW hx).2
  have hC'c : IsCompact (e '' C) :=
    hCc.image_of_continuousOn (e.continuousOn.mono hCs)
  have hS'c : IsCompact (e '' S) :=
    hSc.image_of_continuousOn (e.continuousOn.mono hSs)
  have hdisj : Disjoint (e '' C) (e '' S) := by
    rw [Set.disjoint_left]
    intro y hyC hyS
    obtain ⟨x, hx, rfl⟩ := hyC
    obtain ⟨x', hx', hx'x⟩ := hyS
    have hxx : x' = x := e.toPartialEquiv.injOn (hSs hx') (hCs hx) hx'x
    exact (Set.disjoint_left.mp hCS hx) (hxx ▸ hx')
  have hC'J : e '' C ⊆ Q \ e '' S := by
    intro y hy
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact (hCW hx).1
    · intro hyS
      exact (Set.disjoint_left.mp hdisj hy) hyS
  obtain ⟨r, u, hr, hcov, huJ⟩ := exists_finite_closedBall_cover N (hQ.sdiff hS'c.isClosed) hC'c hC'J
  refine ⟨u.image (fun y : ↥(e '' C) => e.symm (y : EuclideanSpace ℝ (Fin N))), r, hr, ?_, ?_, ?_, ?_⟩
  · -- the centres lie in `C`
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨x₀, hx₀C, hx₀⟩ := y.2
    have : e.symm ((y : EuclideanSpace ℝ (Fin N))) = x₀ := by
      rw [← hx₀]
      exact e.left_inv (hCs hx₀C)
    rw [this]
    exact hx₀C
  · -- the pieces cover `C`
    intro z hz
    have hz1 : e z ∈ ⋃ y ∈ u, Metric.closedBall ((y : EuclideanSpace ℝ (Fin N))) r :=
      hcov ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp hz1
    refine Set.mem_iUnion₂.mpr ⟨e.symm ((y : EuclideanSpace ℝ (Fin N))),
      Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    refine ⟨?_, hCs hz⟩
    have hy' : e (e.symm ((y : EuclideanSpace ℝ (Fin N)))) = (y : EuclideanSpace ℝ (Fin N)) :=
      e.right_inv (hQt (hC'J y.2).1)
    rwa [hy']
  · -- disjointness
    rw [Set.disjoint_left]
    intro z hzS hzU
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hzU
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : e (e.symm ((y : EuclideanSpace ℝ (Fin N)))) = (y : EuclideanSpace ℝ (Fin N)) :=
      e.right_inv (hQt (hC'J y.2).1)
    have hmem : e z ∈ Metric.closedBall ((y : EuclideanSpace ℝ (Fin N))) r := by
      rw [← hy']
      exact hzx.1
    have hnot : e z ∉ e '' S := (huJ y hy hmem).2
    exact hnot ⟨z, hzS, rfl⟩
  · -- the balls lie in `Q`
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : e (e.symm ((y : EuclideanSpace ℝ (Fin N)))) = (y : EuclideanSpace ℝ (Fin N)) :=
      e.right_inv (hQt (hC'J y.2).1)
    rw [hy']
    exact (huJ y hy).trans (Set.sdiff_subset)

open scoped Simplicial in
theorem exists_compact_support_image {X : TopCat} (A : Set X) (n : ℕ)
    (y : (singularChains ℤ (TopCat.of A)).X n) :
    ∃ S : Set X, S ⊆ A ∧ IsCompact S ∧
      (inclChains X A).f n y ∈ LinearMap.range ((inclChains X S).f n).hom := by
  classical
  set c := Crux33.coords (TopCat.toSSet.obj (TopCat.of A)) n y with hc
  set S : Set X := ⋃ σ ∈ c.support,
    simplexRange X ((TopCat.toSSet.map (inclUX A)).app (Opposite.op ⦋n⦌) σ) with hS
  have hSsub : S ⊆ A := by
    intro w hw
    rw [hS] at hw
    obtain ⟨σ, -, hw⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨z, rfl⟩ := hw
    rw [toSSetObjEquiv_map_apply]
    exact (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op ⦋n⦌) σ z).2
  have hSc : IsCompact S := by
    rw [hS]
    exact Finset.isCompact_biUnion c.support
      (fun σ _ => isCompact_simplexRange X _)
  refine ⟨S, hSsub, hSc, ?_⟩
  have hsum : y = ∑ σ ∈ c.support, (c σ) • gen (TopCat.of A) n σ :=
    Crux33.chain_eq_sum_gen (TopCat.toSSet.obj (TopCat.of A)) n y
  have hmain : (inclChains X A).f n y
      = ∑ σ ∈ c.support, (c σ) • (inclChains X A).f n (gen (TopCat.of A) n σ) := by
    rw [hsum, map_sum]
    exact Finset.sum_congr rfl (fun σ _ => by rw [map_zsmul])
  rw [hmain]
  refine Submodule.sum_mem _ (fun σ hσ => ?_)
  have hgen : (inclChains X A).f n (gen (TopCat.of A) n σ)
      ∈ LinearMap.range ((inclChains X S).f n).hom := by
    have hrange : Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)
          ((TopCat.toSSet.map (inclUX A)).app (Opposite.op ⦋n⦌) σ) z) ⊆ S := by
      intro w hw
      rw [hS]
      exact Set.mem_iUnion₂.mpr ⟨σ, hσ, hw⟩
    obtain ⟨τ, hτ⟩ := exists_map_inclUX_of_range_subset S (Opposite.op ⦋n⦌)
      ((TopCat.toSSet.map (inclUX A)).app (Opposite.op ⦋n⦌) σ) hrange
    refine ⟨gen (TopCat.of S) n τ, ?_⟩
    have h1 : (ModuleCat.Hom.hom ((inclChains X S).f n)) (gen (TopCat.of S) n τ)
        = gen X n ((TopCat.toSSet.map (inclUX S)).app (Opposite.op ⦋n⦌) τ) :=
      chainComplexMap_ι_apply (TopCat.toSSet.map (inclUX S)) n τ 1
    have h2 : (ModuleCat.Hom.hom ((inclChains X A).f n)) (gen (TopCat.of A) n σ)
        = gen X n ((TopCat.toSSet.map (inclUX A)).app (Opposite.op ⦋n⦌) σ) :=
      chainComplexMap_ι_apply (TopCat.toSSet.map (inclUX A)) n σ 1
    rw [h1, h2, hτ]
  exact AddSubgroup.zsmul_mem (LinearMap.range ((inclChains X S).f n).hom).toAddSubgroup hgen (c σ)

theorem relative_cycle_lift {M : TopCat} (W C : Set M) (m : ℕ) (hm : 1 ≤ m)
    (ζ : (relChains (TopCat.of W) (pdRelSub W C)).cycles m) :
    ∃ (x : (singularChains ℤ (TopCat.of W)).X m)
      (y : (singularChains ℤ (TopCat.of (pdRelSub W C))).X (m - 1)),
      (cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m x
          = (relChains (TopCat.of W) (pdRelSub W C)).iCycles m ζ ∧
      (inclChains (TopCat.of W) (pdRelSub W C)).f (m - 1) y
          = (singularChains ℤ (TopCat.of W)).d m (m - 1) x := by
  classical
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective _).mp
    (epi_cokernel_π_f (inclChains (TopCat.of W) (pdRelSub W C)) m)
    ((relChains (TopCat.of W) (pdRelSub W C)).iCycles m ζ)
  have h0 : (cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f (m - 1)
      ((singularChains ℤ (TopCat.of W)).d m (m - 1) x) = 0 := by
    have hcomm : (cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m
        ≫ (relChains (TopCat.of W) (pdRelSub W C)).d m (m - 1)
        = (singularChains ℤ (TopCat.of W)).d m (m - 1)
          ≫ (cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f (m - 1) :=
      HomologicalComplex.Hom.comm _ m (m - 1)
    rw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [← hcomm]
    rw [CategoryTheory.ConcreteCategory.comp_apply]
    rw [hx]
    exact CategoryTheory.ConcreteCategory.congr_hom
      (HomologicalComplex.iCycles_d (relChains (TopCat.of W) (pdRelSub W C)) m (m - 1)) ζ
  obtain ⟨y, hy⟩ := (cokernel_pi_f_eq_zero_iff (inclChains (TopCat.of W) (pdRelSub W C))
    (m - 1) ((singularChains ℤ (TopCat.of W)).d m (m - 1) x)).mp h0
  exact ⟨x, y, hx, hy⟩

theorem homologyMap_enlarge_of_lift {M : TopCat} (W C K : Set M) (hCK : C ⊆ K) (m : ℕ)
    {x : (singularChains ℤ (TopCat.of W)).X m}
    (hx : (singularChains ℤ (TopCat.of W)).d m (m - 1) x
        ∈ LinearMap.range ((inclChains (TopCat.of W) (pdRelSub W K)).f (m - 1)).hom) :
    ∃ (γ : (relChains (TopCat.of W) (pdRelSub W K)).cycles m)
      (γ' : (relChains (TopCat.of W) (pdRelSub W C)).cycles m),
      (relChains (TopCat.of W) (pdRelSub W K)).iCycles m γ
          = ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f m) x ∧
      (relChains (TopCat.of W) (pdRelSub W C)).iCycles m γ'
          = ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m) x ∧
      HomologicalComplex.homologyMap (pdRelChainsEnlarge W hCK) m
          ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ m γ)
        = (relChains (TopCat.of W) (pdRelSub W C)).homologyπ m γ' := by
  classical
  have hA : pdRelSub W K ⊆ pdRelSub W C := pdRelSub_mono hCK
  have hx' : (singularChains ℤ (TopCat.of W)).d m (m - 1) x
      ∈ LinearMap.range ((inclChains (TopCat.of W) (pdRelSub W C)).f (m - 1)).hom :=
    mem_range_inclChains_of_subset hA hx
  -- cycle conditions
  have hcycK : (relChains (TopCat.of W) (pdRelSub W K)).d m (m - 1)
      ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f m x) = 0 := by
    change (cokernel (inclChains (TopCat.of W) (pdRelSub W K))).d m (m - 1)
      ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f m x) = 0
    rw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [(cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).comm m (m - 1)]
    rw [CategoryTheory.ConcreteCategory.comp_apply]
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (m - 1) y
  have hcycC : (relChains (TopCat.of W) (pdRelSub W C)).d m (m - 1)
      ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m x) = 0 := by
    change (cokernel (inclChains (TopCat.of W) (pdRelSub W C))).d m (m - 1)
      ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m x) = 0
    rw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [(cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).comm m (m - 1)]
    rw [CategoryTheory.ConcreteCategory.comp_apply]
    obtain ⟨y, hy⟩ := hx'
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (m - 1) y
  refine ⟨cycleOf m _ hcycK, cycleOf m _ hcycC, iCycles_cycleOf m _ hcycK,
    iCycles_cycleOf m _ hcycC, ?_⟩
  -- the functoriality statement
  have h2 : HomologicalComplex.cyclesMap (pdRelChainsEnlarge W hCK) m (cycleOf m _ hcycK)
      = cycleOf m _ hcycC := by
    have hinj : Function.Injective (ConcreteCategory.hom
        ((relChains (TopCat.of W) (pdRelSub W C)).iCycles m)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hinj
    have hcm := CategoryTheory.ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (pdRelChainsEnlarge W hCK) m) (cycleOf m _ hcycK)
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at hcm
    rw [hcm, iCycles_cycleOf m _ hcycK, iCycles_cycleOf m _ hcycC]
    have hcomp : (cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f m
        ≫ (pdRelChainsEnlarge W hCK).f m
        = (cokernel.π (inclChains (TopCat.of W) (pdRelSub W C))).f m := by
      rw [← HomologicalComplex.comp_f, pdRelChainsEnlarge, relCokerMap_comp_π]
    exact CategoryTheory.ConcreteCategory.congr_hom hcomp x
  have hnat := CategoryTheory.ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (pdRelChainsEnlarge W hCK) m) (cycleOf m _ hcycK)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at hnat
  rw [h2] at hnat
  exact hnat

/-- Vanishing of homology is invariant under a homeomorphism. -/
theorem subsingleton_homology_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ)
    (h : Subsingleton ((singularChains ℤ Y).homology n)) :
    Subsingleton ((singularChains ℤ X).homology n) :=
  ModuleCat.subsingleton_of_isZero (isZero_homology_of_homotopyEquiv
    (Homeomorph.toHomotopyEquiv e) n (ModuleCat.isZero_iff_subsingleton.mpr h))

/-- The canonical homeomorphism `A ≅ {x : A ∪ B | x ∈ A}`. -/
def homeomorphSubsetUnion {α : Type} [TopologicalSpace α] {A B : Set α} :
    TopCat.of ↥A ≃ₜ TopCat.of {x : ↥(A ∪ B) // (x : α) ∈ A} :=
  ((flatHomeo (q := fun x : α => x ∈ A ∪ B) (P := fun x : α => x ∈ A)).trans
    (Homeomorph.setCongr (by
      ext x
      constructor
      · rintro ⟨h1, h2⟩; exact h2
      · intro h2; exact ⟨Or.inl h2, h2⟩))).symm

/-- The canonical homeomorphism `B ≅ {x : A ∪ B | x ∈ B}`. -/
def homeomorphSubsetUnionRight {α : Type} [TopologicalSpace α] {A B : Set α} :
    TopCat.of ↥B ≃ₜ TopCat.of {x : ↥(A ∪ B) // (x : α) ∈ B} :=
  ((flatHomeo (q := fun x : α => x ∈ A ∪ B) (P := fun x : α => x ∈ B)).trans
    (Homeomorph.setCongr (by
      ext x
      constructor
      · rintro ⟨h1, h2⟩; exact h2
      · intro h2; exact ⟨Or.inr h2, h2⟩))).symm

/-- The canonical homeomorphism `A ∩ B ≅ {x : A ∪ B | x ∈ A ∧ x ∈ B}`. -/
def homeomorphSubsetInter {α : Type} [TopologicalSpace α] {A B : Set α} :
    TopCat.of ↥(A ∩ B) ≃ₜ TopCat.of {x : ↥(A ∪ B) // (x : α) ∈ A ∧ (x : α) ∈ B} :=
  ((flatHomeo (q := fun x : α => x ∈ A ∪ B) (P := fun x : α => x ∈ A ∧ x ∈ B)).trans
    (Homeomorph.setCongr (by
      ext x
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨Or.inl h2, h2, h3⟩))).symm

/-- Vanishing of homology is invariant under equality of the underlying sets. -/
theorem subsingleton_homology_of_set_eq {α : Type} [TopologicalSpace α] {S T : Set α} (h : S = T)
    (n : ℕ) (hS : Subsingleton ((singularChains ℤ (TopCat.of ↥S)).homology n)) :
    Subsingleton ((singularChains ℤ (TopCat.of ↥T)).homology n) :=
  subsingleton_homology_of_homeomorph (Homeomorph.setCongr h.symm) n hS

/-- The Mayer–Vietoris step in the complement form: vanishing for the complements of `D`, `E` and
`D ∩ E` (in degrees `n` and `n + 1`) gives vanishing for the complement of `D ∪ E`. -/
theorem subsingleton_homology_compl_union {N : ℕ} {D E : Set (EuclideanSpace ℝ (Fin N))}
    (hD : IsCompact D) (hE : IsCompact E) (n : ℕ)
    (hDn : Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ D})).homology n))
    (hEn : Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ E})).homology n))
    (hDn1 : Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ D})).homology (n + 1)))
    (hEn1 : Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ E})).homology (n + 1)))
    (hDE : Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ (D ∩ E)})).homology (n + 1))) :
    Subsingleton ((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ (D ∪ E)})).homology n) := by
  classical
  set A : Set (EuclideanSpace ℝ (Fin N)) := {x | x ∉ D} with hAdef
  set B : Set (EuclideanSpace ℝ (Fin N)) := {x | x ∉ E} with hBdef
  have hDn' : Subsingleton ((singularChains ℤ (TopCat.of ↥A)).homology n) :=
    subsingleton_homology_of_set_eq hAdef.symm n hDn
  have hEn' : Subsingleton ((singularChains ℤ (TopCat.of ↥B)).homology n) :=
    subsingleton_homology_of_set_eq hBdef.symm n hEn
  have hDn1' : Subsingleton ((singularChains ℤ (TopCat.of ↥A)).homology (n + 1)) :=
    subsingleton_homology_of_set_eq hAdef.symm (n + 1) hDn1
  have hEn1' : Subsingleton ((singularChains ℤ (TopCat.of ↥B)).homology (n + 1)) :=
    subsingleton_homology_of_set_eq hBdef.symm (n + 1) hEn1
  have hUn : A ∪ B = {x : EuclideanSpace ℝ (Fin N) | x ∉ (D ∩ E)} := by
    rw [hAdef, hBdef]
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hInt : A ∩ B = {x : EuclideanSpace ℝ (Fin N) | x ∉ (D ∪ E)} := by
    rw [hAdef, hBdef]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union]
    tauto
  have hX : Subsingleton ((singularChains ℤ (TopCat.of ↥(A ∪ B))).homology (n + 1)) :=
    subsingleton_homology_of_set_eq hUn.symm (n + 1) hDE
  have hU : Subsingleton ((singularChains ℤ
      (TopCat.of {x : ↥(A ∪ B) // (x : EuclideanSpace ℝ (Fin N)) ∈ A})).homology n) :=
    subsingleton_homology_of_homeomorph (homeomorphSubsetUnion (A := A) (B := B)).symm n hDn'
  have hV : Subsingleton ((singularChains ℤ
      (TopCat.of {x : ↥(A ∪ B) // (x : EuclideanSpace ℝ (Fin N)) ∈ B})).homology n) :=
    subsingleton_homology_of_homeomorph (homeomorphSubsetUnionRight (A := A) (B := B)).symm n hEn'
  have hU1 : Subsingleton ((singularChains ℤ
      (TopCat.of {x : ↥(A ∪ B) // (x : EuclideanSpace ℝ (Fin N)) ∈ A})).homology (n + 1)) :=
    subsingleton_homology_of_homeomorph (homeomorphSubsetUnion (A := A) (B := B)).symm (n + 1) hDn1'
  have hV1 : Subsingleton ((singularChains ℤ
      (TopCat.of {x : ↥(A ∪ B) // (x : EuclideanSpace ℝ (Fin N)) ∈ B})).homology (n + 1)) :=
    subsingleton_homology_of_homeomorph (homeomorphSubsetUnionRight (A := A) (B := B)).symm
      (n + 1) hEn1'
  have hmain := mv_subsingleton_homology_inter (X := TopCat.of ↥(A ∪ B))
    {x : ↥(A ∪ B) | (x : EuclideanSpace ℝ (Fin N)) ∈ A}
    {x : ↥(A ∪ B) | (x : EuclideanSpace ℝ (Fin N)) ∈ B}
    (hD.isClosed.isOpen_compl.preimage continuous_subtype_val)
    (hE.isClosed.isOpen_compl.preimage continuous_subtype_val)
    (by
      ext x
      constructor
      · intro _; trivial
      · intro _
        rcases (x : ↥(A ∪ B)).2 with h | h
        · exact Or.inl h
        · exact Or.inr h)
    n hU hV hU1 hV1 hX
  exact subsingleton_homology_of_set_eq hInt n
    (subsingleton_homology_of_homeomorph (homeomorphSubsetInter (A := A) (B := B)) n hmain)

/-- The union over `insert a s` of a family of sets. -/
lemma iUnion_insert_finset {α ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι)
    (P : ι → Set α) :
    (⋃ i ∈ insert a s, P i) = (⋃ i ∈ s, P i) ∪ P a := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨i, rfl | hi, hx⟩
    · exact Or.inr hx
    · exact Or.inl ⟨i, hi, hx⟩
  · rintro (⟨i, hi, hx⟩ | h)
    · exact ⟨i, Or.inr hi, hx⟩
    · exact ⟨a, Or.inl rfl, h⟩

/-- The union of the intersections of a family with a fixed set. -/
lemma iUnion_finset_inter_right {α ι : Type} (s : Finset ι) (P : ι → Set α) (Q : Set α) :
    (⋃ i ∈ s, P i ∩ Q) = (⋃ i ∈ s, P i) ∩ Q := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩; exact ⟨⟨i, hi, h1⟩, h2⟩
  · rintro ⟨⟨i, hi, h1⟩, h2⟩; exact ⟨i, hi, h1, h2⟩

theorem flat_compl_union_convex_homology_vanishing {N : ℕ} (hN : 1 ≤ N) {ι : Type}
    (s : Finset ι) (D : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hDc : ∀ i ∈ s, IsCompact (D i)) (hDv : ∀ i ∈ s, Convex ℝ (D i)) :
    ∀ j : ℕ, N ≤ j →
      Subsingleton ((singularChains ℤ
        (TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, D i})).homology j) := by
  classical
  revert D hDc hDv
  refine Finset.induction_on s ?_ ?_
  · intro D hDc hDv j hj
    have hset : {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ (∅ : Finset ι), D i} = Set.univ := by
      ext x; simp
    rw [hset]
    haveI : ContractibleSpace ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))) :=
      convex_univ.contractibleSpace ⟨0, trivial⟩
    exact ModuleCat.subsingleton_of_isZero (homologyContractible j (by omega))
  · intro a s has ih D hDc hDv j hj
    have hset : {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ insert a s, D i}
        = {x : EuclideanSpace ℝ (Fin N) | x ∉ ((⋃ i ∈ s, D i) ∪ D a)} := by
      rw [iUnion_insert_finset a s D]
    rw [hset]
    have hEc : IsCompact (⋃ i ∈ s, D i) :=
      Finset.isCompact_biUnion s (fun i hi => hDc i (Finset.mem_insert_of_mem hi))
    have hDac : IsCompact (D a) := hDc a (Finset.mem_insert_self a s)
    have hDav : Convex ℝ (D a) := hDv a (Finset.mem_insert_self a s)
    have hsingle : ∀ k : ℕ, N ≤ k → Subsingleton ((singularChains ℤ
        (TopCat.of {x : EuclideanSpace ℝ (Fin N) // x ∉ D a})).homology k) := by
      intro k hk
      by_cases hne : (D a).Nonempty
      · exact ModuleCat.subsingleton_of_isZero
          (Duality.complHomologyZero N hN (D a) hDac hDav hne k (by omega) (by omega))
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have hset2 : {x : EuclideanSpace ℝ (Fin N) | x ∉ D a} = Set.univ := by
          rw [hne]; ext x; simp
        haveI huniv : ContractibleSpace ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))) :=
          convex_univ.contractibleSpace ⟨0, trivial⟩
        have hh : ({x : EuclideanSpace ℝ (Fin N) // x ∉ D a}) ≃ₜ
            ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))) :=
          Homeomorph.setCongr hset2
        haveI : ContractibleSpace {x : EuclideanSpace ℝ (Fin N) // x ∉ D a} :=
          hh.contractibleSpace
        exact ModuleCat.subsingleton_of_isZero (homologyContractible k (by omega))
    have hIH : Subsingleton ((singularChains ℤ (TopCat.of
        {x : EuclideanSpace ℝ (Fin N) // x ∉ ⋃ i ∈ s, D i})).homology (j + 1)) :=
      ih D (fun i hi => hDc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hDv i (Finset.mem_insert_of_mem hi)) (j + 1) (by omega)
    have hIHn : Subsingleton ((singularChains ℤ (TopCat.of
        {x : EuclideanSpace ℝ (Fin N) // x ∉ ⋃ i ∈ s, D i})).homology j) :=
      ih D (fun i hi => hDc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hDv i (Finset.mem_insert_of_mem hi)) j hj
    have hIsub : Subsingleton ((singularChains ℤ (TopCat.of
        {x : EuclideanSpace ℝ (Fin N) // x ∉ (⋃ i ∈ s, D i ∩ D a)})).homology (j + 1)) :=
      ih (fun i => D i ∩ D a)
        (fun i hi => (hDc i (Finset.mem_insert_of_mem hi)).inter hDac)
        (fun i hi => (hDv i (Finset.mem_insert_of_mem hi)).inter hDav) (j + 1) (by omega)
    have hIset : {x : EuclideanSpace ℝ (Fin N) | x ∉ (⋃ i ∈ s, D i ∩ D a)}
        = {x : EuclideanSpace ℝ (Fin N) | x ∉ ((⋃ i ∈ s, D i) ∩ D a)} := by
      rw [iUnion_finset_inter_right s D (D a)]
    exact subsingleton_homology_compl_union (D := ⋃ i ∈ s, D i) (E := D a) hEc hDac j
      hIHn (hsingle j hj) hIH (hsingle (j + 1) (by omega))
      (subsingleton_homology_of_set_eq hIset (j + 1) hIsub)

/-- Vanishing of the relative homology of the complement of a finite union of compact convex sets,
above the dimension. -/
theorem flat_rel_union_convex_homology_vanishing {N : ℕ} (hN : 1 ≤ N) {ι : Type}
    (s : Finset ι) (D : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hDc : ∀ i ∈ s, IsCompact (D i)) (hDv : ∀ i ∈ s, Convex ℝ (D i)) (m : ℕ) (hm : N < m) :
    Subsingleton ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, D i}).homology m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hns : N ≤ n := by omega
  haveI hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N)))
      {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, D i} n) :=
    hPairδ_isIso _ _ n (homologyContractible (n + 1) (by omega))
      (homologyContractible n (by omega))
  exact ModuleCat.subsingleton_of_isZero
    (IsZero.of_iso
      (ModuleCat.isZero_iff_subsingleton.mpr
        (flat_compl_union_convex_homology_vanishing hN s D hDc hDv n hns))
      (asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, D i} n)))

/-- Vanishing of the relative homology of a chart piece modulo a finite union of coordinate pieces
over compact convex sets, above the dimension. -/
theorem chart_piece_union_homology_vanishing {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M)
    (Q : Set (EuclideanSpace ℝ (Fin N))) (hQ : IsOpen Q)
    (hQt : Q ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).target)
    {ι : Type} (s : Finset ι) (D : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hDc : ∀ i ∈ s, IsCompact (D i)) (hDv : ∀ i ∈ s, Convex ℝ (D i))
    (hDQ : ∀ i ∈ s, D i ⊆ Q) (m : ℕ) (hm : N < m) :
    Subsingleton ((relChains
        (TopCat.of ↥((chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹' Q
          ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source))
        (pdRelSub ((chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹' Q
            ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source)
          ((chartAt (EuclideanSpace ℝ (Fin N)) cc) ⁻¹' (⋃ i ∈ s, D i)
            ∩ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source))).homology m) := by
  classical
  have hKc : IsCompact (⋃ i ∈ s, D i) :=
    Finset.isCompact_biUnion s (fun i hi => hDc i hi)
  have hKQ : (⋃ i ∈ s, D i) ⊆ Q := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hDQ i hi hxi
  obtain ⟨eiso⟩ := chartConvexPair_relHomology_iso N M cc Q hQ hQt (⋃ i ∈ s, D i) hKc hKQ m
  haveI hsub := flat_rel_union_convex_homology_vanishing hN s D hDc hDv m hm
  exact ⟨fun a b => (ConcreteCategory.bijective_of_isIso eiso.hom).1
    (Subsingleton.elim (eiso.hom a) (eiso.hom b))⟩

theorem homology_vanishing_relative_compact {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M)
    (Q : Set (EuclideanSpace ℝ (Fin N))) (hQ : IsOpen Q)
    (hQt : Q ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).target) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt (EuclideanSpace ℝ (Fin N)) cc
    let W : Set M := (e ⁻¹' Q) ∩ e.source
    ∀ (C : Set M), C ⊆ W → IsCompact C → ∀ m, N < m →
      Subsingleton ((relChains (TopCat.of W) (pdRelSub W C)).homology m) := by
  intro e W C hCW hCc m hm
  classical
  have hzero : ∀ α : (relChains (TopCat.of W) (pdRelSub W C)).homology m, α = 0 := by
    intro α
    obtain ⟨γ, hγ⟩ := (ModuleCat.epi_iff_surjective
      ((relChains (TopCat.of W) (pdRelSub W C)).homologyπ m)).mp inferInstance α
    have hm1 : 1 ≤ m := by omega
    obtain ⟨x, y, hx, hy⟩ := relative_cycle_lift W C m hm1 γ
    obtain ⟨S, hSsub, hSc, hSsupp⟩ :=
      exists_compact_support_image (X := TopCat.of W) (pdRelSub W C) (m - 1) y
    set S' : Set M := Subtype.val '' S with hS'def
    have hS'W : S' ⊆ W := by
      rintro z ⟨w, _, rfl⟩
      exact w.2
    have hS'c : IsCompact S' := hSc.image continuous_subtype_val
    have hdisj : Disjoint C S' := by
      rw [Set.disjoint_left]
      intro z hzC hzS
      obtain ⟨w, hw, hwz⟩ := hzS
      exact (hSsub hw) (hwz ▸ hzC)
    obtain ⟨t, r, hrm, htC, hcover, hdisj2, hballQ⟩ :=
      exists_piece_cover_disjoint hN cc Q hQ hQt C S' hCW hS'W hCc hS'c hdisj
    set K : Set M := e ⁻¹' (⋃ c ∈ t, Metric.closedBall (e c) r) ∩ e.source with hKdef
    have hCK : C ⊆ K := by
      intro z hz
      obtain ⟨c, hc, hcz⟩ := Set.mem_iUnion₂.mp (hcover hz)
      rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion₂]
      exact ⟨⟨c, hc, hcz.1⟩, hcz.2⟩
    have hSK : S ⊆ pdRelSub W K := by
      intro w hw
      show (w : M) ∉ K
      intro hwK
      rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion₂] at hwK
      obtain ⟨⟨c, hc, hcw⟩, hw2⟩ := hwK
      refine (Set.disjoint_left.mp hdisj2 ⟨w, hw, rfl⟩) ?_
      rw [Set.mem_iUnion₂]
      exact ⟨c, hc, hcw, hw2⟩
    have hdxK : (singularChains ℤ (TopCat.of W)).d m (m - 1) x
        ∈ LinearMap.range ((inclChains (TopCat.of W) (pdRelSub W K)).f (m - 1)).hom := by
      have h1 : (singularChains ℤ (TopCat.of W)).d m (m - 1) x
          ∈ LinearMap.range ((inclChains (TopCat.of W) S).f (m - 1)).hom := by
        rw [← hy]; exact hSsupp
      exact mem_range_inclChains_of_subset hSK h1
    obtain ⟨γK, γC, hγK, hγC, heq⟩ := homologyMap_enlarge_of_lift W C K hCK m hdxK
    have hγCγ : γC = γ := by
      have hinj : Function.Injective (ConcreteCategory.hom
          ((relChains (TopCat.of W) (pdRelSub W C)).iCycles m)) :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      apply hinj
      rw [hγC, hx]
    haveI hKsub : Subsingleton ((relChains (TopCat.of W) (pdRelSub W K)).homology m) :=
      chart_piece_union_homology_vanishing hN cc Q hQ hQt t
        (fun c : M => Metric.closedBall (e c) r) (fun c _ => isCompact_closedBall _ _)
        (fun c _ => convex_closedBall _ _) hballQ m hm
    calc α = (relChains (TopCat.of W) (pdRelSub W C)).homologyπ m γ := hγ.symm
      _ = (relChains (TopCat.of W) (pdRelSub W C)).homologyπ m γC := by rw [hγCγ]
      _ = HomologicalComplex.homologyMap (pdRelChainsEnlarge W hCK) m
            ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ m γK) := heq.symm
      _ = HomologicalComplex.homologyMap (pdRelChainsEnlarge W hCK) m 0 := by
            rw [Subsingleton.elim ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ m γK) 0]
      _ = 0 := map_zero _
  refine ⟨fun α β => ?_⟩
  rw [hzero α, hzero β]

end

end Work.Cohomology
