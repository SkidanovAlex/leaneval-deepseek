import Mathlib
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.HomologyPairSequence

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

theorem convexCover (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∃ (m : ℕ) (K : Fin m → Set M),
      (⋃ i, K i) = Set.univ ∧
      (∀ x : M, ∃ i, x ∈ interior (K i)) ∧
      (∀ i, IsCompact (K i)) ∧
      (∀ i, (K i).Nonempty) ∧
      (∀ i, ∃ (z : M) (r : ℝ), 0 < r ∧
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) r ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) z).target ∧
        K i = (chartAt (EuclideanSpace ℝ (Fin n)) z) ⁻¹'
            Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (r / 2)
          ∩ (chartAt (EuclideanSpace ℝ (Fin n)) z).source) := by
  classical
  have hchoice : ∀ a : M, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) ρ ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) a).target := by
    intro a
    have ha : (chartAt (EuclideanSpace ℝ (Fin n)) a) a
        ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).target :=
      (chartAt (EuclideanSpace ℝ (Fin n)) a).map_source (mem_chart_source _ a)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((chartAt (EuclideanSpace ℝ (Fin n)) a).open_target.mem_nhds ha)
    exact ⟨ε / 2, by linarith, fun y hy => hεsub (by
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hy
      rw [dist_comm] at h ⊢
      linarith)⟩
  choose ρ hρpos hρsub using hchoice
  let K : M → Set M := fun a =>
    (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
      ∩ (chartAt (EuclideanSpace ℝ (Fin n)) a).source
  have hKopen : ∀ a, IsOpen ((chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
        ∩ (chartAt (EuclideanSpace ℝ (Fin n)) a).source) := by
    intro a
    rw [Set.inter_comm]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) a).isOpen_inter_preimage Metric.isOpen_ball
  have hsub : ∀ a, ((chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
        ∩ (chartAt (EuclideanSpace ℝ (Fin n)) a).source) ⊆ K a := by
    intro a y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  have hmem : ∀ a, a ∈ ((chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
        ∩ (chartAt (EuclideanSpace ℝ (Fin n)) a).source) := by
    intro a
    refine ⟨?_, mem_chart_source _ a⟩
    rw [Set.mem_preimage]
    exact Metric.mem_ball_self (by linarith [hρpos a])
  have hcov : Set.univ ⊆ ⋃ a : M, interior (K a) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, interior_maximal (hsub x) (hKopen x) (hmem x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun a : M => interior (K a))
    (fun a => isOpen_interior) hcov
  let kp : Fin t.card → M := fun k => ((t.equivFin.symm k : ↥t) : M)
  have hkp : ∀ (a : M) (ha : a ∈ t), kp (t.equivFin ⟨a, ha⟩) = a := by
    intro a ha
    show (((t.equivFin.symm (t.equivFin ⟨a, ha⟩)) : ↥t) : M) = a
    rw [Equiv.symm_apply_apply]
  have hKcompact : ∀ i : Fin t.card, IsCompact (K (kp i)) := by
    intro i
    have heq : K (kp i) = (chartAt (EuclideanSpace ℝ (Fin n)) (kp i)).symm ''
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) (kp i)) (kp i)) (ρ (kp i) / 2) := by
      rw [OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ ?_]
      · exact Set.inter_comm _ _
      · exact fun y hy => hρsub (kp i) (Metric.closedBall_subset_closedBall (by linarith [hρpos (kp i)]) hy)
    rw [heq]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin n)) (kp i)).continuousOn_symm.mono
        (fun y hy => hρsub (kp i) (Metric.closedBall_subset_closedBall
          (by linarith [hρpos (kp i)]) hy)))
  refine ⟨t.card, fun i => K (kp i), ?_, ?_, hKcompact, ?_, ?_⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨a, ha⟩, ?_⟩
    rw [hkp a ha]
    exact interior_subset hxa
  · intro x
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨a, ha⟩, ?_⟩
    show x ∈ interior (K (kp (t.equivFin ⟨a, ha⟩)))
    rw [hkp a ha]
    exact hxa
  · intro i
    exact ⟨kp i, hsub (kp i) (hmem (kp i))⟩
  · intro i
    refine ⟨kp i, ρ (kp i), hρpos _, ?_, ?_⟩
    · exact Metric.ball_subset_closedBall.trans (hρsub (kp i))
    · rfl

/-- **The localisation `H_n(M, M∖K) → H_n(M, M∖{x})` is an isomorphism** for a coordinate
closed ball `K` and any point `x ∈ K`. -/
theorem convexLocalIso (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r / 2) ∩ e.source
    ∀ (x : M) (hx : x ∈ K),
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap M Kᶜ ({x} : Set M)ᶜ
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n) := by
  intro e hball K x hx
  have hsub : Kᶜ ⊆ ({x} : Set M)ᶜ := Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  have hKsub : Metric.closedBall (e z) (r / 2) ⊆ Metric.ball (e z) r := by
    intro v hv
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hv
    linarith
  -- the vanishing of `H_*(M∖{x}, M∖K)` in the honest subspace model
  have hvanish : ∀ i : ℕ, CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of {y : M | y ≠ x})
        {y : ↥{y : M | y ≠ x} |
          (y : M) ∉ e ⁻¹' Metric.closedBall (e z) (r / 2) ∩ e.source}).homology i) := by
    intro i
    exact Work.Cohomology.isZero_relChains_punctured_chart n hn M z r hr
      (Metric.closedBall (e z) (r / 2)) (isCompact_closedBall _ _) (convex_closedBall _ _)
      hball hKsub x hx i
  -- the triple `Kᶜ ⊆ {x}ᶜ ⊆ M`
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort M Kᶜ ({x} : Set M)ᶜ hsub
  have hSEX : S.ShortExact := Work.Cohomology.relChains_triple_shortExact M Kᶜ ({x} : Set M)ᶜ hsub
  have hSg : S.g = Work.Cohomology.relCokerMap M Kᶜ ({x} : Set M)ᶜ hsub :=
    Work.Cohomology.tripleShort_g M Kᶜ ({x} : Set M)ᶜ hsub
  have hz0 : CategoryTheory.Limits.IsZero (S.X₁.homology n) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso M x K hx n
    exact CategoryTheory.Limits.IsZero.of_iso (hvanish n) eiso
  have hz1 : CategoryTheory.Limits.IsZero (S.X₁.homology (n - 1)) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso M x K hx (n - 1)
    exact CategoryTheory.Limits.IsZero.of_iso (hvanish (n - 1)) eiso
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)) := by
    have hf0 : HomologicalComplex.homologyMap S.f n = 0 :=
      CategoryTheory.Limits.IsZero.eq_zero_of_src hz0 _
    have hr2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f n)).range =
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker (hSEX.homology_exact₂ n)
    rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero] at hr2
    exact LinearMap.ker_eq_bot.mp hr2.symm
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)) := by
    have hij : (ComplexShape.down ℕ).Rel n (n - 1) := Nat.sub_add_cancel hn
    have hδ0 : hSEX.δ n (n - 1) hij = 0 :=
      CategoryTheory.Limits.IsZero.eq_zero_of_tgt hz1 _
    have hr3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g n)).range =
        (ModuleCat.Hom.hom (hSEX.δ n (n - 1) hij)).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker (hSEX.homology_exact₃ n (n - 1) hij)
    rw [hδ0, ModuleCat.hom_zero, LinearMap.ker_zero] at hr3
    exact LinearMap.range_eq_top.mp hr3
  have hbij : Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap M Kᶜ ({x} : Set M)ᶜ hsub) n)) := by
    rw [← hSg]
    exact ⟨hinj, hsurj⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end

end Work.ThomBordism
