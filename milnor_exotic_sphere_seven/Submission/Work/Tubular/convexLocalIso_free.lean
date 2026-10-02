import Mathlib
import Submission.Work.ThomBordism.convexLocalIso
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.pd_triple

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Tubular

noncomputable section

theorem convexLocalIso_free (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [T2Space M]
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

end Work.Tubular
