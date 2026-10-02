import Mathlib
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.euclidean_open_cohomology_vanishing
import Submission.Work.ThomBordism.DimVanishingCommon

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism
noncomputable section

/-- `H^k(X;ℤ)`. -/
abbrev singCoh (X : TopCat) (k : ℕ) : ModuleCat ℤ :=
  (Work.Cohomology.singularCochainComplex ℤ X).homology k

/-- Cohomology vanishing transfers along homeomorphisms. -/
theorem subsingleton_singCoh_of_homeo {X Y : TopCat} (h : X ≃ₜ Y) (k : ℕ)
    (hY : Subsingleton (singCoh Y k)) : Subsingleton (singCoh X k) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv (X := ↥X) (Y := ↥Y)
    h.toHomotopyEquiv k
  exact Work.Cohomology.subsingleton_of_iso_aux e.symm hY

/-- **The copy of a subset of a union inside the union.** -/
noncomputable def homeoSetSelfOfSubset {α : Type} [TopologicalSpace α] {S T : Set α}
    (hST : S ⊆ T) : ↥S ≃ₜ ↥(Subtype.val ⁻¹' S : Set ↥T) :=
  (Topology.IsEmbedding.homeomorphOfSubsetRange (f := (Subtype.val : ↥T → α))
    Topology.IsEmbedding.subtypeVal (by rwa [Subtype.range_val])).symm

/-- Cohomology vanishing transports from a set to its copy inside a larger set. -/
theorem subsingleton_singCoh_preimage_subtype_val {α : Type} [TopologicalSpace α] {S T : Set α}
    (hST : S ⊆ T) (k : ℕ) (hS : Subsingleton (singCoh (TopCat.of ↥S) k)) :
    Subsingleton (singCoh (TopCat.of ↥(Subtype.val ⁻¹' S : Set ↥T)) k) :=
  subsingleton_singCoh_of_homeo (homeoSetSelfOfSubset hST).symm k hS

/-- **The Mayer–Vietoris step, vanishing form.**  If `U` and `V` are open and cover `X`, and the
cohomology of `U` and `V` vanishes in degree `m + 1` while that of `U ∩ V` vanishes in degree `m`,
then the cohomology of `X` vanishes in degree `m + 1`. -/
theorem subsingleton_singCoh_of_cover_two {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (m : ℕ)
    (hUm : Subsingleton (singCoh (TopCat.of ↥U) (m + 1)))
    (hVm : Subsingleton (singCoh (TopCat.of ↥V) (m + 1)))
    (hI : Subsingleton (singCoh (TopCat.of ↥(U ∩ V)) m)) :
    Subsingleton (singCoh X (m + 1)) := by
  haveI hzU : IsZero ((Work.Cohomology.cochainU U V).homology (m + 1)) := by
    rw [Work.Cohomology.cochainU, Work.Cohomology.dualComplex_singularChains]
    exact ModuleCat.isZero_iff_subsingleton.mpr hUm
  haveI hzV : IsZero ((Work.Cohomology.cochainV U V).homology (m + 1)) := by
    rw [Work.Cohomology.cochainV, Work.Cohomology.dualComplex_singularChains]
    exact ModuleCat.isZero_iff_subsingleton.mpr hVm
  haveI hzB : IsZero ((Work.Cohomology.cochainU U V ⊞ Work.Cohomology.cochainV U V).homology
      (m + 1)) :=
    Work.Cohomology.isZero_coh_homology_biprod _ _ (m + 1) hzU hzV
  have hg : (ShortComplex.mk (Work.Cohomology.mvCohδ U V m)
      (HomologicalComplex.homologyMap (Work.Cohomology.mvCochainF U V) (m + 1))
      (by
        show Work.Cohomology.mvCohδ U V m ≫ HomologicalComplex.homologyMap
          (Work.Cohomology.mvCochainF U V) (m + 1) = 0
        exact (Work.Cohomology.mvCochainSES U V).δ_comp m (m + 1) (by simp [ComplexShape.up]))).g
      = 0 :=
    IsZero.eq_zero_of_tgt hzB _
  haveI hepi : Epi (Work.Cohomology.mvCohδ U V m) :=
    (ShortComplex.exact_iff_epi _ hg).1 (Work.Cohomology.mvCoh_H_exact₁ U V m)
  have hsurj : Function.Surjective (Work.Cohomology.mvCohδ U V m) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  haveI hI' : Subsingleton ↥((Work.Cohomology.cochainUV U V).homology m) := by
    rw [Work.Cohomology.cochainUV, Work.Cohomology.dualComplex_singularChains]
    exact hI
  have hsmall : Subsingleton ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallChains U V)).homology (m + 1)) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rw [Subsingleton.elim x y]⟩
  obtain ⟨e⟩ := Work.Cohomology.cohSmallIso U V hU hV hcov (m + 1)
  exact Work.Cohomology.subsingleton_of_iso_aux e.symm hsmall

/-- **Vanishing of the cohomology of an open subset of a chart.** -/
theorem singCoh_vanishing_open_subset_chart {N : ℕ} (hN : 1 ≤ N) {M : TopCat}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (z : M) (W : Set M) (hW : IsOpen W)
    (hWsrc : W ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) z).source) (k : ℕ) (hk : N ≤ k) :
    Subsingleton (singCoh (TopCat.of ↥W) k) := by
  set e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z with he
  have hWo : IsOpen (e '' W) := e.isOpen_image_of_subset_source hW hWsrc
  have hE := Work.Cohomology.euclidean_open_cohomology_vanishing hN (e '' W) hWo k hk
  exact subsingleton_singCoh_of_homeo (chartImageHomeo e W hWsrc) k hE

end
end Work.ThomBordism
