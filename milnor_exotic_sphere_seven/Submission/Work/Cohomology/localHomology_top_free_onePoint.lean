import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Cohomology.onePointSpace_compl_point_homeo
import Submission.Work.Cohomology.euclidean_relChains_top_homology_free
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.homology_onePointSpace_free
import Submission.Work.Cohomology.sphereVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

namespace Work.Cohomology

open CategoryTheory

/-- The `N`-th homology of the one-point compactification of `ℝ^N` (an `N`-sphere) is free. -/
theorem onePointSpace_homology_top_free (N : ℕ) (hN : 1 ≤ N) :
    Module.Free ℤ ↥((singularChains ℤ
      (TopCat.of (OnePointSpace N))).homology N) := by
  let e : OnePointSpace N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin N)) (ι := Fin (N + 1)) (by simp)
  obtain ⟨iso⟩ := homologyIso_of_homotopyEquiv e.toHomotopyEquiv N
  obtain ⟨e2⟩ := sphereHomologyTop N hN
  exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ)
    (iso ≪≫ e2).toLinearEquiv.symm

theorem localHomology_top_free_onePoint {N : ℕ} (hN : 1 ≤ N)
    (A : Set (OnePoint (EuclideanSpace ℝ (Fin N)))) (hA : IsCompact A) :
    Module.Free ℤ ↥((Work.Cohomology.relChains
      (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N)))) (Aᶜ)).homology N) := by
  rcases Set.eq_empty_or_nonempty Aᶜ with hAcompl | ⟨q, hq⟩
  · -- `Aᶜ = ∅`: `H_N(S^N, ∅) ≅ H_N(S^N) ≅ ℤ`.
    rw [hAcompl]
    have hIso := relChains_empty_homology_iso (TopCat.of (OnePointSpace N)) N
    exact Module.Free.of_equiv' (onePointSpace_homology_top_free N hN)
      (asIso (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (OnePointSpace N)) (∅ : Set (OnePointSpace N)))) N)).toLinearEquiv
  · -- `Aᶜ ≠ ∅`: excise to the complement of a point `q ∈ Aᶜ`, homeomorphic to `ℝ^N`.
    have hUopen : IsOpen ({q}ᶜ : Set (OnePointSpace N)) := isClosed_singleton.isOpen_compl
    have hAcopen : IsOpen (Aᶜ : Set (OnePointSpace N)) := hA.isClosed.isOpen_compl
    have hcov : ({q}ᶜ : Set (OnePointSpace N)) ∪ Aᶜ = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      by_cases hy : y = q
      · exact Or.inr (hy ▸ hq)
      · exact Or.inl hy
    haveI hiso := excision_relChainsMap_isIso (X := TopCat.of (OnePointSpace N))
      ({q}ᶜ) (Aᶜ) hUopen hAcopen hcov N
    -- Step 1: excision, `H_N(S^N, Aᶜ) ≅ H_N(↥{q}ᶜ, B)` with `B = ↥{q}ᶜ ∩ Aᶜ`.
    have e1 : (relChains (TopCat.of (OnePointSpace N)) (Aᶜ)).homology N ≅
        (relChains (TopCat.of ↥({q}ᶜ : Set (OnePointSpace N)))
          {y : ↥({q}ᶜ : Set (OnePointSpace N)) | (y : OnePointSpace N) ∈ Aᶜ}).homology N :=
      (asIso (HomologicalComplex.homologyMap
        (relChainsMap (TopCat.of (OnePointSpace N)) ({q}ᶜ) (Aᶜ)) N)).symm
    -- Step 2: the homeomorphism `↥{q}ᶜ ≃ₜ ℝ^N`.
    obtain ⟨φ⟩ := onePointSpace_compl_point_homeo N hN q
    set Aq : Set ↥({q}ᶜ : Set (OnePointSpace N)) := {y | (y : OnePointSpace N) ∈ A} with hAqdef
    set B : Set ↥({q}ᶜ : Set (OnePointSpace N)) :=
      {y | (y : OnePointSpace N) ∈ Aᶜ} with hBdef
    have hB : B = Aqᶜ := by
      rw [hBdef, hAqdef]
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    have hAqc : IsCompact Aq := by
      have h1 : Subtype.val '' Aq = A := by
        rw [hAqdef]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx
          exact ⟨⟨x, fun hxq => hq (hxq ▸ hx)⟩, hx, rfl⟩
      rw [Topology.IsInducing.subtypeVal.isCompact_iff, h1]
      exact hA
    -- Step 3: transport along the homeomorphism.
    have he : ∀ y : ↥({q}ᶜ : Set (OnePointSpace N)), (y ∈ B ↔ φ y ∈ (φ '' Aq)ᶜ) := by
      rw [hB]
      intro y
      constructor
      · intro hy hcon
        obtain ⟨a, ha, hay⟩ := hcon
        exact hy ((φ.injective hay) ▸ ha)
      · intro hy ha
        exact hy ⟨y, ha, rfl⟩
    obtain ⟨e2⟩ := relChains_homeomorph (↥({q}ᶜ : Set (OnePointSpace N)))
      (EuclideanSpace ℝ (Fin N)) B ((φ '' Aq)ᶜ) φ he N
    -- Step 4: the flat model.
    have hC : IsCompact (φ '' Aq) := hAqc.image φ.continuous
    have hfree := euclidean_relChains_top_homology_free (N := N) hN (φ '' Aq) hC
    have hcomp : Module.Free ℤ ↥((relChains (TopCat.of ↥({q}ᶜ : Set (OnePointSpace N))) B).homology N) :=
      Module.Free.of_equiv' hfree e2.toLinearEquiv.symm
    exact Module.Free.of_equiv' hcomp e1.toLinearEquiv.symm

end Work.Cohomology
