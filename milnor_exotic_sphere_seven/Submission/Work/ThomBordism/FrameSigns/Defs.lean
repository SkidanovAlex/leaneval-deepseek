import Mathlib
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Cohomology.excisionDualZ
import Submission.Work.Cohomology.euclideanLocalHomologyTop
import Submission.Work.Cohomology.euclideanLocalHomologyZero
import Submission.Work.Cohomology.euclidean_relChains_top_homology_free

import Submission.Work.Tubular.exists_relKronH_eval_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-- The punctured model space `ℝ⁸ ∖ {0}`. -/
abbrev E8p : Set (EuclideanSpace ℝ (Fin 8)) := {v | v ≠ 0}

/-- The relative chain complex of the model pair `(ℝ⁸, ℝ⁸∖0)`. -/
abbrev modelC := Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p

/-- The model pair's relative cohomology in degree `8`. -/
abbrev modelCoh := (Work.Cohomology.relComplex ℤ (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p).homology 8

/-- **The relative homology of the model pair is free in every degree.** -/
theorem modelC_free (j : ℕ) : Module.Free ℤ ↥(modelC.homology j) := by
  rcases eq_or_ne j 8 with rfl | hj
  · exact Work.Cohomology.euclidean_relChains_top_homology_free (N := 8) (by norm_num)
      {0} isCompact_singleton
  · have hz : IsZero (modelC.homology j) :=
      Work.Cohomology.euclideanLocalHomologyZero 8 j (by norm_num) hj
    have h0 : (𝟙 (modelC.homology j)) = 0 := (IsZero.iff_id_eq_zero (modelC.homology j)).mp hz
    haveI : Subsingleton ↥(modelC.homology j) := ⟨fun x y => by
      have hx : x = 0 := by
        have h := congrArg (fun (φ : modelC.homology j ⟶ modelC.homology j) =>
          (ConcreteCategory.hom φ) x) h0
        simpa using h
      have hy : y = 0 := by
        have h := congrArg (fun (φ : modelC.homology j ⟶ modelC.homology j) =>
          (ConcreteCategory.hom φ) y) h0
        simpa using h
      rw [hx, hy]⟩
    exact Module.Free.of_subsingleton ℤ _

/-- A fixed isomorphism `H₈(ℝ⁸, ℝ⁸∖0) ≅ ℤ`. -/
def e8 : modelC.homology 8 ≅ ModuleCat.of ℤ ℤ :=
  Classical.choice (Work.Cohomology.euclideanLocalHomologyTop 8 (by norm_num))

/-- **A generator of the model relative homology `H₈(ℝ⁸, ℝ⁸∖0)`.** -/
def sigma0 : ↥(modelC.homology 8) := (e8.inv).hom (1 : ℤ)

/-- The dual functional on the model homology, an isomorphism onto `ℤ`. -/
def dual0 : ↥(modelC.homology 8) →ₗ[ℤ] ℤ := ((e8.hom).hom : ↥(modelC.homology 8) →ₗ[ℤ] ℤ)

theorem dual0_sigma0 : dual0 sigma0 = 1 := by
  simp only [dual0, sigma0]
  have hh := congrArg (fun (φ : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) =>
    (ConcreteCategory.hom φ) (1 : ℤ)) (Iso.inv_hom_id e8)
  simpa using hh

/-- The pairing isomorphism `H⁸ ≅ Hom(H₈, ℤ)` of the model pair, as a linear equivalence. -/
def kronIso : ↥modelCoh ≃ₗ[ℤ] (↥(modelC.homology 8) →ₗ[ℤ] ℤ) :=
  Classical.choose (Work.Tubular.exists_relKronH_eval_iso (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8 modelC_free)

theorem kronIso_spec (α : ↥modelCoh) (c : ↥(modelC.homology 8)) :
    kronIso α c = (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8) α c :=
  Classical.choose_spec (Work.Tubular.exists_relKronH_eval_iso (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8 modelC_free) α c

/-- **A cohomology class `τ` of the model pair with `⟨τ, σ₀⟩ = 1`.** -/
def tau : ↥modelCoh := kronIso.symm dual0

/-- **`⟨τ, −⟩` is the injective functional `dual0`.** -/
theorem tau_pair (z : ↥(modelC.homology 8)) :
    (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8) tau z = dual0 z := by
  rw [← kronIso_spec]
  simp only [tau, LinearEquiv.apply_symm_apply]

theorem tau_pair_ne_zero {z : ↥(modelC.homology 8)} (hz : z ≠ 0) :
    (Work.Tubular.relKronH (TopCat.of (EuclideanSpace ℝ (Fin 8))) E8p 8) tau z ≠ 0 := by
  rw [tau_pair]
  intro h
  exact hz ((ConcreteCategory.bijective_of_isIso (e8.hom)).1 (by simpa [dual0, map_zero] using h))

end

end Work.ThomBordism.FrameSigns
