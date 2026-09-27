import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompSym.Basic
import Submission.Work.EKLCompSym.exists_perm_of_three
import Submission.Work.EKLCompSym.crossSection_preimage_iso
import Submission.Work.EKLCompSym.relCrossSection_map_iso
import Submission.Work.EKLCompSym.nonExceptional_map_iso
import Submission.Work.EKLCompSym.ergodic_map_iso

/-!
# The `S₃`-symmetry of EKL's low-entropy core

The low-entropy core `P_LowEntropyCore` is proved for the *distinguished* configuration
`(a,b,c) = (0,1,2)` of the three paper indices (the assembly `Work.EKLComp.core_012` and the
mathematics of EKL §4).  This module deduces the general case from it: given an instance of the
core for `(0,1,2)`, we obtain it for an arbitrary ordered triple of distinct indices.

The mechanism is the `S₃`-symmetry of the whole statement, realised by the permutation matrix
`σ.permMatrix ℝ` of the permutation `σ : Fin 3 ≃ Fin 3` sending `0,1,2` to `a,b,c`
(`Work.EKLCompSym.conjPerm`).  Conjugation by that matrix

* maps `Uij hab` to `Uij h01` (and the three factors of `Upar` accordingly, `Basic.lean`),
* maps `aPrime c s` to `aPrime 2 s`,
* preserves the neighbourhoods `V δ` and the centralisers `Lset`,
* preserves `Γ₃`, hence descends to a measurable bijection `iso σ` of `X₃`.

Pushing the measure `μ` forward along `iso σ` therefore turns the `(a,b,c)`-hypotheses on `μ`
into the `(0,1,2)`-hypotheses on `μ.map (iso σ)`, to which `h012` applies; pulling the conclusion
back gives `IsUInvariant μ (Uij hab)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.EKLCompSym

open Work.EKLContract MeasureTheory

/-- `U`-invariance is pulled back along the symmetry `iso τ` of `X₃`: if the push-forward is
invariant under `H.map (conjPerm τ)`, then `μ` is invariant under `H`.

This is the inverse direction of the equivariance `iso_smul`; it is *not* imported from the
sibling module `uInvariant_preimage_iso` because that module declares a helper `isoEquiv` that
clashes with the one declared in `nonExceptional_map_iso` when both are imported. -/
theorem uInvariant_preimage_iso' {μ : Measure X3} [IsProbabilityMeasure μ]
    (τ : Equiv.Perm (Fin 3)) {H : Subgroup SL3}
    (h : IsUInvariant (μ.map (iso τ)) (H.map (conjPerm τ))) : IsUInvariant μ H := by
  intro u hu
  have hu' : conjPerm τ u ∈ H.map (conjPerm τ) := ⟨u, hu, rfl⟩
  have hmp : MeasurePreserving (fun y : X3 => conjPerm τ u • y)
      (μ.map (iso τ)) (μ.map (iso τ)) := h (conjPerm τ u) hu'
  have hf : Measurable (fun x : X3 => u • x) := (continuous_const_smul u).measurable
  have hA : Measurable (fun y : X3 => conjPerm τ u • y) :=
    (continuous_const_smul (conjPerm τ u)).measurable
  refine ⟨hf, ?_⟩
  have hmap : Measure.map (fun y : X3 => conjPerm τ u • y) (Measure.map (iso τ) μ)
      = Measure.map (iso τ) μ := hmp.map_eq
  have hcomp : (fun y : X3 => conjPerm τ u • y) ∘ (iso τ)
      = (iso τ) ∘ (fun x : X3 => u • x) := by
    funext x
    simp only [Function.comp_apply]
    rw [iso_smul]
  have h1 : Measure.map ((fun y : X3 => conjPerm τ u • y) ∘ (iso τ)) μ
      = Measure.map (iso τ) μ := by
    rw [← Measure.map_map hA (measurable_iso τ), hmap]
  rw [hcomp, ← Measure.map_map (measurable_iso τ) hf] at h1
  exact (isoEquiv τ).map_measurableEquiv_injective h1

theorem core_general
    (h012 : ∀ {μ : MeasureTheory.Measure Work.EKLContract.X3}
      [MeasureTheory.IsProbabilityMeasure μ],
      Work.EKLContract.IsAErgodic μ →
      Work.EKLContract.RelCrossSection μ
        (Work.EKLContract.Upar Work.EKLComp.h01 Work.EKLComp.h02 Work.EKLComp.h21)
        (Work.EKLContract.Uij Work.EKLComp.h01) →
      ¬ Work.EKLContract.CrossSection μ (Work.EKLContract.Uij Work.EKLComp.h01) →
      Work.EKLContract.NonExceptional μ Work.EKLComp.h01 2 →
      Work.EKLContract.IsUInvariant μ (Work.EKLContract.Uij Work.EKLComp.h01))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hErg : Work.EKLContract.IsAErgodic μ)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hRel : Work.EKLContract.RelCrossSection μ
      (Work.EKLContract.Upar hab hac hcb) (Work.EKLContract.Uij hab))
    (hNCS : ¬ Work.EKLContract.CrossSection μ (Work.EKLContract.Uij hab))
    (hNE : Work.EKLContract.NonExceptional μ hab c) :
    Work.EKLContract.IsUInvariant μ (Work.EKLContract.Uij hab) := by
  classical
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := exists_perm_of_three hab hac hcb
  -- the inverse permutation sends `a,b,c` to `0,1,2`
  have hsa : σ⁻¹ a = 0 := by
    rw [Equiv.Perm.inv_def, ← hσ0, Equiv.symm_apply_apply]
  have hsb : σ⁻¹ b = 1 := by
    rw [Equiv.Perm.inv_def, ← hσ1, Equiv.symm_apply_apply]
  have hsc : σ⁻¹ c = 2 := by
    rw [Equiv.Perm.inv_def, ← hσ2, Equiv.symm_apply_apply]
  have hab' : σ⁻¹ a ≠ σ⁻¹ b := fun h => hab (σ⁻¹.injective h)
  have hac' : σ⁻¹ a ≠ σ⁻¹ c := fun h => hac (σ⁻¹.injective h)
  have hcb' : σ⁻¹ c ≠ σ⁻¹ b := fun h => hcb (σ⁻¹.injective h)
  -- the three root groups of the `(a,b,c)`-configuration map to those of `(0,1,2)`
  have hH : (Uij hab).map (conjPerm σ) = Uij h01 := by
    rw [Uij_map σ hab hab']
    exact Uij_congr hsa hsb hab' h01
  have hU : (Upar hab hac hcb).map (conjPerm σ) = Upar h01 h02 h21 := by
    rw [Upar_map σ hab hac hcb hab' hac' hcb']
    exact Upar_congr hsa hsb hsc hab' hac' hcb' h01 h02 h21
  -- the transported measure and the four transported hypotheses
  haveI hprob : IsProbabilityMeasure (μ.map (iso σ)) :=
    inferInstance
  have hErg' : IsAErgodic (μ.map (iso σ)) := ergodic_map_iso hErg σ
  have hRel' : RelCrossSection (μ.map (iso σ)) (Upar h01 h02 h21) (Uij h01) := by
    rw [← hU, ← hH]
    exact relCrossSection_map_iso σ hRel
  have hNCS' : ¬ CrossSection (μ.map (iso σ)) (Uij h01) := by
    rw [← hH]
    exact fun h => hNCS (crossSection_preimage_iso σ h)
  have hNE' : NonExceptional (μ.map (iso σ)) h01 2 := by
    have h := nonExceptional_map_iso σ hab hab' hNE
    exact (NonExceptional_congr hsa hsb hsc hab' h01).mp h
  -- apply the distinguished-configuration core and pull the conclusion back
  have key : IsUInvariant (μ.map (iso σ)) (Uij h01) := h012 hErg' hRel' hNCS' hNE'
  rw [← hH] at key
  exact uInvariant_preimage_iso' σ key

end Work.EKLCompSym
