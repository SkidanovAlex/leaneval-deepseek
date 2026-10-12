import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.neuFrac_translate`

The Neumann-resolvent fraction `neuFrac ℓ a² u ψ` (`Work.BoseKinLoc.neuFrac`, the first piece of
FS `eq:DefT`) is **invariant under translating the box by its centre `ℓu`**, provided the state
is translated with it:

    `neuFrac ℓ a² u ψ = neuFrac ℓ a² 0 (ψ(ℓu + ·))`.

## Proof

`neuFrac` is the `sInf` of the trial values

`c_ψ(g) = ∫_{Λ(u)} ψ² − 2a²∫_{Λ(u)} ψ·g + a²·(Σ_k ∫_{Λ(u)} (∂_k g)² + a²∫_{Λ(u)} g²)`

over the globally smooth, compactly supported trials `g`.  The change of variables
`z ↦ ℓu + z` on the box (`Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube`, an identity for
Bochner integrals that holds **unconditionally**) turns each of the four integrals into its
`Λ(0) = acube ℓ` counterpart, with `∂_k` of the shifted trial
`g(ℓu + ·)` equal to the shift of `∂_k g` (`fderiv_comp_add_left`, also unconditional).  Hence

`c_{ψ(ℓu+·)}(g(ℓu+·)) = c_ψ(g)`

for every trial `g`, and since `g ↦ g(ℓu + ·)` is a bijection of the admissible trial class
(smoothness and compact support are preserved by translations), the two trial-value sets
coincide, and so do their infima.  No integrability hypothesis is needed: both sides of the
change of variables are junk-valued (`0`) in exactly the same way.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 1. The anchored box and the two shifts of admissible trials -/

/-- The anchored moving box `Λ(0)` is the centred cube `acube ℓ`. -/
lemma lamBox_zero_eq_acube (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

lemma contDiff_comp_addLeft {c : ℝ³} {g : ℝ³ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun z : ℝ³ => g (c + z) := by
  simpa [Function.comp_def] using hg.comp (contDiff_const.add contDiff_id)

lemma contDiff_comp_addRight {c : ℝ³} {g : ℝ³ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun z : ℝ³ => g (z + c) := by
  simpa [Function.comp_def] using hg.comp (contDiff_id.add contDiff_const)

lemma hasCompactSupport_comp_addLeft {c : ℝ³} {g : ℝ³ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport fun z : ℝ³ => g (c + z) := by
  simpa [Function.comp_def] using hg.comp_homeomorph (Homeomorph.addLeft c)

lemma hasCompactSupport_comp_addRight {c : ℝ³} {g : ℝ³ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport fun z : ℝ³ => g (z + c) := by
  simpa [Function.comp_def] using hg.comp_homeomorph (Homeomorph.addRight c)

/-! ## 2. The trial functional is transported by the box translation -/

/-- The trial functional of `neuFrac` at the translated data: shifting the box, the state and
the trial by `ℓu` does not change the value. -/
theorem neuFracTrialVal_translate (ℓ a2 : ℝ) (u : ℝ³) (ψ g : ℝ³ → ℝ) :
    Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g
      = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 0
          (fun z : ℝ³ => ψ (ℓ • u + z)) (fun z : ℝ³ => g (ℓ • u + z)) := by
  have hA : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
      = ∫ z in acube ℓ, (ψ (ℓ • u + z)) ^ 2 :=
    Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ u (fun z => (ψ z) ^ 2)
  have hB : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * g z)
      = ∫ z in acube ℓ, ψ (ℓ • u + z) * g (ℓ • u + z) :=
    Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ u (fun z => ψ z * g z)
  have hD : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)
      = ∫ z in acube ℓ, (g (ℓ • u + z)) ^ 2 :=
    Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ u (fun z => (g z) ^ 2)
  have hC : ∀ k : Fin 3,
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
        = ∫ z in acube ℓ,
            (fderiv ℝ (fun z : ℝ³ => g (ℓ • u + z)) z (kcStdBasis k)) ^ 2 := by
    intro k
    rw [Work.BoseKinLoc.Gap.setIntegral_lamBox_eq_acube ℓ u
      (fun z => (fderiv ℝ g z (kcStdBasis k)) ^ 2)]
    refine setIntegral_congr_fun (acube_measurable ℓ) (fun z _ => ?_)
    simp only [fderiv_comp_add_left]
  have hCsum : (∑ k : Fin 3,
        ∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ z in acube ℓ,
          (fderiv ℝ (fun z : ℝ³ => g (ℓ • u + z)) z (kcStdBasis k)) ^ 2 :=
    Finset.sum_congr rfl fun k _ => hC k
  unfold Work.BoseKinLoc.NeuFrac.neuFracTrialVal
  rw [lamBox_zero_eq_acube ℓ, hA, hB, hCsum, hD]

/-! ## 3. The translation of the box -/

theorem neuFrac_translate (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u ψ
      = Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z : EuclideanSpace ℝ (Fin 3) => ψ (ℓ • u + z)) := by
  have hkey : ∀ g : ℝ³ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 0 (fun z : ℝ³ => ψ (ℓ • u + z))
          (fun z : ℝ³ => g (ℓ • u + z))
        = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g :=
    fun g _ _ => (neuFracTrialVal_translate ℓ a2 u ψ g).symm
  have hset : {y : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        y = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 u ψ g}
      = {y : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        y = Work.BoseKinLoc.NeuFrac.neuFracTrialVal ℓ a2 0
              (fun z : ℝ³ => ψ (ℓ • u + z)) g} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨g, hg, hgs, hy⟩
      exact ⟨fun z : ℝ³ => g (ℓ • u + z), contDiff_comp_addLeft hg,
        hasCompactSupport_comp_addLeft hgs, hy.trans (hkey g hg hgs).symm⟩
    · rintro y ⟨h, hh, hhs, hy⟩
      set g : ℝ³ → ℝ := fun z => h (z + (-(ℓ • u))) with hgdef
      have hgdiff : ContDiff ℝ ∞ g := by
        simpa [hgdef] using contDiff_comp_addRight (c := -(ℓ • u)) hh
      have hgcs : HasCompactSupport g := by
        simpa [hgdef] using hasCompactSupport_comp_addRight (c := -(ℓ • u)) hhs
      refine ⟨g, hgdiff, hgcs, ?_⟩
      have hfun : (fun z : ℝ³ => g (ℓ • u + z)) = h := by
        funext z
        show h ((ℓ • u + z) + (-(ℓ • u))) = h z
        rw [show (ℓ • u + z) + (-(ℓ • u)) = z by abel]
      have hk := hkey g hgdiff hgcs
      rw [hfun] at hk
      exact hy.trans hk
  rw [Work.BoseKinLoc.NeuFrac.neuFrac_eq_sInf ℓ a2 u ψ,
    Work.BoseKinLoc.NeuFrac.neuFrac_eq_sInf ℓ a2 0 (fun z : ℝ³ => ψ (ℓ • u + z)), hset]

end Work.BoseKinLoc.Kinetic
