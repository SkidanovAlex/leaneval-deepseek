import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.neuFracTrialDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.BoxAux` — box facts for the `neuFrac` trial functional

The Neumann-resolvent fraction `neuFrac ℓ a² u φ` (`FS eq:DefT`'s first term) is the `sInf`
of the Dirichlet trial functional

`T(φ,g) = ∫_{Λ} φ² − 2a²∫_{Λ} φ g + a²(Σ_k∫_{Λ}(∂_k g)² + a²∫_{Λ} g²)`,   `Λ = lamBox ℓ u`,

over globally smooth compactly supported trials `g` (`Work.BoseKinLoc.Kinetic.trialVal`).
This module collects the *elementary box analysis* that every algebra with `T` and
`neuFrac` needs, in the form used by the polarisation computation
(`Work.BoseFixB2.Polar.trialVal_parallelogram`) and by the parallelogram identity for
`neuFrac` (`Work.BoseFixB2.Polar.neuFrac_parallelogram`):

* `isCompact_lamBox` — the moving box `Λ(u) = ℓu + acube ℓ` is compact for `ℓ > 0`;
* `integrableOn_sq_of_continuous` — squares of continuous functions are integrable over
  the box (the box has finite measure and every integrand is continuous);
* `neuFrac_le_trialVal_of_integrableOn` — the one-sided variational inequality, in the
  form that only needs `φ²` integrable **on the box** (`Kinetic.bddBelow_trialSet_of_integrableOn'`);
* `contDiff_add_sub_*`, `hasCompactSupport_add_sub_*` — the trial class (smooth + compactly
  supported) is closed under `+` and `−`, which is what makes the change of variables
  `(A,B) ↦ (A+B, A−B)` of the parallelogram argument a bijection of the trial class.

Everything here is `sorry`-free and independent of the polarisation computation.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The moving box is compact.**  `lamBox ℓ u = ℓ • u + acube ℓ` is a translate of the
centred cube `acube ℓ`, which is compact as soon as `ℓ > 0`
(`Submission.BoseGases.acube_compact`). -/
lemma isCompact_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    IsCompact (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u
      = (fun z : ℝ³ => ℓ • u + z) '' Submission.BoseGases.acube ℓ := by
    ext x
    simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx; exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [h]
  exact (Submission.BoseGases.acube_compact hℓ).image (continuous_const.add continuous_id)

/-- **Squares of continuous functions are integrable over the moving box.**  The box is a
compact set, hence of finite measure, and `z ↦ (φ z)²` is continuous. -/
lemma integrableOn_sq_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : Continuous φ) :
    MeasureTheory.IntegrableOn (fun z : ℝ³ => (φ z) ^ 2) (Work.BoseKinLoc.lamBox ℓ u) :=
  ContinuousOn.integrableOn_compact (isCompact_lamBox hℓ u) (hφ.continuousOn.pow 2)

/-- **The upper-bound direction of the variational principle for `neuFrac`.**

The `sInf` defining `neuFrac ℓ a² u φ` is dominated by the trial value `T(φ,g)` of *every*
admissible trial `g` (smooth, compactly supported), under the box-restricted `L²` hypothesis
on `φ` — the precise hypothesis making the defining trial set bounded below
(`Kinetic.bddBelow_trialSet_of_integrableOn'`).  This is the one-sided inequality that turns
`T` into an upper bound for `neuFrac`; its companion (the reverse inequality) is the exact
resolvent computation, not needed here. -/
lemma neuFrac_le_trialVal_of_integrableOn {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ g : ℝ³ → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : ℝ³ => (φ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)))
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgs : HasCompactSupport g) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ ≤ Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u φ g := by
  rw [Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialSet]
  exact csInf_le (Work.BoseKinLoc.Kinetic.bddBelow_trialSet_of_integrableOn' ha2 u hφ)
    ⟨g, hg, hgs, rfl⟩

/-! ## Closure of the trial class

The trial class `C` of `neuFrac` (globally smooth, compactly supported functions) is a real
vector space, which is what makes the change of variables `(A,B) ↦ (A+B, A−B)` of the
parallelogram argument a bijection of `C × C`.  Only the halved combinations
`(A±B)/2` — which invert that change of variables — need to be named. -/

/-- `(A+B)/2` is an admissible trial when `A`, `B` are. -/
lemma contDiff_half_sum {A B : ℝ³ → ℝ} (hA : ContDiff ℝ (⊤ : ENat) A)
    (hB : ContDiff ℝ (⊤ : ENat) B) :
    ContDiff ℝ (⊤ : ENat) (fun z => (A z + B z) / 2) :=
  (hA.add hB).div_const 2

/-- `(A−B)/2` is an admissible trial when `A`, `B` are. -/
lemma contDiff_half_diff {A B : ℝ³ → ℝ} (hA : ContDiff ℝ (⊤ : ENat) A)
    (hB : ContDiff ℝ (⊤ : ENat) B) :
    ContDiff ℝ (⊤ : ENat) (fun z => (A z - B z) / 2) :=
  (hA.sub hB).div_const 2

/-- `(A+B)/2` has compact support when `A`, `B` do. -/
lemma hasCompactSupport_half_sum {A B : ℝ³ → ℝ} (hA : HasCompactSupport A)
    (hB : HasCompactSupport B) : HasCompactSupport (fun z => (A z + B z) / 2) :=
  (hA.add hB).comp_left (g := fun t : ℝ => t / 2) (by simp)

/-- `(A−B)/2` has compact support when `A`, `B` do. -/
lemma hasCompactSupport_half_diff {A B : ℝ³ → ℝ} (hA : HasCompactSupport A)
    (hB : HasCompactSupport B) : HasCompactSupport (fun z => (A z - B z) / 2) :=
  (hA.sub hB).comp_left (g := fun t : ℝ => t / 2) (by simp)

end Work.BoseFixB2.Polar
