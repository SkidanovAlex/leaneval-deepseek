import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.fsT_nonneg_of_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.kinFormB_nonneg` — the box-restricted kinetic word is nonnegative

FS `eq:Def_HB` writes the localised box Hamiltonian as a quadratic form; its kinetic part,
restricted to the box `abox n ℓ` at the anchored translation `u = 0`, is

`kinFormB n ℓ d s ε_T b Φ = ℓ⁻³ Σᵢ ∫_{abox n ℓ} 1_{Λ(0)}(xᵢ) · 𝒯(fibreᵢΦ_x)`.

This file proves `0 ≤ kinFormB n ℓ d s ε_T b Φ` for every smooth symmetric box state
`Φ : BoxState n ℓ`.  No hypothesis on the state beyond smoothness is used, and the
parameters only need `ℓ > 0`, `d > 0`, `s > 0`, `0 ≤ ε_T ≤ 1`, `b ≥ 0` — exactly the
regime of FS's kinetic word.

## The proof

All three factors are nonnegative:

* the prefactor `ℓ⁻³ ≥ 0` (`zpow_nonneg` of `hℓ.le`);
* each of the `n` summands is the integral of a **pointwise** nonnegative integrand over
  the restricted measure `volume.restrict (abox n ℓ)` (`integral_nonneg`): the box indicator
  `indU ℓ 0 (xᵢ)` is `0` or `1`, and the one-body word `𝒯(fibreᵢΦ_x)` is nonnegative on the
  fibre `z ↦ Φ(x with xᵢ = z)`, which is continuous because `Φ` is smooth
  (`fsT_nonneg_of_continuous`, which needs only continuity of the fibre).  Note that no
  integrability of the fibre word is needed: `integral_nonneg` only asks for pointwise
  nonnegativity.
* a finite sum of nonnegatives is nonnegative (`Finset.sum_nonneg`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Word

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Continuity of the coordinate-update map and of the fibres -/

/-- Replacing the `i`-th coordinate is a continuous operation. -/
lemma kinFormB_continuous_update {n : ℕ} (x : Submission.BoseGases.X n) (i : Fin n) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => Function.update x i z) := by
  refine continuous_pi fun j => ?_
  simp only [Function.update_apply]
  split_ifs
  · exact continuous_id
  · exact continuous_const

/-- The `i`-th coordinate fibre of a continuous `n`-body state is continuous. -/
lemma kinFormB_fibre_continuous {n : ℕ} (i : Fin n) (x : Submission.BoseGases.X n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Continuous (Work.BoseKinLoc.fibre n i Φ x) :=
  hΦ.comp (kinFormB_continuous_update x i)

/-- The indicator of the moving box is nonnegative. -/
lemma kinFormB_indU_nonneg (ℓ : ℝ) (u z : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.BoseKinLoc.indU ℓ u z := by
  rw [Work.BoseKinLoc.indU]
  exact Set.indicator_nonneg (fun a _ => zero_le_one) z

/-! ## 2. The theorem -/

/-- **The box-restricted kinetic word of FS `eq:Def_HB` is nonnegative.** -/
theorem kinFormB_nonneg {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    0 ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ := by
  have hcont : Continuous ((Φ : Work.BoseKinLoc.BoxState n ℓ) : Submission.BoseGases.X n → ℝ) :=
    Φ.contDiff.continuous
  unfold Work.BoseKinLoc.kinFormB
  refine mul_nonneg (zpow_nonneg hℓ.le _) (Finset.sum_nonneg fun i _ => ?_)
  refine integral_nonneg fun x => ?_
  exact mul_nonneg (kinFormB_indU_nonneg ℓ 0 (x i))
    (fsT_nonneg_of_continuous hℓ hd hs hεT hεT1 hb 0 (kinFormB_fibre_continuous i x hcont))

end Work.BoseKinLoc.Word
