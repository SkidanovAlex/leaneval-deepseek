import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet
import Submission.Work.BoseKinLoc.NeuFrac.exists_box_bump
import Submission.Work.BoseKinLoc.NeuFrac.trial_value_mul_eq
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.neuFrac_le_box_of_integrableSq`

The one-sided variational inequality for `neuFrac` against a trial `θ` that need not be
compactly supported — it is invisible outside the box `Λ(u) = lamBox ℓ u` because every
integral in the functional is taken over `Λ(u)` — **under the hypothesis that `ψ` is square
integrable on `ℝ³`**.

## Why the integrability hypothesis is needed (the requested `neuFrac_le_box` is false)

`neuFrac ℓ a2 u ψ` is the `sInf` of the trial values

`c(g) = ∫_Λ ψ² − 2a2∫_Λ ψ·g + a2·(Σ_k ∫_Λ (∂_k g)² + a2·∫_Λ g²)`,  `g` smooth, compactly
supported.

Two Lean conventions then matter:

* the integral of a **non-integrable** real function is `0` (`MeasureTheory.integral_undef`),
  so for `ψ ∉ L²(Λ)` the term `∫_Λ ψ²` is `0`, not the (infinite) genuine value: the
  functional loses the coercivity that makes it bounded below;
* `sInf` of a set that is **not bounded below** is `0` in `ℝ`
  (`Real.sInf_of_not_bddBelow`), and `csInf_le` — the only tool turning `c(g) ∈ S` into
  `sInf S ≤ c(g)` — needs `BddBelow S`.

Both failures occur simultaneously for `ψ ∈ L¹(Λ) \ L²(Λ)` with `ψ ∉ H^{-1}(Λ)`: take
`ψ(x) = ‖x − c‖^(-8/3)` with `c` the centre of the box (`8/3 ∈ (5/2, 3)`, so `ψ ∈ L¹` but
`ψ² ∉ L¹` and the source `ψ` is not `H^{-1}`).  With a bump `η`, `η(0) = 1`, and
`φ_ε(x) = η((x−c)/ε)` one has `∫_Λ ψ·φ_ε = ε^{1/3}K` (`K > 0`), `∫_Λ φ_ε² ≍ ε³` and
`Σ_k∫_Λ (∂_kφ_ε)² ≍ ε`, so the quadratic `t ↦ c(t·φ_ε)` attains the minimum
`−a2·K²·ε^{−1/3}/(C₁ + a2ε²C₂) → −∞`: the trial set is unbounded below, hence
`neuFrac ℓ a2 u ψ = 0`.  Taking `θ ≡ 1` the right-hand side is
`0 − 2a2·M + a2·(0 + a2·|Λ|)` with `M = ∫_Λ ψ > 0`, which is **negative** for small `a2`.
So the requested statement `neuFrac_le_box` fails; `hψ` below is the missing hypothesis
(and is automatic in the corpus, where `ψ` is smooth with compact support — the only case
used by `NeumannBound`).

## Contents

* `neuFrac_le_trial_of_integrableSq` — the trial inequality for an *admissible* `g`;
* `neuFrac_le_box_of_integrableSq` — the same for a smooth `θ` together with a bump `η`
  that equals `1` on a neighbourhood of the box (`exists_box_bump`), the trial `η·θ` being
  admissible and its value being the displayed right-hand side (`trial_value_mul_eq`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The trial inequality for `neuFrac`** under `ψ ∈ L²`: for every smooth compactly
supported `g`, `neuFrac` is at most the value of the variational functional at `g`.
(`NeuFrac` is an `sInf` over these trials, so this is `csInf_le`; it requires `BddBelow` of
the trial set, which `bddBelow_trialSet` supplies from `hψ`.) -/
lemma neuFrac_le_trial_of_integrableSq {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : Integrable (fun z : ℝ³ => (ψ z) ^ 2)) {g : ℝ³ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    Work.BoseKinLoc.neuFrac ℓ a2 u ψ ≤
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * g z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) :=
  csInf_le (bddBelow_trialSet (ℓ := ℓ) ha2 u hψ) ⟨g, hg, hgs, rfl⟩

/-- **The correct form of `neuFrac_le_box`.**  The Neumann-resolvent fraction is dominated
by the value of the variational functional at any smooth `θ`, with the *only* extra
hypothesis that `ψ` be square integrable (which is what makes the `sInf` defining `neuFrac`
bounded below — see the module docstring: the un-hypothesised statement is false).

The trial is `η·θ` with `η` a bump equal to `1` near the box: `η·θ` is admissible (the box is
bounded, `exists_box_bump`) and its value equals the displayed right-hand side because
`η·θ` and `θ` agree, together with their derivatives, on `Λ(u)` (`trial_value_mul_eq`). -/
theorem neuFrac_le_box_of_integrableSq {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) (u : ℝ³)
    (ψ θ : ℝ³ → ℝ) (hθ : ContDiff ℝ ⊤ θ)
    (hψ : Integrable (fun z : ℝ³ => (ψ z) ^ 2)) :
    Work.BoseKinLoc.neuFrac ℓ a2 u ψ ≤
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * θ z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (θ z) ^ 2)) := by
  obtain ⟨R, η, hbox, hηdiff, hηcs, hη1⟩ := exists_box_bump ℓ u
  -- `η·θ` is an admissible trial: smooth and compactly supported.
  have hadm : ContDiff ℝ ∞ (fun z : ℝ³ => η z * θ z) :=
    hηdiff.mul (hθ.of_le (le_top : (∞ : ℕ∞ω) ≤ ⊤))
  have hcs : HasCompactSupport (fun z : ℝ³ => η z * θ z) := hηcs.mul_right
  -- its value is the displayed right-hand side
  have hval : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * (η z * θ z))
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ (fun z : ℝ³ => η z * θ z) z
                    (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (η z * θ z) ^ 2))
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * θ z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (θ z) ^ 2)) :=
    trial_value_mul_eq hbox hη1
  refine csInf_le (bddBelow_trialSet (ℓ := ℓ) ha2 u hψ) ⟨fun z : ℝ³ => η z * θ z,
    hadm, hcs, hval.symm⟩

/-- **Drop-in form of `neuFrac_le_box`** for the corpus's actual setting: `ψ` smooth with
compact support (as in `NeumannBound`), where square integrability is immediate.  The
argument list is that of the requested `neuFrac_le_box` followed by `hψ hcs`. -/
theorem neuFrac_le_box_of_contDiff {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) (u : ℝ³)
    (ψ θ : ℝ³ → ℝ) (hθ : ContDiff ℝ ⊤ θ)
    (hψ : ContDiff ℝ ⊤ ψ) (hcs : HasCompactSupport ψ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u ψ ≤
      (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * θ z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (θ z) ^ 2)) :=
  neuFrac_le_box_of_integrableSq hℓ ha2 u ψ θ hθ
    (Continuous.integrable_of_hasCompactSupport (hψ.continuous.pow 2)
      (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)))

end Work.BoseKinLoc.NeuFrac
