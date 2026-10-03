import Mathlib
import Submission.Work.KMTAreas.A7Hi2.dilPerturbVar
import Submission.Work.KMTAreas.A7Hi2.schwartzDilateMass
import Submission.Work.KMTAreas.A7Hi2.dilVarRealScale_of_perturb
import Submission.Work.A7Hi2.SieveDefs

/-!
# The real-scale lacunary dilation variational estimate: the composition

The real-scale JSW estimate (JSW Theorem 1.1 for real lacunary scales) is assembled here from the
four bricks

* `Work.KMTAreas.A7Hi2.roundRealScale` — the floor rounding `c n := ⌊σ n⌋` of a real lacunary
  sequence (`Submission/Work/KMTAreas/A7Hi2/dilVarRealScale.lean`),
* `Work.KMTAreas.A7Hi2.dilPerturbVar` — the perturbation (difference) half,
* `Work.KMTAreas.A7Hi2.schwartzDilateMass` — the Schwartz `ℓ¹`-mass bound,
* `Work.KMTAreas.A7Hi2.dilVarRealScale_of_perturb` — the assembly socket,

together with the *proved* integer-scale `Work.KMTAreas.A7Hi.DilVarClean` (applied to `⌊σ⌋`) and
`PointwiseErgodicTheorems.variationalNorm_add_le`.

This module is separate from `…/dilVarRealScale.lean` because the socket imports that file (for
`roundRealScale`), so composing there would create an import cycle.  The final theorem
`Work.KMTAreas.A7Hi2.dilVarRealScale` is *verbatim* the `Prop` `Work.A7Hi2.DilVarRealScale` fixed in
`Submission/Work/A7Hi2/SieveDefs.lean`, whose sieve (decimated-dilation) decomposition of the
Ionescu--Wainger comb consumes it; `dilVarRealScale_prop` records that interface.
-/

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The real-scale lacunary dilation variational estimate** (JSW Theorem 1.1 for real lacunary
scales): for `1 < p`, `2 < r` and a Schwartz kernel `K` there is `C > 0` such that for every real
sequence `σ` with `1 ≤ σ n` and `2 σ n ≤ σ (n+1)` and every `f : ℤ → ℂ`,

  `‖ Vʳ (n ↦ Σ'_j (1/σ n) K (j/σ n) · f (x − j)) ‖_{ℓᵖ(ℤ)} ≤ C ‖f‖_{ℓᵖ(ℤ)}`. -/
theorem dilVarRealScale (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / σ n) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count :=
  Work.KMTAreas.A7Hi2.dilVarRealScale_of_perturb K
    (Work.KMTAreas.A7Hi2.schwartzDilateMass K)
    (fun p hp r hr => Work.KMTAreas.A7Hi2.dilPerturbVar p hp r hr K) p hp r hr

/-- **The interface to the sieve decomposition**: the `Prop` `Work.A7Hi2.DilVarRealScale` fixed in
`Submission/Work/A7Hi2/SieveDefs.lean` (the real-scale form of `A7Hi.DilVarClean` / JSW needed by
the sieve decomposition of the Ionescu--Wainger comb) follows from `dilVarRealScale`. -/
theorem dilVarRealScale_prop : Work.A7Hi2.DilVarRealScale :=
  fun p hp r hr K => dilVarRealScale p hp r hr K

end

end Work.KMTAreas.A7Hi2
