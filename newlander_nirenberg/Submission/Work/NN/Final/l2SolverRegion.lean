/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The uniform, region-parametric `L²`-solvability of `∂̄_{Jstd+A}`

`Work.NN.Final.C1aExistence` (`Submission/Work/NN/Final/l2ExistenceDefs.lean`) is the flat-model
uniform solvability statement of the project, with the *conclusion region* hard-wired to
`pd n ρ (21/10)`.  For the frame theorem `Work.NN.Final.FrameHol` — whose region is
`σ ≥ 13/5 + 1/400 = 2.6025` — that region is too small: the frame is needed on `pd n ρ σ` itself.
`UniformDbarL2 n α ρ σ` is the same statement with the conclusion region as a *parameter*; it is
the `L²`-form of the project's crux (the `C^{0,α}`-uniform Hill–Taylor / Kohn–Hörmander theorem
for a small perturbation of the standard structure), and it is what the `L²` route of
`NOTES_l2Solvability_obstruction.md` §61.5 delivers once its three gaps
`(KM)`, `(DENS)`, `(WEAK→CLASS)` are closed.

Everything else in the frame construction is region-flexible: `aPrioriEstimate_local_L2_flex`
(`Submission/Work/NN/Final/aPrioriFlex.lean`, PROVED) turns such an `L²`-solution into the
`C^{1,α}`-bound on any inner polydisc, and `dbarCn_smooth_local_pert`
(`Submission/Work/NN/Final/dbarCn_smooth_local_pert.lean`, PROVED) turns the `C¹` equation into
`C^k`-regularity on any strictly smaller polydisc, with the smallness/almost-complexity hypotheses
only on a polydisc.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Final

/-- **The uniform `L²`-solvability of `∂̄_{Jstd+A}` on the region `pd n ρ σ`.**

There are `C > 0` and a threshold `ε₀ > 0` such that for every perturbation `A` which is smooth,
componentwise `C^{0,α}`-small of size `ε ≤ ε₀` on `pd n ρ 4`, almost complex and integrable there,
and every smooth `J`-antilinear `J`-closed `(0,1)`-form `f` on `pd n ρ 4`, there is `u ∈ C¹(pd n ρ σ)`
solving `∂̄_{J}u = f` there, with the uniform `L²`-bound
`‖u‖_{L²(pd n ρ σ)} ≤ C · Σ_j ‖f·e_j‖_{C^{0,α}(pd n ρ 4)}`. -/
def UniformDbarL2 (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) (σ : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n),
      (∀ m : ℕ, ContDiff ℝ m A) →
      ∀ {ε : ℝ}, ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
        (pd n ρ 4) ≤ ENNReal.ofReal ε) →
      (∀ z, z ∈ pd n ρ 4 → ∀ v : Work.NN.Core.Cn n,
        (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
      (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
        ∀ z, z ∈ pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n,
          proj02 (Work.NN.Core.JstdCn n + A)
            (fun z' => dOne
              (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z') z V W = 0) →
      ∀ f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ,
        (∀ m : ℕ, ContDiff ℝ m f) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V : Work.NN.Core.Cn n,
          f z ((Work.NN.Core.JstdCn n + A) z V) = -Complex.I * f z V) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V W : Work.NN.Core.Cn n,
          proj02 (Work.NN.Core.JstdCn n + A) (fun z' => dOne f z') z V W = 0) →
        ∃ u : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 u (pd n ρ σ) ∧
          (∀ z, z ∈ pd n ρ σ → ∀ V : Work.NN.Core.Cn n,
            Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z V = f z V) ∧
          MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (pd n ρ σ))
            ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
                (fun z => f z (Pi.single j 1)) (pd n ρ 4)

end Work.NN.Final
