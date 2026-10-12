import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.Winchk
import Submission.Work.BoseFixB1B.B1Bfix.DiffVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.SmallBVocab` — the cube-window vocabulary of the port

The two `Prop`s of `Submission.Work.BoseFixB1B.B1Bfix.DiffVocab` (`DiffFibreFacts`,
`FibreDirDiffConv`) state the fibre bookkeeping and the position-space Dirichlet convergence of the
difference state `slotDiffState L d u (γ δ) ψ = cutProd (γ δ) ψ − sharpBoxState (dlBox L d u) ψ`
at the **ball** window `chiB L d u`.  This module twins them at the **cube** window
`chiSmallB M L d u` (definitions only), so that the port of the sharp-fibre convergence chain can
be stated against them:

* `DiffFibreFactsS L d M u ψ K Cb γ` — for every `δ > 0` and slot `i` there is `C ≥ 0` such that
  the box-mean-free slot projection of the difference state is a.e. measurable, bounded on the
  ambient box, has a `chiSmallB`-windowed slot fibre that is `C³` in the slot position in both
  parametrisations, and has fibre Dirichlet energy at most `C` on the box;
* `FibreDirDiffConvS L d M u ψ K Cb γ` — the summed `chiSmallB`-weighted fibre Dirichlet energy of
  the difference is `O(δ)` and tends to `0`.

Both are the *same bodies* as their ball-window twins with `chiB L d u ↦ chiSmallB M L d u` and the
regularity parameter `M` (with `4 ≤ M` where the `C³` window is needed).  Proving them is the
"fibre-Dirichlet" half of the port; see `RECIPE_port_chiSmallB.md`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.PortSmallB

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The fibre facts of the difference state at the cube window** — the cube twin of
`Work.BoseFixB1B.B1Bfix.DiffFibreFacts`. -/
def DiffFibreFactsS {n : ℕ} (L d : ℝ) (M : ℕ) (u : E3) (ψ : X (n+1) → ℝ) (K Cb : ℝ)
    (γ : ℝ → E3 → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1), ∃ C : ℝ, 0 ≤ C ∧
    AEMeasurable
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ))
        MeasureTheory.volume ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L,
        |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ) x| ≤ C) ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L, ContDiff ℝ 3 (fun z : E3 =>
        Submission.BoseGases.chiSmallB M L d u z *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ) (Function.update x i z))) ∧
      (∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ 3 (fun z : E3 =>
        Submission.BoseGases.chiSmallB M L d u z *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ)
            (Submission.BoseGases.kcInsN n i (z, r)))) ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L,
        ∫ z : E3, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 =>
            Submission.BoseGases.chiSmallB M L d u y *
              Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ) (Function.update x i y))
            z (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ C)

/-- **The position-space convergence of the fibre Dirichlet energy at the cube window** — the cube
twin of `Work.BoseFixB1B.B1Bfix.FibreDirDiffConv`. -/
def FibreDirDiffConvS {n : ℕ} (L d : ℝ) (M : ℕ) (u : E3) (ψ : X (n+1) → ℝ) (K Cb : ℝ)
    (γ : ℝ → E3 → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ)) ≤ C * δ) ∧
    Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i
        (Work.BoseFixB1B.B1Bfix.slotDiffState L d u (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)

end Work.BoseB1Cube.PortSmallB
