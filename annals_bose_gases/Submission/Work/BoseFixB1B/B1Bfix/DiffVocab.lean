import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.FibreAlg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix.DiffVocab`

Vocabulary for the two position/fibre-space inputs of the target
`Work.BoseFixB1B.B1Bfix.ampDiff_form_tendsto`:

* `slotDiffState` — the difference `Ψ_δ − Ψ_0` of the smooth approximant `Ψ_δ = cutProd (γ δ) ψ`
  and the sharp box state `Ψ_0 = sharpBoxState (dlBox L d u) ψ`;
* `DiffFibreFacts` — the fibre bookkeeping of that state: a.e. measurability of `Q_{B,i}Ψ`, a
  uniform pointwise bound on the box, smoothness of the windowed slot fibre in the slot position
  (in the two equivalent parametrisations `Function.update x i ·` and `kcInsN n i (·, r)`), and a
  uniform bound on the Dirichlet energy of the windowed slot fibre;
* `FibreDirDiffConv` — the position-space convergence: the summed fibre Dirichlet energy of the
  difference is `O(δ)`, hence tends to `0` as `δ → 0⁺`.

These are the two inputs (besides the already-proved `cutPlancherel_le`, `cutForm_fsKin_le`,
`cutAmplitude_integrable`, `cutFibreMass_facts`) from which `ampDiff_form_tendsto` is assembled.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.B1Bfix

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The difference state** `Ψ_δ − Ψ_0`: the smooth approximant of the sliding box minus the
sharp box state. -/
noncomputable def slotDiffState {n : ℕ} (L d : ℝ) (u : E3) (γ : E3 → ℝ)
    (ψ : Submission.BoseGases.X (n+1) → ℝ) : Submission.BoseGases.X (n+1) → ℝ :=
  fun x => Work.BoseFixB1B.cutProd γ ψ x
    - Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x

@[simp] theorem slotDiffState_apply {n : ℕ} (L d : ℝ) (u : E3) (γ : E3 → ℝ)
    (ψ : Submission.BoseGases.X (n+1) → ℝ) (x : Submission.BoseGases.X (n+1)) :
    slotDiffState L d u γ ψ x
      = Work.BoseFixB1B.cutProd γ ψ x
        - Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x := rfl

/-- **The fibre facts of the difference state.**  For every `δ > 0` and every slot `i` there is a
constant `C` (allowed to depend on `δ`) such that the mean-free projection `Q_{B,i}` of the
difference state is a.e. measurable, is bounded by `C` on the ambient box, has a windowed slot
fibre that is smooth in the slot position (both parametrisations), and has fibre Dirichlet energy
bounded by `C` uniformly over the ambient box. -/
def DiffFibreFacts {n : ℕ} (L d : ℝ) (u : E3) (ψ : Submission.BoseGases.X (n+1) → ℝ)
    (K Cb : ℝ) (γ : ℝ → E3 → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1), ∃ C : ℝ, 0 ≤ C ∧
    AEMeasurable
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ))
        MeasureTheory.volume ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L,
        |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ) x| ≤ C) ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L, ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
        Submission.BoseGases.chiB L d u z *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
            (Function.update x i z))) ∧
      (∀ r ∈ Submission.BoseGases.abox n L, ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
        Submission.BoseGases.chiB L d u z *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
            (Submission.BoseGases.kcInsN n i (z, r)))) ∧
      (∀ x ∈ Submission.BoseGases.abox (n+1) L,
        ∫ z : E3, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 =>
            Submission.BoseGases.chiB L d u y *
              Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Function.update x i y)) z (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ C)

/-- **The position-space convergence of the fibre Dirichlet energy of the difference state.**
The summed fibre Dirichlet energy of `Ψ_δ − Ψ_0` is `O(δ)` (hence tends to `0` as `δ → 0⁺`). -/
def FibreDirDiffConv {n : ℕ} (L d : ℝ) (u : E3) (ψ : Submission.BoseGases.X (n+1) → ℝ)
    (K Cb : ℝ) (γ : ℝ → E3 → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ i : Fin (n+1), Work.BoseFixB1B.fibreDirI L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ)) ≤ C * δ) ∧
    Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.fibreDirI L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)

end Work.BoseFixB1B.B1Bfix
