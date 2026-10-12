import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.B1Bfix

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- The product approximant `cutProd γ ψ = (∏ i, γ (x i))·ψ` is `C^∞` when `γ` and `ψ` are. -/
private theorem contDiff_cutProd' {k : ℕ} {γ : E3 → ℝ} {ψ : Submission.BoseGases.X k → ℝ}
    (hγ : ContDiff ℝ (⊤ : ENat) γ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseFixB1B.cutProd γ ψ) := by
  change ContDiff ℝ (⊤ : ENat)
    (fun x : Submission.BoseGases.X k => (∏ i : Fin k, γ (x i)) * ψ x)
  fun_prop

/-- **Integrability of the slot `p`-form of the smooth approximants.**

`Ψ_δ = cutProd (γ δ) ψ = (∏ᵢ γ_δ(xᵢ))·ψ` is the smooth approximation of the sharp box state
`1_{B(u)^k}·ψ` attached to the cut family `γ` of `Work.BoseFixB1B.IsCutFamily L d u K γ`
(support in `B(u) = dlBox L d u`, values in `[0,1]`, equal to `1` off the `δ`-collar, derivative
bound `K/δ`).  For every `δ > 0` the state `Ψ_δ` is `C^∞` with compact support in the box, so its
windowed slot amplitude satisfies the uniform `(1+‖p‖)⁻³` decay estimate of
`Work.SmallBoxTBWord.tBamp_decay`; the `p`-integrand of the slot form is then integrable by
`Work.BoseFixB1B.slotFormL_integrable_of_decay` (in `Submission/Work/BoseFixB1B/B1Bfix/Basic.lean`).

Intended route: derive the uniform-in-`x ∈ abox` decay bound
`‖tBamp (chiB L d u) p (boxQ (boxMass L d u) (dlBox L d u) i Ψ_δ) i x‖ ≤ C_δ/(1+‖p‖)³`
from `Work.SmallBoxTBWord.tBamp_decay` (which needs only `ContDiff ℝ ⊤ Ψ_δ`, i.e.
`cutProd (γ δ) ψ` with `γ δ` smooth — the `K/δ`-blow-up of the derivatives of `γ δ` affects the
*constant* `C_δ`, which is allowed to depend on `δ`, since only the integrability at each fixed
`δ` is claimed); then apply `slotFormL_integrable_of_decay` with the measurability of
`p ↦ slotY …` (continuity of the amplitude in `(p,x)`). -/
theorem cut_slotForm_integrable {n : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {K : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ) :
    ∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1),
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) p) := by
  intro δ hδ i
  -- Smoothness of the cutoff and of the approximant `Ψ_δ = cutProd (γ δ) ψ`.
  have hγδ : ContDiff ℝ (⊤ : ENat) (γ δ) := (hcut.2 δ hδ).1
  have hΨcd : ContDiff ℝ (⊤ : ENat) (Work.BoseFixB1B.cutProd (γ δ) ψ) :=
    contDiff_cutProd' hγδ hψ
  have hχcd : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.contDiff_chiB hL hd u
  have hχcs : HasCompactSupport (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u
  have hB : IsCompact (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxTBWord.isCompact_dlBox hL hd u
  -- Smoothness of the projected state `Q_{B,i}Ψ_δ`.
  have hΦcd : ContDiff ℝ (⊤ : ENat)
      (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ)) :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact hB (Work.SmallBoxSliding.boxMass L d u) i hΨcd
  -- The uniform `(1+‖p‖)⁻³` decay of the windowed amplitude on the box.
  obtain ⟨C, _hC0, hC⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n+1) hL hχcd hχcs hΦcd
  -- Measurability of `p ↦ slotY …`, from the continuity of the parametric integral.
  have hYm : AEMeasurable (fun p : E3 =>
      Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) p) volume := by
    have hcont : Continuous (fun p : E3 =>
        Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) p) := by
      rw [show (fun p : E3 => Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) p)
          = fun p : E3 => (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
                (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                  (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ)) i x‖ ^ 2
          from rfl]
      exact continuous_const.mul (Work.SmallBoxTBWord.continuous_integral_tBamp_sq hL
        hχcd.continuous hχcs hΦcd.continuous i)
    exact hcont.aemeasurable
  exact Work.BoseFixB1B.slotFormL_integrable_of_decay (a := L) (c := c) (Cdec := C) hL i hYm
    (fun p x hx => hC x hx i p)

end

end Work.BoseFixB1B.B1Bfix
