import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.Basic
import Submission.Work.BoseFixB1B.B1Bfix.FibreAlg
import Submission.Work.BoseFixB1B.fibreSideConditions_cut
import Submission.Work.SmallBoxTBWord.stronglyMeasurable_tBamp
import Submission.Work.SmallBoxTBWord.tBamp_norm_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix.slotAmp_x_integrable`

The `x`-integrability of the squared windowed slot amplitudes of the two states of the sharp-fibre
program (`Ψ_δ = cutProd (γ δ) ψ` for `0 < δ` and `Ψ₀ = sharpBoxState (dlBox L d u) ψ`).

The lemma is the `x`-level bookkeeping of the assembly of `Work.BoseFixB1B.tendsto_tBdiagFormInd_cut`:
it legitimises the arithmetic (`MeasureTheory.integral_sub`, `integral_mono`) of the slot forms at
every fixed `δ`.

## Route

Every slot amplitude is `slotAmpF a A volA χ i v p x = tBamp χ p (boxQ volA A i v) i x`
(by definition), so it suffices to prove, for a state `v` that is *measurable* and *bounded by
`Cb`* on the ambient box:

* `boxQ volA A i v` is measurable (`Work.BoseFixB1B.measurable_boxQ`) and bounded by `2·Cb` on the
  box (`Work.BoseFixB1B.abs_boxQ_le_two`; here `A = dlBox L d u ⊆ acube L` and
  `volA = boxMass L d u = volume.real A`);
* hence the amplitude is strongly measurable in `x`
  (`Work.SmallBoxTBWord.stronglyMeasurable_tBamp`: it is the parametric `z`-integral of the jointly
  strongly measurable integrand `(x,z) ↦ χ z·e^{-i⟪p,z⟫}·Φ(x_{i←z})`, by
  `StronglyMeasurable.integral_prod_right'`) and bounded on the box by
  `χsup²·(2·Cb)·|tsupport χ|` (`Work.SmallBoxTBWord.tBamp_norm_le_of_bound`: the integrand vanishes
  off `tsupport χ ⊆ acube L`, where the updated configuration stays inside the ambient box);
* the ambient box has finite measure, so `MeasureTheory.Integrable.of_bound` closes.

The two states are measurable (a smooth product, resp. the sharp indicator of the measurable set
`dlBox L d u` times the smooth `ψ`) and bounded by `Cb` on the box (`abs_cutProd_le`, resp.
`abs_sharpBoxState_le`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.B1Bfix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

/-! ## The `x`-integrability for an arbitrary measurable bounded state -/

/-- **The squared slot amplitude of any measurable state bounded on the box is integrable.**

`v` is the state; only its measurability and its bound `Cb` on the ambient box are used.  The
window is the sliding cutoff `χ_{B(u)} = chiB L d u`, the box is `B(u) = dlBox L d u` and the
normalisation is its volume `boxMass L d u = volume.real (dlBox L d u)`. -/
private theorem integrable_sq_slotAmpF_of_state {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : E3) {v : Submission.BoseGases.X (n+1) → ℝ} (hvm : Measurable v) {Cb : ℝ}
    (hCb : 0 ≤ Cb)
    (hvb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |v x| ≤ Cb) (i : Fin (n+1)) (p : E3) :
    Integrable (fun x : Submission.BoseGases.X (n+1) =>
      ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i v p x‖ ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n+1) L)) := by
  have hAc : Submission.BoseGases.dlBox L d u ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hvolA : Work.SmallBoxSliding.boxMass L d u
      = volume.real (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal L d u
  have hχc : Continuous (Submission.BoseGases.chiB L d u) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous
  -- measurability and boundedness of the mean-free projection
  have hQm : Measurable (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
      (Submission.BoseGases.dlBox L d u) i v) :=
    Work.BoseFixB1B.measurable_boxQ (A := Submission.BoseGases.dlBox L d u)
      (Work.SmallBoxSliding.boxMass L d u) i hvm
  have hQb : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i v x| ≤ 2 * Cb :=
    Work.BoseFixB1B.abs_boxQ_le_two hL.le hAc hvolA hCb hvb
  -- the amplitude bound and its strong measurability
  have hbd : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i v) i x‖
        ≤ Submission.BoseGases.chiSup ^ 2 * (2 * Cb)
            * volume.real (tsupport (Submission.BoseGases.chiB L d u)) :=
    fun x hx => Work.SmallBoxTBWord.tBamp_norm_le_of_bound
      (χ := Submission.BoseGases.chiB L d u) (Cχ := Submission.BoseGases.chiSup ^ 2)
      (M := 2 * Cb) (pow_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) 2)
      (fun z _ => Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z)
      (Work.SmallBoxTBWord.tsupport_chiB_subset_acube hL hd u) hQb i p (x := x) hx
  have hsm : StronglyMeasurable (fun x : Submission.BoseGases.X (n+1) =>
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i v) i x‖ ^ 2) :=
    (Work.SmallBoxTBWord.stronglyMeasurable_tBamp hχc hQm i p).norm.pow 2
  haveI : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X (n+1))).restrict
        (Submission.BoseGases.abox (n+1) L)) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (Submission.BoseGases.abox_compact (n+1) hL).measure_lt_top)
  refine Integrable.of_bound ?_ ((Submission.BoseGases.chiSup ^ 2 * (2 * Cb)
      * volume.real (tsupport (Submission.BoseGases.chiB L d u))) ^ 2) ?_
  · exact hsm.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (Submission.BoseGases.abox_isClosed (n+1) L).measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa only [Work.BoseFixB1B.slotAmpF_apply] using hbd x hx

/-- **The `x`-integrability of the squared slot amplitudes of the two states.**

The windowed slot amplitudes `x ↦ slotAmpF L (dlBox L d u) (boxMass L d u) (chiB L d u) i
(cutProd (γ δ) ψ) p x` (for `0 < δ`) and `x ↦ slotAmpF … i (sharpBoxState (dlBox L d u) ψ) p x`
are — for every frequency `p` and every slot `i` — square-integrable over the ambient box
`abox (n+1) L`.  This is the `x`-level bookkeeping that legitimises the arithmetic
(`MeasureTheory.integral_sub`, `integral_mono`) of the slot forms at each fixed `δ`.

Intended route:

* joint measurability of `(p,x) ↦ slotAmpF … p x`: the amplitude is the `z`-integral of the
  jointly measurable integrand `(x,z) ↦ χ z·e^{-i⟪p,z⟫}·boxQ volA A i v (Function.update x i z)`,
  and `Measurable (boxQ volA A i v)` follows from the measurability of the state (its `boxP` part
  is a parametric integral, `StronglyMeasurable.integral_prod_right'`);
* uniform boundedness of `boxQ volA A i v` on the box: `boxQ = id − boxP` and the box mean is
  bounded by `Cb·(volume.real A)/volA` (the pointwise bound `hψb` over the box, the set-integral
  bound, `volA ≥ 0`; if `volA = 0` then `boxP = 0`);
* on the finite-measure box, `AEStronglyMeasurable + bounded` gives `Integrable`
  (`MeasureTheory.Integrable.of_bound`). -/
theorem slotAmp_x_integrable {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {K : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ) :
    (∀ (δ : ℝ), 0 < δ → ∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (Work.BoseFixB1B.cutProd (γ δ) ψ) p x‖ ^ 2)
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n+1) L))) ∧
    (∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n+1) L))) := by
  constructor
  · -- the smooth approximant `cutProd (γ δ) ψ`
    intro δ hδ i p
    obtain ⟨hγcd, -, hγ01, -, -⟩ := hcut.2 δ hδ
    exact integrable_sq_slotAmpF_of_state hL hd u
      (Work.BoseFixB1B.contDiff_cutProd hγcd hψ).continuous.measurable hCb
      (Work.BoseFixB1B.abs_cutProd_le hγ01 hψb) i p
  · -- the sharp in-box state
    intro i p
    exact integrable_sq_slotAmpF_of_state hL hd u
      (Work.BoseFixB1B.sharpBoxState_measurable
        (Work.SmallBoxSliding.measurableSet_dlBox L d u) hψ.continuous.measurable) hCb
      (Work.BoseFixB1B.abs_sharpBoxState_le hCb hψb) i p

end Work.BoseFixB1B.B1Bfix
