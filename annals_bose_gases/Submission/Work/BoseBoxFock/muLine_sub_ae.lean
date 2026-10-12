import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiLinearAux
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.muLine_sub_ae` — additivity of the `μ`-line in the weight, a.e. form

The `μ`-line of the χ-row, `muLine n ℓ w Φ = 2 Σ_j ∫_{abox}(Q_jΦ)·w(x_j)·(P_jΦ)`, is additive in
the weight: `muLine ℓ (w − w') Φ = muLine ℓ w Φ − muLine ℓ w' Φ`.

`Work.BoseBoxFock.muLine_sub` (`chiRow_slot_linear.lean`) proves this for a weight that is
`Measurable` and *globally* bounded.  The χ-row assembly only ever evaluates the weight at points
`x_j` of the box `abox n ℓ`, i.e. `x_j ∈ acube ℓ`, so the natural hypotheses are much weaker:
`AEStronglyMeasurable` **on the cube** and a bound **on the cube**.  This file supplies that
version.

The only new ingredient is the a.e. analogue `integrableOn_cont_slot_bounded_ae` of the slot
toolbox lemma `integrableOn_cont_slot_bounded`: on the product measure `Measure.pi (fun _ =>
volume.restrict (acube ℓ))` — which is `volume.restrict (abox n ℓ)` by
`Submission.BoseGases.restrict_abox_eq_pi` — the coordinate map `Function.eval i` is
quasi-measure-preserving (`MeasureTheory.Measure.quasiMeasurePreserving_eval`), so
a.e. strong measurability and a.e. boundedness transfer from the cube to the box.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **Slot-weighted products are integrable on the box, a.e. form.**  The product of two
continuous factors with a slot factor `u (x i)` which is only a.e. strongly measurable *on the
cube* and bounded *on the cube* is integrable over the centred box. -/
lemma integrableOn_cont_slot_bounded_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {A B : X n → ℝ} (hAc : Continuous A) (hBc : Continuous B)
    {u : Sp → ℝ} (hum : AEStronglyMeasurable u (volume.restrict (acube ℓ)))
    {K : ℝ} (huK : ∀ z ∈ acube ℓ, |u z| ≤ K) :
    IntegrableOn (fun x : X n => A x * u (x i) * B x) (abox n ℓ) volume := by
  have hAB : IntegrableOn (fun x : X n => A x * B x) (abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hAc.mul hBc)
  -- Reduce to the product measure `Measure.pi (fun _ => volume.restrict (acube ℓ))`.
  rw [IntegrableOn, restrict_abox_eq_pi n ℓ] at hAB ⊢
  haveI : SigmaFinite ((volume : Measure Sp).restrict (acube ℓ)) := inferInstance
  -- The coordinate map is quasi-measure-preserving.
  have hqmp : Measure.QuasiMeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : Fin n => (volume : Measure Sp).restrict (acube ℓ)))
      ((volume : Measure Sp).restrict (acube ℓ)) :=
    Measure.quasiMeasurePreserving_eval _ i
  have hu : AEStronglyMeasurable (fun x : X n => u (x i))
      (Measure.pi (fun _ : Fin n => (volume : Measure Sp).restrict (acube ℓ))) :=
    hum.comp_quasiMeasurePreserving hqmp
  -- The cube membership holds a.e., hence the bound holds a.e. on the box.
  have hmem : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => (volume : Measure Sp).restrict (acube ℓ))),
      x i ∈ acube ℓ :=
    hqmp.ae (self_mem_ae_restrict (acube_measurable ℓ))
  have hbdd : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => (volume : Measure Sp).restrict (acube ℓ))),
      ‖u (x i)‖ ≤ K := by
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs]
    exact huK (x i) hx
  refine (hAB.mul_bdd hu hbdd).congr ?_
  exact Filter.EventuallyEq.of_eq (funext (fun x => by ring))

/-- **Set-integral linearity from a pointwise identity**: if `H = F − G` on the box and both `F`
and `G` are integrable there, then `∫ H = ∫ F − ∫ G`. -/
private lemma integral_eq_sub_of_pointwise {n : ℕ} {ℓ : ℝ} {F G H : X n → ℝ}
    (hF : IntegrableOn F (abox n ℓ) volume) (hG : IntegrableOn G (abox n ℓ) volume)
    (hpt : ∀ x ∈ abox n ℓ, H x = F x - G x) :
    (∫ x in abox n ℓ, H x) = (∫ x in abox n ℓ, F x) - (∫ x in abox n ℓ, G x) := by
  rw [show (∫ x in abox n ℓ, H x) = ∫ x in abox n ℓ, (F x - G x) from by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
    exact hpt x hx]
  exact integral_sub hF hG

theorem muLine_sub_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w w' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwm : MeasureTheory.AEStronglyMeasurable w
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hw'm : MeasureTheory.AEStronglyMeasurable w'
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {K K' : ℝ} (hw : ∀ z ∈ Submission.BoseGases.acube ℓ, |w z| ≤ K)
    (hw' : ∀ z ∈ Submission.BoseGases.acube ℓ, |w' z| ≤ K') :
    Work.BoseBoxFock.muLine n ℓ (fun z => w z - w' z) Φ
      = Work.BoseBoxFock.muLine n ℓ w Φ - Work.BoseBoxFock.muLine n ℓ w' Φ := by
  have hterm : ∀ j : Fin n,
      (∫ x in abox n ℓ, (aQ ℓ j Φ x) * (fun z : Sp => w z - w' z) (x j) * (aP ℓ j Φ x))
      = (∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))
        - (∫ x in abox n ℓ, (aQ ℓ j Φ x) * w' (x j) * (aP ℓ j Φ x)) := by
    intro j
    have hAc : Continuous (aQ ℓ j Φ) := aQ_cont hℓ j hΦc
    have hBc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
    exact integral_eq_sub_of_pointwise
      (integrableOn_cont_slot_bounded_ae hℓ j hAc hBc hwm hw)
      (integrableOn_cont_slot_bounded_ae hℓ j hAc hBc hw'm hw')
      (fun x _ => by ring)
  simp only [muLine]
  have hsum : (∑ j : Fin n, ∫ x in abox n ℓ,
        (aQ ℓ j Φ x) * (fun z : Sp => w z - w' z) (x j) * (aP ℓ j Φ x))
      = (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))
        - (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w' (x j) * (aP ℓ j Φ x)) := by
    have h1 : (∑ j : Fin n, ∫ x in abox n ℓ,
          (aQ ℓ j Φ x) * (fun z : Sp => w z - w' z) (x j) * (aP ℓ j Φ x))
        = ∑ j : Fin n, ((∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))
            - (∫ x in abox n ℓ, (aQ ℓ j Φ x) * w' (x j) * (aP ℓ j Φ x))) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    rw [h1]
    simp only [Finset.sum_sub_distrib]
  rw [hsum]
  ring

end Work.BoseBoxFock
