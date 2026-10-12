import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uSlot_int_eq_aPC` — the condensate row's analytic identity

Let `u : Sp → ℂ` be a.e. equal to `c · θ_Λ` with `conj c * c = (ℓ³)⁻¹` (FS's pinning
`e 0 = c·θ`, `|c|² = ℓ⁻³`), and `Θ : Xn d → ℂ` an arbitrary state.  The condensate row

    `bomb m Ψ (n₀ Ψ) = cS1 ℓ Θ`,      `Θ = boxRealise e d Ψ`,

is, after the dictionary (`Work.BoseDict.bomb_dGamma_slot` +
`Work.BoseBoxFock.boxSlotSum_proj0`), the identity

    `Re ∫_{abox d ℓ} conj Θ · Σ_j uSlot u j Θ = Σ_j ∫_{abox d ℓ} ‖aPC ℓ j Θ‖²`

with `u = e 0` — i.e. the statement that the slot operator of the one-particle vector
`c·θ_Λ` is the box mean underlying `aPC`.  This module proves the *per-slot* form.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => Work.BoseDict.Sp

/-- The localization function is real: its conjugate is itself. -/
theorem conj_thetaFun_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ) (z : Sp) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
      = Work.BoseK15.corpusBox.thetaFun ℓ z := by
  rw [thetaFun_eq_indicator hℓ]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]

/-- Replacing `u` by its a.e. value `c · thetaFun ℓ` turns the `z`-integral defining `uSlot`
into `conj c` times the centred-box integral of `Θ`. -/
theorem uSlot_eq_mul_setIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(volume : Measure Sp), u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {d : ℕ} (j : Fin d) (Θ : Work.BoseDict.Xn d → ℂ) (x : Work.BoseDict.Xn d) :
    uSlot u j Θ x = u (x j) * (starRingEnd ℂ) c
      * ∫ z in Submission.BoseGases.acube ℓ, Θ (Function.update x j z) := by
  have hconjae : ∀ᵐ z ∂(volume : Measure Sp),
      (starRingEnd ℂ) (u z) = (starRingEnd ℂ) c * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    filter_upwards [huc] with z hz
    rw [hz, map_mul, conj_thetaFun_eq_self hℓ]
  have hθind : (fun z : Sp => Work.BoseK15.corpusBox.thetaFun ℓ z
        * Θ (Function.update x j z))
      = fun z : Sp => (Submission.BoseGases.acube ℓ).indicator
          (fun z => Θ (Function.update x j z)) z := by
    funext z
    rw [thetaFun_eq_indicator hℓ]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  unfold uSlot
  rw [show (∫ z : Sp, (starRingEnd ℂ) (u z) * Θ (Function.update x j z))
      = ∫ z : Sp, (starRingEnd ℂ) c
          * (Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z)) from by
    refine integral_congr_ae ?_
    filter_upwards [hconjae] with z hz
    rw [hz, mul_assoc]]
  rw [MeasureTheory.integral_const_mul, hθind,
    MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ), mul_assoc]

/-- The measure-preserving peel of a slot of the centred box, in the orientation needed here. -/
theorem abox_peel_mp_insN (n : ℕ) (ℓ : ℝ) (i : Fin (n + 1)) :
    MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) := by
  have h := MeasureTheory.MeasurePreserving.symm
    (e := MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i)
    (Submission.BoseGases.abox_peel_mp n ℓ i)
  simpa [Submission.BoseGases.kcInsN] using h

private lemma update_kcInsN {n : ℕ} (i : Fin (n + 1))
    (y z : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n) :
    Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z
      = Submission.BoseGases.kcInsN n i (z, r) := by
  funext t
  by_cases ht : t = i
  · subst ht
    simp [Function.update_apply, Submission.BoseGases.kc_insN_apply_same]
  · rw [Function.update_apply, if_neg ht,
      Submission.BoseGases.kc_insN_other_indep n i y z r t ht]

/-- The cube integral of a constant. -/
theorem integral_const_acube {ℓ C : ℝ} (hℓ : 0 < ℓ) :
    (∫ y in Submission.BoseGases.acube ℓ, C) = ℓ ^ 3 * C := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real,
    Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ),
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **The per-slot analytic identity of the condensate row.** -/
theorem uSlot_int_eq_aPC {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin d)
    {u : Sp → ℂ} {c : ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (huc : ∀ᵐ z ∂(volume : Measure Sp), u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hInt : MeasureTheory.IntegrableOn
      (fun x => (starRingEnd ℂ) (Θ x) * uSlot u j Θ x) (Submission.BoseGases.abox d ℓ))
    (hInt2 : MeasureTheory.IntegrableOn
      (fun x => ‖aPC ℓ j Θ x‖ ^ 2) (Submission.BoseGases.abox d ℓ)) :
    (∫ x in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Θ x) * uSlot u j Θ x).re
      = ∫ x in Submission.BoseGases.abox d ℓ, ‖aPC ℓ j Θ x‖ ^ 2 := by
  cases d with
  | zero => exact absurd j.isLt (Nat.not_lt_zero _)
  | succ n =>
    have hℓ3 : (ℓ : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have hc3 : c * (starRingEnd ℂ) c = Complex.ofReal ((ℓ ^ 3 : ℝ)⁻¹) := by
      rw [mul_comm]; exact hcc
    let Z : Submission.BoseGases.X n → ℂ := fun r =>
      ∫ z in Submission.BoseGases.acube ℓ, Θ (Submission.BoseGases.kcInsN n j (z, r))
    have huae : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.acube ℓ)), u y = c := by
      have h2 : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.acube ℓ)),
          u y = c * Work.BoseK15.corpusBox.thetaFun ℓ y :=
        ae_mono MeasureTheory.Measure.restrict_le_self huc
      filter_upwards [h2, self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
        with y hy hyc
      rw [hy, thetaFun_eq_indicator hℓ, Set.indicator_of_mem hyc, mul_one]
    -- ## the two pointwise fibre identities
    have hpt : ∀ r : Submission.BoseGases.X n,
        (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r)))
              * uSlot u j Θ (Submission.BoseGases.kcInsN n j (y, r)))
          = (((ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      have hU : ∀ y : EuclideanSpace ℝ (Fin 3),
          uSlot u j Θ (Submission.BoseGases.kcInsN n j (y, r))
            = u y * (starRingEnd ℂ) c * Z r := by
        intro y
        have hZ : (∫ z in Submission.BoseGases.acube ℓ,
            Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z)) = Z r := by
          show (∫ z in Submission.BoseGases.acube ℓ,
              Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z))
            = ∫ z in Submission.BoseGases.acube ℓ, Θ (Submission.BoseGases.kcInsN n j (z, r))
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          show Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z)
            = Θ (Submission.BoseGases.kcInsN n j (z, r))
          rw [update_kcInsN j y z r]
        rw [uSlot_eq_mul_setIntegral hℓ huc j Θ (Submission.BoseGases.kcInsN n j (y, r)),
          Submission.BoseGases.kc_insN_apply_same, hZ]
      have step1 : (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r)))
              * uSlot u j Θ (Submission.BoseGases.kcInsN n j (y, r)))
          = (∫ y in Submission.BoseGases.acube ℓ,
              (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))) * u y)
            * ((starRingEnd ℂ) c * Z r) := by
        rw [show (∫ y in Submission.BoseGases.acube ℓ,
              (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r)))
                * uSlot u j Θ (Submission.BoseGases.kcInsN n j (y, r)))
            = ∫ y in Submission.BoseGases.acube ℓ,
                ((starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))) * u y)
                  * ((starRingEnd ℂ) c * Z r) from
          MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun y _ => by rw [hU y]; ring)]
        rw [MeasureTheory.integral_mul_const]
      have step2 : (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))) * u y)
          = (∫ y in Submission.BoseGases.acube ℓ,
              (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r)))) * c := by
        rw [MeasureTheory.integral_congr_ae
          (huae.mono (fun y hy => congrArg
            (fun t => (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))) * t) hy)),
          MeasureTheory.integral_mul_const]
      have step3 : (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))))
          = (starRingEnd ℂ) (Z r) := by
        show (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r))))
          = (starRingEnd ℂ) (∫ y in Submission.BoseGases.acube ℓ,
              Θ (Submission.BoseGases.kcInsN n j (y, r)))
        exact integral_conj
      rw [step1, step2, step3]
      have hKsq : (starRingEnd ℂ) (Z r) * Z r = (((‖Z r‖ ^ 2 : ℝ)) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      rw [show (starRingEnd ℂ) (Z r) * c * ((starRingEnd ℂ) c * Z r)
          = ((starRingEnd ℂ) (Z r) * Z r) * (c * (starRingEnd ℂ) c) by ring,
        hKsq, hc3, ← Complex.ofReal_mul]
      congr 1
      ring
    have hpt2 : ∀ r : Submission.BoseGases.X n,
        (∫ y in Submission.BoseGases.acube ℓ,
          ‖aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))‖ ^ 2)
        = (ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2 := by
      intro r
      have hA : ∀ y : EuclideanSpace ℝ (Fin 3),
          aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))
            = ((1 / ℓ ^ 3 : ℝ) : ℂ) * Z r := by
        intro y
        have hZ : (∫ z in Submission.BoseGases.acube ℓ,
            Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z)) = Z r := by
          show (∫ z in Submission.BoseGases.acube ℓ,
              Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z))
            = ∫ z in Submission.BoseGases.acube ℓ, Θ (Submission.BoseGases.kcInsN n j (z, r))
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          show Θ (Function.update (Submission.BoseGases.kcInsN n j (y, r)) j z)
            = Θ (Submission.BoseGases.kcInsN n j (z, r))
          rw [update_kcInsN j y z r]
        rw [aPC, hZ]
      have hnormC : ‖(((1 / ℓ ^ 3 : ℝ)) : ℂ)‖ ^ 2 = ((1 / ℓ ^ 3 : ℝ)) ^ 2 := by
        rw [sq_norm_eq_re_sq_add_im_sq, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hcst : ∀ y : EuclideanSpace ℝ (Fin 3),
          ‖aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))‖ ^ 2
            = ((1 / ℓ ^ 3 : ℝ)) ^ 2 * ‖Z r‖ ^ 2 := by
        intro y
        rw [hA y, norm_mul, mul_pow, hnormC]
      rw [show (∫ y in Submission.BoseGases.acube ℓ,
              ‖aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))‖ ^ 2)
            = ∫ y in Submission.BoseGases.acube ℓ,
                ((1 / ℓ ^ 3 : ℝ)) ^ 2 * ‖Z r‖ ^ 2 from
          MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun y _ => hcst y)]
      rw [integral_const_acube hℓ]
      have hpow : (ℓ ^ 3 : ℝ) * ((1 / ℓ ^ 3 : ℝ) ^ 2) = (ℓ ^ 3 : ℝ)⁻¹ := by
        have h1 : (ℓ ^ 3 : ℝ) * (1 / ℓ ^ 3) = 1 := by
          rw [mul_one_div, div_self (ne_of_gt (pow_pos hℓ 3))]
        rw [sq, ← mul_assoc, h1, one_mul, one_div]
      rw [← mul_assoc, hpow]
    -- ## integrability of the common fibre value
    have hintg : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        (ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := by
      have hmp := abox_peel_mp_insN n ℓ j
      have h1 : MeasureTheory.Integrable
          ((fun x => ‖aPC ℓ j Θ x‖ ^ 2) ∘ ⇑(Submission.BoseGases.kcInsN n j))
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) :=
        (hmp.integrable_comp (hg := hInt2.aestronglyMeasurable)).mpr hInt2
      have h2 := h1.integral_prod_right
      refine h2.congr (Filter.Eventually.of_forall (fun r => ?_))
      show (∫ y : EuclideanSpace ℝ (Fin 3),
          ‖aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))‖ ^ 2
            ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)))
          = (ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2
      exact hpt2 r
    -- ## the peels and the assembly
    have hL := Submission.BoseGases.abox_integral_peel_gen (n := n) (ℓ := ℓ) (E := ℂ) j
      (fun x => (starRingEnd ℂ) (Θ x) * uSlot u j Θ x) hInt
    have hR := Submission.BoseGases.abox_integral_peel_gen (n := n) (ℓ := ℓ) (E := ℝ) j
      (fun x => ‖aPC ℓ j Θ x‖ ^ 2) hInt2
    have hfinal : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (starRingEnd ℂ) (Θ x) * uSlot u j Θ x)
        = Complex.ofReal (∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ j Θ x‖ ^ 2) := by
      rw [hL, hR]
      rw [show (∫ r in Submission.BoseGases.abox n ℓ,
            (∫ y in Submission.BoseGases.acube ℓ,
              (starRingEnd ℂ) (Θ (Submission.BoseGases.kcInsN n j (y, r)))
                * uSlot u j Θ (Submission.BoseGases.kcInsN n j (y, r))))
          = ∫ r in Submission.BoseGases.abox n ℓ,
              ((((ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2 : ℝ)) : ℂ) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      rw [show (∫ r in Submission.BoseGases.abox n ℓ,
              ((((ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2 : ℝ)) : ℂ))
          = Complex.ofReal (∫ r in Submission.BoseGases.abox n ℓ,
              ((ℓ ^ 3 : ℝ)⁻¹ * ‖Z r‖ ^ 2)) from
        Complex.ofRealCLM.integral_comp_comm hintg]
      congr 1
      exact (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall hpt2)).symm
    rw [hfinal, Complex.ofReal_re]

/-- **The condensate row on the box side**: the pairing of `Θ` with the sum of the slot
operators of `e 0` is the condensate count `cS1C`. -/
theorem uSlot_sum_cIPn_eq_cS1C {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ} {c : ℂ} {Θ : Work.BoseDict.Xn d → ℂ}
    (hun : ∀ᵐ z ∂(volume : Measure Sp),
      e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ)
    (hInt : ∀ j : Fin d, MeasureTheory.IntegrableOn
      (fun x => (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x) (Submission.BoseGases.abox d ℓ))
    (hInt2 : ∀ j : Fin d, MeasureTheory.IntegrableOn
      (fun x => ‖aPC ℓ j Θ x‖ ^ 2) (Submission.BoseGases.abox d ℓ)) :
    (Work.BoseDict.cIPn d Θ (fun x => ∑ j : Fin d, uSlot (e 0) j Θ x)).re
      = cS1C ℓ Θ := by
  have hzero : ∀ x : Work.BoseDict.Xn d, x ∉ Submission.BoseGases.abox d ℓ →
      (starRingEnd ℂ) (Θ x) * (∑ j : Fin d, uSlot (e 0) j Θ x) = 0 := by
    intro x hx
    have hΘ0 : Θ x = 0 := by
      by_contra h
      exact hx (hΘsupp (Function.mem_support.mpr h))
    rw [hΘ0]
    simp
  rw [cS1C, Work.BoseDict.cIPn,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox d ℓ) hzero]
  rw [show (∫ x in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Θ x) * ∑ j : Fin d, uSlot (e 0) j Θ x)
      = ∫ x in Submission.BoseGases.abox d ℓ,
          ∑ j : Fin d, (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        show (starRingEnd ℂ) (Θ x) * (∑ j : Fin d, uSlot (e 0) j Θ x)
          = ∑ j : Fin d, (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x
        rw [Finset.mul_sum]))]
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hInt j)]
  rw [show (∑ j : Fin d, ∫ x in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x).re
      = ∑ j : Fin d, (∫ x in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x).re from
    Complex.re_sum (s := Finset.univ) (f := fun j : Fin d =>
      ∫ x in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Θ x) * uSlot (e 0) j Θ x)]
  exact Finset.sum_congr rfl (fun j _ => uSlot_int_eq_aPC hℓ j hun hcc (hInt j) (hInt2 j))

end Work.BoseBoxFock
