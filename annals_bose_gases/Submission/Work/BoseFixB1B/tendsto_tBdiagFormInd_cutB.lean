import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.B1Bfix.cut_slotForm_integrable
import Submission.Work.BoseFixB1B.B1Bfix.sharp_slotForm_integrable
import Submission.Work.BoseFixB1B.B1Bfix.slotAmpDiff_x_integrable
import Submission.Work.BoseFixB1B.B1Bfix.slotAmp_x_integrable
import Submission.Work.BoseFixB1B.B1Bfix2.diffFibre_factsB
import Submission.Work.BoseFixB1B.aemeasurable_kinFT_fibre
import Submission.Work.BoseFixB1B.cutAmplitude_integrable
import Submission.Work.BoseFixB1B.cutForm_fsKin_le
import Submission.Work.BoseFixB1B.cutPlancherel_le
import Submission.Work.BoseFixB1B.tBamp_fibre_bound
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.tendsto_tBdiagFormInd_cutB`

The `p`-diagonal kinetic form `Work.UBBInputs8.tBdiagFormInd` of the smooth approximants
`Ψ_δ = cutProd (γ δ) ψ` of the sharp box state converges to its value at the sharp state.

The proof is the comparison of the slot forms of `Ψ_δ − Ψ₀` and `Ψ₀` (`main_slotTendsto`,
from `Submission.Work.BoseFixB1B.B1Bfix._asm`), fed by

* the four slot-bookkeeping lemmas `B1Bfix.{cut,sharp}_slotForm_integrable`,
  `B1Bfix.{slotAmp,slotAmpDiff}_x_integrable`;
* `B1Bfix2.diffFibre_factsB` (the fibre facts of the difference state: measurability, bound,
  smoothness in both parametrisations, and the Dirichlet bound) and
* `B1Bfix2.fibreDirI_diff_tendstoB` (the fibre Dirichlet energy of the difference state is `O(δ)`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.B1Bfix

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

/-! ## 1. Elementary facts -/

/-- The norm of the coercion of a real number. -/
private lemma norm_coe_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The phase factor of the windowed amplitude has norm one. -/
private lemma norm_exp_phase (p z : E3) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im]

/-- The windowed amplitude at an inserted configuration, as the defining `z`-integral. -/
private lemma tBamp_kcInsN_apply {N : ℕ} (χ : E3 → ℝ) (p : E3)
    (Φ : Submission.BoseGases.X (N+1) → ℝ) (i : Fin (N+1)) (y : E3)
    (r : Submission.BoseGases.X N) :
    Work.SmallBoxTBWord.tBamp χ p Φ i (Submission.BoseGases.kcInsN N i (y, r))
      = ∫ z : E3, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (Φ (Submission.BoseGases.kcInsN N i (z, r)) : ℂ) := by
  unfold Work.SmallBoxTBWord.tBamp
  simp only [Work.SmallBoxBridge.Fourier.update_kcInsN]

/-! ## 2. Additivity of the windowed slot amplitude in the state -/

/-- **Additivity of the windowed slot amplitude in the state**, on the ambient box: the amplitude
of the difference of two states is the difference of the amplitudes.  Both states are assumed
bounded by `Cb` on the ambient box, which is what makes the slices over the box and the windowed
fibres over `ℝ³` integrable. -/
private theorem slotAmpF_sub_abox {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : E3) {ψ : Submission.BoseGases.X (n+1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {K Cb : ℝ}
    {γ : ℝ → E3 → ℝ} (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    (δ : ℝ) (hδ : 0 < δ) (i : Fin (n+1)) (p : E3) {x : Submission.BoseGases.X (n+1)}
    (hx : x ∈ Submission.BoseGases.abox (n+1) L) :
    Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
      - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x
      = Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) p x := by
  classical
  set F : Submission.BoseGases.X (n+1) → ℝ := Work.BoseFixB1B.cutProd (γ δ) ψ with hF
  set G : Submission.BoseGases.X (n+1) → ℝ :=
    Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ with hG
  set D : Submission.BoseGases.X (n+1) → ℝ := slotDiffState L d u (γ δ) ψ with hD
  set r : Submission.BoseGases.X n := fun j => x (i.succAbove j) with hr
  have hr_mem : r ∈ Submission.BoseGases.abox n L := by
    rw [Submission.BoseGases.mem_abox_iff]
    intro j
    rw [hr]
    exact (Submission.BoseGases.mem_abox_iff (n+1) L x).mp hx (i.succAbove j)
  have hxr : Submission.BoseGases.kcInsN n i (x i, r) = x := by
    rw [hr]
    exact kcInsN_reconstruct i x
  have hFb : ∀ y ∈ Submission.BoseGases.abox (n+1) L, |F y| ≤ Cb := fun y hy => by
    rw [hF]
    exact Work.BoseFixB1B.cutFibre_abs_cutProd_le hL hcut hδ hCb hψb y hy
  have hGb : ∀ y ∈ Submission.BoseGases.abox (n+1) L, |G y| ≤ Cb := fun y hy => by
    rw [hG]
    exact Work.BoseFixB1B.cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb y hy
  have hFmeas : Measurable F := by
    rw [hF]
    exact Work.BoseFixB1B.cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ.continuous
  have hGmeas : Measurable G := by
    rw [hG]
    exact Work.BoseFixB1B.cutFibre_measurable_sharpBoxState
      (Work.SmallBoxSliding.measurableSet_dlBox L d u) hψ.continuous.measurable
  have hkc : Measurable (fun z : E3 => Submission.BoseGases.kcInsN n i (z, r)) :=
    (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r).continuous.measurable
  have hbqmeas : ∀ (H : Submission.BoseGases.X (n+1) → ℝ), Measurable H →
      AEStronglyMeasurable (fun z : E3 => (Work.SmallBoxTBWord.boxQ
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.dlBox L d u) i H)
        (Submission.BoseGases.kcInsN n i (z, r))) volume := by
    intro H hH
    have h2 : AEStronglyMeasurable (fun z : E3 => H (Submission.BoseGases.kcInsN n i (z, r))
        - (1 / Work.SmallBoxSliding.boxMass L d u)
          * ∫ t in Submission.BoseGases.dlBox L d u, H (Submission.BoseGases.kcInsN n i (t, r)))
        volume := ((hH.comp hkc).sub measurable_const).aestronglyMeasurable
    exact h2.congr (Filter.Eventually.of_forall fun z =>
      (Work.BoseFixB1B.boxQ_kcInsN_eq i (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) H z r).symm)
  have hsliceF : IntegrableOn (fun t : E3 => F (Submission.BoseGases.kcInsN n i (t, r)))
      (Submission.BoseGases.dlBox L d u) := by
    refine IntegrableOn.of_bound ((Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top)
      ((hFmeas.comp hkc).aestronglyMeasurable) Cb ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Work.SmallBoxSliding.measurableSet_dlBox L d u)] with t ht
    rw [Real.norm_eq_abs]
    exact hFb _ (Work.BoseFixB1B.kcInsN_mem_abox i
      (Work.SmallBoxSliding.dlBox_subset_acube L d u ht) hr_mem)
  have hsliceG : IntegrableOn (fun t : E3 => G (Submission.BoseGases.kcInsN n i (t, r)))
      (Submission.BoseGases.dlBox L d u) := by
    refine IntegrableOn.of_bound ((Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top)
      ((hGmeas.comp hkc).aestronglyMeasurable) Cb ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Work.SmallBoxSliding.measurableSet_dlBox L d u)] with t ht
    rw [Real.norm_eq_abs]
    exact hGb _ (Work.BoseFixB1B.kcInsN_mem_abox i
      (Work.SmallBoxSliding.dlBox_subset_acube L d u ht) hr_mem)
  have hmean : (∫ t in Submission.BoseGases.dlBox L d u, D (Submission.BoseGases.kcInsN n i (t, r)))
      = (∫ t in Submission.BoseGases.dlBox L d u, F (Submission.BoseGases.kcInsN n i (t, r)))
        - (∫ t in Submission.BoseGases.dlBox L d u, G (Submission.BoseGases.kcInsN n i (t, r))) := by
    rw [← MeasureTheory.integral_sub hsliceF hsliceG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hD, hF, hG, slotDiffState_apply]
  have hboxQ : ∀ z : E3, Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i D (Submission.BoseGases.kcInsN n i (z, r))
      = Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i F (Submission.BoseGases.kcInsN n i (z, r))
        - Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i G (Submission.BoseGases.kcInsN n i (z, r)) := by
    intro z
    rw [Work.BoseFixB1B.boxQ_kcInsN_eq, Work.BoseFixB1B.boxQ_kcInsN_eq,
      Work.BoseFixB1B.boxQ_kcInsN_eq, hmean, hD, hF, hG, slotDiffState_apply]
    ring
  have hamb : ∀ (H : Submission.BoseGases.X (n+1) → ℝ), Measurable H →
      (∀ z ∈ Submission.BoseGases.acube L,
        |(Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i H) (Submission.BoseGases.kcInsN n i (z, r))| ≤ 2 * Cb) →
      Integrable (fun z : E3 => (Submission.BoseGases.chiB L d u z : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i H)
            (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) volume := by
    intro H hH hboxB
    have hχint : Integrable (fun z : E3 => (2 * Cb) * ‖Submission.BoseGases.chiB L d u z‖)
        volume :=
      (((Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous.integrable_of_hasCompactSupport
        (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u)).norm).const_mul (2 * Cb)
    refine hχint.mono' ?_ ?_
    · have h1 : Continuous (fun z : E3 => (Submission.BoseGases.chiB L d u z : ℂ)) :=
        Complex.continuous_ofReal.comp (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous
      have h2 : Continuous (fun z : E3 =>
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) := by fun_prop
      exact (h1.mul h2).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable (hbqmeas H hH))
    · filter_upwards with z
      have hexp := norm_exp_phase p z
      by_cases hz : Submission.BoseGases.chiB L d u z = 0
      · simp [hz]
      · have hzac : z ∈ Submission.BoseGases.acube L :=
          Work.SmallBoxTBWord.tsupport_chiB_subset_acube hL hd u
            (subset_tsupport _ (Function.mem_support.mpr hz))
        have hb := hboxB z hzac
        simp only [norm_mul, norm_coe_real, hexp, mul_one, Real.norm_eq_abs]
        calc |Submission.BoseGases.chiB L d u z|
              * |(Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                  (Submission.BoseGases.dlBox L d u) i H)
                  (Submission.BoseGases.kcInsN n i (z, r))|
            ≤ |Submission.BoseGases.chiB L d u z| * (2 * Cb) :=
              mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = (2 * Cb) * |Submission.BoseGases.chiB L d u z| := by ring
  have hboxB_F : ∀ z ∈ Submission.BoseGases.acube L,
      |(Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i F) (Submission.BoseGases.kcInsN n i (z, r))| ≤ 2 * Cb := by
    intro z hz
    have hmem := Work.BoseFixB1B.kcInsN_mem_abox i hz hr_mem
    have h2 := Work.BoseFixB1B.boxP_fibre_abs_le hL hd u hCb hFb i hr_mem
    rw [Work.BoseFixB1B.boxQ_kcInsN_eq]
    calc |F (Submission.BoseGases.kcInsN n i (z, r))
            - (1 / Work.SmallBoxSliding.boxMass L d u)
              * ∫ t in Submission.BoseGases.dlBox L d u,
                  F (Submission.BoseGases.kcInsN n i (t, r))|
          ≤ |F (Submission.BoseGases.kcInsN n i (z, r))|
            + |(1 / Work.SmallBoxSliding.boxMass L d u)
              * ∫ t in Submission.BoseGases.dlBox L d u,
                  F (Submission.BoseGases.kcInsN n i (t, r))| := abs_sub _ _
        _ ≤ 2 * Cb := by
            have h1 := hFb _ hmem
            linarith
  have hboxB_G : ∀ z ∈ Submission.BoseGases.acube L,
      |(Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i G) (Submission.BoseGases.kcInsN n i (z, r))| ≤ 2 * Cb := by
    intro z hz
    have hmem := Work.BoseFixB1B.kcInsN_mem_abox i hz hr_mem
    have h2 := Work.BoseFixB1B.boxP_fibre_abs_le hL hd u hCb hGb i hr_mem
    rw [Work.BoseFixB1B.boxQ_kcInsN_eq]
    calc |G (Submission.BoseGases.kcInsN n i (z, r))
            - (1 / Work.SmallBoxSliding.boxMass L d u)
              * ∫ t in Submission.BoseGases.dlBox L d u,
                  G (Submission.BoseGases.kcInsN n i (t, r))|
          ≤ |G (Submission.BoseGases.kcInsN n i (z, r))|
            + |(1 / Work.SmallBoxSliding.boxMass L d u)
              * ∫ t in Submission.BoseGases.dlBox L d u,
                  G (Submission.BoseGases.kcInsN n i (t, r))| := abs_sub _ _
        _ ≤ 2 * Cb := by
            have h1 := hGb _ hmem
            linarith
  have hintF := hamb F hFmeas hboxB_F
  have hintG := hamb G hGmeas hboxB_G
  rw [Work.BoseFixB1B.slotAmpF_apply, Work.BoseFixB1B.slotAmpF_apply,
    Work.BoseFixB1B.slotAmpF_apply]
  rw [← hxr]
  rw [tBamp_kcInsN_apply, tBamp_kcInsN_apply, tBamp_kcInsN_apply]
  have hDamp : (∫ z : E3, (Submission.BoseGases.chiB L d u z : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i D)
            (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))
      = (∫ z : E3, (Submission.BoseGases.chiB L d u z : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i F)
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))
        - (∫ z : E3, (Submission.BoseGases.chiB L d u z : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i G)
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) := by
    rw [show (∫ z : E3, (Submission.BoseGases.chiB L d u z : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i D)
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ))
        = ∫ z : E3, ((Submission.BoseGases.chiB L d u z : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i F)
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)
          - (Submission.BoseGases.chiB L d u z : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
            * ((Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i G)
                (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hboxQ]
      push_cast
      ring]
    rw [MeasureTheory.integral_sub hintF hintG]
  rw [hDamp]

/-! ## 3. The main theorem -/

/-- **The slot form of the amplitude difference vanishes as `δ → 0⁺`.**

`A_δ := slotAmpF L A volA χ i (cutProd (γ δ) ψ)` and `A₀ := slotAmpF L A volA χ i (sharpBoxState A ψ)`
are the windowed slot amplitudes of the approximant `Ψ_δ` and of the sharp state `Ψ₀` (with
`A = dlBox L d u`, `volA = boxMass L d u`, `χ = chiB L d u`), and the claim is that the slot form of
their difference, `(2π)⁻³∫_p fsKinCoeff c ‖p‖·(L³)⁻¹∫_x ‖A_δ − A₀‖²`, tends to `0` as `δ → 0⁺`.

The difference is a collar-localised object:

* by `Work.BoseFixB1B.boxQ_cut_kcInsN` and `Work.BoseFixB1B.boxQ_sharp_kcInsN` (both slot functions
  are *explicit* and, as functions of the slot position `z`, smooth and supported in
  `tsupport (chiB L d u)`),
  `tBamp χ p (Q_{B,i}Ψ_δ) i x = P_δ(r)·∫_z χ z e^{-i⟪p,z⟫}(γ δ z·ψ(z,r) − c_δ(r))dz` and
  `tBamp χ p (Q_{B,i}Ψ₀) i x = 1_{r∈B^n}·∫_z χ z e^{-i⟪p,z⟫}(ψ(z,r) − c₀(r))dz` with `r = x_{i^c}`;
* the *difference* of the two integrands `χ z (P_δ(r)γ δ z·ψ(z,r) − 1_{r∈B^n}ψ(z,r))` vanishes
  unless `z` lies in the `δ`-collar of `B` or some coordinate of `r` does, and the
  `χ·∇γ δ`-term is bounded by `C·K` (from `|chiB| ≤ C·boxMargin` and `‖fderiv (γ δ)‖ ≤ K/δ`, the
  `δ`-cancellation of `Work.BoseFixB1B.chiB_abs_le_boxMargin`), so both the `L²`-norm and the
  Dirichlet energy of the difference are `O(δ)` — the collar volume estimate is
  `Work.BoseFixB1B.volume_iUnion_collar_le`;
* `slotAmpF` is the `kinFT` of that windowed slot fibre
  (`Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT`), so the per-fibre Plancherel identities
  (`Work.BSKinetic.plancherel_pconv` for the mass, `Work.SmallBoxTBWord.windowPlancherel` for the
  symbol `‖·‖²`) turn `(2π)⁻³∫_p fsKinCoeff c ‖p‖ ‖A_δ − A₀‖²` into the `O(δ)` position-space
  quantities (via the symbol bound `fsKinCoeff c r ≤ 2r² + 2c²` and Tonelli/`lintegral`).

The integrability conjunct follows from the uniform `(1+‖p‖)⁻³` decay of both amplitudes
(`Work.SmallBoxTBWord.tBamp_decay`). -/
theorem ampDiff_form_tendstoB {n : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {K : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ) :
    (∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1),
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
            ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
              - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2))) ∧
    Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n+1),
        ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
              ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
                - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  classical
  have hfacts := diffFibre_factsB (n := n) (L := L) (d := d) (u := u) (ψ := ψ)
    (K := K) (Cb := Cb) (γ := γ) hL hd hcut hψ hCb hψb
  have hconv := fibreDirI_diff_tendstoB (n := n) (L := L) (d := d) (u := u) (ψ := ψ)
    (K := K) (Cb := Cb) (γ := γ) hL hd hcut hψ hCb hψb
  have hχcd : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.contDiff_chiB hL hd u
  have hχcs : HasCompactSupport (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u
  have hχac : tsupport (Submission.BoseGases.chiB L d u) ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxTBWord.tsupport_chiB_subset_acube hL hd u
  -- the amplitude-difference integral is the slot energy of the difference state
  have hlin : ∀ (δ : ℝ), 0 < δ → ∀ (i : Fin (n+1)) (p : E3),
      ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
        ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
          - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)
      = Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ) p := by
    intro δ hδ i p
    rw [Work.BoseFixB1B.slotY]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable (n+1) L)
      (fun x hx => ?_)
    simp only [slotAmpF_sub_abox hL hd u hψ hcut hCb hψb δ hδ i p hx]
  -- the per-slot estimate
  have hper : ∀ (δ : ℝ), 0 < δ → ∀ i : Fin (n+1),
      Work.BoseFixB1B.slotFormL L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i (slotDiffState L d u (γ δ) ψ)
        ≤ 2 * Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ)
          + 2 * c ^ 2 * Work.BoseFixB1B.cutFibreMass L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (slotDiffState L d u (γ δ) ψ) := by
    intro δ hδ i
    obtain ⟨C, hC0, hΦm, hB, hfibU, hfibK, hdir⟩ := hfacts δ hδ i
    have hint := Work.BoseFixB1B.cutAmplitude_integrable
      (A := Submission.BoseGases.dlBox L d u) (volA := Work.SmallBoxSliding.boxMass L d u)
      (χ := Submission.BoseGases.chiB L d u) hL hχcd hχcs hχac i hΦm hB hfibU hC0 hdir
    have hint1 : Integrable (fun p : E3 => ‖p‖ ^ 2 * Work.BoseFixB1B.cutSlotAmp L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p) := by
      simpa only [Work.BoseFixB1B.cutSlotAmp] using hint.1
    have hint2 : Integrable (fun p : E3 => Work.BoseFixB1B.cutSlotAmp L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p) := by
      simpa only [Work.BoseFixB1B.cutSlotAmp] using hint.2
    have hfs := Work.BoseFixB1B.cutForm_fsKin_le (L := L) (A := Submission.BoseGases.dlBox L d u)
      (volA := Work.SmallBoxSliding.boxMass L d u) (χ := Submission.BoseGases.chiB L d u)
      hL c i hint1 hint2
    have hp := Work.BoseFixB1B.cutPlancherel_le (L := L) (A := Submission.BoseGases.dlBox L d u)
      (volA := Work.SmallBoxSliding.boxMass L d u) (χ := Submission.BoseGases.chiB L d u)
      hL hχcd hχcs hχac i hΦm hB hfibK
    have hp2' : Work.BoseFixB1B.cutSlotForm L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
        (fun t => t ^ 2) i (slotDiffState L d u (γ δ) ψ)
        ≤ Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ) := by
      simpa only [Work.BoseFixB1B.cutSlotForm, Work.BoseFixB1B.cutSlotAmp] using hp.1
    have hp1' : Work.BoseFixB1B.cutSlotForm L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
        (fun _ => 1) i (slotDiffState L d u (γ δ) ψ)
        ≤ Work.BoseFixB1B.cutFibreMass L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ) := by
      simpa only [Work.BoseFixB1B.cutSlotForm, Work.BoseFixB1B.cutSlotAmp, one_mul] using hp.2
    have h2c : (0 : ℝ) ≤ 2 * c ^ 2 := by positivity
    calc Work.BoseFixB1B.slotFormL L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i (slotDiffState L d u (γ δ) ψ)
        = Work.BoseFixB1B.cutSlotForm L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i (slotDiffState L d u (γ δ) ψ) := rfl
      _ ≤ 2 * Work.BoseFixB1B.cutSlotForm L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (fun t => t ^ 2) i (slotDiffState L d u (γ δ) ψ)
          + 2 * c ^ 2 * Work.BoseFixB1B.cutSlotForm L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (fun _ => 1) i (slotDiffState L d u (γ δ) ψ) := hfs
      _ ≤ 2 * Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ)
          + 2 * c ^ 2 * Work.BoseFixB1B.cutFibreMass L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ) :=
          add_le_add (mul_le_mul_of_nonneg_left hp2' (by norm_num : (0 : ℝ) ≤ 2))
            (mul_le_mul_of_nonneg_left hp1' h2c)
  -- the upper comparison, slot by slot
  have hsum : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ i : Fin (n+1), ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
              ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
                - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2))
      ≤ 2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (slotDiffState L d u (γ δ) ψ))
        + 2 * c ^ 2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
            (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have h1 : (∑ i : Fin (n+1), ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
              ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
                - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2))
        = ∑ i : Fin (n+1), Work.BoseFixB1B.slotFormL L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i (slotDiffState L d u (γ δ) ψ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Work.BoseFixB1B.slotFormL]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [hlin δ hδ i]
    rw [h1]
    calc (∑ i : Fin (n+1), Work.BoseFixB1B.slotFormL L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i (slotDiffState L d u (γ δ) ψ))
        ≤ ∑ i : Fin (n+1), (2 * Work.BoseFixB1B.cutFibreDir L
              (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ)
            + 2 * c ^ 2 * Work.BoseFixB1B.cutFibreMass L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (slotDiffState L d u (γ δ) ψ)) := Finset.sum_le_sum (fun i _ => hper δ hδ i)
      _ = 2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L
              (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ))
            + 2 * c ^ 2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
              (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the upper bound tends to zero
  have hup : Tendsto (fun δ : ℝ =>
        2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
              (slotDiffState L d u (γ δ) ψ))
          + 2 * c ^ 2 * (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
              (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreDir L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := hconv.2
    have h2 : Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      (Work.BoseFixB1B.cutFibreMass_facts (n := n) (L := L) (d := d) (u := u) (ψ := ψ)
        (K := K) (Cb := Cb) (γ := γ) hL hd hcut hψ hCb hψb).2
    have h3 := (h1.const_mul 2).add (h2.const_mul (2 * c ^ 2))
    simpa using h3
  constructor
  · -- integrability at each `δ`
    intro δ hδ i
    obtain ⟨C, hC0, hΦm, hB, hfibU, hfibK, hdir⟩ := hfacts δ hδ i
    have hint := Work.BoseFixB1B.cutAmplitude_integrable
      (A := Submission.BoseGases.dlBox L d u) (volA := Work.SmallBoxSliding.boxMass L d u)
      (χ := Submission.BoseGases.chiB L d u) hL hχcd hχcs hχac i hΦm hB hfibU hC0 hdir
    have hint1 : Integrable (fun p : E3 => ‖p‖ ^ 2 * Work.BoseFixB1B.cutSlotAmp L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p) := by
      simpa only [Work.BoseFixB1B.cutSlotAmp] using hint.1
    have hint2 : Integrable (fun p : E3 => Work.BoseFixB1B.cutSlotAmp L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p) := by
      simpa only [Work.BoseFixB1B.cutSlotAmp] using hint.2
    have haesm : AEStronglyMeasurable (fun p : E3 => Work.BoseFixB1B.cutSlotAmp L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p) volume := by
      have hjoint := Work.BoseFixB1B.aesm_tBamp_joint hL hχcd.continuous
        (fun z hz => by
          by_contra h
          exact hz (hχac (subset_tsupport _ (Function.mem_support.mpr h))))
        (hΦm.mono_measure MeasureTheory.Measure.restrict_le_self) i
      have h2 : AEStronglyMeasurable (fun p : E3 => ∫ x, ‖Work.SmallBoxTBWord.tBamp
            (Submission.BoseGases.chiB L d u) p
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)) i x‖ ^ 2
          ∂((volume : Measure (Submission.BoseGases.X (n+1))).restrict
            (Submission.BoseGases.abox (n+1) L))) volume :=
        (hjoint.norm.pow 2).integral_prod_right'
      exact (h2.const_mul ((L ^ 3)⁻¹)).congr (Filter.Eventually.of_forall fun p => by
        simp only [Work.BoseFixB1B.cutSlotAmp])
    have hcont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm
    have hfmeas : AEStronglyMeasurable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.cutSlotAmp L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ) p) volume :=
      hcont.aestronglyMeasurable.mul haesm
    have hnn : ∀ p : E3, 0 ≤ Work.BoseFixB1B.cutSlotAmp L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (slotDiffState L d u (γ δ) ψ) p := by
      intro p
      rw [Work.BoseFixB1B.cutSlotAmp]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le 3)) (integral_nonneg fun x => sq_nonneg _)
    have hdom : Integrable (fun p : E3 => (2 * ‖p‖ ^ 2 + 2 * c ^ 2) *
        Work.BoseFixB1B.cutSlotAmp L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ) p) := by
      refine ((hint1.const_mul 2).add (hint2.const_mul (2 * c ^ 2))).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply]
      ring
    have hbdd : ∀ᵐ p : E3 ∂volume, ‖Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.cutSlotAmp L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
          (slotDiffState L d u (γ δ) ψ) p‖
        ≤ (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * Work.BoseFixB1B.cutSlotAmp L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (slotDiffState L d u (γ δ) ψ) p := by
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (hnn p))]
      exact mul_le_mul_of_nonneg_right
        (Work.BoseFixB1B.fsKinCoeff_le_two_mul_sq_add (c := c) (r := ‖p‖)) (hnn p)
    refine (hdom.mono' hfmeas hbdd).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [hlin δ hδ i]
    rfl
  · -- the squeeze
    have hnn2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 ≤ (∑ i : Fin (n+1), ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
              ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
                - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
                  (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
                  (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)) := by
      refine Filter.Eventually.of_forall (fun δ => Finset.sum_nonneg (fun i _ => ?_))
      refine mul_nonneg (by positivity) (MeasureTheory.integral_nonneg ?_)
      intro p
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le 3)) (integral_nonneg fun x => sq_nonneg _))
    exact squeeze_zero' hnn2 hsum hup

end Work.BoseFixB1B.B1Bfix

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

attribute [local instance] Classical.propDecidable
/-! ## 1. Elementary pointwise lemmas -/

/-- The pointwise bound behind the slot-`p`-form comparison. -/
private lemma abs_normSq_sub_le_cutB (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := by
  have h4 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h5 : |‖a‖ + ‖b‖| ≤ 2 * ‖b‖ + ‖a - b‖ := by
    rw [abs_of_nonneg (by positivity)]
    have h := norm_add_le b (a - b)
    rw [show b + (a - b) = a from by ring] at h
    linarith
  have h3 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  rw [h3, abs_mul]
  calc |‖a‖ - ‖b‖| * |‖a‖ + ‖b‖|
      ≤ ‖a - b‖ * (2 * ‖b‖ + ‖a - b‖) :=
        mul_le_mul h4 h5 (abs_nonneg _) (norm_nonneg _)
    _ = 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := by ring

/-- The AM-GM inequality with a free positive parameter. -/
private lemma two_mul_le_of_pos_cutB {x y t : ℝ} (ht : 0 < t) :
    2 * x * y ≤ t * x ^ 2 + y ^ 2 / t := by
  have h : 0 ≤ (t * x - y) ^ 2 := sq_nonneg _
  have htne : t ≠ 0 := ne_of_gt ht
  have h2 : 2 * x * y * t ≤ (t * x ^ 2 + y ^ 2 / t) * t := by
    field_simp
    nlinarith [h]
  exact le_of_mul_le_mul_right h2 ht

/-! ## 2. The per-slot bound -/

/-- The abstract `p`-pointwise comparison of two slot energies. -/
private theorem slotY_aux {n : ℕ} {L t : ℝ} (hL' : 0 < L)
    {A B : Submission.BoseGases.X (n + 1) → ℂ}
    (ht : 0 < t) {μ : Measure (Submission.BoseGases.X (n + 1))}
    (hA : Integrable (fun x => ‖A x‖ ^ 2) μ) (hB : Integrable (fun x => ‖B x‖ ^ 2) μ)
    (hD : Integrable (fun x => ‖A x - B x‖ ^ 2) μ) :
    |(L ^ 3)⁻¹ * (∫ x, ‖A x‖ ^ 2 ∂μ) - (L ^ 3)⁻¹ * (∫ x, ‖B x‖ ^ 2 ∂μ)|
      ≤ t * ((L ^ 3)⁻¹ * (∫ x, ‖B x‖ ^ 2 ∂μ))
        + t⁻¹ * ((L ^ 3)⁻¹ * (∫ x, ‖A x - B x‖ ^ 2 ∂μ))
        + (L ^ 3)⁻¹ * (∫ x, ‖A x - B x‖ ^ 2 ∂μ) := by
  have h3 : (0 : ℝ) < L ^ 3 := by positivity
  have hsub : (∫ x, ‖A x‖ ^ 2 ∂μ) - (∫ x, ‖B x‖ ^ 2 ∂μ)
      = ∫ x, (‖A x‖ ^ 2 - ‖B x‖ ^ 2) ∂μ := (MeasureTheory.integral_sub hA hB).symm
  have hIntRhs : Integrable (fun x => t * ‖B x‖ ^ 2 + t⁻¹ * ‖A x - B x‖ ^ 2
      + ‖A x - B x‖ ^ 2) μ := ((hB.const_mul t).add (hD.const_mul t⁻¹)).add hD
  have habs : |∫ x, (‖A x‖ ^ 2 - ‖B x‖ ^ 2) ∂μ| ≤ ∫ x, |‖A x‖ ^ 2 - ‖B x‖ ^ 2| ∂μ := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := μ)
        (fun x : Submission.BoseGases.X (n + 1) => ‖A x‖ ^ 2 - ‖B x‖ ^ 2)
  have key : |∫ x, (‖A x‖ ^ 2 - ‖B x‖ ^ 2) ∂μ|
      ≤ ∫ x, (t * ‖B x‖ ^ 2 + t⁻¹ * ‖A x - B x‖ ^ 2 + ‖A x - B x‖ ^ 2) ∂μ := by
    refine habs.trans ?_
    refine MeasureTheory.integral_mono_ae (hA.sub hB).abs hIntRhs ?_
    filter_upwards with x
    have h1 := abs_normSq_sub_le_cutB (A x) (B x)
    have h2 : 2 * ‖B x‖ * ‖A x - B x‖ ≤ t * ‖B x‖ ^ 2 + t⁻¹ * ‖A x - B x‖ ^ 2 := by
      have h := two_mul_le_of_pos_cutB (x := ‖B x‖) (y := ‖A x - B x‖) ht
      rw [div_eq_mul_inv, mul_comm (‖A x - B x‖ ^ 2) t⁻¹] at h
      linarith
    linarith
  have hL3 : (0 : ℝ) < (L ^ 3)⁻¹ := inv_pos.mpr h3
  calc |(L ^ 3)⁻¹ * (∫ x, ‖A x‖ ^ 2 ∂μ) - (L ^ 3)⁻¹ * (∫ x, ‖B x‖ ^ 2 ∂μ)|
      = (L ^ 3)⁻¹ * |(∫ x, ‖A x‖ ^ 2 ∂μ) - (∫ x, ‖B x‖ ^ 2 ∂μ)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hL3.le]
    _ = (L ^ 3)⁻¹ * |∫ x, (‖A x‖ ^ 2 - ‖B x‖ ^ 2) ∂μ| := by rw [hsub]
    _ ≤ (L ^ 3)⁻¹ * ∫ x, (t * ‖B x‖ ^ 2 + t⁻¹ * ‖A x - B x‖ ^ 2
          + ‖A x - B x‖ ^ 2) ∂μ := mul_le_mul_of_nonneg_left key hL3.le
    _ = t * ((L ^ 3)⁻¹ * (∫ x, ‖B x‖ ^ 2 ∂μ))
        + t⁻¹ * ((L ^ 3)⁻¹ * (∫ x, ‖A x - B x‖ ^ 2 ∂μ))
        + (L ^ 3)⁻¹ * (∫ x, ‖A x - B x‖ ^ 2 ∂μ) := by
        have h1 : Integrable (fun x : Submission.BoseGases.X (n + 1) =>
            t * ‖B x‖ ^ 2 + t⁻¹ * ‖A x - B x‖ ^ 2) μ :=
          (hB.const_mul t).add (hD.const_mul t⁻¹)
        rw [MeasureTheory.integral_add h1 hD,
          MeasureTheory.integral_add (hB.const_mul t) (hD.const_mul t⁻¹),
          MeasureTheory.integral_const_mul (f := fun x : Submission.BoseGases.X (n + 1) => ‖B x‖ ^ 2)
            (r := t),
          MeasureTheory.integral_const_mul (f := fun x : Submission.BoseGases.X (n + 1) =>
            ‖A x - B x‖ ^ 2) (r := t⁻¹)]
        ring

/-- The `p`-pointwise comparison of the slot energies of two states. -/
private theorem slotY_diff_le {n : ℕ} {L d : ℝ} (hL : 0 < L) (u : E3)
    (i : Fin (n + 1)) (v w : Submission.BoseGases.X (n + 1) → ℝ) {t : ℝ} (ht : 0 < t)
    (hXV : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i v p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (hXW : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i w p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (hXD : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i v p x
        - slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i w p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (p : E3) :
    |slotY L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i v p
      - slotY L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i w p|
      ≤ t * (slotY L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i w p)
        + t⁻¹ * (slotYDiff L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i v w p)
        + (slotYDiff L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i v w p) := by
  unfold slotY slotYDiff
  exact slotY_aux (L := L) (t := t) hL ht
    (A := fun x => slotAmpF L (Submission.BoseGases.dlBox L d u)
      (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i v p x)
    (B := fun x => slotAmpF L (Submission.BoseGases.dlBox L d u)
      (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i w p x)
    (μ := volume.restrict (Submission.BoseGases.abox (n + 1) L)) (hXV p) (hXW p) (hXD p)

/-- The abstract `p`-integral comparison. -/
private theorem slotFormL_aux {c' t : ℝ} {Yv Yw YD : E3 → ℝ} (ht : 0 < t)
    (hFV : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yv p))
    (hFW : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p))
    (hFD : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p))
    (hbound : ∀ p : E3, |Yv p - Yw p| ≤ t * Yw p + t⁻¹ * YD p + YD p) :
    |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yv p)
      - ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)|
      ≤ t * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p))
        + t⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p))
        + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p) := by
  have hpos : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  have hFnn : ∀ p : E3, 0 ≤ Submission.BoseGases.fsKinCoeff c' ‖p‖ :=
    fun p => Submission.BoseGases.fsKinCoeff_nonneg c' ‖p‖
  -- the `p`-integrand algebra
  have hdiff : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yv p)
      - (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)
      = ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p) := by
    rw [← MeasureTheory.integral_sub hFV hFW]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Pi.sub_apply]; ring)
  have hInt1 : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p)) :=
    (hFV.sub hFW).congr (Filter.Eventually.of_forall fun p => by
      simp only [Pi.sub_apply]; ring)
  have hInt2 : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yw p - Yv p)) :=
    (hFW.sub hFV).congr (Filter.Eventually.of_forall fun p => by
      simp only [Pi.sub_apply]; ring)
  have hInt1' : Integrable (fun p : E3 => t * (Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)
      + t⁻¹ * (Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p)) :=
    (hFW.const_mul t).add (hFD.const_mul t⁻¹)
  have hRhs : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c' ‖p‖ *
      (t * Yw p + t⁻¹ * YD p + YD p)) := by
    refine (hInt1'.add hFD).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]; ring
  have hmono1 : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p))
      ≤ ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (t * Yw p + t⁻¹ * YD p + YD p) :=
    MeasureTheory.integral_mono_ae hInt1 hRhs (Filter.Eventually.of_forall fun p =>
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound p)) (hFnn p))
  have hmono2 : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yw p - Yv p))
      ≤ ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (t * Yw p + t⁻¹ * YD p + YD p) :=
    MeasureTheory.integral_mono_ae hInt2 hRhs (Filter.Eventually.of_forall fun p =>
      mul_le_mul_of_nonneg_left (by
        rw [show Yw p - Yv p = -(Yv p - Yw p) from by ring]
        exact le_trans (neg_le_abs _) (hbound p)) (hFnn p))
  have hneg : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yw p - Yv p))
      = - ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p) := by
    rw [← MeasureTheory.integral_neg]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Pi.sub_apply]; ring)
  have hkey : |∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p)|
      ≤ ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (t * Yw p + t⁻¹ * YD p + YD p) := by
    rw [abs_le]
    exact ⟨by rw [hneg] at hmono2; linarith, hmono1⟩
  -- the integral arithmetic
  have harith : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (t * Yw p + t⁻¹ * YD p + YD p))
      = t * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)
        + t⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p)
        + ∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p := by
    have hcongr : (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (t * Yw p + t⁻¹ * YD p + YD p))
        = ∫ p : E3, (t * (Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)
          + t⁻¹ * (Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p)
          + Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    rw [hcongr, MeasureTheory.integral_add hInt1' hFD,
      MeasureTheory.integral_add (hFW.const_mul t) (hFD.const_mul t⁻¹),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yv p)
        - ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)|
      = ((2 * Real.pi) ^ 3)⁻¹ *
          |(∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yv p)
            - (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hpos.le]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          |∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * (Yv p - Yw p)| := by rw [hdiff]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ *
          (t * Yw p + t⁻¹ * YD p + YD p)) := mul_le_mul_of_nonneg_left hkey hpos.le
    _ = t * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * Yw p))
        + t⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p))
        + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff c' ‖p‖ * YD p) := by
        rw [harith]; ring

/-- The per-slot bound in the `p`-integral: the comparison of the slot forms of two states. -/
private theorem slotFormL_bound {n : ℕ} {L d c : ℝ} (hL : 0 < L) (u : E3)
    (i : Fin (n + 1)) (v w : Submission.BoseGases.X (n + 1) → ℝ) {t : ℝ} (ht : 0 < t)
    (hXV : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i v p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (hXW : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i w p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (hXD : ∀ p : E3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i v p x
        - slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i w p x‖ ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (hFV : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      slotY L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i v p))
    (hFW : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      slotY L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i w p))
    (hFD : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      slotYDiff L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i v w p)) :
    |slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i v
      - slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i w|
      ≤ t * slotFormL L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i w
        + t⁻¹ * slotFormDiff L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i v w
        + slotFormDiff L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) i v w := by
  unfold slotFormL slotFormDiff
  exact slotFormL_aux (c' := c) ht hFV hFW hFD
    (fun p => slotY_diff_le hL u i v w ht hXV hXW hXD p)

/-- The general squeeze step: a `δ`-dependent upper bound with a `√(B δ + δ²)` tuning. -/
private lemma squeeze_aux {G : ℝ → ℝ} {H : ℝ} {Bf : ℝ → ℝ}
    (hB : Filter.Tendsto Bf (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hBnn : ∀ δ : ℝ, 0 < δ → 0 ≤ Bf δ)
    (hbound : ∀ δ : ℝ, 0 < δ → ∀ t : ℝ, 0 < t →
      |G δ - H| ≤ t * H + t⁻¹ * Bf δ + Bf δ) :
    Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds H) := by
  have hsqrt : Filter.Tendsto (fun δ : ℝ => Real.sqrt (Bf δ + δ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h2 : Filter.Tendsto (fun δ : ℝ => δ ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using h.pow 2
    have hcont : Filter.Tendsto Real.sqrt (nhds 0) (nhds 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    refine hcont.comp ?_
    simpa using hB.add h2
  have hg : Filter.Tendsto (fun δ : ℝ =>
      Real.sqrt (Bf δ + δ ^ 2) * H + Real.sqrt (Bf δ + δ ^ 2) + Bf δ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun δ : ℝ => Real.sqrt (Bf δ + δ ^ 2) * H)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hsqrt.mul_const H
    have h3 : Filter.Tendsto (fun δ : ℝ =>
        Real.sqrt (Bf δ + δ ^ 2) * H + Real.sqrt (Bf δ + δ ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using h1.add hsqrt
    simpa using h3.add hB
  have hbd : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖G δ - H‖ ≤ Real.sqrt (Bf δ + δ ^ 2) * H + Real.sqrt (Bf δ + δ ^ 2) + Bf δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [Real.norm_eq_abs]
    have hδpos : (0 : ℝ) < δ := hδ
    have hB0 : 0 ≤ Bf δ := hBnn δ hδpos
    have hpos : 0 < Bf δ + δ ^ 2 := by
      have := sq_pos_of_ne_zero (ne_of_gt hδpos)
      linarith
    have ht0 : 0 < Real.sqrt (Bf δ + δ ^ 2) := Real.sqrt_pos.mpr hpos
    have ht2 : Bf δ ≤ Real.sqrt (Bf δ + δ ^ 2) * Real.sqrt (Bf δ + δ ^ 2) := by
      rw [← sq, Real.sq_sqrt hpos.le]
      linarith [sq_nonneg δ]
    have h := hbound δ hδ _ ht0
    have hle : Bf δ / Real.sqrt (Bf δ + δ ^ 2) ≤ Real.sqrt (Bf δ + δ ^ 2) := by
      rw [div_le_iff₀ ht0]
      exact ht2
    have hexp : (Real.sqrt (Bf δ + δ ^ 2))⁻¹ * Bf δ
        = Bf δ / Real.sqrt (Bf δ + δ ^ 2) := inv_mul_eq_div _ _
    rw [hexp] at h
    linarith [h, hle]
  have hnorm : Filter.Tendsto (fun δ : ℝ => ‖G δ - H‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun δ => norm_nonneg _) hbd hg
  have h1 : Filter.Tendsto (fun δ : ℝ => G δ - H) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have h3 : Filter.Tendsto (fun δ : ℝ => (G δ - H) + H)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds H) := by
    have hc : Filter.Tendsto (fun _ : ℝ => H) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds H) :=
      tendsto_const_nhds
    simpa using h1.add hc
  exact h3.congr fun δ => by ring

/-- The assembled convergence of the slot-form sums. -/
private theorem main_slotTendsto {n : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) {Cb : ℝ}
    (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n + 1) L, |ψ x| ≤ Cb)
    {K : ℝ} {γ : ℝ → E3 → ℝ} (hcut : IsCutFamily L d u K γ) :
    Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n + 1),
        slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
          (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ i : Fin (n + 1),
        slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
          (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
  have hCut := B1Bfix.cut_slotForm_integrable (c := c) hL hd u hψ hCb hψb hcut
  have hSharp := B1Bfix.sharp_slotForm_integrable (c := c) hL hd u hψ hCb hψb
  have hDiff := B1Bfix.ampDiff_form_tendstoB (c := c) hL hd u hψ hCb hψb hcut
  have hX := B1Bfix.slotAmp_x_integrable hL hd u hψ hCb hψb hcut
  have hXD := B1Bfix.slotAmpDiff_x_integrable hL hd u hψ hCb hψb hcut
  -- the `p`-level difference tends to zero
  have hDTend : Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n + 1),
      slotFormDiff L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
        (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [slotFormDiff, slotYDiff, slotAmpDiff, slotAmpF] using hDiff.2
  -- the per-`δ` bound
  have hPoint : ∀ δ : ℝ, 0 < δ → ∀ t : ℝ, 0 < t →
      |(∑ i : Fin (n + 1),
          slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ))
        - (∑ i : Fin (n + 1),
          slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))|
      ≤ t * (∑ i : Fin (n + 1),
          slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
        + t⁻¹ * (∑ i : Fin (n + 1),
          slotFormDiff L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
        + (∑ i : Fin (n + 1),
          slotFormDiff L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)) := by
    intro δ hδ t ht
    have hper : ∀ i : Fin (n + 1),
        |slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ)
          - slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)|
        ≤ t * slotFormL L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          + t⁻¹ * slotFormDiff L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          + slotFormDiff L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) :=
      fun i => slotFormL_bound hL u i _ _ ht (fun p => (hX.1 δ hδ i p)) (fun p => hX.2 i p)
        (fun p => hXD δ hδ i p) (hCut δ hδ i) (hSharp i) (hDiff.1 δ hδ i)
    have hsum : |(∑ i : Fin (n + 1),
          slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (cutProd (γ δ) ψ))
        - (∑ i : Fin (n + 1),
          slotFormL L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))|
        ≤ ∑ i : Fin (n + 1),
          (t * slotFormL L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
              (Submission.BoseGases.fsKinCoeff c) i
              (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            + t⁻¹ * slotFormDiff L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
              (Submission.BoseGases.fsKinCoeff c) i
              (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            + slotFormDiff L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
              (Submission.BoseGases.fsKinCoeff c) i
              (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)) := by
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hper i)
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- the nonnegativity of the difference form
  have hBnn : ∀ δ : ℝ, 0 < δ → 0 ≤ (∑ i : Fin (n + 1),
      slotFormDiff L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) i
        (cutProd (γ δ) ψ) (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)) := by
    intro δ hδ
    refine Finset.sum_nonneg fun i _ => ?_
    rw [slotFormDiff]
    refine mul_nonneg (by positivity) (MeasureTheory.integral_nonneg_of_ae ?_)
    filter_upwards with p
    refine mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) ?_
    rw [slotYDiff]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le 3))
      (integral_nonneg fun x => sq_nonneg _)
  exact squeeze_aux hDTend hBnn hPoint

/-- The window vanishes off the sliding box. -/
private theorem chiB_eq_zero_of_notMem_dlBox_cutB {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∀ z : E3, z ∉ Submission.BoseGases.dlBox L d u → Submission.BoseGases.chiB L d u z = 0 := by
  intro z hz
  by_contra hne
  exact hz (Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hL hd u
    (subset_tsupport _ (Function.mem_support.mpr hne)))

/-- The target statement, assembled from the pieces (scratch version). -/
theorem tendsto_tBdiagFormInd_cutB {k : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox k L, |ψ x| ≤ Cb) :
    Filter.Tendsto (fun δ : ℝ => Work.UBBInputs8.tBdiagFormInd L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c)
        (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
        (Submission.BoseGases.fsKinCoeff c)
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
  rcases k with _ | n
  · -- the zero-particle case: both forms vanish
    have h0 : ∀ Ψ : Submission.BoseGases.X 0 → ℝ, Work.UBBInputs8.tBdiagFormInd L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) (Submission.BoseGases.fsKinCoeff c) Ψ = 0 := by
      intro Ψ
      simp [Work.UBBInputs8.tBdiagFormInd]
    simp only [h0]
    exact tendsto_const_nhds
  · have hmain := main_slotTendsto (n := n) (c := c) hL hd u hψ hCb hψb hcut
    have hEq : ∀ Ψ : Submission.BoseGases.X (n + 1) → ℝ,
        Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) Ψ
        = ∑ i : Fin (n + 1), slotFormL L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i Ψ := by
      intro Ψ
      rw [Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (Submission.BoseGases.fsKinCoeff c) Ψ
        (chiB_eq_zero_of_notMem_dlBox_cutB hL hd u)]
      exact tBdiagForm_eq_sum_slotFormL L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
        (Submission.BoseGases.fsKinCoeff c) Ψ
    rw [show (fun δ : ℝ => Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
          (Submission.BoseGases.fsKinCoeff c) (cutProd (γ δ) ψ))
        = fun δ : ℝ => ∑ i : Fin (n + 1), slotFormL L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u)
            (Submission.BoseGases.fsKinCoeff c) i (cutProd (γ δ) ψ) from
      funext fun δ => hEq (cutProd (γ δ) ψ),
      hEq (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)]
    exact hmain

end Work.BoseFixB1B
