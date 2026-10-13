/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/srestBound`: the `Srest` term of the per-slot transport estimate

The Leibniz expansion of the transport pairing is split (in `FinalAux`) into the main summand
`Smain`, the delicate summand `Sdel` and the remainder `Srest`, and `FinalAux.canonW_mul_Srest_le`
proves the *pointwise* bound

  `canonW q z θ · |Srest f g a b z θ| · |mixed b a g z θ| ≤ 6400 · Maj1 α f g Mf MK Mg z θ`

on the open quadrant, where

  `Maj1 = (Mf + MK) · HkIntegrand α 4 g + Mg · √(HkIntegrand α 4 f) · √(HkIntegrand α 4 g)`.

This module turns that pointwise estimate into the two conclusions needed by the per-slot
assembly (integrability of the angular marginal, and the bound on the iterated integral):

* `continuousOn_uncurry_Srest` — `Srest f g a b` is continuous on the open quadrant as soon as
  `f` and `g` are (`SmoothOpen`), which supplies the a.e. strong measurability of the marginal;
* `srest_aux` — the abstract domination argument: a pointwise majorant of the shape `6400 · Maj1`
  whose radial marginal is integrable (through the two slot energies of `HkMem α 4 f`,
  `HkMem α 4 g` and one Cauchy–Schwarz in `z`) yields both the integrability of the marginal and
  the bound `6400 · ((Mf + MK) · HkSq α 4 g + Mg · |f|_{ℋ⁴} |g|_{ℋ⁴})`;
* `srestBound` — the instantiation.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.slotCS
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.TransportS.T2Sup.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.TransportS.SlotT2

/-! ## Continuity of the remainder on the open quadrant -/

/-- Each summand of `Srest` (a product of two mixed derivatives of `f` resp. `g` with a
binomial coefficient) is continuous on the open quadrant when `f` and `g` are. -/
theorem continuousOn_uncurry_Srest {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) :
    ContinuousOn (Function.uncurry (Srest f g a b))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => Srest f g a b p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    simp only [Srest]
    refine continuousOn_finsetSum _ (fun a1 _ => continuousOn_finsetSum _ (fun b1 _ => ?_))
    split_ifs with h
    · exact continuousOn_const
    · exact continuousOn_const.mul
        (((hf.mixed b1 a1).continuousOn).mul
          ((hg.mixed (b + 1 - b1) (a - a1)).continuousOn))
  exact hmain

/-! ## The abstract domination argument -/

/-- **The `Srest` estimate.**  Given a pointwise majorant of the shape `6400 · Maj1` for the
`Srest`-pairing on the open quadrant, the a.e. strong measurability of the pairing (supplied
here by continuity on the open quadrant), and the `ℋ⁴`-membership of `f` and `g`, the angular
marginal is integrable and its iterated integral is at most

  `6400 · ((Mf + MK) · HkSq α 4 g + Mg · (HkNorm α 4 f · HkNorm α 4 g))`.

The bound is `∫_z (∫_θ |…|) ≤ ∫_z 6400 · ((Mf + MK) · ∫_θ HkIntegrand g + Mg · √Ff · √Gg)`,
with the angular Cauchy–Schwarz `∫_θ √(HkIntegrand f) √(HkIntegrand g) ≤ √Ff · √Gg` and the
radial Cauchy–Schwarz `∫_z √Ff · √Gg ≤ |f|_{ℋ⁴} |g|_{ℋ⁴}`. -/
theorem srest_aux {α : ℝ}
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hcont : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ| ≤ 6400 * Maj1 α f g Mf MK Mg z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the two slot energies and their integrability
  have hFf_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      Work.Spaces.Iz := hmf.2
  have hGg_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      Work.Spaces.Iz := hmg.2
  have hFf_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
  have hGg_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  have hCS_int : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      Work.Spaces.Iz :=
    integrable_sqrt_mul_sqrt_slice hFf_int hGg_int hFf_nn hGg_nn
  have hLim_int : MeasureTheory.IntegrableOn
      (fun z => 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      Work.Spaces.Iz :=
    ((hGg_int.const_mul (Mf + MK)).add (hCS_int.const_mul Mg)).const_mul 6400
  -- the angular slice of the majorant is integrable, for every `z ∈ Iz`
  have hMaj_slice_int : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.Integrable (fun θ => Maj1 α f g Mf MK Mg z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hmg.1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (integrable_sqrt_mul_sqrt_slice (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (hmf.1 z hz) (hmg.1 z hz)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).const_mul Mg
    refine (h1.add h2).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply, Maj1]
  -- the angular slice bound `∫ |·| ≤ 6400 ∫ Maj1`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        ≤ 6400 * ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (fun θ : ℝ =>
          |Work.FTS.TransportS.SlotT2.canonW q 0 θ * Srest f g a b 0 θ
            * Work.Spaces.mixed b a g 0 θ|) = fun _ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul, zero_mul, abs_zero]
      rw [hzero, MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num)
        (MeasureTheory.setIntegral_nonneg hIθm
          (fun θ _ => Maj1_nonneg (by linarith [hMf, hMK]) hMg 0 θ))
    · rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        (g := fun θ => 6400 * Maj1 α f g Mf MK Mg z θ) ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ => abs_nonneg _)
      · exact (hMaj_slice_int z hz).const_mul 6400
      · exact ae_of_forall_Ioo (fun θ hθ => hpt z θ hz0 hθ.1 hθ.2)
  -- the angular slice of `Maj1` is bounded by the explicit radial majorant
  have hMaj_le : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
        ≤ (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ => (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hmg.1 z hz).const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (integrable_sqrt_mul_sqrt_slice (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (hmf.1 z hz) (hmg.1 z hz)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).const_mul Mg
    have hsplit : (∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
        = (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
      simp only [Maj1]
      rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hcs := cs_sqrt_le (s := Work.Spaces.Iθ)
      (A := fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
      (B := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (hmf.1 z hz) (hmg.1 z hz)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    rw [hsplit]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hcs hMg)
      ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
  -- the slice bound in the form used by the radial domination
  have hslice2 : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|)
        ≤ 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    intro z hz
    exact le_trans (hslice z hz)
      (mul_le_mul_of_nonneg_left (hMaj_le z hz) (by norm_num))
  -- the marginal bound
  have hmarg : ∀ z ∈ Work.Spaces.Iz,
      ‖∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ‖
        ≤ 6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    intro z hz
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) ?_
    simpa only [Real.norm_eq_abs] using hslice2 z hz
  -- a.e. strong measurability of the marginal
  have hInner_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * Srest f g a b p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) hcont).integral_prod_right'
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa [Function.uncurry] using h
  -- the integrability of the marginal
  have hInner_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' hLim_int hInner_aesm
      (MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => hmarg z hz))
  refine ⟨hInner_int, ?_⟩
  -- the two exact identities for the majorant integral
  have hGgEq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ) = Work.Spaces.HkSq α 4 g := rfl
  have hCSeq : (∫ z in Work.Spaces.Iz,
        Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
    have h := cs_sqrt_le (s := Work.Spaces.Iz)
      (A := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (B := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      hFf_int hGg_int hFf_nn hGg_nn
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    simpa only [Work.Spaces.HkSq] using h
  have hCompute : (∫ z in Work.Spaces.Iz,
        6400 * ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add (hGg_int.const_mul (Mf + MK)) (hCS_int.const_mul Mg)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (le_of_eq (by rw [hGgEq])) (mul_le_mul_of_nonneg_left hCSeq hMg))
      (by norm_num)
  have hstep1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ| ≤
      ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
    simpa only [Real.norm_eq_abs] using h
  have hstep2 : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ|) ≤
      ∫ z in Work.Spaces.Iz, 6400 * ((Mf + MK) *
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hLim_int
      (MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => by
        simpa only [Real.norm_eq_abs] using hmarg z hz))
  exact le_trans hstep1 (le_trans hstep2 hCompute)

/-! ## The requested statement -/

theorem srestBound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg) (hqnn : 0 ≤ q)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hqcase : q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Srest f g a b z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ((continuousOn_canonW q).mul (continuousOn_uncurry_Srest hFsm hGsm a b)).mul
      ((hGsm.mixed b a).continuousOn)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
        * Work.Spaces.mixed b a g z θ| ≤ 6400 * Maj1 α f g Mf MK Mg z θ := by
    intro z θ hz hθ hθ2
    have h := canonW_mul_Srest_le (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b)
      (q := q) (Mf := Mf) (MK := MK) (Mg := Mg) hMf hMK hMg hqnn hab hq0 hqγ hqcase
      hFsup hFσ hGsup z θ hz hθ hθ2
    calc |Work.FTS.TransportS.SlotT2.canonW q z θ * Srest f g a b z θ
          * Work.Spaces.mixed b a g z θ|
        = Work.FTS.TransportS.SlotT2.canonW q z θ * |Srest f g a b z θ|
            * |Work.Spaces.mixed b a g z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)]
      _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := h
  exact srest_aux hMf hMK hMg hmf hmg hcont hpt

end Work.FTS.TransportS.T2Sup
