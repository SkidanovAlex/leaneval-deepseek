import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.FinalMain
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Stability.mul_rpow_le

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

/-! ## Bookkeeping for the majorant `Maj1` -/

/-- Every `θ`-slice of the majorant `Maj1` is integrable. -/
theorem integrableOn_Maj1_slice_fts {α : ℝ} {f g : ℝ → ℝ → ℝ} {Mf MK Mg : ℝ}
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Maj1 α f g Mf MK Mg z θ) Work.Spaces.Iθ := by
  intro z hz
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ) Work.Spaces.Iθ :=
    (hmemg.1 z hz).const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))) Work.Spaces.Iθ :=
    (integrable_sqrt_mul_sqrt_slice (hmemf.1 z hz) (hmemg.1 z hz)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).const_mul Mg
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [Pi.add_apply, Maj1]


/-! ## The `Sdel` summand at exponents `q ≤ η` -/

theorem sdel_integral_le_of_eta {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg)
    (hqnn : 0 ≤ q) (hab : a + b ≤ 4) (hq0 : a = 0 → q ≤ Work.Spaces.eta)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : q ≤ Work.Spaces.eta)
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
      ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) := by
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hpoint : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
        ≤ 16 * ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ := by
    intro z hz
    have hnorm : |∫ θ in Work.Spaces.Iθ,
          canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |canonW q z θ * Sdel f g a b z θ
          * Work.Spaces.mixed b a g z θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ))
    refine le_trans hnorm ?_
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun θ => abs_nonneg _)) ((integrableOn_Maj1_slice_fts hmemf hmemg z hz).const_mul 16) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      filter_upwards with θ
      rw [canonW_zero_z, zero_mul, zero_mul, abs_zero]
      exact mul_nonneg (by norm_num) (Maj1_nonneg (add_nonneg hMf hMK) hMg 0 θ)
    · refine ae_of_forall_Ioo (fun θ hθ => ?_)
      have h := canonW_Sdel_le (α := α) hα hα1 hMf hMK hMg hqnn hab hq0 hqγ hqη
        hFsup hFσ hGsup z θ hz0 hθ.1 hθ.2
      calc |canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
          = canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
        _ ≤ 16 * Maj1 α f g Mf MK Mg z θ := h
  have hFf_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      Work.Spaces.Iz := hmemf.2
  have hGg_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      Work.Spaces.Iz := hmemg.2
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
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun z => (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)))
      Work.Spaces.Iz :=
    (hGg_int.const_mul (Mf + MK)).add (hCS_int.const_mul Mg)
  have hstep1 : |∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ
          * Work.Spaces.mixed b a g z θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ
          * Work.Spaces.mixed b a g z θ))
  have hstep2 : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ
          * Work.Spaces.mixed b a g z θ|)
      ≤ ∫ z in Work.Spaces.Iz, 16 * ((Mf + MK) *
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun z => abs_nonneg _)) (hmaj_int.const_mul 16) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz =>
      le_trans (hpoint z hz)
        (mul_le_mul_of_nonneg_left (integral_Maj1_le hmemf hmemg hMg hz) (by norm_num)))
  have hcompute : (∫ z in Work.Spaces.Iz, 16 * ((Mf + MK) *
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      = 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (∫ z in Work.Spaces.Iz,
              Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
                * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hGg_int.const_mul (Mf + MK)) (hCS_int.const_mul Mg),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rfl
  have hCS2 : (∫ z in Work.Spaces.Iz,
        Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
    have h := cs_sqrt_le (s := Work.Spaces.Iz) hFf_int hGg_int hFf_nn hGg_nn
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    simpa only [Work.Spaces.HkSq] using h
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW q z θ * Sdel f g a b z θ
          * Work.Spaces.mixed b a g z θ| := hstep1
    _ ≤ ∫ z in Work.Spaces.Iz, 16 * ((Mf + MK) *
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := hstep2
    _ = 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (∫ z in Work.Spaces.Iz,
              Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
                * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := hcompute
    _ ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hCS2 hMg))
          (by norm_num)

/-! ## The delicate `Sdel` summand at the slot `(1,3)` with `q = γ` -/


/-! ## The arithmetic of the final constant -/

private theorem slot_arith {r Xf Kf Xg Cs Cl Cg Cd : ℝ}
    (hr1 : 1 ≤ r) (hr0 : 0 ≤ r) (hXf : 0 ≤ Xf) (hKf : 0 ≤ Kf) (hXg : 0 ≤ Xg)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (h10 : Real.sqrt 10 ≤ 10) :
    2 * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      ≤ 10 ^ 6 * (Cs + Cl + Cg + Cd + 1) * r * (Xf + Kf) * Xg ^ 2 := by
  have hsq : (0 : ℝ) ≤ Xg ^ 2 := sq_nonneg Xg
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  set T : ℝ := r * (Xf + Kf) * Xg ^ 2 with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have h1 : r * Xf * Xg ^ 2 ≤ T := by
    rw [hTdef]; nlinarith [mul_nonneg hr0 (mul_nonneg hKf hsq)]
  have h3 : Kf * Xg ^ 2 ≤ T := by
    rw [hTdef]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1) (mul_nonneg hKf hsq),
      mul_nonneg hr0 (mul_nonneg hXf hsq), mul_nonneg hKf hsq]
  have H1 : Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2 ≤ 10 * Cs * T := by
    rw [show Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2
        = Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cs * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCs hsq10)
      _ ≤ 10 * Cs * T := by
          have hc : Cs * Real.sqrt 10 ≤ 10 * Cs := by nlinarith [hCs, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H2 : Cl * Kf * Xg ^ 2 ≤ Cl * T := by
    rw [show Cl * Kf * Xg ^ 2 = Cl * (Kf * Xg ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left h3 hCl
  have H3 : Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg) ≤ 10 * Cg * T := by
    rw [show Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg)
        = Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cg * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCg hsq10)
      _ ≤ 10 * Cg * T := by
          have hc : Cg * Real.sqrt 10 ≤ 10 * Cg := by nlinarith [hCg, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H4 : Cd * r * (Xf + Kf) * Xg ^ 2 = Cd * T := by rw [hTdef]; ring
  have hLHS : 2 * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      = 2 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
        + (6400 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
          + (6400 * (Cl * Kf * Xg ^ 2)
            + (6400 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
              + (16 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
                + (16 * (Cl * Kf * Xg ^ 2)
                  + (16 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
                    + Cd * r * (Xf + Kf) * Xg ^ 2)))))) := by ring
  rw [hLHS, H4]
  have hA : (0 : ℝ) ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCsA : Cs ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hClA : Cl ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCgA : Cg ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCdA : Cd ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hbig : (0 : ℝ) ≤ 10 ^ 6 := by norm_num
  nlinarith [H1, H2, H3, hT, mul_le_mul_of_nonneg_left hCsA hT,
    mul_le_mul_of_nonneg_left hClA hT, mul_le_mul_of_nonneg_left hCgA hT,
    mul_le_mul_of_nonneg_left hCdA hT, mul_le_mul_of_nonneg_right hbig (mul_nonneg hA hT),
    hA, hT, hXg]


end Work.FTS.TransportS.T2Sup
