import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.absIntegralAddLe
import Submission.Work.FTS.TransportS.T2Sup.integrableOnSliceDelicate
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.T2Sup.delicateMargInt
import Submission.Work.FTS.TransportS.T2Sup.Main
import Submission.Work.FTS.TransportS.T2Sup.FinalMain
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS.TransportS.Slots

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

/-- The iterated integral of the majorant `Maj1`, bounded by the two `ℋ⁴`-energies
(angular Cauchy–Schwarz, then radial Cauchy–Schwarz). -/
theorem Maj1_integral_le_fts {α : ℝ} {f g : ℝ → ℝ → ℝ} {Mf MK Mg : ℝ}
    (hM : 0 ≤ Mf + MK) (hMg : 0 ≤ Mg)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
      ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := by
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
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
  have hLim_int : MeasureTheory.IntegrableOn
      (fun z => (Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)))
      Work.Spaces.Iz :=
    (hGg_int.const_mul (Mf + MK)).add (hCS_int.const_mul Mg)
  have hstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
            + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hLim_int ?_
    · exact Filter.Eventually.of_forall (fun z => MeasureTheory.setIntegral_nonneg hIθm
        (fun θ _ => Maj1_nonneg hM hMg z θ))
    · exact MeasureTheory.ae_restrict_of_forall_mem hIzm
        (fun z hz => integral_Maj1_le hmemf hmemg hMg hz)
  have hsplit : (∫ z in Work.Spaces.Iz,
        ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))))
      = (Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (∫ z in Work.Spaces.Iz,
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [MeasureTheory.integral_add (hGg_int.const_mul (Mf + MK)) (hCS_int.const_mul Mg),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rfl
  have hCS2 : (∫ z in Work.Spaces.Iz,
        Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
    have h := cs_sqrt_le (s := Work.Spaces.Iz) hFf_int hGg_int hFf_nn hGg_nn
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    simpa only [Work.Spaces.HkSq] using h
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Maj1 α f g Mf MK Mg z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          ((Mf + MK) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
            + Mg * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))) := hstep
    _ = (Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (∫ z in Work.Spaces.Iz,
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := hsplit
    _ ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hCS2 hMg)

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

theorem sdel_integral_le_of_gam {α Cd : ℝ} {f g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsf : Work.FTS.TransportS.T2SF α f)
    (hsg : Work.FTS.TransportS.T2SG α g)
    (hDelb : ∀ q : ℝ, 0 ≤ q → q ≤ Work.Spaces.gam α →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ Cd * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
      ≤ Cd * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgam : 0 ≤ Work.Spaces.gam α := le_of_lt hγpos
  have hHd_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iz :=
    delicateMargInt α (Work.Spaces.gam α) f g hα hα1 hgam le_rfl hsf hsg
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
        * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW (Work.Spaces.gam α) 0 θ * |Work.Spaces.DzIter 3 f 0 θ|
            * |Work.Spaces.mixed 1 1 g 0 θ| * |Work.Spaces.mixed 3 1 g 0 θ|)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · exact integrableOnSliceDelicate hα hα1 hsf.1 hsf.2.1
        (SmoothQuad.smoothOpen hsg.1.1) hsg.1.2.1 hz0
  have hpoint : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ
            * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ| := by
    intro z hz
    have hnorm : |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
            * Work.Spaces.mixed 3 1 g z θ))
    refine le_trans hnorm ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun θ => abs_nonneg _)) (hslice z hz) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      filter_upwards with θ
      rw [canonW_zero_z, zero_mul, zero_mul, abs_zero]
      simp
    · refine ae_of_forall_Ioo (fun θ hθ => ?_)
      dsimp only
      have hsdel : Sdel f g 1 3 z θ
          = Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed 1 1 g z θ := by
        simp only [Sdel, Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
      rw [hsdel, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
      simp only [Work.Spaces.mixed_zero_right]
      exact le_of_eq (by ring)
  have hstep1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ * Work.Spaces.mixed 3 1 g z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ))
  have hstep2 : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
            * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ| :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
      hHd_int (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => hpoint z hz))
  refine le_trans (le_trans hstep1 hstep2) ?_
  simpa only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.mixed_zero_right] using
    hDelb (Work.Spaces.gam α) hgam le_rfl

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

/-- Per-slot estimate in the canonical weight.  NOTE (route): take

* `Mf := Cs / √(gam α - 1) * Xn α f` with `Cs` from `Work.FTS.TransportS.sup_dz_le_hk`
  (this is an *α-dependent* bound — the `1/√(gam α - 1) = √10 · α^{-1/2}` factor is exactly
  the `α^{-1/2}` of the right-hand side, so **no** α-uniform bound on `D_z²f` is needed),
* `MK := Cl * CoefTh 1 f` with `Cl` from `Work.FTS.TransportS.flat_mixed_le 1` (used through
  `Work.FTS.TransportS.t2SupF_pth_le_coefTh` for the sup data of `∂_θf`),
* `Mg := Cg / √(gam α - 1) * Xn α g` with `Cg` from `Work.FTS.H2.T2Qaux.supQ_T2Q`.

Then rewrite the integral with `FinalAux.Ssum_eq_leibniz`, split
`FinalAux.Ssum_eq_Smain_Srest_Sdel`, bound the `Smain` part by `Main.topSlotBound` when
`a + b = 4` (and pointwise by `Main.canonW_mul_abs_le_slotW` when `a + b ≤ 3`), the `Srest` part
by `FinalAux.canonW_mul_Srest_le` (+ the two-level Cauchy–Schwarz of `Main.termBoundG` for the
`∫∫ √(HkIntegrand f)·√(HkIntegrand g)` term), and the `Sdel` part by `hDel`
(`delicateBound`) together with `integrableOnSliceDelicate` / `delicateMargInt` for the
integrability bookkeeping (`absIntegralAddLe` handles the triangle inequality without needing
integrability of both pieces). -/
theorem slotAbsBound (hDel : Work.FTS.TransportS.T2Sup.DelicateProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ),
      0 < α → α ≤ 1 → Work.FTS.TransportS.T2SF α f → Work.FTS.TransportS.T2SG α g →
      a + b ≤ 4 → 0 ≤ q →
      (a = 0 → q ≤ Work.Spaces.eta) → q ≤ Work.Spaces.gam α →
      (q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ
            * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Cs, hCs0, hCs⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cl, hCl0, hCl⟩ := Work.FTS.TransportS.flat_mixed_le 1
  obtain ⟨Cg, hCg0, hCg⟩ := Work.FTS.H2.T2Qaux.supQ_T2Q
  obtain ⟨Cd, hCd0, hCd⟩ := hDel
  refine ⟨10 ^ 6 * (Cs + Cl + Cg + Cd + 1), by positivity, ?_⟩
  intro α f g a b q hα hα1 hf hg hab hqnn hq0 hqγ hqcase
  have hFsm : Work.FTS.EllipticEst.SmoothOpen f := hf.smoothOpen
  have hmf : Work.Spaces.HkMem α 4 f := hf.hk
  have hGq : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hGsm : Work.FTS.EllipticEst.SmoothOpen g := SmoothQuad.smoothOpen hGq
  have hmg4 : Work.Spaces.HkMem α 4 g := hg.hk4
  have hmg5 : Work.Spaces.HkMem α 5 g := hg.hk5
  have hbdr : Work.FTS.Nonlin.BdryTraces α 4 g := hg.reg.2.2
  have hdec : Work.Spaces.DecayAll 4 g := hg.decay
  set Mf : ℝ := Cs / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f with hMfdef
  set MK : ℝ := Cl * Work.FTS.VocabO.CoefTh 1 f with hMKdef
  set Mg : ℝ := Cg / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g with hMgdef
  have hXn_f_nn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hXn_g_nn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hKf_nn : 0 ≤ Work.FTS.VocabO.CoefTh 1 f := coefTh_nonneg 1 f
  have hMf0 : 0 ≤ Mf := by
    rw [hMfdef]
    exact mul_nonneg (div_nonneg hCs0.le (Real.sqrt_nonneg _)) hXn_f_nn
  have hMK0 : 0 ≤ MK := by rw [hMKdef]; exact mul_nonneg hCl0.le hKf_nn
  have hMg0 : 0 ≤ Mg := by
    rw [hMgdef]
    exact mul_nonneg (div_nonneg hCg0.le (Real.sqrt_nonneg _)) hXn_g_nn
  have hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf := by
    intro j hj z θ hz hθ hθ2
    rw [hMfdef]
    exact hCs α f hα hα1 hFsm hmf j hj z θ hz hθ hθ2
  have hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ) := by
    intro j i hi hij z θ hz hθ hθ2
    have hK : ∀ b i' : ℕ, b + i' ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i' (Work.Spaces.pth f) z θ| ≤ Work.FTS.VocabO.CoefTh 1 f :=
      fun b i' hbi z θ hz hθ hθ2 => Work.FTS.TransportS.t2SupF_pth_le_coefTh hf hbi hz hθ hθ2
    have h := hCl f hFsm (Work.FTS.VocabO.CoefTh 1 f) hKf_nn hK i j hi hij z θ hz hθ hθ2
    rw [hMKdef]
    calc |Work.Spaces.mixed j i f z θ|
        ≤ Cl * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 1 f := h
      _ = (Cl * Work.FTS.VocabO.CoefTh 1 f) * Real.sin (2 * θ) := by ring
  have hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg := by
    intro j i hij z θ hz hθ hθ2
    rw [hMgdef]
    exact hCg α g j i hα hα1 hij hGq hdec hmg4 z hz θ ⟨hθ, hθ2⟩
  have hSmain := smainBound (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b) (q := q)
    (Mf := Mf) hMf0 hFsm hGq hmg4 hmg5 hbdr hab hq0 hqγ
    (fun z θ hz hθ hθ2 => hFsup 0 (by norm_num) z θ hz hθ hθ2)
    (fun z θ hz hθ hθ2 => hFsup 1 (by norm_num) z θ hz hθ hθ2)
  have hSrest := srestBound (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b) (q := q)
    (Mf := Mf) (MK := MK) (Mg := Mg) hMf0 hMK0 hMg0 hqnn hFsm hGsm hmf hmg4 hab
    hq0 hqγ hqcase hFsup hFσ hGsup
  set FA : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ with hFAdef
  set Fr : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ with hFrdef
  set Fd : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ with hFddef
  set FL : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    canonW q z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
      * Work.Spaces.mixed b a g z θ with hFLdef
  have hsliceA : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Smain f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · refine MeasureTheory.Integrable.mono' ((hmg5.1 z hz).const_mul Mf) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Smain f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        have hS : ContinuousOn (fun p : ℝ × ℝ => Smain f g a b p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
          simp only [Smain, Function.uncurry_apply_pair]
          exact hFsm.continuousOn.mul (hGsm.mixed (b + 1) a).continuousOn
        exact ((continuousOn_canonW q).mul hS).mul (hGsm.mixed b a).continuousOn
      · refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_Smain_le (α := α) (f := f) (g := g) hα hMf0 hqnn hab hq0 hqγ
          (fun z θ hz hθ hθ2 => hFsup 0 (by norm_num) z θ hz hθ hθ2) z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Smain f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ := h
  have hsliceR : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Srest f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · refine MeasureTheory.Integrable.mono'
          ((integrableOn_Maj1_slice_fts (α := α) (f := f) (g := g) (Mf := Mf) (MK := MK) (Mg := Mg) hmf hmg4 z hz).const_mul 6400) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Srest f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        exact ((continuousOn_canonW q).mul (continuousOn_uncurry_Srest hFsm hGsm a b)).mul
          (hGsm.mixed b a).continuousOn
      · refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_mul_Srest_le (α := α) hα hα1 (f := f) (g := g) (a := a) (b := b)
          (q := q) (Mf := Mf) (MK := MK) (Mg := Mg) hMf0 hMK0 hMg0 hqnn hab hq0 hqγ hqcase
          hFsup hFσ hGsup z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Srest f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := h
  have hsliceD : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * Sdel f g a b 0 θ * Work.Spaces.mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun θ => canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          canonW q p.1 p.2 * Sdel f g a b p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2) ?_ hz0
        have hS : ContinuousOn (fun p : ℝ × ℝ => Sdel f g a b p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
          simp only [Sdel, Function.uncurry_apply_pair]
          exact continuousOn_const.mul ((hFsm.mixed 3 0).continuousOn.mul
            ((hGsm.mixed (b - 2) a).continuousOn))
        exact ((continuousOn_canonW q).mul hS).mul (hGsm.mixed b a).continuousOn
      rcases hqcase with hqη | hqγ'
      · refine MeasureTheory.Integrable.mono'
            ((integrableOn_Maj1_slice_fts (α := α) (f := f) (g := g) (Mf := Mf) (MK := MK) (Mg := Mg) hmf hmg4 z hz).const_mul 16) haesm ?_
        refine ae_of_forall_Ioo (fun θ hθ => ?_)
        rw [Real.norm_eq_abs]
        have h := canonW_Sdel_le (α := α) hα hα1 hMf0 hMK0 hMg0 hqnn hab hq0 hqγ hqη
          hFsup hFσ hGsup z θ hz0 hθ.1 hθ.2
        calc |canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ|
            = canonW q z θ * |Sdel f g a b z θ| * |Work.Spaces.mixed b a g z θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          _ ≤ 16 * Maj1 α f g Mf MK Mg z θ := h
      · subst hqγ'
        by_cases hb2 : b ≤ 2
        · rw [show (fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g a b z θ
              * Work.Spaces.mixed b a g z θ) = fun _ => (0 : ℝ) from by
            funext θ
            rw [Sdel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
            ring]
          exact MeasureTheory.integrableOn_zero
        · have ha0 : a ≠ 0 := by
            intro h0
            exact absurd (hq0 h0) (not_le.mpr (eta_lt_gam_of_pos hα))
          have ha1 : a = 1 := by omega
          have hb3 : b = 3 := by omega
          have hmaj : MeasureTheory.IntegrableOn (fun θ => canonW (Work.Spaces.gam α) z θ
              * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
              * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iθ :=
            integrableOnSliceDelicate hα hα1 hFsm hmf hGsm hmg4 hz0
          refine MeasureTheory.Integrable.mono' hmaj haesm ?_
          refine ae_of_forall_Ioo (fun θ hθ => ?_)
          rw [Real.norm_eq_abs, ha1, hb3]
          have hsdel : Sdel f g 1 3 z θ
              = Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed 1 1 g z θ := by
            simp only [Sdel, Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
          rw [hsdel, abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
          simp only [Work.Spaces.mixed_zero_right]
          exact le_of_eq (by ring)
  have hsplit : ∀ z : ℝ, 0 < z → FL z = FA z + (Fr z + Fd z) := by
    intro z hz0
    have h1 : FL z = ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ := by
      simp only [hFLdef]
      refine MeasureTheory.integral_congr_ae ?_
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      show canonW q z θ * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          * Work.Spaces.mixed b a g z θ
        = canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ
      rw [Ssum_eq_leibniz b a hFsm hGsm z θ hz0 hθ.1 hθ.2]
    have h2 : (∫ θ in Work.Spaces.Iθ,
          canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show canonW q z θ * Ssum f g a b z θ * Work.Spaces.mixed b a g z θ
        = canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
          + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
            + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
      rw [Ssum_eq_Smain_Srest_Sdel]
      ring
    have h3 : (∫ θ in Work.Spaces.Iθ,
            (canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)))
        = FA z + (Fr z + Fd z) := by
      have hAB : (∫ θ in Work.Spaces.Iθ,
            canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ
              + (canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ))
          = (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
            + (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ) :=
        MeasureTheory.integral_add (hsliceA z hz0.le)
          ((hsliceR z hz0.le).add (hsliceD z hz0.le))
      have hBC : (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ
                + canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ)
          = (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Srest f g a b z θ * Work.Spaces.mixed b a g z θ)
            + (∫ θ in Work.Spaces.Iθ,
              canonW q z θ * Sdel f g a b z θ * Work.Spaces.mixed b a g z θ) :=
        MeasureTheory.integral_add (hsliceR z hz0.le) (hsliceD z hz0.le)
      rw [hAB, hBC]
    rw [h1, h2, h3]
  have hFd_le : |∫ z in Work.Spaces.Iz, Fd z|
      ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
          + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
        + Cd * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g := by
    rcases hqcase with hqη | hqγ'
    · have h := sdel_integral_le_of_eta (α := α) (f := f) (g := g) (a := a) (b := b) (q := q)
        (Mf := Mf) (MK := MK) (Mg := Mg) hα hα1 hMf0 hMK0 hMg0 hqnn hab hq0
        hqγ hqη hFsup hFσ hGsup hmf hmg4
      simp only [hFddef] at h ⊢
      simp only [Work.FTS.Nonlin.Xn] at h ⊢
      have hnn : 0 ≤ Cd * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g :=
        mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (Real.rpow_nonneg hα.le _))
          (add_nonneg hXn_f_nn hKf_nn)) (Work.Spaces.HkSq_nonneg α 4 g)
      linarith
    · subst hqγ'
      by_cases hb2 : b ≤ 2
      · have hfd : Fd = fun _ => (0 : ℝ) := by
          rw [hFddef]
          funext z
          rw [show (fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g a b z θ
                * Work.Spaces.mixed b a g z θ) = fun _ => (0 : ℝ) from by
            funext θ
            rw [Sdel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
            ring]
          simp
        rw [hfd]
        simp only [MeasureTheory.integral_zero, abs_zero]
        have hnn : 0 ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
            + Cd * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
              * Work.Spaces.HkSq α 4 g := by
          have h1 : 0 ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (add_nonneg hMf0 hMK0) (Work.Spaces.HkSq_nonneg α 4 g)
          have h2 : 0 ≤ Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :=
            mul_nonneg hMg0 (mul_nonneg hXn_f_nn hXn_g_nn)
          have h3 : 0 ≤ Cd * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
              * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (Real.rpow_nonneg hα.le _))
              (add_nonneg hXn_f_nn hKf_nn)) (Work.Spaces.HkSq_nonneg α 4 g)
          linarith
        linarith
      · have ha0 : a ≠ 0 := by
          intro h0
          exact absurd (hq0 h0) (not_le.mpr (eta_lt_gam_of_pos hα))
        have ha1 : a = 1 := by omega
        have hb3 : b = 3 := by omega
        have h := sdel_integral_le_of_gam (α := α) (Cd := Cd) (f := f) (g := g) hα hα1 hf hg
          (fun q hq0 hqγ => hCd α q f g hα hα1 hq0 hqγ hf hg)
        have hFdval : (∫ z in Work.Spaces.Iz, Fd z)
            = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
                  * Work.Spaces.mixed 3 1 g z θ) := by
          simp only [hFddef]
          rw [ha1, hb3]
        rw [hFdval]
        have hnn : 0 ≤ 16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
            + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
          have h1 : 0 ≤ (Mf + MK) * Work.Spaces.HkSq α 4 g :=
            mul_nonneg (add_nonneg hMf0 hMK0) (Work.Spaces.HkSq_nonneg α 4 g)
          have h2 : 0 ≤ Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :=
            mul_nonneg hMg0 (mul_nonneg hXn_f_nn hXn_g_nn)
          linarith
        linarith
  have hFL_eq : (∫ z in Work.Spaces.Iz, FL z)
      = ∫ z in Work.Spaces.Iz, (FA z + (Fr z + Fd z)) :=
    MeasureTheory.integral_congr_ae (ae_of_forall_Ioi (fun z hz => hsplit z hz))
  have hb1 : |∫ z in Work.Spaces.Iz, FL z|
      ≤ |∫ z in Work.Spaces.Iz, FA z| + |∫ z in Work.Spaces.Iz, (Fr z + Fd z)| := by
    rw [hFL_eq]
    exact absIntegralAddLe (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := FA) (g := fun z => Fr z + Fd z) hSmain.1
  have hb2 : |∫ z in Work.Spaces.Iz, (Fr z + Fd z)|
      ≤ |∫ z in Work.Spaces.Iz, Fr z| + |∫ z in Work.Spaces.Iz, Fd z| :=
    absIntegralAddLe (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := Fr) (g := Fd) hSrest.1
  have htotal : |∫ z in Work.Spaces.Iz, FL z|
      ≤ 2 * Mf * Work.Spaces.HkSq α 4 g
        + (6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
              + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
          + (16 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
                + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g))
            + Cd * α ^ (-(1 / 2 : ℝ))
                * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
                * Work.Spaces.HkSq α 4 g)) := by
    have h1 : |∫ z in Work.Spaces.Iz, FA z| ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
      simpa only [hFAdef] using hSmain.2
    have h2 : |∫ z in Work.Spaces.Iz, Fr z| ≤ 6400 * ((Mf + MK) * Work.Spaces.HkSq α 4 g
        + Mg * (Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)) := by
      simpa only [hFrdef] using hSrest.2
    linarith [hb1, hb2, h1, h2, hFd_le]
  have hsq10 : Real.sqrt 10 ≤ 10 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]
  have hr1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    simpa using h
  have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hMfeq : Mf = Cs * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α f := by
    rw [hMfdef, show Cs / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f
        = Cs * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.Nonlin.Xn α f from by ring,
      Work.FTS.TransportS.T2Sup.one_div_sqrt_gam_sub_one hα]
  have hMgeq : Mg = Cg * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α g := by
    rw [hMgdef, show Cg / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g
        = Cg * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.Nonlin.Xn α g from by ring,
      Work.FTS.TransportS.T2Sup.one_div_sqrt_gam_sub_one hα]
  have harith := slot_arith (r := α ^ (-(1 / 2 : ℝ))) (Xf := Work.FTS.Nonlin.Xn α f)
    (Kf := Work.FTS.VocabO.CoefTh 1 f) (Xg := Work.FTS.Nonlin.Xn α g)
    (Cs := Cs) (Cl := Cl) (Cg := Cg) (Cd := Cd) hr1 hr0 hXn_f_nn hKf_nn hXn_g_nn
    hCs0.le hCl0.le hCg0.le hCd0.le hsq10
  rw [hMfeq, hMgeq, hMKdef, ← Xn_sq α g] at htotal
  exact le_trans htotal harith

end Work.FTS.TransportS.T2Sup
