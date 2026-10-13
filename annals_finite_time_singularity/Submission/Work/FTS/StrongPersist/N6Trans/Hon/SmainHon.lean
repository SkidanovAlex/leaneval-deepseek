/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/SmainHon`: the `Smain` summand in the honest class

This is the honest (`SmoothOpen`-based) copy of
`Submission/Work/FTS/TransportS/T2Sup/smainBound.lean`: the estimate for the `Smain` summand of
the Leibniz expansion of the transport pairing, i.e. for the pairing

  `canonW q z θ · f z θ · D_z(mixed b a g) z θ · mixed b a g z θ`

with `a + b ≤ 4`.  The frozen version takes `SmoothQuad g` (used only to obtain the
open-quadrant continuity of the slots of `g`) and, in the top case `a + b = 4`, the pointwise
boundary traces `BdryTraces α 4 g` (consumed by `Main.topSlotBound`).  Here:

* `SmoothQuad g` is replaced by `SmoothOpen g` — the only use is the continuity of the two
  `g`-slots on the *open* quadrant (`SmoothOpen.mixed`);
* the top case is discharged by the honest radial integration by parts
  (`Hon.TopSlotHonProp`), whose proof uses `HkMem α 4 g` (integrability of the slot of order
  `4`) and `HkMem α 5 g` (integrability of the slot of order `5`) instead of the traces.

The easy case `a + b ≤ 3` is unchanged pointwise AM–GM.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.TransportS.T2Sup.smainBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.TransportS.SlotT2 (canonW continuousOn_canonW)
open Work.FTS.TransportS.T2Sup (Smain ae_of_forall_Ioi canonW_mul_z_le_of_le
  canonW_mul_mixed_le_of_le smain_slice_abs_le)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Integrability of the radial marginal -/

/-- **The marginal of the `Smain` summand is integrable** (honest class). -/
theorem smain_marginal_integrable_hon {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    {k₁ k₂ : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hm1 : Work.Spaces.HkMem α k₁ g) (hm2 : Work.Spaces.HkMem α k₂ g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₂ g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz := by
  have hdom : MeasureTheory.Integrable
      (fun z => Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₁ g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₂ g z θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := (hm1.2.add hm2.2).const_mul Mf
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
          * Work.Spaces.mixed (b + 1) a g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        ((((continuousOn_canonW q).mul hFsm.continuousOn).mul
          ((hGsm.mixed (b + 1) a) |>.continuousOn)).mul
          ((hGsm.mixed b a) |>.continuousOn)))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  refine ae_of_forall_Ioi (fun z hz => ?_)
  have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
    (hm1.1 z (le_of_lt hz)) (hm2.1 z (le_of_lt hz))
    (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
    (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
  simpa [Real.norm_eq_abs] using hslice

/-! ## The easy case `a + b ≤ 3` -/

/-- **The easy case** (honest class): when `a + b ≤ 3` both `g`-factors are honest order-`≤ 4`
slots, so the pointwise AM–GM bound gives the sharp constant `2 Mf`. -/
theorem smain_easy_hon {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
        ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  refine ⟨smain_marginal_integrable_hon (k₁ := 4) (k₂ := 4) hMf hFsm hGsm hm4 hm4 hf hX hY, ?_⟩
  have h1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz, Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [← Real.norm_eq_abs]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
      ((hm4.2.add hm4.2).const_mul Mf) ?_
    refine ae_of_forall_Ioi fun z hz => ?_
    have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
      (hm4.1 z (le_of_lt hz)) (hm4.1 z (le_of_lt hz))
      (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
      (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
    simpa [Real.norm_eq_abs] using hslice
  refine le_trans h1 (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hm4.2 hm4.2,
    Work.Spaces.HkSq]
  ring

/-! ## The main statement -/

/-- **The `Smain` bound in the honest class.**  The top case `a + b = 4` is discharged by the
honest radial integration by parts (`TopSlotHonProp`), the easy case by AM–GM. -/
theorem smainBound_hon (hTop : TopSlotHonProp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q Mf : ℝ),
      0 < α → α ≤ 1 → 0 ≤ Mf → a + b ≤ 4 → (a = 0 → q ≤ Work.Spaces.eta) →
      q ≤ Work.Spaces.gam α →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
        |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ|
          ≤ C * Mf * Work.Spaces.HkSq α 4 g := by
  obtain ⟨Ct, hCt, hTop⟩ := hTop
  refine ⟨max 2 Ct, le_trans (by norm_num : (1:ℝ) ≤ 2) (le_max_left 2 Ct), ?_⟩
  intro α f g a b q Mf hα hα1 hMf hab hq0 hqγ hFsm hGsm hmg4 hmg5 hdec hf hDf
  have hHknn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  -- unfold `Smain` (up to the reassociation of the product)
  have hInt : (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
      = fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ := by
    funext z
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    rw [show Smain f g a b z θ = f z θ * Work.Spaces.mixed (b + 1) a g z θ from rfl]
    ring
  rw [hInt]
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- ## Case `a + b ≤ 3`
    have hle : 2 * Mf * Work.Spaces.HkSq α 4 g ≤ max 2 Ct * Mf * Work.Spaces.HkSq α 4 g :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (2:ℝ) Ct) hMf) hHknn
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- `a = 0`, `b ≤ 3`: two pure `D_z`-slots
      have hqη : q ≤ Work.Spaces.eta := hq0 ha0
      have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ2
        rw [ha0]
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b + 1) (by omega))
      have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ2
        rw [ha0]
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b) (by omega))
      exact ⟨(smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm hGsm
          hmg4 hf hX hY).1,
        le_trans (smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm
          hGsm hmg4 hf hX hY).2 hle⟩
    · -- `a ≥ 1`, `a + b ≤ 3`: two mixed slots
      have ha1 : 1 ≤ a := by omega
      have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        fun z θ hz hθ0 hθ2 =>
          canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b + 1) (i := a)
            ha1 (by omega)
      have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        fun z θ hz hθ0 hθ2 =>
          canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
            ha1 (by omega)
      exact ⟨(smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm hGsm
          hmg4 hf hX hY).1,
        le_trans (smain_easy_hon (α := α) (q := q) (Mf := Mf) (a := a) (b := b) hMf hFsm
          hGsm hmg4 hf hX hY).2 hle⟩
  · -- ## Case `a + b = 4`: the top slot
    have hsub : 4 - a = b := by omega
    have hDzfun : Work.Spaces.Dz (Work.Spaces.mixed b a g)
        = Work.Spaces.mixed (b + 1) a g := by
      funext z θ
      simp only [Work.Spaces.mixed]
      rw [Work.Spaces.DzIter_succ]
    have hint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · have hqη : q ≤ Work.Spaces.eta := hq0 ha0
        have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
          intro z θ hz hθ0 hθ2
          rw [ha0]
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 5 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b + 1) (by omega))
        have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
          intro z θ hz hθ0 hθ2
          rw [ha0]
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b) (by omega))
        exact smain_marginal_integrable_hon (k₁ := 5) (k₂ := 4) (a := a) (b := b) hMf hFsm
          hGsm hmg5 hmg4 hf hX hY
      · have ha1 : 1 ≤ a := by omega
        have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 5 g z θ :=
          fun z θ hz hθ0 hθ2 =>
            canonW_mul_mixed_le_of_le (α := α) 5 hqγ hθ0 hθ2 (j := b + 1) (i := a)
              ha1 (by omega)
        have hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
          fun z θ hz hθ0 hθ2 =>
            canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
              ha1 (by omega)
        exact smain_marginal_integrable_hon (k₁ := 5) (k₂ := 4) (a := a) (b := b) hMf hFsm
          hGsm hmg5 hmg4 hf hX hY
    refine ⟨hint, ?_⟩
    -- the integrand is the top slot with the weight `canonW q`
    have hgoal_eq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          * Work.Spaces.mixed b a g z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      rw [hDzfun]
    rw [hgoal_eq]
    have hres := hTop α f g a b q Mf hα hα1 hMf heq hq0 hqγ hFsm hGsm hdec hmg4 hmg5 hf hDf
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ Ct * Mf * Work.Spaces.HkSq α 4 g := hres
      _ ≤ max 2 Ct * Mf * Work.Spaces.HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right (2:ℝ) Ct) hMf) hHknn

end Work.FTS.StrongPersist.N6Trans.Hon
