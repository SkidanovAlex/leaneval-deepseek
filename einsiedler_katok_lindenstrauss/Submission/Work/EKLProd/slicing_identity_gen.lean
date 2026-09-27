import Mathlib
import Submission.Work.EKLProd.slicing_identity
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLProd.condExp_mul_condExp_tower
import Submission.Work.EKLContract.Defs

/-!
# `Work.EKLProd.slicing_identity_gen`

The general form of the slicing identity of Pisa Lemma 8.10 (EKL §2): for a probability `μ`, two
leafwise systems `νH` (`H`-leaves) and `νT` (`T`-leaves) restricted to a common measurable set
`Z`, and *aligned* plaque algebras `mH ≤ mT` (`mH` for `H`, `mT` for `T`), the `νH x`-average over
the `H`-shape of `g · f` equals the `νH x`-average of `g` times the `T`-slice averages of `f`,
`νH x`-a.e. on `Z`.

The proof is the tower/pull-out identity for conditional expectations,
`E[g·f | mH] = E[g·E[f|mT] | mH]`, transported to the leafwise averages by the `condexp` field of
`IsLeafwise`: the pointwise conditional expectations are the normalised shape averages.  The one
point that needs the leafwise structure (rather than the condexp field alone) is that the `νT`-slices
must be replaced by the `mT`-conditional expectation inside the `νH x`-integral; this is the
(plaque-algebra-local) null transfer `leafwise_null_transfer_gen`, derived from the same
`condexp` field.  The two supporting lemmas are `Work.EKLProd.leafwise_null_transfer_gen` (the plaque-algebra-local
null transfer) and `Work.EKLProd.condExp_mul_condExp_tower` (the tower/pull-out identity), proved
in the sibling files `Submission/Work/EKLProd/leafwise_null_transfer_gen.lean` and
`Submission/Work/EKLProd/condExp_mul_condExp_tower.lean`.
-/

namespace Work.EKLProd

open MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## The main theorem -/

theorem slicing_identity_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {H T : Subgroup Work.EKLContract.SL3}
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    {Z : Set Work.EKLContract.X3} (mH mT : MeasurableSpace Work.EKLContract.X3)
    (hZ : Work.EKLContract.IsPlaqueAlgebra H Z mH)
    (hplaT : Work.EKLContract.IsPlaqueAlgebra T Z mT) (halign : mH ≤ mT)
    (hmass : ∀ᵐ x ∂(μ.restrict Z), 0 < (νH x) (Work.EKLContract.shape mH H x) ∧
      (νH x) (Work.EKLContract.shape mH H x) < ⊤)
    (f g : Work.EKLContract.X3 → ℝ)
    (hf : @Measurable Work.EKLContract.X3 ℝ (borel Work.EKLContract.X3) (borel ℝ) f)
    (hfb : ∃ C, ∀ y, |f y| ≤ C)
    (hgm : @Measurable Work.EKLContract.X3 ℝ (borel Work.EKLContract.X3) (borel ℝ) g)
    (hgmT : @Measurable Work.EKLContract.X3 ℝ mT (borel ℝ) g)
    (hgb : ∃ C, ∀ y, |g y| ≤ C) :
    ∀ᵐ x ∂(μ.restrict Z),
      (∫ h in Work.EKLContract.shape mH H x, g (h • x) * f (h • x) ∂(νH x))
          / ((νH x) (Work.EKLContract.shape mH H x)).toReal
        = (∫ h in Work.EKLContract.shape mH H x, g (h • x)
            * ((∫ t in Work.EKLContract.shape mT T (h • x), f (t • (h • x)) ∂(νT (h • x)))
                / ((νT (h • x)) (Work.EKLContract.shape mT T (h • x))).toReal)
            ∂(νH x))
          / ((νH x) (Work.EKLContract.shape mH H x)).toReal := by
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  -- ## 0. Basic bounds and σ-algebra bookkeeping
  haveI hμfin : IsFiniteMeasure μ :=
    ⟨by rw [MeasureTheory.IsProbabilityMeasure.measure_univ]; norm_num⟩
  haveI hμzfin : IsFiniteMeasure (μ.restrict Z) := inferInstance
  have hbf : ∃ C, ∀ y, |f y| ≤ C := hfb
  have hbg : ∃ C, ∀ y, |g y| ≤ C := hgb
  obtain ⟨C, hC⟩ := hbf
  obtain ⟨Cg, hCg⟩ := hbg
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (Work.EKLContract.mkX 1))
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hCg (Work.EKLContract.mkX 1))
  have hmT_borel : mT ≤ borel Work.EKLContract.X3 := hplaT.1
  have hmT_env : mT ≤ (inferInstance : MeasurableSpace Work.EKLContract.X3) := hmT_borel
  haveI : IsFiniteMeasure ((μ.restrict Z).trim hmT_env) := inferInstance
  haveI : SigmaFinite ((μ.restrict Z).trim hmT_env) := inferInstance
  -- ## 1. Abbreviations
  let Cf : Work.EKLContract.X3 → ℝ := MeasureTheory.condExp mT (μ.restrict Z) f
  let Cfb : Work.EKLContract.X3 → ℝ := fun y => max (-C) (min (Cf y) C)
  let Tavg : Work.EKLContract.X3 → ℝ := fun y =>
    (∫ t in Work.EKLContract.shape mT T y, f (t • y) ∂(νT y))
      / ((νT y) (Work.EKLContract.shape mT T y)).toReal
  let F0 : Work.EKLContract.X3 → ℝ := fun y => g y * f y
  let Fb : Work.EKLContract.X3 → ℝ := fun y => g y * Cfb y
  -- ## 2. Measurability
  have hCf_meas : Measurable Cf := by
    show Measurable (MeasureTheory.condExp mT (μ.restrict Z) f)
    exact (MeasureTheory.stronglyMeasurable_condExp (μ := μ.restrict Z) (m := mT)
      (f := f)).measurable.mono hmT_env le_rfl
  have hCfb_meas : Measurable Cfb := by
    show Measurable (fun y => max (-C) (min (Cf y) C))
    exact measurable_const.max (hCf_meas.min measurable_const)
  have hF0_meas : Measurable F0 := by
    show Measurable (fun y => g y * f y)
    exact hgm.mul hf
  have hFb_meas : Measurable Fb := by
    show Measurable (fun y => g y * Cfb y)
    exact hgm.mul hCfb_meas
  -- ## 3. Boundedness
  have hF0_bdd : ∃ C', ∀ y, |F0 y| ≤ C' := ⟨Cg * C, fun y => by
    show |g y * f y| ≤ Cg * C
    rw [abs_mul]
    exact mul_le_mul (hCg y) (hC y) (abs_nonneg _) hCg0⟩
  have hFb_bdd : ∃ C', ∀ y, |Fb y| ≤ C' := ⟨Cg * C, fun y => by
    show |g y * Cfb y| ≤ Cg * C
    rw [abs_mul]
    refine mul_le_mul (hCg y) ?_ (abs_nonneg _) hCg0
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩⟩
  have hCf_bound : ∀ᵐ y ∂(μ.restrict Z), |Cf y| ≤ C := by
    have h1 : (fun y => ‖Cf y‖) ≤ᵐ[μ.restrict Z]
        MeasureTheory.condExp mT (μ.restrict Z) (fun y => ‖f y‖) := by
      show (fun y => ‖MeasureTheory.condExp mT (μ.restrict Z) f y‖)
          ≤ᵐ[μ.restrict Z] _
      exact norm_condExp_le (μ := μ.restrict Z) (m := mT) f
    have h2 : MeasureTheory.condExp mT (μ.restrict Z) (fun y => ‖f y‖) ≤ᵐ[μ.restrict Z]
        (fun _ => C) :=
      MeasureTheory.condExp_le_nonneg_const (μ := μ.restrict Z) (m := mT)
        (f := fun y => ‖f y‖) (c := C) hC0
        (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hC y))
    filter_upwards [h1, h2] with y hy1 hy2
    rw [Real.norm_eq_abs] at hy1
    exact hy1.trans hy2
  -- ## 4. `Tavg` equals `Cf` a.e., and `Cfb =ᵐ Cf`
  have hTavg : Tavg =ᵐ[μ.restrict Z] Cf := by
    have hfield := hνT.condexp Z mT hplaT f hf hfb
    filter_upwards [hfield] with x hx
    exact hx.symm
  have hCfb_eq : Cfb =ᵐ[μ.restrict Z] Cf := by
    filter_upwards [hCf_bound] with y hy
    show max (-C) (min (Cf y) C) = Cf y
    rw [min_eq_left (le_of_abs_le hy), max_eq_right (neg_le_of_abs_le hy)]
  -- ## 5. The null set of disagreement, and the null transfer
  have hN0 : (μ.restrict Z) {y : Work.EKLContract.X3 | ¬ (Tavg y = Cfb y)} = 0 :=
    MeasureTheory.ae_iff.mp (hTavg.trans hCfb_eq.symm)
  obtain ⟨N0', hN0sub, hN0'meas, hN0'zero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hN0
  have hNT := leafwise_null_transfer_gen (μ := μ) (Z := Z) (m := mH)
    hνH hZ hmass hN0'zero
  -- ## 6. Replacing `Tavg (· • x)` by `Fb (· • x)` inside the `νH x`-integral
  have hstep1 : ∀ᵐ x ∂(μ.restrict Z),
      (∫ h in Work.EKLContract.shape mH H x, g (h • x) * Tavg (h • x) ∂(νH x))
        = (∫ u in Work.EKLContract.shape mH H x, Fb (u • x) ∂(νH x)) := by
    filter_upwards [hNT] with x hx
    apply MeasureTheory.integral_congr_ae
    show ∀ᵐ u ∂((νH x).restrict (Work.EKLContract.shape mH H x)),
        g (u • x) * Tavg (u • x) = Fb (u • x)
    rw [MeasureTheory.ae_iff]
    have hcont : Continuous (fun u : Work.EKLContract.SL3 => u • x) :=
      continuous_id.smul continuous_const
    have hDmeas : MeasurableSet {u : Work.EKLContract.SL3 | u • x ∈ N0'} :=
      hN0'meas.preimage hcont.measurable
    have hDsub : {u : Work.EKLContract.SL3 | ¬ (g (u • x) * Tavg (u • x) = Fb (u • x))}
        ⊆ {u : Work.EKLContract.SL3 | u • x ∈ N0'} := by
      intro u hu
      by_contra hnu
      have hT : Tavg (u • x) = Cfb (u • x) := by
        by_contra hc
        exact hnu (hN0sub hc)
      exact hu (by rw [hT])
    have hx' : (νH x) ({u : Work.EKLContract.SL3 | u • x ∈ N0'}
        ∩ Work.EKLContract.shape mH H x) = 0 := by
      rw [show ({u : Work.EKLContract.SL3 | u • x ∈ N0'}
            ∩ Work.EKLContract.shape mH H x)
          = {u : Work.EKLContract.SL3 | u ∈ Work.EKLContract.shape mH H x ∧ u • x ∈ N0'}
        from by ext u; exact and_comm]
      exact hx
    have hle : ((νH x).restrict (Work.EKLContract.shape mH H x))
        {u : Work.EKLContract.SL3 | ¬ (g (u • x) * Tavg (u • x) = Fb (u • x))} ≤ 0 := by
      calc ((νH x).restrict (Work.EKLContract.shape mH H x))
            {u : Work.EKLContract.SL3 | ¬ (g (u • x) * Tavg (u • x) = Fb (u • x))}
          ≤ ((νH x).restrict (Work.EKLContract.shape mH H x))
              {u : Work.EKLContract.SL3 | u • x ∈ N0'} := MeasureTheory.measure_mono hDsub
        _ = (νH x) ({u : Work.EKLContract.SL3 | u • x ∈ N0'}
              ∩ Work.EKLContract.shape mH H x) := MeasureTheory.Measure.restrict_apply hDmeas
        _ = 0 := hx'
    exact le_antisymm hle bot_le
  -- ## 7. `condExp mH μz Fb =ᵐ condExp mH μz F0`
  have hsec : MeasureTheory.condExp mH (μ.restrict Z) Fb
      =ᵐ[μ.restrict Z] MeasureTheory.condExp mH (μ.restrict Z) F0 := by
    have hP2 := condExp_mul_condExp_tower (μ := μ.restrict Z) (mH := mH) (mT := mT)
      halign hmT_borel g f hgmT hf hfb hgb
    have hclamp : Fb =ᵐ[μ.restrict Z] (fun y => g y * Cf y) := by
      filter_upwards [hCf_bound] with y hy
      have hval : max (-C) (min (Cf y) C) = Cf y := by
        rw [min_eq_left (le_of_abs_le hy), max_eq_right (neg_le_of_abs_le hy)]
      show g y * max (-C) (min (Cf y) C) = g y * Cf y
      rw [hval]
    exact (MeasureTheory.condExp_congr_ae (μ := μ.restrict Z) (m := mH) hclamp).trans hP2
  -- ## 8. Both sides equal `condExp mH μz F0`
  have hL : ∀ᵐ x ∂(μ.restrict Z),
      (∫ h in Work.EKLContract.shape mH H x, g (h • x) * f (h • x) ∂(νH x))
          / ((νH x) (Work.EKLContract.shape mH H x)).toReal
        = MeasureTheory.condExp mH (μ.restrict Z) F0 x := by
    have hfield0 := hνH.condexp Z mH hZ F0 hF0_meas hF0_bdd
    filter_upwards [hfield0] with x hx
    have key : (∫ h in Work.EKLContract.shape mH H x, g (h • x) * f (h • x) ∂(νH x))
        = (∫ u in Work.EKLContract.shape mH H x, F0 (u • x) ∂(νH x)) := by
      simp only [F0]
    rw [key, hx]
  have hR2 : ∀ᵐ x ∂(μ.restrict Z),
      (∫ h in Work.EKLContract.shape mH H x, g (h • x)
          * ((∫ t in Work.EKLContract.shape mT T (h • x), f (t • (h • x)) ∂(νT (h • x)))
              / ((νT (h • x)) (Work.EKLContract.shape mT T (h • x))).toReal) ∂(νH x))
        / ((νH x) (Work.EKLContract.shape mH H x)).toReal
      = MeasureTheory.condExp mH (μ.restrict Z) F0 x := by
    have hfieldFb := hνH.condexp Z mH hZ Fb hFb_meas hFb_bdd
    filter_upwards [hstep1, hfieldFb, hsec] with x h1 h2 h3
    rw [show (∫ h in Work.EKLContract.shape mH H x, g (h • x)
          * ((∫ t in Work.EKLContract.shape mT T (h • x), f (t • (h • x)) ∂(νT (h • x)))
              / ((νT (h • x)) (Work.EKLContract.shape mT T (h • x))).toReal) ∂(νH x))
        = (∫ h in Work.EKLContract.shape mH H x, g (h • x) * Tavg (h • x) ∂(νH x))
      from by simp only [Tavg]]
    rw [h1, ← h3, h2]
  -- ## 9. Assembly
  filter_upwards [hL, hR2] with x h1 h2
  rw [h1, h2]

end

end Work.EKLProd
