import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Cchan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.chiScale_W1fun_slice_integrable
import Submission.Work.BoseBoxFock.PCFU.chi_aP_wordB_eq_slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 12000000

/-- A measurable bounded function supported in a set of finite measure is integrable. -/
private theorem integrable_of_bounded_support_cw {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

theorem Cchan_dzero_word_split_v4 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i - z)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j Θ x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
                      (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ z : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                      * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i - z)
                          - ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
                            * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                                (x i - z) : ℝ) : ℂ))
                      * ((Work.BoseBoxFix.lowSlot fc
                            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                            (Work.BoseBoxFock.ellH v μ) j
                            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                            (Function.update x j z) : ℝ) : ℂ))) := by
  classical
  obtain ⟨C0, hC0⟩ := hΘb
  have hCθ : 0 ≤ max C0 0 := le_max_right _ _
  have hΘb' : ∀ x : Submission.BoseGases.X n, |Θ x| ≤ max C0 0 :=
    fun x => le_trans (hC0 x) (le_max_left _ _)
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κ := hκ
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  -- ### the low-slot factor: measurability and uniform boundedness
  obtain ⟨hLSm, D, hD0, hLSb⟩ :=
    lowSlot_aQ_aP_measurable_bounded (fc := fc) (μ := 0) (ℓ := ℓ) (κ := κ) (Cθ := max C0 0)
      (i := i) (j := j) hℓpos hκpos hCθ hΘm hΘb'
  -- ### abbreviations
  set chiC : E3 → ℂ := fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) with hchiCdef
  set Kc : E3 → ℂ := fun z => Work.BoseBoxFock.PCFU.KfrU v h μ fu N z with hKcdef
  set Wc : E3 → ℂ := fun z => ((Work.BoseFixR.W1fun v h ℓ z : ℝ) : ℂ) with hWcdef
  set LS : Submission.BoseGases.X n → E3 → ℂ := fun x z =>
      ((Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update x j z) : ℝ) : ℂ) with hLSdef
  set A : Submission.BoseGases.X n → ℂ := fun x => ∫ z : E3, chiC z * Kc (x i - z) * LS x z
    with hAdef
  set CW : Submission.BoseGases.X n → ℂ := fun x => ∫ z : E3, chiC z * Wc (x i - z) * LS x z
    with hCWdef
  set BR : Submission.BoseGases.X n → ℂ := fun x => ∫ z : E3,
      chiC z * (Kc (x i - z) - ((ℓ : ℂ)) ^ 3 * Wc (x i - z)) * LS x z with hBRdef
  set G : Submission.BoseGases.X n → ℝ :=
    Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ with hGdef
  set Psi1 : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ) * chiC (x i) * A x
    with hPsi1def
  set Psi2 : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ) * chiC (x i) * BR x
    with hPsi2def
  set Psi3 : Submission.BoseGases.X n → ℂ := fun x => ((ℓ : ℂ)) ^ 6 * ((Θ x : ℝ) : ℂ)
    * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) with hPsi3def
  -- ### basic bounds
  set Cχ : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hCχdef
  have hCχ0 : 0 ≤ Cχ := by rw [hCχdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hχb : ∀ z : E3, ‖chiC z‖ ≤ Cχ := fun z => by
    rw [hchiCdef, hCχdef]
    exact norm_chiLam_le ℓ z
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| with hKwdef
  have hKw0 : 0 ≤ Kw := by rw [hKwdef]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hKwb : ∀ z : E3, ‖Kc z‖ ≤ Kw := fun z => by
    rw [hKcdef, hKwdef]
    exact norm_KfrU_le v h μ fu N z
  have hLSb' : ∀ (x : Submission.BoseGases.X n) (z : E3), ‖LS x z‖ ≤ D := fun x z => by
    simp only [hLSdef]
    exact le_trans (le_of_eq (RCLike.norm_ofReal _)) (hLSb (Function.update x j z))
  -- ### continuity and measurability facts
  have hχcont : Continuous chiC := by
    simp only [hchiCdef]
    exact Complex.continuous_ofReal.comp
      (Submission.BoseGases.chi_continuous.comp (by fun_prop))
  have hχcs : HasCompactSupport chiC := by
    rw [hchiCdef]
    exact (Submission.BoseGases.chiScale_hasCompactSupport hℓne).comp_left
      (g := fun t : ℝ => ((t : ℝ) : ℂ)) (by simp)
  have hLSmeas : Measurable (fun p : Submission.BoseGases.X n × E3 => LS p.1 p.2) := by
    rw [hLSdef]
    exact Complex.measurable_ofReal.comp (hLSm.comp (measurable_update' (a := j)))
  have hKcmeas : Measurable Kc := by
    rw [hKcdef]
    exact (continuous_KfrU v h μ fu N).measurable
  have haesm_ls : ∀ x : Submission.BoseGases.X n,
      AEStronglyMeasurable (fun z : E3 => LS x z) (volume : Measure E3) := fun x =>
    (hLSmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  -- ### integrability of the `K`-slice
  have hKslice : ∀ u : E3, Integrable (fun z : E3 => chiC z * Kc (u - z)) := by
    intro u
    have hKcont : Continuous (fun z : E3 => Kc (u - z)) := by
      rw [hKcdef]
      exact (continuous_KfrU v h μ fu N).comp (continuous_const.sub continuous_id)
    exact (hχcont.mul hKcont).integrable_of_hasCompactSupport
      (hχcs.mul_right (f' := fun z : E3 => Kc (u - z)))
  have hAint : ∀ x : Submission.BoseGases.X n, Integrable (fun z : E3 =>
      chiC z * Kc (x i - z) * LS x z) := by
    intro x
    refine ((hKslice (x i)).mul_bdd (haesm_ls x)
      (Filter.Eventually.of_forall (fun z => hLSb' x z))).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    show chiC z * Kc (x i - z) * LS x z = (chiC z * Kc (x i - z)) * LS x z
    ring
  -- ### the uniform bound on `A`
  have hAbd : ∀ x : Submission.BoseGases.X n, ‖A x‖ ≤ Cχ * Kw * D * ℓ ^ 3 := by
    intro x
    simp only [hAdef]
    have hvanish : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
        chiC z * Kc (x i - z) * LS x z = 0 := by
      intro z hz
      have h0 : chiC z = 0 := by
        simp only [hchiCdef]
        have hz0 : Submission.BoseGases.chiScale ℓ z = 0 := by
          by_contra hne
          exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓpos.le
            (Submission.BoseGases.chiScale_support_le hℓpos hne))
        rw [show ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) by
          rw [Work.BoseBoxFock.PCFU.wsc_chiLam_eq_chiScale]]
        rw [hz0]
        simp
      rw [h0, zero_mul, zero_mul]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.acube ℓ) hvanish]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓpos.le))
    have hbd : ∀ᵐ z ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖chiC z * Kc (x i - z) * LS x z‖ ≤ Cχ * Kw * D := by
      filter_upwards with z
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hχb z) (hKwb _) (norm_nonneg _) hCχ0)
        (hLSb' x z) (norm_nonneg _) (mul_nonneg hCχ0 hKw0)
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hfin
    exact hfin
  -- ### measurability of `A`
  have hAm : Measurable A := by
    rw [hAdef]
    have hjoint : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        chiC p.2 * Kc (p.1 i - p.2) * LS p.1 p.2) :=
      ((hχcont.measurable.comp measurable_snd).mul
        (hKcmeas.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd))).mul
        hLSmeas
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3))).measurable
  -- ### integrability of `Psi1`
  have hPsi1int : Integrable Psi1 := by
    rw [hPsi1def]
    refine integrable_of_bounded_support_cw (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le) ?_ ?_ ?_
    · exact ((Complex.measurable_ofReal.comp hΘm).mul
        (hχcont.measurable.comp (measurable_pi_apply i))).mul hAm
    · refine ⟨max C0 0 * Cχ * (Cχ * Kw * D * ℓ ^ 3), fun x => ?_⟩
      have h1 : ‖((Θ x : ℝ) : ℂ)‖ ≤ max C0 0 :=
        le_trans (le_of_eq (RCLike.norm_ofReal _)) (hΘb' x)
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul h1 (hχb (x i)) (norm_nonneg _) hCθ)
        (hAbd x) (norm_nonneg _) (mul_nonneg hCθ hCχ0)
    · intro x hx
      rw [Function.mem_support] at hx
      apply hΘs
      rw [Function.mem_support]
      intro h0
      exact hx (by rw [h0]; simp)
  -- ### integrability of the `W1`-slice whenever `χ(x i) ≠ 0`
  have hWslice : ∀ x : Submission.BoseGases.X n, Submission.BoseGases.chiScale ℓ (x i) ≠ 0 →
      Integrable (fun z : E3 => chiC z * Wc (x i - z) * LS x z) := by
    intro x hx
    have h0 : Integrable (fun z : E3 => Submission.BoseGases.chiScale ℓ z
        * Work.BoseFixR.W1fun v h ℓ (x i - z)) :=
      chiScale_W1fun_slice_integrable h hℓpos hx
    have h1 : Integrable (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z
        * Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ)) := h0.ofReal
    have h2 : Integrable (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z
        * Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ) * LS x z) :=
      h1.mul_bdd (haesm_ls x) (Filter.Eventually.of_forall (fun z => hLSb' x z))
    refine h2.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hchiCdef, hWcdef]
    rw [Complex.ofReal_mul]
    rw [← Work.BoseBoxFock.PCFU.wsc_chiLam_eq_chiScale]
  -- ### `BR = A - ℓ³·CW` whenever `χ(x i) ≠ 0`
  have hBRval : ∀ x : Submission.BoseGases.X n, Submission.BoseGases.chiScale ℓ (x i) ≠ 0 →
      BR x = A x - ((ℓ : ℂ)) ^ 3 * CW x := by
    intro x hx
    have hW3 : Integrable (fun z : E3 => chiC z * (((ℓ : ℂ)) ^ 3 * Wc (x i - z)) * LS x z) := by
      refine ((hWslice x hx).const_mul (((ℓ : ℂ)) ^ 3)).congr
        (Filter.Eventually.of_forall (fun z => ?_))
      ring
    have hsub := MeasureTheory.integral_sub (hAint x) hW3
    have hBeq : BR x = ∫ z : E3, (chiC z * Kc (x i - z) * LS x z
        - chiC z * (((ℓ : ℂ)) ^ 3 * Wc (x i - z)) * LS x z) := by
      rw [hBRdef]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      ring
    have hWint : (∫ z : E3, chiC z * (((ℓ : ℂ)) ^ 3 * Wc (x i - z)) * LS x z)
        = ((ℓ : ℂ)) ^ 3 * CW x := by
      rw [hCWdef]
      rw [show (∫ z : E3, chiC z * (((ℓ : ℂ)) ^ 3 * Wc (x i - z)) * LS x z)
          = ∫ z : E3, ((ℓ : ℂ)) ^ 3 * (chiC z * Wc (x i - z) * LS x z) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))]
      rw [MeasureTheory.integral_const_mul]
    rw [hBeq, hsub, hAdef, hWint]
  -- ### the main identity (the `d = 0` term of the `C`-channel)
  have hMain : ∀ x : Submission.BoseGases.X n,
      chiC (x i) * ((ℓ : ℂ)) ^ 3 * CW x
        = ((ℓ : ℂ)) ^ 6 * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) := by
    intro x
    have h' := chi_aP_wordB_eq_slice (hij := hij) (h := h) (fc := fc) (ℓ := ℓ) (κ := κ)
      (Θ := Θ) hℓpos x
    simp only [hCWdef, hGdef, hchiCdef, hWcdef, hLSdef, Complex.ofReal_pow,
      Work.BoseBoxFock.PCFU.wsc_chiLam_eq_chiScale,
      Work.BoseBoxFock.PCFU.wordF, Work.BoseBoxFock.PCFU.wordB] at h' ⊢
    exact h'
  -- ### the vanishing case
  have hGGzero : ∀ x : Submission.BoseGases.X n, Submission.BoseGases.chiScale ℓ (x i) = 0 →
      Submission.BoseGases.aP ℓ j G x = 0 := by
    intro x hx
    have hz : ∀ y : E3, G (Function.update x j y) = 0 := by
      intro y
      have h1 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0
          ((Function.update x j y) i) ((Function.update x j y) j) = 0 := by
        simp only [Submission.BoseGases.wLoc, Submission.BoseGases.chiU, sub_zero]
        rw [Function.update_of_ne hij]
        rw [show Submission.BoseGases.chi ((ℓ⁻¹) • x i) = 0 from hx]
        ring
      rw [hGdef]
      show Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
          (Function.update x j y)
        * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0
            ((Function.update x j y) i) ((Function.update x j y) j) = 0
      rw [h1, mul_zero]
    rw [Submission.BoseGases.aP]
    rw [show (fun y : E3 => G (Function.update x j y)) = fun _ : E3 => (0 : ℝ) from
      funext hz]
    rw [MeasureTheory.integral_zero, mul_zero]
  -- ### the pointwise identity for the integrands
  have hpt : ∀ x : Submission.BoseGases.X n, Psi1 x = Psi2 x + Psi3 x := by
    intro x
    by_cases hx : Submission.BoseGases.chiScale ℓ (x i) = 0
    · have hχ0 : chiC (x i) = 0 := by
        simp only [hchiCdef]
        rw [show ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
            = ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ) by
          rw [Work.BoseBoxFock.PCFU.wsc_chiLam_eq_chiScale]]
        rw [hx]
        simp
      have hz := hGGzero x hx
      simp only [hPsi1def, hPsi2def, hPsi3def, hχ0, hz]
      simp
    · have h1 := hBRval x hx
      have h2 := hMain x
      simp only [hPsi1def, hPsi2def, hPsi3def]
      rw [h1]
      have h4 : ((Θ x : ℝ) : ℂ) * (chiC (x i) * ((ℓ : ℂ)) ^ 3 * CW x)
          = ((ℓ : ℂ)) ^ 6 * ((Θ x : ℝ) : ℂ) * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) := by
        rw [h2]
        ring
      linear_combination h4
  -- ### the first term: reduction to the box and self-adjointness
  have hGint : IntegrableOn G (Submission.BoseGases.abox n ℓ) volume := by
    rw [hGdef]
    exact (wordB_integrable_family hij h hℓpos hκpos hΘm hΘb' hCθ).1
  have hPGint : IntegrableOn (Submission.BoseGases.aP ℓ j G)
      (Submission.BoseGases.abox n ℓ) volume :=
    (aP_integrable_of_integrable hℓpos j hGint).2
  have hPaP₁ : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ j Θ x * G x) (Submission.BoseGases.abox n ℓ) volume :=
    (hGint.mul_bdd ((Weak.aP_measurable j hΘm).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact Weak.aP_abs_le hℓpos j hCθ hΘb' x))).congr
      (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  have hPaP₂ : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Θ x * Submission.BoseGases.aP ℓ j G x) (Submission.BoseGases.abox n ℓ) volume :=
    (hPGint.mul_bdd (hΘm.aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hΘb' x))).congr
      (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  have hsymm : (∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ j Θ x * G x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Θ x * Submission.BoseGases.aP ℓ j G x :=
    aP_sym_box_L1 hℓpos j hPaP₁ hPaP₂
  -- ### integrability of `Psi3`
  have hΘPGint : Integrable (fun x : Submission.BoseGases.X n =>
      ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) * ((Θ x : ℝ) : ℂ)) := by
    have h1 : Integrable (fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) * ((Θ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      hPGint.ofReal.mul_bdd ((Complex.measurable_ofReal.comp hΘm).aestronglyMeasurable.restrict)
        (Filter.Eventually.of_forall (fun x =>
          le_trans (le_of_eq (RCLike.norm_ofReal _)) (hΘb' x)))
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset
      (s := Submission.BoseGases.abox n ℓ) (f := fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) * ((Θ x : ℝ) : ℂ)) ?_).mp h1
    intro x hx
    rw [Function.mem_support] at hx
    apply hΘs
    rw [Function.mem_support]
    intro h0
    exact hx (by rw [h0]; simp)
  have hPsi3int : Integrable Psi3 := by
    simp only [hPsi3def]
    refine (hΘPGint.const_mul (((ℓ : ℂ)) ^ 6)).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- ### the value of the `Psi3`-integral
  have hvanishBox : ∀ x : Submission.BoseGases.X n, x ∉ Submission.BoseGases.abox n ℓ →
      ((Θ x : ℝ) : ℂ) * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) = 0 := by
    intro x hx
    have h0 : Θ x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    rw [h0]
    simp
  have hMval : (∫ x : Submission.BoseGases.X n, Psi3 x)
      = ((ℓ : ℂ)) ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
          ((Submission.BoseGases.aP ℓ j Θ x : ℝ) : ℂ)
            * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ)) := by
    simp only [hPsi3def]
    rw [show (fun x : Submission.BoseGases.X n => ((ℓ : ℂ)) ^ 6 * ((Θ x : ℝ) : ℂ)
          * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ))
        = fun x : Submission.BoseGases.X n => ((ℓ : ℂ)) ^ 6
          * (((Θ x : ℝ) : ℂ) * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ)) from by
      funext x
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox n ℓ) hvanishBox]
    rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          ((Θ x : ℝ) : ℂ) * ((Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ))
          = ∫ x in Submission.BoseGases.abox n ℓ,
              ((Θ x * Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        simp only [Complex.ofReal_mul]))]
    have hcast1 : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Θ x * Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ))
        = ((∫ x in Submission.BoseGases.abox n ℓ,
            Θ x * Submission.BoseGases.aP ℓ j G x : ℝ) : ℂ) := _root_.integral_ofReal
    have hcast2 : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Submission.BoseGases.aP ℓ j Θ x * G x : ℝ) : ℂ))
        = ((∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ j Θ x * G x : ℝ) : ℂ) := _root_.integral_ofReal
    rw [hcast1, ← hsymm, ← hcast2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hgv : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
        * Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x = G x := by
      rw [hGdef]
      show Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
          * Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x
        = Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
      rw [mul_comm]
    simp only []
    rw [Complex.ofReal_mul]
    rw [show ((G x : ℝ) : ℂ) = ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
        * Work.BoseBoxFix.lowSlot fc κ ℓ j
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ) by rw [hgv]]
    rw [Complex.ofReal_mul]
    ring
  -- ### integrability of `Psi2` and the final assembly
  have hPsi2int : Integrable Psi2 := by
    refine (hPsi1int.sub hPsi3int).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply]
    rw [hpt x]
    ring
  have hfinal : (∫ x : Submission.BoseGases.X n, Psi1 x)
      = (∫ x : Submission.BoseGases.X n, Psi2 x) + ∫ x : Submission.BoseGases.X n, Psi3 x := by
    rw [← MeasureTheory.integral_add hPsi2int hPsi3int]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => hpt x))
  have hPsi2val : (∫ x : Submission.BoseGases.X n, Psi2 x)
      = ∫ x : Submission.BoseGases.X n,
          ((Θ x : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
            * (∫ z : E3,
                ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                  * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i - z)
                      - ((ℓ : ℂ)) ^ 3 * ((Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ))
                  * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                        (Function.update x j z) : ℝ) : ℂ)) := by
    simp only [hPsi2def, hBRdef, hchiCdef, hKcdef, hWcdef, hLSdef]
  have hPsi1val : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * (∫ z : E3,
              ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i - z)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ∫ x : Submission.BoseGases.X n, Psi1 x := by
    simp only [hPsi1def, hAdef, hchiCdef, hKcdef, hLSdef]
  rw [hPsi1val, hfinal, hPsi2val, hMval]
  exact add_comm _ _

end Work.BoseBoxFock.PCFU
