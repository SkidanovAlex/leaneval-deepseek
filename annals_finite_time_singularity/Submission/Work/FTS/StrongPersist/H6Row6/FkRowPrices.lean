import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Row6.RowFlatAux
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The angular moment `z ↦ FK (D_z^k f) z` of an open-quadrant datum is a.e. strongly
measurable: it is the `θ`-marginal of the jointly continuous (on the open quadrant)
function `(z,θ) ↦ D_z^k f z θ · K θ`. -/
theorem aesm_fk_DzIter {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2
      * Work.Spaces.K p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter k).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2
      * Work.Spaces.K p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h := hjoint.integral_prod_right'
  simpa only [Work.Construction.FK] using h

/-- The radial weight squared, `z ↦ w z ^ 2`, is a.e. strongly measurable on `Iz`. -/
theorem aesm_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hm_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    unfold Work.Spaces.w
    refine ContinuousOn.pow (ContinuousOn.div
      ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2) ?_) 2
    intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)
  rw [hm_eq]
  exact ContinuousOn.aestronglyMeasurable hcont measurableSet_Ioi

theorem FkRowPrices : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      (∀ k : ℕ, k ≤ 3 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          |Work.Construction.FK (Work.Spaces.DzIter k f) z| ≤ C * M) ∧
      (∀ k : ℕ, k ≤ 6 →
        MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
            * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2)
          ≤ C * Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨max 16 (max 1 (Real.sqrt C₁)),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (le_max_left _ _), ?_⟩
  intro α hα f M hQ h7 hM
  have hαpos : 0 < α := hα.1
  -- the lower `H`-orders, by monotonicity from `HkMem α 7 f`
  have h4mem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hQ.1 4 (by norm_num) h7
  have h6mem : Work.Spaces.HkMem α 6 f := hQ.2
  -- `M` is nonnegative, and `(Xn α f)^2 = HkSq α 4 f`
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  have hXnSq : (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)
  have hCge16 : (16 : ℝ) ≤ max 16 (max 1 (Real.sqrt C₁)) := le_max_left _ _
  have hCgeS : Real.sqrt C₁ ≤ max 16 (max 1 (Real.sqrt C₁)) :=
    le_trans (le_max_right 1 (Real.sqrt C₁)) (le_max_right 16 _)
  constructor
  · -- Part 1: the a.e. pointwise bound by `C·M`
    intro k hk3
    have hk6 : k ≤ 6 := by omega
    have hae1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.DzIter k (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          ≤ C₁ * Work.Spaces.HkSq α (k + 1) f := hC₁ hαpos hQ.1 h6mem h7 k hk6
    have hae2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ θ : ℝ,
        Work.Spaces.DzIter k (fun z _ => Work.Construction.FK f z) z θ
          = Work.Construction.FK (Work.Spaces.DzIter k f) z :=
      Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hQ.1 h6mem k hk6
    filter_upwards [hae1, hae2] with z h1 h2
    rw [h2 0] at h1
    have hM2 : Work.Spaces.HkSq α (k + 1) f ≤ M ^ 2 := by
      calc Work.Spaces.HkSq α (k + 1) f ≤ Work.Spaces.HkSq α 4 f :=
            Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (show k + 1 ≤ 4 by omega) h4mem
        _ = (Work.FTS.Nonlin.Xn α f) ^ 2 := hXnSq.symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hM 2
    have hsq : (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2 ≤ C₁ * M ^ 2 :=
      le_trans h1 (mul_le_mul_of_nonneg_left hM2 hC₁pos.le)
    have habs : |Work.Construction.FK (Work.Spaces.DzIter k f) z| ≤ Real.sqrt C₁ * M := by
      have h2' : (|Work.Construction.FK (Work.Spaces.DzIter k f) z|) ^ 2
          ≤ (Real.sqrt C₁ * M) ^ 2 := by
        rw [sq_abs, mul_pow, Real.sq_sqrt hC₁pos.le]
        exact hsq
      have h3 := Real.sqrt_le_sqrt h2'
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hMnn)] at h3
      simpa using h3
    exact le_trans habs (mul_le_mul_of_nonneg_right hCgeS hMnn)
  · -- Part 2: integrability and the `L²`-price of the angular moment
    intro k hk6
    -- the a.e. domination of the weighted square of the angular moment
    have hdom : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Spaces.w z) ^ 2 * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2
          ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne
      intro hzI
      have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
      have hFK := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
        (α := α) (f := f) hQ.1 h6mem k hk6 hzpos
      have hIeq : (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k f z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter k f z θ) ^ 2 :=
        (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
          (fun θ : ℝ => (Work.Spaces.DzIter k f z θ) ^ 2)).symm
      have hIle : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter k f z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ ((h6mem.1 z hzI)) ?_
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
          have h := Work.FTS.StrongPersist.H6Row6.canonW_pure_le_Hk
            (α := α) (q := 0) (f := f) (j := k) (z := z) (θ := θ)
            (by norm_num [Work.Spaces.eta]) hk6 hθ
          simpa [neg_zero, Real.rpow_zero] using h
      calc (Work.Spaces.w z) ^ 2 * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2
          ≤ (Work.Spaces.w z) ^ 2
              * (16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k f z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hFK (sq_nonneg _)
        _ = 16 * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter k f z θ) ^ 2) := by ring
        _ = 16 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter k f z θ) ^ 2 := by rw [hIeq]
        _ ≤ 16 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_left hIle (by norm_num)
    have hDint : MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        Work.Spaces.Iz := h6mem.2
    have hΦmeas : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hm_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
          = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
      have hfk : AEStronglyMeasurable
          (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
        rw [← hm_eq]; exact aesm_fk_DzIter hQ.1 k
      have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
        rw [← hm_eq]; exact aesm_w_sq
      rw [hm_eq]
      exact hw.mul (hfk.pow 2)
    have hΦint : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2) Work.Spaces.Iz := by
      show MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
      refine MeasureTheory.Integrable.mono' (hDint.const_mul 16) hΦmeas ?_
      filter_upwards [hdom] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hz
    refine ⟨hΦint, ?_⟩
    have hle16 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2)
        ≤ 16 * Work.Spaces.HkSq α 6 f := by
      have hmain : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (Work.Construction.FK (Work.Spaces.DzIter k f) z) ^ 2)
          ≤ ∫ z in Work.Spaces.Iz,
              16 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hDint.const_mul 16) hdom
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
          (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      refine le_trans hmain ?_
      rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    exact le_trans hle16 (mul_le_mul_of_nonneg_right hCge16 (Work.Spaces.HkSq_nonneg α 6 f))

end

end Work.FTS.StrongPersist.H6Row6
