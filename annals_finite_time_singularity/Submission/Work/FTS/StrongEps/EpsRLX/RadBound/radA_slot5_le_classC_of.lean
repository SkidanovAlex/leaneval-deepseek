import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnLGammaT
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.GalFields.Norm.RadA4.Efun_le_Maj_four
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.slot5_radA_pointwise_le
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.GalFields.Norm.RadA4.Own
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.StrongPersist.H6Aux.q0Sm_Corr
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.RadBound

theorem radA_slot5_le_classC_of
    (hL12 : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          ∑ c ∈ Finset.range 5, (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range 5,
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.GalFields.Norm.slot5
          (Work.FTS.CoercivityFix.Transfer.radA α f) z) ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C1, hC1pos, hL12b⟩ := hL12
  obtain ⟨K, hKnn, hKb⟩ := Work.FTS.StrongPersist.H6Aux.Alt_ampA_dzdIter_bound6
  obtain ⟨Kb, hKbpos, hKbBd⟩ := Work.FTS.GalFields.Norm.RadA4.ampB_slotSum5_bound
  obtain ⟨C0c, hC0cpos, hC0bd⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨2 * (6400 * K ^ 2) * C1 + 200 * C0c ^ 2 * Kb + 1, by positivity, ?_⟩
  intro α hαIoc f hsm hmem h0
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- ### the four delegated inputs
  obtain ⟨hL12cont, hL12diff⟩ := L12f_iter_regular_open α hα hα1 f hsm hmem h0
  have hAdiff := diffDzd_ampA_mul_L12f_open α hα hα1 f hL12diff
  have hexp := radA_dzdIter_expansion_open α hα hα1 f hL12diff hAdiff
  have hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
    fun b hb z hz => hKb α hαIoc b (by omega) z hz
  -- ### the hypothesis at `(α, f)`
  obtain ⟨hL12int, hL12bd⟩ := hL12b α hαIoc f hsm hmem h0
  have hL12int' : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
      Work.Spaces.Iz := by
    simpa only [Work.FTS.GalFields.Norm.slot5] using hL12int
  have hL12bd' : (∫ z in Work.Spaces.Iz,
        Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
      ≤ C1 * Work.Spaces.HkSq α 4 f := by
    simpa only [Work.FTS.GalFields.Norm.slot5] using hL12bd
  -- ### integrability of the `ampB`-slot sum
  have hampBint : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      Work.Spaces.Iz := by
    have hcoeff := Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1
    show MeasureTheory.Integrable (fun z : ℝ => ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz)
    exact MeasureTheory.integrable_finsetSum _ (fun j hj =>
      hcoeff.2 j (by have := Finset.mem_range.mp hj; omega))
  -- ### the pointwise bound, a.e. on `Iz`
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z
        ≤ 2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
              * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hz : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    exact slot5_radA_pointwise_le α hα hα1 f hL12diff hAdiff hKnn hKbd hz
  -- ### a.e. strong measurability
  have htransport : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  have haesm_of_cont : ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Ioi (0 : ℝ)) →
      AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro g hg
    rw [htransport]
    exact hg.aestronglyMeasurable measurableSet_Ioi
  have hampA_cont : ∀ b : ℕ, b ≤ 4 → ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z) (Set.Ioi (0 : ℝ)) := by
    intro b hb
    have hcd : ContDiffOn ℝ (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α)
        (Set.Ioi (0 : ℝ)) :=
      Work.FTS.StrongPersist.H6Aux.contDiffOn_ampA α hα hα1 (b + 1)
    have h := Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
      (u := Work.FTS.CoercivityFix.Transfer.ampA α) (b := b) (n := 1) (by simpa using hcd)
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using h
  have hampB_cont : ∀ q : ℕ, q ≤ 4 → ContinuousOn (fun z : ℝ =>
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) (Set.Ioi (0 : ℝ)) := by
    intro q hq
    have hcd : ContDiffOn ℝ (q + 1) (Work.FTS.CoercivityFix.Transfer.ampB α)
        (Set.Ioi (0 : ℝ)) :=
      Work.FTS.StrongPersist.H6Aux.contDiffOn_ampB α (q + 1)
    have h := Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
      (u := Work.FTS.CoercivityFix.Transfer.ampB α) (b := q) (n := 1) (by simpa using hcd)
    simpa only [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter] using h
  have hw_sq_aesm : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hw : Measurable Work.Spaces.w := by
      have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
      rw [hfun]
      exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)
    exact (hw.pow_const 2).aestronglyMeasurable
  have hradA_aesm : ∀ q : ℕ, q ≤ 4 → AEStronglyMeasurable (fun z : ℝ =>
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro q hq
    have hae : (fun z : ℝ =>
          Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => -(∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
              * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
              * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
      rw [htransport]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z hz => hexp q hq z hz)
    have hpart : ∀ b ∈ Finset.range (q + 1), AEStronglyMeasurable (fun z : ℝ =>
        (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      intro b hb
      have hb4 : b ≤ 4 := by have := Finset.mem_range.mp hb; omega
      have hqb : q - b ≤ 4 := by omega
      have h1 : AEStronglyMeasurable (fun z : ℝ =>
          Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := haesm_of_cont (hampA_cont b hb4)
      have h2 : AEStronglyMeasurable (fun z : ℝ =>
          Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        haesm_of_cont (hL12cont (q - b) hqb)
      exact AEStronglyMeasurable.congr ((h1.mul h2).const_mul ((q.choose b : ℝ)))
        (Filter.Eventually.of_forall (fun z => by simp only [Pi.mul_apply, mul_assoc]))
    have hsum0 : AEStronglyMeasurable (∑ b ∈ Finset.range (q + 1), fun z : ℝ =>
        (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      Finset.aestronglyMeasurable_sum _ hpart
    have hsum : AEStronglyMeasurable (fun z : ℝ => ∑ b ∈ Finset.range (q + 1),
        (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hsum0.congr (Filter.Eventually.of_forall (fun z => by simp only [Finset.sum_apply]))
    have hB : AEStronglyMeasurable (fun z : ℝ =>
        Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := haesm_of_cont (hampB_cont q hq)
    exact ((hsum.neg).add (hB.const_mul _)).congr hae.symm
  have hmeas : AEStronglyMeasurable (fun z : ℝ =>
      Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hpart : ∀ q ∈ Finset.range 5, AEStronglyMeasurable (fun z : ℝ =>
        (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      intro q hq
      have hq4 : q ≤ 4 := by have := Finset.mem_range.mp hq; omega
      exact ((hradA_aesm q hq4).pow 2).mul hw_sq_aesm
    have hsum0 : AEStronglyMeasurable (∑ q ∈ Finset.range 5, fun z : ℝ =>
        (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      Finset.aestronglyMeasurable_sum _ hpart
    have hsum : AEStronglyMeasurable (fun z : ℝ => ∑ q ∈ Finset.range 5,
        (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hsum0.congr (Filter.Eventually.of_forall (fun z => by simp only [Finset.sum_apply]))
    simpa only [Work.FTS.GalFields.Norm.slot5] using hsum
  -- ### integrability of the dominating function
  have hdomint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      Work.Spaces.Iz :=
    (hL12int'.const_mul _).add (hampBint.const_mul _)
  -- ### the integrability of the target
  have hint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hdomint hmeas ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_of_nonneg (Work.FTS.GalFields.Norm.slot5_nonneg _ z)]
    exact hz
  -- ### the integrals
  have hC0abs : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0|
      ≤ C0c * Work.Spaces.HkNorm α 4 f := hC0bd α f hα hα1 hmem
  have hC0sq : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ C0c ^ 2 * Work.Spaces.HkSq α 4 f := by
    calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        = |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ^ 2 := by rw [sq_abs]
      _ ≤ (C0c * Work.Spaces.HkNorm α 4 f) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hC0abs 2
      _ = C0c ^ 2 * Work.Spaces.HkSq α 4 f := by
          rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
  have hcq : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
      ≤ 100 * (C0c ^ 2 * Work.Spaces.HkSq α 4 f) := by
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hc2 : (1 / Work.Spaces.c α) ^ 2 ≤ 100 := by
      rw [div_pow, one_pow]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
            * (1 / Work.Spaces.c α) ^ 2 := by ring
      _ ≤ (C0c ^ 2 * Work.Spaces.HkSq α 4 f) * 100 :=
          mul_le_mul hC0sq hc2 (by positivity)
            (mul_nonneg (sq_nonneg C0c) (Work.Spaces.HkSq_nonneg α 4 f))
      _ = 100 * (C0c ^ 2 * Work.Spaces.HkSq α 4 f) := by ring
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z : ℝ =>
      Work.FTS.GalFields.Norm.slot5_nonneg _ z)) hdomint hpt
  rw [MeasureTheory.integral_add (hL12int'.const_mul _) (hampBint.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  have hstep1 : 2 * (6400 * K ^ 2) * (∫ z in Work.Spaces.Iz,
        Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
      ≤ 2 * (6400 * K ^ 2) * (C1 * Work.Spaces.HkSq α 4 f) :=
    mul_le_mul_of_nonneg_left hL12bd' (by positivity)
  have hampBbd : (∫ z in Work.Spaces.Iz,
        Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z) ≤ Kb := by
    simpa only [Work.FTS.GalFields.Norm.slot5] using hKbBd α hα hα1
  have hstep2 : 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
          / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
        Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z)
      ≤ 2 * (100 * (C0c ^ 2 * Work.Spaces.HkSq α 4 f)) * Kb := by
    have h2 : (∫ z in Work.Spaces.Iz,
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z) ≤ Kb :=
      hampBbd
    refine mul_le_mul (mul_le_mul_of_nonneg_left hcq (by norm_num)) h2 ?_ ?_
    · exact MeasureTheory.integral_nonneg (fun z =>
        Work.FTS.GalFields.Norm.slot5_nonneg _ z)
    · exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg C0c) (Work.Spaces.HkSq_nonneg α 4 f)))
  have hkey : (∫ z in Work.Spaces.Iz,
      Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      ≤ (2 * (6400 * K ^ 2) * C1 + 200 * C0c ^ 2 * Kb) * Work.Spaces.HkSq α 4 f := by
    have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    have hK2 : 0 ≤ 2 * (6400 * K ^ 2) := by positivity
    calc (∫ z in Work.Spaces.Iz,
          Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ 2 * (6400 * K ^ 2) * (∫ z in Work.Spaces.Iz,
              Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
              * (∫ z in Work.Spaces.Iz,
                  Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z) :=
          hmono
      _ ≤ 2 * (6400 * K ^ 2) * (C1 * Work.Spaces.HkSq α 4 f)
            + 2 * (100 * (C0c ^ 2 * Work.Spaces.HkSq α 4 f)) * Kb :=
          add_le_add hstep1 hstep2
      _ = (2 * (6400 * K ^ 2) * C1 + 200 * C0c ^ 2 * Kb) * Work.Spaces.HkSq α 4 f := by ring
  refine ⟨hint, ?_⟩
  have hge : (2 * (6400 * K ^ 2) * C1 + 200 * C0c ^ 2 * Kb) * Work.Spaces.HkSq α 4 f
      ≤ (2 * (6400 * K ^ 2) * C1 + 200 * C0c ^ 2 * Kb + 1) * Work.Spaces.HkSq α 4 f := by
    apply mul_le_mul_of_nonneg_right _ (Work.Spaces.HkSq_nonneg α 4 f)
    linarith
  exact hkey.trans hge

end Work.FTS.StrongEps.EpsRLX.RadBound
