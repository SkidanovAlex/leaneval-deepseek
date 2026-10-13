import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.StrongEps.LocUnif.ThetaAux
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le_theta
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_subbox_eq_iSup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

/-- The uniform bound for the `θ`-direction backward difference quotient: for every `e > 0`,
eventually in `j`, the weighted `L¹`-norm of the difference quotient of `V n` at scale
`hq j = 1 / (j+1)` is bounded by `(1 + e/m0)^2` times the weighted `L¹`-norm of `∂_θ V n`. -/
theorem backwardDiffQuot_theta_bound {a b c c' d' d : ℝ} (hcc' : c < c') (hd'd : d' < d)
    (hab : a < b) {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    {hq : ℕ → ℝ} (hq_eq : ∀ j : ℕ, hq j = 1 / ((j : ℝ) + 1))
    {m0 : ℝ} (hm0_pos : 0 < m0)
    (hm0_le : ∀ (k : ι) (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d → m0 ≤ ρ k z θ)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ k : ι, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        ∀ y ∈ Set.Icc c d, |θ - y| < δ → |ρ k z θ - ρ k z y| < ε)
    (hq_lt : ∀ᶠ j : ℕ in Filter.atTop, hq j < c' - c)
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ j : ℕ in Filter.atTop, ∀ n : ℕ,
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
        (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) *
        ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal
          (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) := by
  have hq_pos : ∀ j : ℕ, 0 < hq j := fun j => by rw [hq_eq j]; positivity
  have hq_tendsto : Filter.Tendsto hq Filter.atTop (nhds 0) := by
    rw [show hq = fun j : ℕ => 1 / ((j : ℝ) + 1) from funext hq_eq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨δ, hδpos, hδspec⟩ := hunif e he
  refine ((hq_tendsto.eventually (Iio_mem_nhds hδpos)).and hq_lt).mono fun j hh n => ?_
  obtain ⟨hj, hjlt⟩ := hh
  have hshift : ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c' d',
      (q.1, q.2 - hq j) ∈ Set.Icc a b ×ˢ Set.Icc c d := by
    intro q hqS
    obtain ⟨h1, h2⟩ := hqS
    exact ⟨h1, ⟨by linarith [h2.1, hjlt], by linarith [h2.2, hd'd, hq_pos j]⟩⟩
  have hC : 1 ≤ (1 + e / m0) ^ 2 := by
    have h1 : 0 ≤ e / m0 := le_of_lt (div_pos he hm0_pos)
    nlinarith
  have hratio : ∀ (k : ι) (z y θ : ℝ), z ∈ Set.Icc a b → y ∈ Set.Icc c d →
      θ ∈ Set.Icc c d → |θ - y| ≤ hq j →
      (ρ k z θ) ^ 2 ≤ (1 + e / m0) ^ 2 * (ρ k z y) ^ 2 := by
    intro k z y θ hz hy hθ hyθ
    have h1 : |ρ k z θ - ρ k z y| < e :=
      hδspec k z hz θ hθ y hy (lt_of_le_of_lt hyθ hj)
    have hlt : ρ k z θ < ρ k z y * (1 + e / m0) := by
      have h2 : ρ k z θ < ρ k z y + e := by linarith [(abs_lt.mp h1).2]
      have h3 : e ≤ e * ρ k z y / m0 := by
        have h4 : 1 ≤ ρ k z y / m0 := by
          rw [le_div_iff₀ hm0_pos]; linarith [hm0_le k z y hz hy]
        calc e = e * 1 := by ring
          _ ≤ e * (ρ k z y / m0) := mul_le_mul_of_nonneg_left h4 (le_of_lt he)
          _ = e * ρ k z y / m0 := by ring
      have h5 : ρ k z y * (1 + e / m0) = ρ k z y + e * ρ k z y / m0 := by ring
      rw [h5]; linarith
    have h5 : 0 ≤ ρ k z θ := le_of_lt (hρp k z hz θ hθ)
    have h6 : (ρ k z θ) ^ 2 ≤ (ρ k z y * (1 + e / m0)) ^ 2 := by nlinarith [h5, hlt]
    calc (ρ k z θ) ^ 2 ≤ (ρ k z y * (1 + e / m0)) ^ 2 := h6
      _ = (1 + e / m0) ^ 2 * (ρ k z y) ^ 2 := by ring
  have hper_meas : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
    intro k
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
        * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c' d') := by
      have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq j))
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (hVc n k).mono (fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1,
          le_trans hp.2.2 (le_of_lt hd'd)⟩⟩)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq j))
          (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs hshift
      have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (hρc k).mono (fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1,
          le_trans hp.2.2 (le_of_lt hd'd)⟩⟩)
      exact (((h1.sub h2).mul_const ((j : ℝ) + 1)).mul h3).pow 2
    have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
        * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2‖ₑ)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
      AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc))
    refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
    exact Real.enorm_eq_ofReal (by positivity)
  have hper : ∀ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
          * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) := by
    intro k
    by_cases hcd' : c' < d'
    · -- the interior sub-box exhaustion of the difference-quotient region
      rw [lintegral_subbox_eq_iSup hab hcd' (hper_meas k)]
      refine iSup_le fun l => ?_
      set al : ℝ := a + (b - a) / ((l : ℝ) + 2) with haldef
      set bl : ℝ := b - (b - a) / ((l : ℝ) + 2) with hbldef
      set cl : ℝ := c' + (d' - c') / ((l : ℝ) + 2) with hcldef
      set dl : ℝ := d' - (d' - c') / ((l : ℝ) + 2) with hdldef
      have hposb : 0 < (b - a) / ((l : ℝ) + 2) := div_pos (by linarith) (by positivity)
      have hposd : 0 < (d' - c') / ((l : ℝ) + 2) := div_pos (by linarith) (by positivity)
      have hal : a < al := by rw [haldef]; linarith
      have hbl : bl < b := by rw [hbldef]; linarith
      have hcl : c' < cl := by rw [hcldef]; linarith
      have hdl : dl < d' := by rw [hdldef]; linarith
      have hreg : (Set.Icc (a + (b - a) / ((l : ℝ) + 2)) (b - (b - a) / ((l : ℝ) + 2))
            ×ˢ Set.Icc (c' + (d' - c') / ((l : ℝ) + 2)) (d' - (d' - c') / ((l : ℝ) + 2))
            : Set (ℝ × ℝ)) = (Set.Icc al bl ×ˢ Set.Icc cl dl) := by
        rw [haldef, hbldef, hcldef, hdldef]
      rw [hreg]
      have hsm_sub : ∀ z ∈ Set.Icc al bl, ContDiffOn ℝ 1 (fun θ => V n k z θ) (Set.Ioo c d) := by
        intro z hz
        have hzab : z ∈ Set.Ioo a b := ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩
        have hlin : ContDiffOn ℝ 1 (fun θ : ℝ => (z, θ)) (Set.Ioo c d) := by
          have h1 : ContDiff ℝ 1 (fun θ : ℝ => (z, θ)) := by fun_prop
          exact h1.contDiffOn
        exact (hVsm n k).comp hlin fun θ hθ => ⟨hzab, hθ⟩
      have hc_sub : ∀ z ∈ Set.Icc al bl, ContinuousOn (fun θ => V n k z θ) (Set.Icc c d) := by
        intro z hz
        exact (hVc n k).comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩, hθ⟩)
      have hmeas_sub : AEMeasurable (fun p : ℝ × ℝ =>
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2))
          (MeasureTheory.volume.restrict (Set.Icc al bl ×ˢ Set.Icc c d)) := by
        have hsubst : Set.Icc al bl ×ˢ Set.Icc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
          intro p hp
          exact ⟨⟨by linarith [hp.1.1, hal], by linarith [hp.1.2, hbl]⟩, hp.2⟩
        exact AEMeasurable.mono_set hsubst (aemeasurable_pth_sq_mul (hVsm n k) (hρc k))
      have hDQ := diffQuot_backward_lintegral_le_theta (a := al) (b := bl) (c := c) (d := d)
        (c' := cl) (d' := dl) (h := hq j) (C := (1 + e / m0) ^ 2) (w := ρ k) (u := V n k)
        (by linarith) (by linarith) (hq_pos j) (by linarith [hjlt, hcl]) hC
        (fun z hz θ hθ => hρp k z ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩ θ hθ)
        (fun z hz y hy θ hθ hzy =>
          hratio k z y θ ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩ hy hθ hzy)
        hsm_sub hc_sub hmeas_sub
      refine le_trans (le_of_eq ?_) (le_trans hDQ ?_)
      · -- identify the difference-quotient integrands
        refine lintegral_congr fun p => ?_
        congr 1
        rw [← mul_pow]
        congr 1
        have hh : (V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) / hq j
            = (V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) := by
          rw [hq_eq j]
          field_simp
        rw [hh]
      · -- enlarge the integration region `Icc al bl ×ˢ Icc c d ⊆ Icc a b ×ˢ Icc c d`
        refine mul_le_mul' le_rfl (setLIntegral_mono_subset
          (measurableSet_Icc.prod measurableSet_Icc) (measurableSet_Icc.prod measurableSet_Icc) ?_)
        intro p hp
        exact ⟨⟨le_trans (le_of_lt hal) hp.1.1, le_trans hp.1.2 (le_of_lt hbl)⟩, hp.2⟩
    · -- degenerate `θ`-box: the region is null
      have h0 : (MeasureTheory.volume (Set.Icc c' d') : ℝ≥0∞) = 0 := by
        rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
        linarith [not_lt.mp hcd']
      have hSnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Set.Icc a b ×ˢ Set.Icc c' d') = 0 := by
        rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, h0, mul_zero]
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hSnull, MeasureTheory.lintegral_zero_measure]
      exact bot_le
  have hd_meas : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun k => aemeasurable_pth_sq_mul (hVsm n k) (hρc k)
  calc ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
        (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      = ∑ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) := by
        rw [show (fun p : ℝ × ℝ => ENNReal.ofReal
            (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
            = fun p : ℝ × ℝ => ∑ k : ι, ENNReal.ofReal
              (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) from by
          funext p
          exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
        exact lintegral_finsetSum' Finset.univ fun k _ => hper_meas k
    _ ≤ ∑ k : ι, ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) :=
        Finset.sum_le_sum fun k _ => hper k
    _ = ENNReal.ofReal ((1 + e / m0) ^ 2) * (∑ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2)) :=
        (Finset.mul_sum _ _ _).symm
    _ = ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) := by
        congr 1
        rw [show (fun p : ℝ × ℝ => ENNReal.ofReal
            (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
            = fun p : ℝ × ℝ => ∑ k : ι, ENNReal.ofReal
              ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) from by
          funext p
          rw [show (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2)
              = ∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2 from
            Finset.sum_congr rfl fun k _ => mul_pow _ _ 2]
          exact ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact (lintegral_finsetSum' Finset.univ fun k _ => hd_meas k).symm

end Work.FTS.StrongEps.LocUnif
