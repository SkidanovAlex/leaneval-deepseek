import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.ThetaAux
import Submission.Work.FTS.StrongEps.LocUnif.ThetaBound
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le_theta
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub_snd
import Submission.Work.FTS.StrongEps.LocUnif.rho_bounds
import Submission.Work.FTS.StrongEps.LocUnif.deriv_sq_weighted_le_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

theorem lintegral_backwardDiffQuot_majorant_le_liminf_theta {a b c c' d' d : ℝ}
    (hcc' : c < c') (hd'd : d' < d) (hab : a < b)
    {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ} {W : ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hWmeas : ∀ k, MeasureTheory.AEStronglyMeasurable (Function.uncurry (W k))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hconv : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), ∀ k,
      Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
          Filter.atTop := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · -- ## Degenerate case: empty index type
    haveI : IsEmpty ι := hempty
    have hL : ∀ (j : ℕ) (p : ℝ × ℝ), (∑ k : ι, ENNReal.ofReal
        (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
          * ρ k p.1 p.2) ^ 2)) = 0 := by
      intro j p
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hR : ∀ (n : ℕ) (p : ℝ × ℝ), (∑ k : ι,
        (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) = 0 := by
      intro n p
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hLHS : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop) = 0 := by
      simp only [hL, Filter.liminf_const, MeasureTheory.lintegral_zero]
    have hRHS : (Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
          Filter.atTop) = 0 := by
      simp only [hR, ENNReal.ofReal_zero, MeasureTheory.lintegral_zero, Filter.liminf_const]
    rw [hLHS, hRHS]
  · -- ## Main case
    haveI : Nonempty ι := hne
    let hq : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    let Fr : ℕ → ℝ × ℝ → ℝ := fun j p =>
      ∑ k, ((W k p.1 p.2 - W k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2
    let FrN : ℕ → ℕ → ℝ × ℝ → ℝ := fun n j p =>
      ∑ k, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2
    let Gr : ℕ → ℝ × ℝ → ℝ := fun n p =>
      ∑ k, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2
    have hSmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c' d') :=
      measurableSet_Icc.prod measurableSet_Icc
    have hRmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hSR : Set.Icc a b ×ˢ Set.Icc c' d' ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
      fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1, le_trans hp.2.2 (le_of_lt hd'd)⟩⟩
    by_cases hcd : c < d
    swap
    · -- degenerate case `d ≤ c`: the sub-box is empty, hence the left integral vanishes
      have hcd' : d' < c' := by linarith [not_lt.mp hcd, hcc', hd'd]
      have hempty : (Set.Icc a b ×ˢ Set.Icc c' d' : Set (ℝ × ℝ)) = ∅ := by
        rw [Set.Icc_eq_empty (not_le.mpr hcd'), Set.prod_empty]
      have hnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Set.Icc a b ×ˢ Set.Icc c' d') = 0 := by
        rw [hempty, measure_empty]
      have hzero : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
            (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
              * ρ k p.1 p.2) ^ 2)) Filter.atTop) = 0 := by
        rw [MeasureTheory.Measure.restrict_eq_zero.mpr hnull, MeasureTheory.lintegral_zero_measure]
      rw [hzero]
      exact bot_le
    -- ## 1. A uniform lower bound for `ρ` and a modulus of continuity in `θ`
    have hlow : ∀ k : ι, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m ≤ ρ k z θ :=
      fun k => (rho_bounds hab hcd (hρc k) (hρp k)).1
    choose m hm_pos hm_le using hlow
    let m0 : ℝ := Finset.univ.inf' Finset.univ_nonempty m
    have hm0_pos : 0 < m0 := by
      show (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty m
      rw [Finset.lt_inf'_iff]
      intro k _
      exact hm_pos k
    have hm0_le : ∀ (k : ι) (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d → m0 ≤ ρ k z θ := by
      intro k z θ hz hθ
      exact le_trans (Finset.inf'_le m (Finset.mem_univ k)) (hm_le k z hz θ hθ)
    have hunif : ∀ ε > 0, ∃ δ > 0, ∀ k : ι, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        ∀ y ∈ Set.Icc c d, |θ - y| < δ → |ρ k z θ - ρ k z y| < ε := by
      intro ε hε
      choose δ hδ_pos hδ_spec using fun k => rho_bounds_theta (hρc k) ε hε
      refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
      · show (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty δ
        rw [Finset.lt_inf'_iff]
        intro k _
        exact hδ_pos k
      · intro k z hz θ hθ y hy hlt
        exact hδ_spec k z hz θ hθ y hy (lt_of_lt_of_le hlt (Finset.inf'_le δ (Finset.mem_univ k)))
    -- ## 2. The shift `J`
    have hq_pos : ∀ j : ℕ, 0 < hq j := by intro j; dsimp only [hq]; positivity
    have hq_tendsto : Filter.Tendsto hq Filter.atTop (nhds 0) := by
      simpa only [hq] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, hq J < c' - c :=
      (hq_tendsto.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < c' - c))).exists
    have hq_mono : ∀ j : ℕ, hq (j + J) ≤ hq J := by
      intro j
      dsimp only [hq]
      rw [Nat.cast_add]
      have h1 : (0:ℝ) < (J:ℝ) + 1 := by positivity
      have h2 : (J:ℝ) + 1 ≤ (j:ℝ) + (J:ℝ) + 1 := by
        have h3 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith
      exact one_div_le_one_div_of_le h1 h2
    have hq_lt : ∀ j : ℕ, hq (j + J) < c' - c := fun j => lt_of_le_of_lt (hq_mono j) hJ
    have hshift_map : ∀ j : ℕ, ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c' d',
        (q.1, q.2 - hq (j + J)) ∈ Set.Icc a b ×ˢ Set.Icc c d := by
      intro j q hqS
      obtain ⟨h1, h2⟩ := hqS
      exact ⟨h1, ⟨by linarith [h2.1, hq_lt j], by linarith [h2.2, hd'd, hq_pos (j + J)]⟩⟩
    -- ## 3. Measurability of `W` (and of its shift)
    have hWm : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      intro k
      have hV : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => V n k p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        fun n => (hVc n k).aemeasurable hRmeas
      refine AEMeasurable.congr (AEMeasurable.liminf hV) ?_
      filter_upwards [hconv] with p hp
      exact (hp k).liminf_eq
    have hWmS : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
      fun k => (hWm k).mono_set hSR
    have hWshift : ∀ j : ℕ, ∀ k : ι,
        AEMeasurable (fun p : ℝ × ℝ => W k p.1 (p.2 - hq (j + J)))
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j k
      have hV : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
        intro n
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        exact ((hVc n k).comp hcs (hshift_map j)).aemeasurable hSmeas
      refine AEMeasurable.congr (AEMeasurable.liminf hV) ?_
      filter_upwards [ae_shift_preimage_sub_snd hRmeas hSmeas hconv (hshift_map j)] with p hp
      exact (hp k).liminf_eq
    -- ## 4. Measurability of the integrands
    have hFr_meas : ∀ j : ℕ, AEMeasurable (Fr (j + J))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j
      have hterm : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ =>
          ((W k p.1 p.2 - W k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
        intro k
        have h1 : AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2 - W k p.1 (p.2 - hq (j + J)))
            (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
          (hWmS k).sub (hWshift j k)
        have h2 : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
          ((hρc k).mono hSR).aemeasurable hSmeas
        exact AEMeasurable.pow ((h1.mul_const ((((j + J : ℕ) : ℝ) + 1))).mul h2) aemeasurable_const
      exact Finset.aemeasurable_fun_sum Finset.univ fun k _ => hterm k
    have hFmeas : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Fr (j + J) p))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖Fr (j + J) p‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hFr_meas j).aestronglyMeasurable
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- the per-`k` difference-quotient integrand is continuous on the small box
    have hper_meas : ∀ n j : ℕ, ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro n j k
      have hcont : ContinuousOn (fun p : ℝ × ℝ => ((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J)))
          * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c' d') := by
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).mono hSR
        have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs (hshift_map j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hρc k).mono hSR
        exact (((h1.sub h2).mul_const (((j + J : ℕ) : ℝ) + 1)).mul h3).pow 2
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J)))
          * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable hSmeas)
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- ## 5. The a.e. convergence at both the point and the shifted point
    have hae_conv : ∀ j : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')),
        (∀ k : ι, Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) ∧
        (∀ k : ι, Filter.Tendsto (fun n => V n k p.1 (p.2 - hq (j + J))) Filter.atTop
          (nhds (W k p.1 (p.2 - hq (j + J))))) := by
      intro j
      refine (Eventually.filter_mono
        (MeasureTheory.ae_mono (Measure.restrict_mono hSR le_rfl)) hconv).and ?_
      exact ae_shift_preimage_sub_snd hRmeas hSmeas hconv (hshift_map j)
    have hfrN_meas : ∀ j n : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (FrN n (j + J) p))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
      intro j n
      have hcont : ContinuousOn (FrN n (j + J)) (Set.Icc a b ×ˢ Set.Icc c' d') := by
        refine continuousOn_finsetSum Finset.univ fun k _ => ?_
        have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') :=
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).mono hSR
        have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq (j + J)))
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs (hshift_map j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
            (Set.Icc a b ×ˢ Set.Icc c' d') := (hρc k).mono hSR
        exact (((h1.sub h2).mul_const (((j + J : ℕ) : ℝ) + 1)).mul h3).pow 2
      have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖FrN n (j + J) p‖ₑ)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
        AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable hSmeas)
      refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
      exact Real.enorm_eq_ofReal (by positivity)
    -- ## 6. The two Fatou steps
    have hFatou1 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop :=
      lintegral_liminf_le' hFmeas
    have hshift_liminf : ∀ p : ℝ × ℝ,
        Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
          = Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop := by
      intro p
      have h := Filter.liminf_comp (fun j : ℕ => ENNReal.ofReal (Fr j p)) (fun j : ℕ => j + J) Filter.atTop
      rw [Filter.map_add_atTop_eq_nat] at h
      exact h
    have hFatou2 : ∀ j : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal (Fr (j + J) p)
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop := by
      intro j
      refine lintegral_le_liminf_of_eventually_le (hfrN_meas j) ?_
      filter_upwards [hae_conv j] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hlim : Filter.Tendsto (fun n : ℕ => FrN n (j + J) p) Filter.atTop (nhds (Fr (j + J) p)) := by
        have hterm : ∀ k : ι, Filter.Tendsto (fun n : ℕ =>
            ((V n k p.1 p.2 - V n k p.1 (p.2 - hq (j + J))) * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
            Filter.atTop (nhds (((W k p.1 p.2 - W k p.1 (p.2 - hq (j + J)))
              * (((j + J : ℕ) : ℝ) + 1) * ρ k p.1 p.2) ^ 2)) := by
          intro k
          exact ((((hp1 k).sub (hp2 k)).mul_const ((((j + J : ℕ) : ℝ) + 1))).mul_const (ρ k p.1 p.2)).pow 2
        exact tendsto_finsetSum Finset.univ fun k _ => hterm k
      have hlim2 := ENNReal.tendsto_ofReal hlim
      rw [hlim2.liminf_eq]
    -- ## 7. The uniform bound, with the weight ratio tending to `1`
    have hq_ltF : ∀ᶠ j : ℕ in Filter.atTop, hq j < c' - c := by
      refine Filter.eventually_atTop.mpr ⟨J, fun j hj => ?_⟩
      rw [show j = (j - J) + J from (Nat.sub_add_cancel hj).symm]
      exact hq_lt (j - J)
    have hbound : ∀ e : ℝ, 0 < e → ∃ K : ℕ, ∀ j ≥ K, ∀ n : ℕ,
        ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal (FrN n (j + J) p)
          ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
              ENNReal.ofReal (Gr n p) := by
      intro e he
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
        (backwardDiffQuot_theta_bound hcc' hd'd hab hρc hρp hVsm hVc (fun j => rfl) hm0_pos
          hm0_le hunif hq_ltF e he)
      exact ⟨K, fun j hj n => hK (j + J) (le_trans hj (Nat.le_add_right j J)) n⟩
    -- ## 9. The chain of inequalities
    set A : ℝ≥0∞ := Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal (Gr n p)) Filter.atTop with hAdef
    have hstep1 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop := by
      refine le_trans (le_of_eq ?_) hFatou1
      exact lintegral_congr fun p => (hshift_liminf p).symm
    have hstep2 : Filter.liminf (fun j : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (Fr (j + J) p)) Filter.atTop
        ≤ Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop :=
      liminf_le_liminf_of_le' hFatou2
    have hstep3 : ∀ e : ℝ, 0 < e →
        Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
            ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop
        ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * A := by
      intro e he
      obtain ⟨K, hK⟩ := hbound e he
      refine liminf_le_of_eventually_le_const (K := K) fun j hj => ?_
      refine le_trans (liminf_le_liminf_of_le' fun n => hK j hj n) ?_
      have hC0 : ENNReal.ofReal ((1 + e / m0) ^ 2) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]
        have : 0 < (1 + e / m0) ^ 2 := by positivity
        linarith
      exact le_of_eq (liminf_const_mul_of_ne_top hC0 ENNReal.ofReal_ne_top _)
    have hlast : Filter.liminf (fun j : ℕ => Filter.liminf (fun n : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
          ENNReal.ofReal (FrN n (j + J) p)) Filter.atTop) Filter.atTop ≤ A := by
      by_cases hAtop : A = ⊤
      · rw [hAtop]; exact le_top
      · have hcn : Filter.Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2)
            Filter.atTop (nhds 1) := by
          have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h2 : Filter.Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) Filter.atTop
              (nhds ((1 + 0 / m0) ^ 2)) :=
            ((tendsto_const_nhds.add (h1.div_const m0))).pow 2
          simpa using h2
        have hseq : Filter.Tendsto (fun n : ℕ =>
            ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A) Filter.atTop (nhds A) := by
          have h3 : Filter.Tendsto (fun n : ℕ =>
              (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2 * A.toReal) Filter.atTop (nhds (1 * A.toReal)) :=
            hcn.mul_const A.toReal
          have h4 : Filter.Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2 * A.toReal))
              Filter.atTop (nhds (ENNReal.ofReal (1 * A.toReal))) := ENNReal.tendsto_ofReal h3
          have h5 : Filter.Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A)
              Filter.atTop (nhds (ENNReal.ofReal (1 * A.toReal))) := by
            refine h4.congr' ?_
            filter_upwards with n
            rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2)]
            congr 1
            exact ENNReal.ofReal_toReal hAtop
          simpa only [one_mul, ENNReal.ofReal_toReal hAtop] using h5
        have hle : ∀ n : ℕ, Filter.liminf (fun j : ℕ => Filter.liminf (fun m : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
              ENNReal.ofReal (FrN m (j + J) p)) Filter.atTop) Filter.atTop
            ≤ ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A :=
          fun n => hstep3 (1 / ((n : ℝ) + 1))
            (one_div_pos.mpr (by have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith))
        calc Filter.liminf (fun j : ℕ => Filter.liminf (fun m : ℕ => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
                ENNReal.ofReal (FrN m (j + J) p)) Filter.atTop) Filter.atTop
            ≤ Filter.liminf (fun n : ℕ =>
                ENNReal.ofReal ((1 + (1 / ((n : ℝ) + 1)) / m0) ^ 2) * A) Filter.atTop := by
              refine le_trans (le_iInf fun n => hle n) ?_
              rw [Filter.liminf_eq_iSup_iInf_of_nat]
              refine le_trans ?_ (le_iSup (fun j : ℕ => ⨅ i : ℕ, ⨅ (_ : i ≥ j),
                ENNReal.ofReal ((1 + (1 / ((i : ℝ) + 1)) / m0) ^ 2) * A) 0)
              exact le_iInf fun i => le_iInf fun _ => iInf_le _ i
          _ = A := hseq.liminf_eq
    have hgoalL : (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
            (((W k p.1 p.2 - W k p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
              * ρ k p.1 p.2) ^ 2)) Filter.atTop)
        = ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c' d'),
          Filter.liminf (fun j : ℕ => ENNReal.ofReal (Fr j p)) Filter.atTop := by
      refine lintegral_congr fun p => ?_
      refine Filter.liminf_congr (Filter.Eventually.of_forall fun j => ?_)
      exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    rw [hgoalL]
    exact le_trans hstep1 (le_trans hstep2 hlast)

end Work.FTS.StrongEps.LocUnif
