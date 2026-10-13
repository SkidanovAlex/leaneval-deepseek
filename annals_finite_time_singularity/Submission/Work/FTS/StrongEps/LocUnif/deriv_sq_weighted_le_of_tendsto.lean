import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.rho_bounds
import Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_subbox_eq_iSup
import Submission.Work.FTS.StrongEps.LocUnif.tendsto_backward_diffQuot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Fatou's lemma for real-valued functions: if `ofReal (f x) ≤ liminf_n ofReal (G n x)` almost
everywhere, then `∫⁻ ofReal f ≤ liminf_n ∫⁻ ofReal (G n)`.  This is the sharp lower-semicontinuity
statement for the lower Lebesgue integral, stated at the `ENNReal` level so no integrability
hypothesis is needed. -/
theorem lintegral_le_liminf_of_eventually_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {f : α → ℝ}
    (hG : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (G n x)) μ)
    (h : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤
      Filter.liminf (fun n => ENNReal.ofReal (G n x)) Filter.atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) Filter.atTop :=
  (MeasureTheory.lintegral_mono_ae h).trans (MeasureTheory.lintegral_liminf_le' hG)

theorem deriv_sq_weighted_le_of_tendsto {a b c d M : ℝ} (hab : a < b) (hcd : c < d)
    {ρ : ℝ → ℝ → ℝ} (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ z θ)
    {X : ℕ → ℝ → ℝ → ℝ} {Y : ℝ → ℝ → ℝ}
    (hXsm : ∀ n, ContDiffOn ℝ 1 (Function.uncurry (X n)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hXc : ∀ n, ContinuousOn (Function.uncurry (X n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hYc : ContinuousOn (Function.uncurry Y) (Set.Icc a b ×ˢ Set.Icc c d))
    (hconv : ∀ z θ, (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d →
      Filter.Tendsto (fun n => X n z θ) Filter.atTop (nhds (Y z θ)))
    (hIntX : ∀ n, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (fun z' => X n z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hbd : ∀ n, ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      (deriv (fun z' => X n z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2 ≤ M) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      (deriv (fun z' => Y z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2 ≤ M := by
  classical
  let box : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  let ff : ℝ × ℝ → ℝ := fun p => (deriv (fun z' => Y z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2
  let gn : ℕ → ℝ × ℝ → ℝ := fun n p =>
    (deriv (fun z' => X n z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2
  change ∫ p in Set.Icc a b ×ˢ Set.Icc c d, ff p ≤ M
  have hM : 0 ≤ M := by
    have h0 : (0 : ℝ) ≤ ∫ p in Set.Icc a b ×ˢ Set.Icc c d, gn 0 p :=
      integral_nonneg (fun p => by positivity)
    exact h0.trans (hbd 0)
  obtain ⟨⟨m, hm_pos, hm_le⟩, hunif⟩ := rho_bounds hab hcd hρc hρp
  have hslice_sm : ∀ n, ∀ θ ∈ Set.Ioo c d,
      ContDiffOn ℝ 1 (fun z => X n z θ) (Set.Ioo a b) := by
    intro n θ hθ
    have hlin : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioo a b) := by
      have h1 : ContDiff ℝ 1 (fun z : ℝ => (z, θ)) := by fun_prop
      exact h1.contDiffOn
    exact (hXsm n).comp hlin (fun z hz => ⟨hz, hθ⟩)
  have hslice_c : ∀ n, ∀ θ ∈ Set.Icc c d,
      ContinuousOn (fun z => X n z θ) (Set.Icc a b) := by
    intro n θ hθ
    have hφ : Continuous (fun z : ℝ => (z, θ)) := continuous_id.prodMk continuous_const
    exact (hXc n).comp hφ.continuousOn (fun z hz => ⟨hz, hθ⟩)
  let eps : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have heps_pos : ∀ j, 0 < eps j := by intro j; simp only [eps]; positivity
  have heps_tendsto : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let del : ℕ → ℝ := fun j => Classical.choose (hunif (eps j) (heps_pos j))
  have hdel_pos : ∀ j, 0 < del j :=
    fun j => (Classical.choose_spec (hunif (eps j) (heps_pos j))).1
  have hdel_spec : ∀ j, ∀ z ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - t| < del j → |ρ z θ - ρ t θ| < eps j :=
    fun j => (Classical.choose_spec (hunif (eps j) (heps_pos j))).2
  let hhh : ℕ → ℝ := fun j => min (del j / 2) (eps j)
  have hhh_pos : ∀ j, 0 < hhh j := fun j =>
    lt_min (by linarith [hdel_pos j]) (heps_pos j)
  have hhh_le_eps : ∀ j, hhh j ≤ eps j := fun j => min_le_right _ _
  have hhh_lt_del : ∀ j, hhh j < del j := by
    intro j
    calc hhh j ≤ del j / 2 := min_le_left _ _
      _ < del j := by linarith [hdel_pos j]
  have hhh_tendsto : Tendsto hhh atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds heps_tendsto
      (fun j => le_of_lt (hhh_pos j)) hhh_le_eps
  let Cc : ℕ → ℝ := fun j => (1 + eps j / m) ^ 2
  have hCc_ge : ∀ j, 1 ≤ Cc j := by
    intro j
    have h1 : 0 ≤ eps j / m := le_of_lt (div_pos (heps_pos j) hm_pos)
    have h2 : (1 : ℝ) ≤ 1 + eps j / m := by linarith
    simp only [Cc]
    nlinarith [h2, h1]
  have hCc_tendsto : Tendsto Cc atTop (𝓝 1) := by
    have h1 : Tendsto (fun j => eps j / m) atTop (𝓝 0) := by
      simpa using heps_tendsto.div_const m
    have h2 : Tendsto (fun j => 1 + eps j / m) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h1
    have h3 := h2.pow 2
    simpa [Cc] using h3
  have hCc_ratio : ∀ j, ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ hhh j → (ρ z θ) ^ 2 ≤ Cc j * (ρ y θ) ^ 2 := by
    intro j z hz y hy θ hθ hzy
    have h1 : |ρ z θ - ρ y θ| < eps j :=
      hdel_spec j z hz y hy θ hθ (lt_of_le_of_lt hzy (hhh_lt_del j))
    have hypos : 0 < ρ y θ := lt_of_lt_of_le hm_pos (hm_le y hy θ hθ)
    have hzpos : 0 < ρ z θ := hρp z hz θ hθ
    have hlt : ρ z θ < ρ y θ * (1 + eps j / m) := by
      have h2 : ρ z θ - ρ y θ < eps j := (abs_lt.mp h1).2
      have h3 : ρ z θ < ρ y θ + eps j := by linarith
      have h4 : eps j / ρ y θ ≤ eps j / m :=
        div_le_div_of_nonneg_left (le_of_lt (heps_pos j)) hm_pos (hm_le y hy θ hθ)
      have hyne : ρ y θ ≠ 0 := ne_of_gt hypos
      have h5 : ρ y θ * (eps j / ρ y θ) = eps j := by field_simp
      have h6 : ρ y θ * (1 + eps j / ρ y θ) ≤ ρ y θ * (1 + eps j / m) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hypos); linarith
      nlinarith [h3, h5, h6]
    have h7 : (ρ z θ) ^ 2 < (ρ y θ * (1 + eps j / m)) ^ 2 := by nlinarith [hzpos, hypos]
    have h8 : (ρ y θ * (1 + eps j / m)) ^ 2 = Cc j * (ρ y θ) ^ 2 := by
      simp only [Cc]; ring
    linarith [h7, le_of_eq h8]
  by_cases hffm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (ff p)) (volume.restrict box)
  · have hkey : ∀ a' b' c' d' : ℝ, a < a' → b' < b → c < c' → d' < d →
        ∫⁻ p in (Set.Icc a' b' ×ˢ Set.Icc c' d'), ENNReal.ofReal (ff p) ≤ ENNReal.ofReal M := by
      intro a' b' c' d' haa' hb'b hcc' hd'd
      obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
        (hhh_tendsto.eventually (Iio_mem_nhds (show (0 : ℝ) < a' - a by linarith)))
      let hs : ℕ → ℝ := fun j => hhh (j + J)
      let Cs : ℕ → ℝ := fun j => Cc (j + J)
      have hs_pos : ∀ j, 0 < hs j := fun j => hhh_pos (j + J)
      have hs_lt : ∀ j, hs j < a' - a := fun j => hJ (j + J) (Nat.le_add_left J j)
      have hs_tendsto : Tendsto hs atTop (𝓝 0) :=
        hhh_tendsto.comp (tendsto_add_atTop_nat J)
      have hCs_ge : ∀ j, 1 ≤ Cs j := fun j => hCc_ge (j + J)
      have hCs_tendsto : Tendsto Cs atTop (𝓝 1) := hCc_tendsto.comp (tendsto_add_atTop_nat J)
      have hCs_ratio : ∀ j, ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c' d',
          |z - y| ≤ hs j → (ρ z θ) ^ 2 ≤ Cs j * (ρ y θ) ^ 2 := by
        intro j z hz y hy θ hθ hzy
        exact hCc_ratio (j + J) z hz y hy θ
          ⟨le_trans (le_of_lt hcc') hθ.1, le_trans hθ.2 (le_of_lt hd'd)⟩ hzy
      let sub : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c' d'
      have hsub_meas : MeasurableSet sub := measurableSet_Icc.prod measurableSet_Icc
      have hsub_box : sub ⊆ box := by
        intro p hp
        exact ⟨⟨le_trans (le_of_lt haa') hp.1.1, le_trans hp.1.2 (le_of_lt hb'b)⟩,
          ⟨le_trans (le_of_lt hcc') hp.2.1, le_trans hp.2.2 (le_of_lt hd'd)⟩⟩
      let Kf : ℕ → ℝ × ℝ → ℝ := fun j p =>
        ((Y p.1 p.2 - Y (p.1 - hs j) p.2) / hs j) ^ 2 * (ρ p.1 p.2) ^ 2
      let Knf : ℕ → ℕ → ℝ × ℝ → ℝ := fun j n p =>
        ((X n p.1 p.2 - X n (p.1 - hs j) p.2) / hs j) ^ 2 * (ρ p.1 p.2) ^ 2
      have hYc_sub : ContinuousOn (fun p : ℝ × ℝ => Y p.1 p.2) sub := hYc.mono hsub_box
      have hρc_sub : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) sub := hρc.mono hsub_box
      have hXc_sub : ∀ n, ContinuousOn (fun p : ℝ × ℝ => X n p.1 p.2) sub :=
        fun n => (hXc n).mono hsub_box
      have hshift_map : ∀ j, Set.MapsTo (fun p : ℝ × ℝ => (p.1 - hs j, p.2)) sub box := by
        intro j p hp
        refine ⟨⟨?_, ?_⟩, (hsub_box hp).2⟩
        · have h1 := hp.1.1; have h2 := hs_lt j; linarith
        · have h1 := hp.1.2; have h2 := hs_pos j; linarith
      have hshift_cont : ∀ j, ContinuousOn (fun p : ℝ × ℝ => Y (p.1 - hs j) p.2) sub := by
        intro j
        have hφ : Continuous (fun p : ℝ × ℝ => (p.1 - hs j, p.2)) :=
          (continuous_fst.sub continuous_const).prodMk continuous_snd
        have h := hYc.comp hφ.continuousOn (hshift_map j)
        exact h
      have hxshift_cont : ∀ j n, ContinuousOn (fun p : ℝ × ℝ => X n (p.1 - hs j) p.2) sub := by
        intro j n
        have hφ : Continuous (fun p : ℝ × ℝ => (p.1 - hs j, p.2)) :=
          (continuous_fst.sub continuous_const).prodMk continuous_snd
        have h := (hXc n).comp hφ.continuousOn (hshift_map j)
        exact h
      have hKf_cont : ∀ j, ContinuousOn (Kf j) sub := by
        intro j
        have h1 : ContinuousOn (fun p : ℝ × ℝ => Y p.1 p.2 - Y (p.1 - hs j) p.2) sub :=
          hYc_sub.sub (hshift_cont j)
        have h2 : ContinuousOn (fun p : ℝ × ℝ => (Y p.1 p.2 - Y (p.1 - hs j) p.2) / hs j) sub :=
          h1.div_const (hs j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ =>
            ((Y p.1 p.2 - Y (p.1 - hs j) p.2) / hs j) ^ 2 * (ρ p.1 p.2) ^ 2) sub :=
          (h2.pow 2).mul (hρc_sub.pow 2)
        exact h3
      have hKnf_cont : ∀ j n, ContinuousOn (Knf j n) sub := by
        intro j n
        have h1 : ContinuousOn (fun p : ℝ × ℝ => X n p.1 p.2 - X n (p.1 - hs j) p.2) sub :=
          (hXc_sub n).sub (hxshift_cont j n)
        have h2 : ContinuousOn (fun p : ℝ × ℝ =>
            (X n p.1 p.2 - X n (p.1 - hs j) p.2) / hs j) sub := h1.div_const (hs j)
        have h3 : ContinuousOn (fun p : ℝ × ℝ =>
            ((X n p.1 p.2 - X n (p.1 - hs j) p.2) / hs j) ^ 2 * (ρ p.1 p.2) ^ 2) sub :=
          (h2.pow 2).mul (hρc_sub.pow 2)
        exact h3
      have hKf_meas : ∀ j,
          AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Kf j p)) (volume.restrict sub) := by
        intro j
        refine ((hKf_cont j).aestronglyMeasurable hsub_meas).enorm.congr ?_
        filter_upwards with p
        exact Real.enorm_eq_ofReal (by positivity)
      have hKnf_meas : ∀ j n,
          AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Knf j n p)) (volume.restrict sub) := by
        intro j n
        refine ((hKnf_cont j n).aestronglyMeasurable hsub_meas).enorm.congr ?_
        filter_upwards with p
        exact Real.enorm_eq_ofReal (by positivity)
      have hpoint : ∀ᵐ p ∂(volume.restrict sub), ENNReal.ofReal (ff p) ≤
          Filter.liminf (fun j => ENNReal.ofReal (Kf j p)) Filter.atTop := by
        rw [MeasureTheory.ae_restrict_iff' hsub_meas]
        refine Filter.Eventually.of_forall (fun p hp => ?_)
        by_cases hdiff : DifferentiableAt ℝ (fun z' => Y z' p.2) p.1
        · have hlim : Tendsto (fun j => (Y p.1 p.2 - Y (p.1 - hs j) p.2) / hs j) atTop
              (𝓝 (deriv (fun z' => Y z' p.2) p.1)) :=
            tendsto_backward_diffQuot hdiff hs_tendsto hs_pos
          have hlimK : Tendsto (fun j => Kf j p) atTop (𝓝 (ff p)) := by
            have h3 := (hlim.pow 2).mul_const ((ρ p.1 p.2) ^ 2)
            simpa only [Kf, ff] using h3
          have hlimO := ENNReal.tendsto_ofReal hlimK
          rw [hlimO.liminf_eq]
        · have h0 : deriv (fun z' => Y z' p.2) p.1 = 0 := deriv_zero_of_not_differentiableAt hdiff
          have hff0 : ff p = 0 := by simp only [ff, h0]; ring
          rw [hff0, ENNReal.ofReal_zero]
          exact zero_le
      have hFatou1 : ∫⁻ p in sub, ENNReal.ofReal (ff p) ≤
          Filter.liminf (fun j => ∫⁻ p in sub, ENNReal.ofReal (Kf j p)) Filter.atTop :=
        lintegral_le_liminf_of_eventually_le hKf_meas hpoint
      have hFatou2 : ∀ j, ∫⁻ p in sub, ENNReal.ofReal (Kf j p) ≤
          Filter.liminf (fun n => ∫⁻ p in sub, ENNReal.ofReal (Knf j n p)) Filter.atTop := by
        intro j
        refine lintegral_le_liminf_of_eventually_le (hKnf_meas j) ?_
        rw [MeasureTheory.ae_restrict_iff' hsub_meas]
        refine Filter.Eventually.of_forall (fun p hp => ?_)
        have h1 : Tendsto (fun n => X n p.1 p.2) atTop (𝓝 (Y p.1 p.2)) :=
          hconv p.1 p.2 (hsub_box hp)
        have h2 : Tendsto (fun n => X n (p.1 - hs j) p.2) atTop (𝓝 (Y (p.1 - hs j) p.2)) :=
          hconv (p.1 - hs j) p.2 (hshift_map j hp)
        have hlim : Tendsto (fun n => Knf j n p) atTop (𝓝 (Kf j p)) := by
          have h3 := (((h1.sub h2).div_const (hs j)).pow 2).mul_const ((ρ p.1 p.2) ^ 2)
          simpa only [Knf, Kf] using h3
        have hlimO := ENNReal.tendsto_ofReal hlim
        rw [hlimO.liminf_eq]
      have hSsub : Set.Icc a b ×ˢ Set.Icc c' d' ⊆ box := by
        intro p hp
        exact ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1, le_trans hp.2.2 (le_of_lt hd'd)⟩⟩
      have hbd_jn : ∀ j n, ∫⁻ p in sub, ENNReal.ofReal (Knf j n p) ≤
          ENNReal.ofReal (Cs j) * ENNReal.ofReal M := by
        intro j n
        have hmeasD : AEMeasurable (fun p : ℝ × ℝ =>
            ENNReal.ofReal ((deriv (fun z' => X n z' p.2) p.1) ^ 2 * (ρ p.1 p.2) ^ 2))
            (volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
          have h1 : AEStronglyMeasurable (gn n) (volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
            ((hIntX n).mono_set hSsub).aestronglyMeasurable
          have h2 : AEMeasurable (fun p => ENNReal.ofReal (gn n p))
              (volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
            refine (h1.enorm).congr ?_
            filter_upwards with p
            exact Real.enorm_eq_ofReal (by positivity)
          exact h2
        have hD := diffQuot_backward_lintegral_le (a := a) (b := b) (a' := a') (b' := b')
          (c := c') (d := d') (h := hs j) (C := Cs j) (w := ρ) (u := X n)
          haa' hb'b (hs_pos j) (hs_lt j) (hCs_ge j)
          (fun z hz θ hθ => hρp z hz θ
            ⟨le_trans (le_of_lt hcc') hθ.1, le_trans hθ.2 (le_of_lt hd'd)⟩)
          (hCs_ratio j)
          (fun θ hθ => hslice_sm n θ ⟨lt_of_lt_of_le hcc' hθ.1, lt_of_le_of_lt hθ.2 hd'd⟩)
          (fun θ hθ => hslice_c n θ ⟨le_trans (le_of_lt hcc') hθ.1, le_trans hθ.2 (le_of_lt hd'd)⟩)
          hmeasD
        refine hD.trans ?_
        have hR : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal (gn n p) ≤
            ENNReal.ofReal M := by
          have hInt' : IntegrableOn (gn n) (Set.Icc a b ×ˢ Set.Icc c' d') :=
            (hIntX n).mono_set hSsub
          have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')] gn n :=
            ae_of_all _ (fun p => by positivity)
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt' hnn]
          refine ENNReal.ofReal_le_ofReal ?_
          refine le_trans (MeasureTheory.setIntegral_mono_set (hIntX n)
            (ae_of_all _ (fun p => by positivity)) (Filter.Eventually.of_forall hSsub)) (hbd n)
        exact mul_le_mul' le_rfl hR
      have hA_le_B : ∀ j, ∫⁻ p in sub, ENNReal.ofReal (Kf j p) ≤
          ENNReal.ofReal (Cs j) * ENNReal.ofReal M := fun j =>
        (hFatou2 j).trans (Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall (hbd_jn j)))
      have step1 : Filter.liminf (fun j => ∫⁻ p in sub, ENNReal.ofReal (Kf j p)) Filter.atTop ≤
          Filter.liminf (fun j => ENNReal.ofReal (Cs j) * ENNReal.ofReal M) Filter.atTop := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
        refine iSup_le (fun n => ?_)
        refine le_trans ?_ (le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n),
          ENNReal.ofReal (Cs i) * ENNReal.ofReal M) n)
        refine le_iInf (fun j => ?_)
        refine le_iInf (fun hj => ?_)
        calc (⨅ i, ⨅ (_ : i ≥ n), ∫⁻ p in sub, ENNReal.ofReal (Kf i p))
            ≤ ⨅ (_ : j ≥ n), ∫⁻ p in sub, ENNReal.ofReal (Kf j p) := iInf_le _ j
          _ ≤ ∫⁻ p in sub, ENNReal.ofReal (Kf j p) := iInf_le _ hj
          _ ≤ ENNReal.ofReal (Cs j) * ENNReal.ofReal M := hA_le_B j
      have step2 : Filter.liminf (fun j => ENNReal.ofReal (Cs j) * ENNReal.ofReal M) Filter.atTop
          = ENNReal.ofReal M := by
        have h1 : Tendsto (fun j => Cs j * M) atTop (𝓝 M) := by
          simpa using hCs_tendsto.mul_const M
        have h2 : Tendsto (fun j => ENNReal.ofReal (Cs j * M)) atTop (𝓝 (ENNReal.ofReal M)) :=
          ENNReal.tendsto_ofReal h1
        have h3 : Tendsto (fun j => ENNReal.ofReal (Cs j) * ENNReal.ofReal M) atTop
            (𝓝 (ENNReal.ofReal M)) := by
          refine h2.congr' ?_
          filter_upwards with j
          rw [ENNReal.ofReal_mul (le_of_lt (lt_of_lt_of_le zero_lt_one (hCs_ge j)))]
        rw [h3.liminf_eq]
      exact hFatou1.trans (step1.trans (le_of_eq step2))
    have hli : ∫⁻ p in box, ENNReal.ofReal (ff p) ≤ ENNReal.ofReal M := by
      rw [lintegral_subbox_eq_iSup (a := a) (b := b) (c := c) (d := d) hab hcd hffm]
      refine iSup_le (fun k => ?_)
      refine hkey (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2))
        (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2)) ?_ ?_ ?_ ?_
      · have : 0 < (b - a) / ((k : ℝ) + 2) := by positivity
        linarith
      · have : 0 < (b - a) / ((k : ℝ) + 2) := by positivity
        linarith
      · have : 0 < (d - c) / ((k : ℝ) + 2) := by positivity
        linarith
      · have : 0 < (d - c) / ((k : ℝ) + 2) := by positivity
        linarith
    have hnn : (0 : ℝ) ≤ ∫ p in Set.Icc a b ×ˢ Set.Icc c d, ff p :=
      integral_nonneg (fun p => by positivity)
    have hfin : ENNReal.ofReal (∫ p in Set.Icc a b ×ˢ Set.Icc c d, ff p) ≤ ENNReal.ofReal M := by
      calc ENNReal.ofReal (∫ p in Set.Icc a b ×ˢ Set.Icc c d, ff p)
          = ‖∫ p in Set.Icc a b ×ˢ Set.Icc c d, ff p‖ₑ := (Real.enorm_eq_ofReal hnn).symm
        _ ≤ ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ‖ff p‖ₑ :=
              MeasureTheory.enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal (ff p) :=
              lintegral_congr (fun p => Real.enorm_eq_ofReal (by positivity))
        _ ≤ ENNReal.ofReal M := hli
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp hfin
  · have hnotint : ¬ IntegrableOn ff box := by
      intro hInt
      refine hffm ?_
      refine (hInt.aestronglyMeasurable.enorm).congr ?_
      filter_upwards with p
      exact Real.enorm_eq_ofReal (by positivity)
    rw [MeasureTheory.integral_undef (show ¬ Integrable ff (volume.restrict
      (Set.Icc a b ×ˢ Set.Icc c d)) from hnotint)]
    exact hM

end Work.FTS.StrongEps.LocUnif
