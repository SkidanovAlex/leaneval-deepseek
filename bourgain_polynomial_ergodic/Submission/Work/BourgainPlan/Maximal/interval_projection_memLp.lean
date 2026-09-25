import Mathlib
import Submission.Work.BourgainPlan.Maximal.interval_projection_schwartz_lp
import Submission.Work.Analysis.Fourier.fourier_sub

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology
open Commons.Analysis.CalderonZygmund
open Commons.Analysis.Fourier
open Work.Analysis.Fourier

noncomputable section

/-! ## Density of Schwartz functions in `L¹ ∩ Lᵖ` (a self-contained proof)

Given `g : ℝ → ℂ` with `g ∈ L¹ ∩ Lᵖ`, `1 < p`, we construct a sequence of Schwartz functions
`G n` with `∫ ‖G n - g‖ → 0` and `∫⁻ ‖G n‖^p → ∫⁻ ‖g‖^p`.  The construction truncates `g` to
`[-k,k]`, approximates the truncation in `Lᵖ` by a smooth compactly supported function, and cuts
the result off with a smooth bump so that the difference is supported in a *fixed* compact set
(allowing the `Lᵖ → L¹` Hölder conversion).  The `Lᵖ`-norm convergence is then deduced from
`eLpNorm (G n - g) → 0` via the `Lᵖ` space norm. -/
private lemma lintegral_rpow_enorm_eq_eLpNorm_rpow (p : ℝ) (hp : 0 < p) (u : ℝ → ℂ)
    (hu : AEStronglyMeasurable u volume) :
    (∫⁻ x : ℝ, ‖u x‖ₑ ^ p) = (eLpNorm u (ENNReal.ofReal p) (volume : MeasureTheory.Measure ℝ)) ^ p := by
  have h := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (volume : MeasureTheory.Measure ℝ))
    (f := u) (p := ENNReal.ofReal p) (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal hp.le] at h
  rw [h, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

private lemma trunc_tendsto (q : ℝ) (hq : 0 < q) (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (hfin : (∫⁻ x : ℝ, ‖g x‖ₑ ^ q) ≠ ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x : ℝ,
        ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ q) atTop (nhds 0) := by
  have hmeas : ∀ k : ℕ, AEMeasurable (fun x : ℝ =>
      ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ q) volume := fun k =>
    (((hg.indicator measurableSet_Icc).sub hg).aemeasurable).enorm.pow_const q
  have hbound : ∀ k : ℕ, (fun x : ℝ =>
      ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ q) ≤ᵐ[volume]
      (fun x : ℝ => ‖g x‖ₑ ^ q) := by
    intro k
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-(k:ℝ)) (k:ℝ)
    · rw [Set.indicator_of_mem hx, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hq]
      positivity
    · rw [Set.indicator_of_notMem hx, zero_sub]
      simp
  have hlim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun k : ℕ =>
      ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ q) atTop (nhds (0:ℝ≥0∞)) := by
    filter_upwards with x
    have hev : (fun _ : ℕ => (0:ℝ≥0∞)) =ᶠ[atTop]
        (fun k : ℕ => ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ q) := by
      obtain ⟨K, hK⟩ := exists_nat_ge |x|
      filter_upwards [Filter.eventually_ge_atTop K] with k hk
      have hk' : |x| ≤ (k:ℝ) := by
        have : (K:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        linarith
      have hX : x ∈ Set.Icc (-(k:ℝ)) (k:ℝ) := by
        rw [Set.mem_Icc]; exact ⟨by linarith [neg_abs_le x, hk'], by linarith [le_abs_self x, hk']⟩
      rw [Set.indicator_of_mem hX, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hq]
    exact tendsto_const_nhds.congr' hev
  have H := tendsto_lintegral_of_dominated_convergence' (f := fun _ : ℝ => (0:ℝ≥0∞))
    (fun x : ℝ => ‖g x‖ₑ ^ q) hmeas hbound hfin hlim
  simpa using H

private noncomputable def cutBump (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(k:ℝ) + 1, (k:ℝ) + 2, by positivity, by linarith⟩

private noncomputable def cutFun (k : ℕ) : ℝ → ℂ := fun x => ((cutBump k : ℝ → ℝ) x : ℂ)

private lemma mem_Icc_iff_abs_le (k : ℕ) (x : ℝ) :
    x ∈ Set.Icc (-(k:ℝ)) (k:ℝ) ↔ |x| ≤ (k:ℝ) := by
  rw [Set.mem_Icc, abs_le]

private lemma mem_closedBall_iff_abs_le (r x : ℝ) :
    x ∈ Metric.closedBall (0:ℝ) r ↔ |x| ≤ r := by
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]

private lemma cutFun_one (k : ℕ) {x : ℝ} (hx : x ∈ Metric.closedBall (0:ℝ) ((k:ℝ)+1)) :
    cutFun k x = 1 := by
  have h := (cutBump k).one_of_mem_closedBall hx
  simpa [cutFun] using congrArg (fun t : ℝ => (t : ℂ)) h

private lemma cutFun_norm_le_one (k : ℕ) (x : ℝ) : ‖cutFun k x‖ ≤ 1 := by
  have h1 : (0:ℝ) ≤ (cutBump k : ℝ → ℝ) x := (cutBump k).nonneg
  have h2 : (cutBump k : ℝ → ℝ) x ≤ 1 := (cutBump k).le_one
  rw [cutFun, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

private lemma cutFun_zero (k : ℕ) {x : ℝ} (hx : (k:ℝ)+2 ≤ dist x 0) : cutFun k x = 0 := by
  have h := (cutBump k).zero_of_le_dist hx
  simp [cutFun, h]

private lemma cutFun_contDiff (k : ℕ) :
    ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (cutFun k) := by
  have h := Complex.ofRealCLM.contDiff.comp ((cutBump k).contDiff (n := ⊤))
  have hfun : (Complex.ofRealCLM ∘ (cutBump k : ℝ → ℝ)) = cutFun k := by
    funext x; simp [cutFun]
  rwa [hfun] at h

private lemma cutFun_hasCompactSupport (k : ℕ) : HasCompactSupport (cutFun k) := by
  refine ((cutBump k).hasCompactSupport).mono ?_
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [cutFun, h])

set_option maxHeartbeats 4000000 in
private theorem density_self (p : ℝ) (hp : 1 < p) (g : ℝ → ℂ) (hg : Integrable g)
    (hgp : MemLp g (ENNReal.ofReal p) (volume : MeasureTheory.Measure ℝ)) :
    ∃ G : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n : ℕ => ∫ x : ℝ, ‖(G n : ℝ → ℂ) x - g x‖ ∂(volume : MeasureTheory.Measure ℝ)) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫⁻ x : ℝ, ‖(G n : ℝ → ℂ) x‖ₑ ^ p) atTop
        (nhds (∫⁻ x : ℝ, ‖g x‖ₑ ^ p)) := by
  classical
  have hp0 : 0 < p := by linarith
  have h1mp : (0:ℝ) < 1 - 1/p := by
    have h : 1/p < 1 := (div_lt_one hp0).mpr hp
    linarith
  have hgfin1 : (∫⁻ x : ℝ, ‖g x‖ₑ ^ (1:ℝ)) ≠ ⊤ := by
    have h2 : (∫⁻ x : ℝ, ‖g x‖ₑ ^ (1:ℝ)) = (∫⁻ x : ℝ, ‖g x‖ₑ) := by
      refine lintegral_congr fun x => ?_
      exact ENNReal.rpow_one _
    rw [h2]; exact hg.2.ne
  have hgfinp : (∫⁻ x : ℝ, ‖g x‖ₑ ^ p) ≠ ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := volume)
      (p := ENNReal.ofReal p) (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hgp.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hp0.le] at h
    exact h.ne
  have htrLp : Tendsto (fun k : ℕ => ∫⁻ x : ℝ,
      ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ p) atTop (nhds 0) :=
    trunc_tendsto p hp0 g hg.1 hgfinp
  have htrL1 : Tendsto (fun k : ℕ => ∫⁻ x : ℝ,
      ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ) atTop (nhds 0) := by
    have h := trunc_tendsto 1 (by norm_num) g hg.1 hgfin1
    simpa [ENNReal.rpow_one] using h
  have htrLp' : Tendsto (fun k : ℕ => eLpNorm
      (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
      (ENNReal.ofReal p) volume) atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ => (eLpNorm
        (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
        (ENNReal.ofReal p) volume) ^ p) atTop (nhds 0) := by
      have hrw : ∀ k : ℕ, (∫⁻ x : ℝ,
          ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ₑ ^ p)
          = (eLpNorm (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
            (ENNReal.ofReal p) volume) ^ p := fun k =>
        lintegral_rpow_enorm_eq_eLpNorm_rpow p hp0
          (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
          ((hg.1.indicator measurableSet_Icc).sub hg.1)
      simpa only [hrw] using htrLp
    have key : ∀ k : ℕ, ((eLpNorm (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
        (ENNReal.ofReal p) volume) ^ p) ^ (1/p)
        = eLpNorm (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
            (ENNReal.ofReal p) volume := by
      intro k
      rw [← ENNReal.rpow_mul, mul_one_div, div_self hp0.ne', ENNReal.rpow_one]
    have hcomp := ((ENNReal.continuous_rpow_const (y := 1/p)).tendsto (0:ℝ≥0∞)).comp hpow
    rw [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/p)] at hcomp
    have heq : ((fun a : ℝ≥0∞ => a ^ (1/p)) ∘ fun k : ℕ => (eLpNorm
        (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
        (ENNReal.ofReal p) volume) ^ p)
        = fun k : ℕ => eLpNorm
            (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
            (ENNReal.ofReal p) volume := by
      funext k; exact key k
    rw [heq] at hcomp
    exact hcomp
  let Cv : ℕ → ℝ := fun k => (2 * ((k:ℝ)+2)) ^ (1 - 1/p)
  let δ : ℕ → ℝ := fun k => (1/((k:ℝ)+1)) / (1 + Cv k)
  have hCvnn : ∀ k, 0 ≤ Cv k := fun k => Real.rpow_nonneg (by positivity) _
  have hδpos : ∀ k, 0 < δ k := fun k => by
    have h := hCvnn k
    show (0:ℝ) < (1/((k:ℝ)+1)) / (1 + Cv k)
    exact div_pos (by positivity) (by linarith)
  have hδle : ∀ k, δ k ≤ 1/((k:ℝ)+1) := fun k => by
    have h := hCvnn k
    show (1/((k:ℝ)+1)) / (1 + Cv k) ≤ 1/((k:ℝ)+1)
    have hb : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + Cv k)]
    nlinarith
  have hδCv : ∀ k, δ k * Cv k ≤ 1/((k:ℝ)+1) := fun k => by
    have h := hCvnn k
    show (1/((k:ℝ)+1)) / (1 + Cv k) * Cv k ≤ 1/((k:ℝ)+1)
    have hb : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 1 + Cv k)]
    nlinarith
  have hδtend : Tendsto δ atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun k => le_of_lt (hδpos k)) hδle h1
  have hex : ∀ k : ℕ, ∃ A : ℝ → ℂ, HasCompactSupport A ∧
      ContDiff ℝ (((⊤:ℕ∞)) : WithTop ℕ∞) A ∧
      eLpNorm (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - A x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (δ k) := by
    intro k
    refine MemLp.exist_eLpNorm_sub_le (μ := volume) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
      (ENNReal.one_le_ofReal.mpr hp.le) ?_ (hδpos k)
    refine lt_of_le_of_lt ?_ hgp.eLpNorm_lt_top
    refine eLpNorm_mono (hg.1.indicator measurableSet_Icc) (fun x : ℝ => ?_)
    by_cases hx : x ∈ Set.Icc (-(k:ℝ)) (k:ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp
  choose A hAcs hAcd hAerr using hex
  let Gf : ℕ → ℝ → ℂ := fun k => A k * cutFun k
  have hGf_eq : ∀ k x, Gf k x = A k x * cutFun k x := fun k x => rfl
  have hGcs : ∀ k, HasCompactSupport (Gf k) := fun k => (cutFun_hasCompactSupport k).mul_left
  have hGcd : ∀ k, ContDiff ℝ (((⊤:ℕ∞)) : WithTop ℕ∞) (Gf k) := fun k =>
    ((hAcd k).mul (cutFun_contDiff k))
  let Gs : ℕ → SchwartzMap ℝ ℂ := fun k => (hGcs k).toSchwartzMap (hGcd k)
  have hGs_apply : ∀ k, (Gs k : ℝ → ℂ) = Gf k := fun k => rfl
  have hmk : ∀ k, MemLp (Gf k) (ENNReal.ofReal p) volume := fun k => by
    have h := SchwartzMap.memLp (Gs k) (ENNReal.ofReal p) (volume : MeasureTheory.Measure ℝ)
    rwa [hGs_apply k] at h
  have hdom : ∀ k x, ‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖
      ≤ ‖A k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖ := by
    intro k x
    rw [hGf_eq k x]
    by_cases h1 : |x| ≤ (k:ℝ) + 1
    · have hxb : x ∈ Metric.closedBall (0:ℝ) ((k:ℝ)+1) :=
        (mem_closedBall_iff_abs_le _ _).mpr h1
      rw [cutFun_one k hxb, mul_one]
    · by_cases h2 : |x| ≤ (k:ℝ) + 2
      · have hnotmem : x ∉ Set.Icc (-(k:ℝ)) (k:ℝ) := fun hmem =>
          absurd (mem_Icc_iff_abs_le k x |>.mp hmem) (by linarith)
        rw [Set.indicator_of_notMem hnotmem, sub_zero, sub_zero, norm_mul]
        calc ‖A k x‖ * ‖cutFun k x‖ ≤ ‖A k x‖ * 1 :=
              mul_le_mul_of_nonneg_left (cutFun_norm_le_one k x) (norm_nonneg _)
          _ = ‖A k x‖ := mul_one _
      · have hdist : (k:ℝ) + 2 ≤ dist x 0 := by
          rw [Real.dist_eq, sub_zero]
          exact le_of_lt (not_le.mp h2)
        have hc : cutFun k x = 0 := cutFun_zero k hdist
        have hnotmem : x ∉ Set.Icc (-(k:ℝ)) (k:ℝ) := fun hmem =>
          absurd (mem_Icc_iff_abs_le k x |>.mp hmem) (by linarith)
        rw [hc, mul_zero, Set.indicator_of_notMem hnotmem, sub_zero, sub_zero, norm_zero]
        positivity
  have hGerr : ∀ k, eLpNorm (fun x : ℝ => Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (δ k) := by
    intro k
    refine le_trans (eLpNorm_mono ((hmk k).aestronglyMeasurable.sub
      (hg.1.indicator measurableSet_Icc)) (fun x => (hdom k x).trans ?_)) (hAerr k)
    rw [norm_sub_rev]
  have hind_memLp : ∀ k : ℕ, MemLp ((Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g) (ENNReal.ofReal p) volume := by
    intro k
    refine lt_of_le_of_lt ?_ hgp.eLpNorm_lt_top
    refine eLpNorm_mono (hg.1.indicator measurableSet_Icc) (fun x : ℝ => ?_)
    by_cases hx : x ∈ Set.Icc (-(k:ℝ)) (k:ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp
  have hB : ∀ k, (∫ x : ℝ, ‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖) ≤ δ k * Cv k := by
    intro k
    set K : Set ℝ := Metric.closedBall (0:ℝ) ((k:ℝ)+2) with hK
    set F : ℝ → ℂ := fun x => Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x with hF
    have hFmemLp : MemLp F (ENNReal.ofReal p) volume := (hmk k).sub (hind_memLp k)
    have hsupp : Function.support F ⊆ K := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      have hdist : (k:ℝ) + 2 ≤ dist x 0 := by
        rw [hK, mem_closedBall_iff_abs_le] at hcon
        rw [Real.dist_eq, sub_zero]
        exact le_of_lt (not_le.mp hcon)
      have hc : cutFun k x = 0 := cutFun_zero k hdist
      have hnotmem : x ∉ Set.Icc (-(k:ℝ)) (k:ℝ) := by
        intro hmem
        have := (mem_Icc_iff_abs_le k x).mp hmem
        rw [Real.dist_eq, sub_zero] at hdist
        linarith
      apply hx
      rw [hF]
      simp only [hGf_eq k x, hc, mul_zero, Set.indicator_of_notMem hnotmem, sub_zero]
    have hsupp' : Function.support (fun x => ‖F x‖ₑ) ⊆ K := by
      intro x hx
      rw [Function.mem_support] at hx
      apply hsupp
      rw [Function.mem_support]
      intro h
      exact hx (by rw [h, enorm_zero])
    have hKmeas : MeasurableSet K := measurableSet_closedBall
    have hIntF : Integrable F volume := by
      have h1 : Integrable (Gf k) volume := by
        have h := SchwartzMap.integrable (Gs k) (μ := volume)
        rwa [hGs_apply k] at h
      have h2 : Integrable ((Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g) volume :=
        (integrable_indicator_iff measurableSet_Icc).mpr hg.integrableOn
      exact h1.sub h2
    have hleft : eLpNorm F 1 ((volume : MeasureTheory.Measure ℝ).restrict K) = ∫⁻ x : ℝ, ‖F x‖ₑ := by
      rw [eLpNorm_one_eq_lintegral_enorm
        (hIntF.aestronglyMeasurable.mono_measure Measure.restrict_le_self),
        ← lintegral_indicator hKmeas]
      refine lintegral_congr fun x => ?_
      rw [Set.indicator_apply]
      by_cases hx : x ∈ K
      · rw [if_pos hx]
      · rw [if_neg hx]
        have : ‖F x‖ₑ = 0 := by
          have h2 : x ∉ Function.support (fun x => ‖F x‖ₑ) := fun h => hx (hsupp' h)
          simpa [Function.mem_support] using h2
        rw [this]
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume : MeasureTheory.Measure ℝ).restrict K) (f := F)
      (p := (1:ℝ≥0∞)) (q := ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr hp.le)
      (hIntF.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    rw [hleft, Measure.restrict_apply_univ, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le,
      div_one] at hb
    have hb2 : ∫⁻ x : ℝ, ‖F x‖ₑ ≤ eLpNorm F (ENNReal.ofReal p) volume *
        (volume K) ^ (1 - 1/p) :=
      le_trans hb (mul_le_mul_of_nonneg_right
        (eLpNorm_mono_measure F Measure.restrict_le_self) bot_le)
    have hreal : ∫ x : ℝ, ‖F x‖ = (∫⁻ x : ℝ, ‖F x‖ₑ).toReal :=
      integral_norm_eq_lintegral_enorm hIntF.aestronglyMeasurable
    rw [hreal]
    have hpowfin : (volume K) ^ (1 - 1/p) ≠ ⊤ := by
      rw [hK, Real.volume_closedBall,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) h1mp.le]
      exact ENNReal.ofReal_ne_top
    have hfin : (eLpNorm F (ENNReal.ofReal p) volume * (volume K) ^ (1 - 1/p)) ≠ ⊤ :=
      ENNReal.mul_ne_top hFmemLp.eLpNorm_ne_top hpowfin
    refine le_trans (ENNReal.toReal_le_toReal hIntF.2.ne hfin |>.mpr hb2) ?_
    have hpowval : (volume K ^ (1 - 1/p)).toReal = Cv k := by
      rw [hK, Real.volume_closedBall, ENNReal.ofReal_rpow_of_nonneg (by positivity) h1mp.le,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]
    rw [ENNReal.toReal_mul, hpowval]
    exact mul_le_mul_of_nonneg_right
      (by
        have h := (ENNReal.toReal_le_toReal hFmemLp.eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
          (hGerr k)
        rwa [ENNReal.toReal_ofReal (hδpos k).le] at h)
      (hCvnn k)
  refine ⟨Gs, ?_, ?_⟩
  · have hind_int : ∀ k, Integrable (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x) volume :=
      fun k => (integrable_indicator_iff measurableSet_Icc).mpr hg.integrableOn
    have hGf_int : ∀ k : ℕ, Integrable (Gf k) volume := fun k => by
      have h := SchwartzMap.integrable (Gs k) (μ := volume); rwa [hGs_apply k] at h
    have hupper : ∀ k, (∫ x : ℝ, ‖Gf k x - g x‖) ≤ 1/((k:ℝ)+1) +
        (∫ x : ℝ, ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) := by
      intro k
      have hInt1 : Integrable (fun x : ℝ => ‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖) volume :=
        ((hGf_int k).sub (hind_int k)).norm
      have hInt2 : Integrable (fun x : ℝ => ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) volume :=
        ((hind_int k).sub hg).norm
      have hpt : ∀ x, ‖Gf k x - g x‖ ≤ ‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖
          + ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖ := by
        intro x
        have h := norm_add_le (Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x)
          ((Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
        simpa using h
      calc (∫ x : ℝ, ‖Gf k x - g x‖)
          ≤ ∫ x : ℝ, (‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖
              + ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) :=
            integral_mono ((hGf_int k).sub hg).norm (hInt1.add hInt2) hpt
        _ = (∫ x : ℝ, ‖Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x‖)
              + (∫ x : ℝ, ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) :=
            integral_add hInt1 hInt2
        _ ≤ 1/((k:ℝ)+1) + (∫ x : ℝ, ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) :=
            add_le_add_left ((hB k).trans (hδCv k)) _
    have hconv : Tendsto (fun k : ℕ => 1/((k:ℝ)+1) +
        (∫ x : ℝ, ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖)) atTop (nhds 0) := by
      have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun k : ℕ => ∫ x : ℝ,
          ‖(Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x‖) atTop (nhds 0) := by
        have h := (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).comp htrL1
        simp only [ENNReal.toReal_zero, Function.comp_apply] at h
        refine h.congr' ?_
        filter_upwards with k
        exact (integral_norm_eq_lintegral_enorm
          ((hg.1.indicator measurableSet_Icc).sub hg.1)).symm
      simpa using h1.add h2
    have := squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _)) hupper hconv
    simpa only [hGs_apply] using this
  · letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    have hsubLp : Tendsto (fun k : ℕ => eLpNorm (fun x : ℝ => Gf k x - g x)
        (ENNReal.ofReal p) volume) atTop (nhds 0) := by
      have hupper : ∀ k, eLpNorm (fun x : ℝ => Gf k x - g x) (ENNReal.ofReal p) volume
          ≤ ENNReal.ofReal (δ k) + eLpNorm
              (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
              (ENNReal.ofReal p) volume := by
        intro k
        have hsm1 : AEStronglyMeasurable
            (fun x : ℝ => Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x) volume :=
          (hmk k).aestronglyMeasurable.sub (hg.1.indicator measurableSet_Icc)
        have hsm2 : AEStronglyMeasurable
            (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x) volume :=
          (hg.1.indicator measurableSet_Icc).sub hg.1
        have hsplit : (fun x : ℝ => Gf k x - g x) = fun x : ℝ =>
            (Gf k x - (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x)
              + ((Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x) := by
          funext x; ring
        rw [hsplit]
        exact le_trans (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp.le))
          (add_le_add_left (hGerr k) _)
      have hconv : Tendsto (fun k : ℕ => ENNReal.ofReal (δ k)
          + eLpNorm (fun x : ℝ => (Set.Icc (-(k:ℝ)) (k:ℝ)).indicator g x - g x)
              (ENNReal.ofReal p) volume) atTop (nhds 0) := by
        have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal (δ k)) atTop (nhds 0) := by
          have h := (ENNReal.continuous_ofReal.tendsto 0).comp hδtend
          have hfun : (ENNReal.ofReal ∘ δ) = fun k : ℕ => ENNReal.ofReal (δ k) := rfl
          rw [hfun] at h
          simpa using h
        simpa using h1.add htrLp'
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
        (fun k => bot_le) hupper
    have hLptend : Tendsto (fun k : ℕ => (hmk k).toLp (Gf k)) atTop (nhds (hgp.toLp g)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hdeq : ∀ k : ℕ, dist ((hmk k).toLp (Gf k)) (hgp.toLp g)
          = (eLpNorm (fun x : ℝ => Gf k x - g x) (ENNReal.ofReal p) volume).toReal := by
        intro k
        rw [Lp.dist_def]
        congr 1
        apply eLpNorm_congr_ae
        filter_upwards [(hmk k).coeFn_toLp, hgp.coeFn_toLp] with x h1 h2
        simp only [Pi.sub_apply, h1, h2]
      simp only [hdeq]
      have h := (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).comp hsubLp
      have hfun : (ENNReal.toReal ∘ fun k : ℕ => eLpNorm (fun x : ℝ => Gf k x - g x)
          (ENNReal.ofReal p) volume) = fun k : ℕ => (eLpNorm (fun x : ℝ => Gf k x - g x)
          (ENNReal.ofReal p) volume).toReal := rfl
      rw [hfun] at h
      simpa using h
    have hnorm := hLptend.enorm
    have hgoal : Tendsto (fun k : ℕ => eLpNorm (Gf k) (ENNReal.ofReal p) volume) atTop
        (nhds (eLpNorm g (ENNReal.ofReal p) volume)) := by
      simpa only [Lp.enorm_toLp] using hnorm
    have h2 : Tendsto (fun k : ℕ => (eLpNorm (Gf k) (ENNReal.ofReal p) volume) ^ p) atTop
        (nhds ((eLpNorm g (ENNReal.ofReal p) volume) ^ p)) := by
      have h := ((ENNReal.continuous_rpow_const (y := p)).tendsto
        (eLpNorm g (ENNReal.ofReal p) volume)).comp hgoal
      have hfun : ((fun a : ℝ≥0∞ => a ^ p) ∘ fun k : ℕ =>
          eLpNorm (Gf k) (ENNReal.ofReal p) volume) = fun k : ℕ =>
          (eLpNorm (Gf k) (ENNReal.ofReal p) volume) ^ p := rfl
      rwa [hfun] at h
    have hrwG : ∀ k : ℕ, (∫⁻ x : ℝ, ‖Gf k x‖ₑ ^ p)
        = (eLpNorm (Gf k) (ENNReal.ofReal p) volume) ^ p := fun k =>
      lintegral_rpow_enorm_eq_eLpNorm_rpow p hp0 (Gf k) (hmk k).aestronglyMeasurable
    have hrwg : (∫⁻ x : ℝ, ‖g x‖ₑ ^ p) = (eLpNorm g (ENNReal.ofReal p) volume) ^ p :=
      lintegral_rpow_enorm_eq_eLpNorm_rpow p hp0 g hg.1
    simpa only [hGs_apply, hrwG, hrwg] using h2


theorem interval_projection_memLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℂ),
      MeasureTheory.Integrable f →
      MeasureTheory.MemLp f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
              * FourierTransform.fourier f ξ) x)) p)
        ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (fun x : ℝ => ENNReal.rpow (enorm (f x)) p) := by
  obtain ⟨C, hCpos, hC⟩ := interval_projection_schwartz_lp p hp
  refine ⟨C, hCpos, fun a b hab f hf hfp => ?_⟩
  obtain ⟨G, hG1, hG3⟩ := density_self p hp f hf hfp
  have hIoo_ne_top : (volume : MeasureTheory.Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  -- the interval-indicator is integrable
  have hIint : Integrable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)) volume := by
    have h : (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0))
        = (Set.Ioo a b).indicator (fun _ => (1:ℂ)) := by
      funext ξ; rw [Set.indicator_apply]
    rw [h]
    exact (integrable_indicator_iff measurableSet_Ioo).mpr
      (integrableOn_const hIoo_ne_top (by simp))
  -- integrability of the multiplier function for a Schwartz map
  have hmulint : ∀ n : ℕ, Integrable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
      * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) volume := by
    intro n
    have h := hIint.bdd_mul (c := ∫ y : ℝ, ‖(G n : ℝ → ℂ) y‖)
      ((continuous_fourier_of_integrable (SchwartzMap.integrable (G n))).aestronglyMeasurable)
      (Eventually.of_forall (fun ξ => Commons.Analysis.CalderonZygmund.norm_fourier_le _ ξ))
    simpa [mul_comm] using h
  -- integrability of the multiplier function for f
  have hmulintf : Integrable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
      * FourierTransform.fourier f ξ) volume := by
    have h := hIint.bdd_mul (c := ∫ y : ℝ, ‖f y‖)
      ((continuous_fourier_of_integrable hf).aestronglyMeasurable)
      (Eventually.of_forall (fun ξ => Commons.Analysis.CalderonZygmund.norm_fourier_le f ξ))
    simpa [mul_comm] using h
  -- Step 1: the Schwartz bound for each approximant
  have hbound : ∀ n : ℕ,
      ∫⁻ x : ℝ, ENNReal.rpow (enorm (FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) x)) p
      ≤ ENNReal.ofReal (C^p) *
        ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p :=
    fun n => hC a b hab (G n)
  -- Step 2: pointwise convergence
  have hIndnorm : ∀ ξ : ℝ, ‖(if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)‖
      = (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ := by
    intro ξ
    have h1 : (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
        = (Set.Ioo a b).indicator (fun _ => (1:ℂ)) ξ := by
      rw [Set.indicator_apply]
    rw [h1, norm_indicator_eq_indicator_norm]
    congr 1
    funext a
    simp
  have hbound_four : ∀ (n : ℕ) (ξ : ℝ), ‖FourierTransform.fourier ((G n : ℝ → ℂ)) ξ‖
      ≤ (∫ y : ℝ, ‖f y‖) + (∫ y : ℝ, ‖(G n : ℝ → ℂ) y - f y‖) := by
    intro n ξ
    have h1 : ‖FourierTransform.fourier ((G n : ℝ → ℂ)) ξ‖ ≤ ∫ y : ℝ, ‖(G n : ℝ → ℂ) y‖ :=
      Commons.Analysis.CalderonZygmund.norm_fourier_le _ ξ
    have hpt : ∀ y : ℝ, ‖(G n : ℝ → ℂ) y‖ ≤ ‖(G n : ℝ → ℂ) y - f y‖ + ‖f y‖ := by
      intro y
      have := norm_add_le ((G n : ℝ → ℂ) y - f y) (f y)
      simpa using this
    have hint1 : Integrable (fun y : ℝ => ‖(G n : ℝ → ℂ) y‖) volume :=
      (SchwartzMap.integrable (G n)).norm
    have hint2 : Integrable (fun y : ℝ => ‖(G n : ℝ → ℂ) y - f y‖ + ‖f y‖) volume :=
      (((SchwartzMap.integrable (G n)).sub hf).norm).add hf.norm
    have h2 : (∫ y : ℝ, ‖(G n : ℝ → ℂ) y‖) ≤ ∫ y : ℝ, (‖(G n : ℝ → ℂ) y - f y‖ + ‖f y‖) :=
      integral_mono hint1 hint2 hpt
    have h2' : (∫ y : ℝ, (‖(G n : ℝ → ℂ) y - f y‖ + ‖f y‖))
        = (∫ y : ℝ, ‖(G n : ℝ → ℂ) y - f y‖) + (∫ y : ℝ, ‖f y‖) := by
      have := integral_add (f := fun y : ℝ => ‖(G n : ℝ → ℂ) y - f y‖)
        (g := fun y : ℝ => ‖f y‖) (((SchwartzMap.integrable (G n)).sub hf).norm) hf.norm
      simpa using this
    calc ‖FourierTransform.fourier ((G n : ℝ → ℂ)) ξ‖ ≤ ∫ y : ℝ, ‖(G n : ℝ → ℂ) y‖ := h1
      _ ≤ ∫ y : ℝ, (‖(G n : ℝ → ℂ) y - f y‖ + ‖f y‖) := h2
      _ = (∫ y : ℝ, ‖(G n : ℝ → ℂ) y - f y‖) + (∫ y : ℝ, ‖f y‖) := h2'
      _ = (∫ y : ℝ, ‖f y‖) + (∫ y : ℝ, ‖(G n : ℝ → ℂ) y - f y‖) := by ring
  have hpoint : ∀ x : ℝ, Tendsto
      (fun n : ℕ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) x)
      atTop (nhds (FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier f ξ) x)) := by
    intro x
    obtain ⟨M, hM⟩ := hG1.bddAbove_range
    have hMnn : ∀ n : ℕ, (∫ y : ℝ, ‖(G n : ℝ → ℂ) y - f y‖) ≤ M := fun n => hM ⟨n, rfl⟩
    have hfour : ∀ ξ : ℝ, Tendsto (fun n : ℕ => FourierTransform.fourier ((G n : ℝ → ℂ)) ξ)
        atTop (nhds (FourierTransform.fourier f ξ)) := by
      intro ξ
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) ?_ hG1)
      intro n
      rw [← fourier_sub_of_integrable ((G n : ℝ → ℂ)) f (SchwartzMap.integrable (G n)) hf ξ]
      exact Commons.Analysis.CalderonZygmund.norm_fourier_le ((G n : ℝ → ℂ) - f) ξ
    have hbf : ∀ (n : ℕ) (ξ : ℝ), ‖FourierTransform.fourier ((G n : ℝ → ℂ)) ξ‖ ≤ (∫ y : ℝ, ‖f y‖) + M := by
      intro n ξ
      exact (hbound_four n ξ).trans (add_le_add_right (hMnn n) (∫ y : ℝ, ‖f y‖))
    have hDint : Integrable (fun ξ : ℝ => ((∫ y : ℝ, ‖f y‖) + M) *
        (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ) volume :=
      ((integrable_indicator_iff measurableSet_Ioo).mpr
        (integrableOn_const hIoo_ne_top (by simp))).const_mul _
    have hDCT : Tendsto (fun n : ℕ => ∫ ξ : ℝ, czE x ξ • ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
        * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ)) atTop
        (nhds (∫ ξ : ℝ, czE x ξ • ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
        * FourierTransform.fourier f ξ))) := by
      refine tendsto_integral_of_dominated_convergence
        (fun ξ : ℝ => ((∫ y : ℝ, ‖f y‖) + M) * (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ)
        ?_ hDint ?_ ?_
      · intro n
        have hInd : Measurable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)) :=
          Measurable.ite measurableSet_Ioo measurable_const measurable_const
        have hfour_meas : Measurable
            (fun ξ : ℝ => FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) :=
          (continuous_fourier_of_integrable (SchwartzMap.integrable (G n))).measurable
        exact ((continuous_czE x).measurable.mul (hInd.mul hfour_meas)).aestronglyMeasurable
      · intro n
        filter_upwards with ξ
        calc ‖czE x ξ • ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
              * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ)‖
            = (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ
                * ‖FourierTransform.fourier ((G n : ℝ → ℂ)) ξ‖ := by
                rw [norm_smul, norm_czE, one_mul, norm_mul, hIndnorm ξ]
          _ ≤ (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ * ((∫ y : ℝ, ‖f y‖) + M) := by
              refine mul_le_mul_of_nonneg_left (hbf n ξ) ?_
              rw [Set.indicator_apply]; split <;> norm_num
          _ = ((∫ y : ℝ, ‖f y‖) + M) * (Set.Ioo a b).indicator (fun _ => (1:ℝ)) ξ := by ring
      · filter_upwards with ξ
        exact ((hfour ξ).const_mul ((if ξ ∈ Set.Ioo a b then (1:ℂ) else 0))).const_smul (czE x ξ)
    simpa only [fourierInv_czE] using hDCT
  -- Step 3: Fatou
  have hmeas_n : ∀ n : ℕ, AEMeasurable (fun x : ℝ => ENNReal.rpow
      (enorm (FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
          * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) x)) p) volume := by
    intro n
    exact ((fourierInv_continuous_of_integrable (hmulint n)).aestronglyMeasurable).enorm.pow_const p
  calc ∫⁻ x : ℝ, ENNReal.rpow (enorm (FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
            * FourierTransform.fourier f ξ) x)) p
      = ∫⁻ x : ℝ, liminf (fun n : ℕ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
            * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) x)) p) atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards with x
        exact (((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp (hpoint x).enorm).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ x : ℝ, ENNReal.rpow (enorm (FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
            * FourierTransform.fourier ((G n : ℝ → ℂ)) ξ) x)) p) atTop :=
        lintegral_liminf_le' hmeas_n
    _ ≤ liminf (fun n : ℕ => ENNReal.ofReal (C^p) *
          ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal (C^p) * liminf (fun n : ℕ =>
          ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p) atTop :=
        ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (C^p) * ∫⁻ x : ℝ, ENNReal.rpow (enorm (f x)) p := by
        simp only [ENNReal.rpow_eq_pow]
        rw [hG3.liminf_eq]


end

end Work.BourgainPlan.Maximal
