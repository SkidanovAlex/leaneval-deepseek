import Mathlib
import Submission.Work.KMTAreas.A7.IwKernelEqFourier
import Submission.Work.KMTAreas.schwartz_decay_bound
import Submission.Work.KMTAreas.schwartz_shift_summable

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators

namespace Work.KMTAreas.A4

/-- Translates of a continuous function with power decay have summable sup-norms on any compact
set.  This is the Schwartz-decay substitute for `Work.KMTContract.summableShiftRestrict`: for
Schwartz `f` (indeed for any `f` decaying like `|·|⁻²`) the family
`n ↦ ‖(f (· + n))|_{K}‖` is summable over `ℤ`. -/
lemma summable_translate_restrict {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C) {R : ℝ}
    (hR : 1 ≤ R) (hdec : ∀ y : ℝ, R ≤ |y| → ‖f y‖ ≤ C / |y| ^ 2)
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun n : ℤ => ‖((⟨f, hf⟩ : ContinuousMap ℝ ℂ).comp
      (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  -- A nonnegative bound `M` for the compact set `K`.
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ (K : Set ℝ), |y| ≤ M := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp K.isCompact.isBounded
    refine ⟨max r 0, le_max_right _ _, fun y hy => ?_⟩
    have h1 : |y| ≤ r := by
      have h := hr hy
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    exact le_trans h1 (le_max_left _ _)
  -- The comparison series `∑ 1/|n|²` (Kronecker's series).
  have hser0 : Summable (fun n : ℤ => 1 / |(n : ℝ)| ^ (2 : ℝ)) := by
    have h := (Real.summable_one_div_int_add_rpow (0 : ℝ) (2 : ℝ)).mpr (by norm_num : (1 : ℝ) < 2)
    simpa using h
  have hser : Summable (fun n : ℤ => (4 * C) * (1 / |(n : ℝ)| ^ (2 : ℝ))) :=
    hser0.mul_left (4 * C)
  -- The explicit bound, valid as soon as `2 * (M + R) ≤ |n|`.
  have hbound : ∀ n : ℤ, 2 * (M + R) ≤ |(n : ℝ)| →
      ‖((⟨f, hf⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖
        ≤ (4 * C) * (1 / |(n : ℝ)| ^ (2 : ℝ)) := by
    intro n hn
    have hnpos : 0 < |(n : ℝ)| := by linarith
    have hpow : |(n : ℝ)| ^ (2 : ℝ) = |(n : ℝ)| ^ 2 := by
      have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h2, Real.rpow_natCast]
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro y
    show ‖f ((y : ℝ) + (n : ℝ))‖ ≤ (4 * C) * (1 / |(n : ℝ)| ^ (2 : ℝ))
    have hy : |(y : ℝ)| ≤ M := hM y y.2
    have hyn : |(n : ℝ)| - M ≤ |(y : ℝ) + (n : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub (n : ℝ) (-(y : ℝ))
      rw [abs_neg, sub_neg_eq_add, add_comm (n : ℝ) (y : ℝ)] at h
      linarith [le_abs_self (|(n : ℝ)| - |(y : ℝ)|), h]
    have hlev : R ≤ |(y : ℝ) + (n : ℝ)| := by linarith
    have hdec' : ‖f ((y : ℝ) + (n : ℝ))‖ ≤ C / |(y : ℝ) + (n : ℝ)| ^ 2 := hdec _ hlev
    have hhalf : |(n : ℝ)| / 2 ≤ |(y : ℝ) + (n : ℝ)| := by linarith
    have hstep : C / |(y : ℝ) + (n : ℝ)| ^ 2 ≤ C / (|(n : ℝ)| / 2) ^ 2 := by
      refine div_le_div_of_nonneg_left hC (by positivity) ?_
      nlinarith [abs_nonneg ((y : ℝ) + (n : ℝ)), abs_nonneg ((n : ℝ))]
    have hfin : C / (|(n : ℝ)| / 2) ^ 2 = (4 * C) * (1 / |(n : ℝ)| ^ (2 : ℝ)) := by
      rw [hpow]
      have hnn : (|(n : ℝ)| : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
      ring
    linarith [hdec', hstep, hfin]
  refine Summable.of_norm_bounded_eventually hser ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (-(⌈2 * (M + R)⌉)) ⌈2 * (M + R)⌉).subset ?_
  intro n hn
  have hn' : ¬ (‖((⟨f, hf⟩ : ContinuousMap ℝ ℂ).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖ ≤ (4 * C) * (1 / |(n : ℝ)| ^ (2 : ℝ))) :=
    fun h => hn (by simpa using h)
  rw [Set.mem_Icc]
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  refine hn' (hbound n ?_)
  have hceil : 2 * (M + R) ≤ (((⌈2 * (M + R)⌉ : ℤ) : ℝ)) := Int.le_ceil _
  rcases hc with hc | hc
  · have h1 : ((n : ℤ) : ℝ) < -(((⌈2 * (M + R)⌉ : ℤ) : ℝ)) := by exact_mod_cast hc
    have h2 : ((n : ℤ) : ℝ) < 0 := by linarith
    rw [abs_of_neg h2]
    linarith
  · have h1 : (((⌈2 * (M + R)⌉ : ℤ) : ℝ)) < ((n : ℤ) : ℝ) := by exact_mod_cast hc
    have h2 : 0 ≤ ((n : ℤ) : ℝ) := by linarith
    rw [abs_of_nonneg h2]
    linarith


theorem offKernelId (ρ : ℝ) (l : ℕ) (Φ : SchwartzMap ℝ ℂ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))) j
      = FourierTransform.fourier (fun y : ℝ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
            Φ (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) (j : ℝ) := by
  set F : ℝ → ℂ := (Φ : ℝ → ℂ) with hF
  have hFcont : Continuous F := by rw [hF]; exact Φ.continuous
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set a : Work.Analysis.IonescuWainger.Circle → ℝ :=
    fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val with ha
  have ha_coe : ∀ α : Work.Analysis.IonescuWainger.Circle,
      ((a α : ℝ) : Work.Analysis.IonescuWainger.Circle) = α := by
    intro α; rw [ha]; exact AddCircle.coe_equivIco
  have ha_mem : ∀ α : Work.Analysis.IonescuWainger.Circle, a α ∈ Set.Ico (0 : ℝ) 1 := by
    intro α; rw [ha]; simpa using (AddCircle.equivIco (1 : ℝ) 0 α).2
  obtain ⟨C, hC0, hCdec⟩ := Work.KMTAreas.schwartz_decay_bound Φ
  set G : ℝ → ℂ := fun y => ∑ α ∈ A, F (y - a α) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact continuous_finsetSum _ (fun α _ => hFcont.comp (continuous_id.sub continuous_const))
  -- Decay of `G` (a finite sum of shifted Schwartz functions).
  have hGdec : ∀ y : ℝ, 4 ≤ |y| → ‖G y‖ ≤ ((A.card : ℝ) * (4 * C)) / |y| ^ 2 := by
    intro y hy
    have hypos : 0 < |y| := by linarith
    have hterm : ∀ α ∈ A, ‖F (y - a α)‖ ≤ (4 * C) / |y| ^ 2 := by
      intro α _
      obtain ⟨h1, h2⟩ := ha_mem α
      have habs : |a α| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hge : |y| - |a α| ≤ |y - a α| := by
        have h := abs_sub_abs_le_abs_sub y (a α)
        linarith [le_abs_self (|y| - |a α|)]
      have hhalf : |y| / 2 ≤ |y - a α| := by linarith
      have hlt : C / (1 + |y - a α|) ^ 2 ≤ C / |y - a α| ^ 2 := by
        refine div_le_div_of_nonneg_left hC0
          (by nlinarith [abs_nonneg (y - a α), hhalf, hy]) ?_
        nlinarith [abs_nonneg (y - a α)]
      have hstep : C / |y - a α| ^ 2 ≤ (4 * C) / |y| ^ 2 := by
        have h1' : C / |y - a α| ^ 2 ≤ C / (|y| / 2) ^ 2 :=
          div_le_div_of_nonneg_left hC0 (by positivity)
            (by nlinarith [abs_nonneg y, abs_nonneg (y - a α)])
        have h2' : C / (|y| / 2) ^ 2 = (4 * C) / |y| ^ 2 := by
          have hyne : (|y| : ℝ) ≠ 0 := ne_of_gt hypos
          field_simp
          ring
        linarith
      linarith [hCdec (y - a α), hlt, hstep]
    calc ‖G y‖ = ‖∑ α ∈ A, F (y - a α)‖ := by simp only [hG]
      _ ≤ ∑ α ∈ A, ‖F (y - a α)‖ := norm_sum_le A _
      _ ≤ ∑ _α ∈ A, (4 * C) / |y| ^ 2 := Finset.sum_le_sum hterm
      _ = ((A.card : ℝ) * (4 * C)) / |y| ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  -- Local uniform summability of the translates of `G`, and hence the Poisson summation data.
  have hGsumm : ∀ K : TopologicalSpace.Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ :=
    fun K => summable_translate_restrict hGcont (C := (A.card : ℝ) * (4 * C)) (by
        have h4 : (0 : ℝ) ≤ 4 * C := by linarith
        positivity) (R := 4) (by norm_num) hGdec K
  have hper : Function.Periodic (⇑(∑' n : ℤ,
      (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n • (1 : ℝ))))) 1 :=
    (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).periodic_tsum_comp_add_zsmul 1
  have hsum : Summable (fun n : ℤ =>
      (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp (ContinuousMap.addRight (n • (1 : ℝ)))) :=
    ContinuousMap.summable_of_locally_summable_norm (fun K => by
      simpa [Int.smul_one_eq_cast] using hGsumm K)
  -- The symbol is the periodisation of `G`.
  have hSymb : Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize F) = Function.Periodic.lift hper := by
    funext ξ
    set u : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hudef
    have huξ : ((u : ℝ) : Work.Analysis.IonescuWainger.Circle) = ξ := by
      rw [hudef]; exact AddCircle.coe_equivIco
    have hLHS : Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize F) ξ
        = ∑ α ∈ A, ∑' n : ℤ, F (u - a α + n) := by
      simp only [Work.Analysis.IonescuWainger.iwSymbolSet]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      have hcoe : (((u - a α) : ℝ) : Work.Analysis.IonescuWainger.Circle)
          = ((u : ℝ) : Work.Analysis.IonescuWainger.Circle)
            - ((a α : ℝ) : Work.Analysis.IonescuWainger.Circle) :=
        AddCircle.coe_sub (1 : ℝ) u (a α)
      have harg : ξ - α = (((u - a α) : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
        conv_lhs => rw [huξ.symm, (ha_coe α).symm, ← hcoe]
      rw [harg, Work.KMTContract.periodizeCoeEqTsum]
    have hRHS : Function.Periodic.lift hper ξ = ∑' n : ℤ, ∑ α ∈ A, F (u + n - a α) := by
      rw [← huξ, Function.Periodic.lift_coe]
      rw [← ContinuousMap.tsum_apply hsum u]
      refine tsum_congr (fun n => ?_)
      have h1 : ((⟨G, hGcont⟩ : ContinuousMap ℝ ℂ).comp
            (ContinuousMap.addRight (n • (1 : ℝ)))) u = G (u + (n : ℝ)) := by
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, Int.smul_one_eq_cast]
        rfl
      rw [h1, hG]
    rw [hLHS, hRHS]
    have hsummα : ∀ α ∈ A, Summable (fun n : ℤ => F (u - a α + (n : ℝ))) := by
      intro α _
      exact Summable.of_norm (Work.KMTAreas.schwartz_shift_summable Φ (u - a α))
    have hswap : (∑' n : ℤ, ∑ α ∈ A, F (u + (n : ℝ) - a α))
        = ∑ α ∈ A, ∑' n : ℤ, F (u - a α + (n : ℝ)) := by
      rw [← Summable.tsum_finsetSum (f := fun α (n : ℤ) => F (u - a α + (n : ℝ))) hsummα]
      refine tsum_congr (fun n => Finset.sum_congr rfl (fun α _ => ?_))
      congr 1
      ring
    exact hswap.symm
  rw [Work.Analysis.IWMultiplier.iwKernel, hSymb]
  exact Real.fourierCoeff_tsum_comp_add (f := (⟨G, hGcont⟩ : ContinuousMap ℝ ℂ))
    (fun K => hGsumm K) j

end Work.KMTAreas.A4
