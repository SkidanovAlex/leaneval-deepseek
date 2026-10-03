import Mathlib
import Submission.Work.KMTAreas.A7Hi.residueLp_fiberOpP_le_of_range
import Submission.Work.KMTAreas.A7Hi.FiberVarSamplingGLarge
import Submission.Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass
import Submission.Work.KMTAreas.A7Rescue.fiberVarSamplingGRepLargeBdd
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Rescue

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

noncomputable section

/-- Pointwise value ≤ `ℓᵖ`-norm, for `ℝ≥0∞`-valued functions on `ℤ` with the counting measure. -/
lemma apply_le_eLpNorm {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (W : ℤ → ENNReal) (x : ℤ) :
    W x ≤ MeasureTheory.eLpNorm W p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  have hpt' : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpt⟩
  have h1 : ‖W x‖ₑ ^ p.toReal ≤ ∫⁻ y : ℤ, ‖W y‖ₑ ^ p.toReal ∂Measure.count := by
    rw [MeasureTheory.lintegral_count]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (f := fun y : ℤ => ‖W y‖ₑ ^ p.toReal) x)
    simp
  have h2 : (‖W x‖ₑ ^ p.toReal) ^ (1 / p.toReal) ≤
      (∫⁻ y : ℤ, ‖W y‖ₑ ^ p.toReal ∂Measure.count) ^ (1 / p.toReal) :=
    ENNReal.rpow_le_rpow h1 (by positivity)
  rw [show (‖W x‖ₑ ^ p.toReal) ^ (1 / p.toReal) = ‖W x‖ₑ from ?_] at h2
  · simpa using h2
  · rw [← ENNReal.rpow_mul, show p.toReal * (1 / p.toReal) = 1 by field_simp, ENNReal.rpow_one]

/-- **A bound uniform in the residues propagates to the `residueLp` average.** -/
theorem eLpNorm_residueLp_le_of_forall_le (p : ℝ) (hp : 0 < p) (q : ℕ) (K : ENNReal)
    (F : ℤ → ℕ → ENNReal)
    (h : ∀ n₀ : ℕ, n₀ < q →
      eLpNorm (fun y : ℤ => F y n₀) (ENNReal.ofReal p) Measure.count ≤ K) :
    eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q F x) (ENNReal.ofReal p)
        Measure.count ≤ K := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have hzero : (fun x : ℤ => Work.KMTAreas.A7.residueLp p 0 F x) = fun _ : ℤ => (0 : ENNReal) := by
      funext x
      simp only [Work.KMTAreas.A7.residueLp, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact ENNReal.zero_rpow_of_pos (by positivity)
    rw [hzero]
    simp
  · have hqE : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
    have hqT : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hqinv : ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ :=
      ENNReal.rpow_neg_one (q : ENNReal)
    rw [Work.KMTAreas.A7Hi.eLpNormResidueLpEq p hp q F]
    have hsum_le : (∑ n₀ ∈ Finset.range q,
          (eLpNorm (fun y : ℤ => F y n₀) (ENNReal.ofReal p) Measure.count) ^ p)
        ≤ (q : ENNReal) * K ^ p := by
      calc (∑ n₀ ∈ Finset.range q,
            (eLpNorm (fun y : ℤ => F y n₀) (ENNReal.ofReal p) Measure.count) ^ p)
          ≤ ∑ _n₀ ∈ Finset.range q, K ^ p :=
            Finset.sum_le_sum (fun n₀ hn =>
              ENNReal.rpow_le_rpow (h n₀ (Finset.mem_range.mp hn)) hp.le)
        _ = (q : ENNReal) * K ^ p := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q,
              (eLpNorm (fun y : ℤ => F y n₀) (ENNReal.ofReal p) Measure.count) ^ p) (1 / p)
        ≤ ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ((q : ENNReal) * K ^ p)) (1 / p) :=
          ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hsum_le bot_le) (by positivity)
      _ = ENNReal.rpow (K ^ p) (1 / p) := by
          rw [hqinv, ← mul_assoc, ENNReal.inv_mul_cancel hqE hqT, one_mul]
      _ = K := by
          simpa [one_div, inv_inv] using
            ENNReal.rpow_inv_rpow (y := p⁻¹) (inv_ne_zero hp.ne') K

/-- **The bounded-scale (small `L`) case of the target, in "inner" form:** the constant is
produced for each `ρ ∈ (0,1]` separately (the threshold function `B` is free, hence may itself
depend on `ρ`).  This is the form the gluing needs, because the large-scale threshold
`max Bfas Bna + 1` is `ρ`-dependent. -/
theorem fiberVarSamplingGRepSmallL_inner (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (B : ℝ → ℕ) (r : NNReal) (hr : 2 < r) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
          Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ B ρ →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
              < Nat.floor (a n)) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree
                      (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₂
                      (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                        (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) x)) p
                  MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨Cstar, hCstar_pos, hCstar⟩ := Work.A7.exists_cw_mStargF_tsum_le P.natDegree (by omega)
  obtain ⟨Ccard, hCcard_pos, hCcard⟩ :=
    Work.KMTAreas.A7.iwArithFreqs_card_le ρ hρ hρ1
  refine ⟨(2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ)))) * Cstar + 1, by positivity, ?_⟩
  intro a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g S _ hL ht hband hsplit
  set K : ℝ := (2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ)))) * Cstar + 1 with hK
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]
    have : 0 ≤ (2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ)))) * Cstar := by positivity
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  set u : ℕ → ℤ → ℂ := fun n => if S n then Work.KMTAreas.A7.Tex ρ l₂
      (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0 with hu
  set U : ℕ := Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ with hU
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hq
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) hptop'
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop'
  have hU1 : 1 ≤ U := by
    rw [hU]
    exact le_trans (by omega) (le_max_right _ _)
  have hdmul : 1 ≤ P.natDegree * U := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmU : Work.KMTAreas.A7.mStargF P.natDegree U = Work.KMTAreas.A7.mStarF (P.natDegree * U) :=
    (Work.KMTAreas.A7.mStargF_band P.natDegree U hdmul).1
  have hqpos : 0 < q := by rw [hq]; exact Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)
  -- the uniform mass bound
  have hl₂B : l₂ ≤ B ρ :=
    le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hL
  have hcard_le : ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)
      ≤ (2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ)))) := by
    have h1 : ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.sdiff_subset (s := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
          (t := Work.Analysis.IonescuWainger.iwArithFreqs ρ (l₂ - 1)))
    have h2 : ρ * ((l₂ : ℝ)) ≤ ρ * ((B ρ : ℝ)) := by
      have hll : (l₂ : ℝ) ≤ (B ρ : ℝ) := by exact_mod_cast hl₂B
      nlinarith [hρ.le]
    have h3 : (2 : ℝ) ^ (ρ * ((l₂ : ℝ))) ≤ (2 : ℝ) ^ (ρ * ((B ρ : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2
    refine h1.trans ((hCcard l₂).trans ?_)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    exact mul_le_mul_of_nonneg_left h3 hCcard_pos.le
  have hmass : ∀ n₀ : ℤ,
      (∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ)
        ≤ ENNReal.ofReal K := by
    intro n₀
    have h1 : ∀ j : ℤ,
        ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
            fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ENNReal)
          * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ := by
      intro j
      rw [enorm_mul]
      refine mul_le_mul_left ?_ _
      have h2 : ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - j) α‖ ≤
          ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ) := by
        calc ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
              fourier (T := 1) (n₀ - j) α‖
            ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
                ‖fourier (T := 1) (n₀ - j) α‖ := norm_sum_le _ _
          _ = ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, (1 : ℝ) := by
              refine Finset.sum_congr rfl (fun α _ => ?_)
              rw [fourier_apply]
              exact Circle.norm_coe _
          _ = _ := by simp
      rw [← ofReal_norm, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal h2
    have h2 : (∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ENNReal)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ) :=
      (ENNReal.tsum_le_tsum h1).trans (le_of_eq (ENNReal.tsum_mul_left))
    have h3 : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ)
        ≤ ENNReal.ofReal Cstar := by
      have h5 : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
          (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖) ≤ Cstar := by
        rw [← hmU]
        exact hCstar U
      have hsumm : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw
          (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖) := by
        rw [← hmU]
        exact Work.KMTAreas.A7Hi.summable_cw_mStargF_fin P.natDegree U
      have heq : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
            (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ)
          = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
              (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsumm]
        exact tsum_congr (fun j => (ofReal_norm _).symm)
      rw [heq]
      exact ENNReal.ofReal_le_ofReal h5
    have h7 : (((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ENNReal))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ))))) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard_le
    calc (∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ENNReal)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (P.natDegree * U)) j‖ₑ) :=
          h2
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ))))) *
            ENNReal.ofReal Cstar := mul_le_mul' h7 h3
      _ = ENNReal.ofReal ((2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * ((B ρ : ℝ)))) * Cstar) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal K := by
          rw [hK]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- per-residue bound
  have hper : ∀ n₀ : ℕ,
      MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
            (n₀ : ℤ) (u n) y)) (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
    intro n₀
    have hfun : (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U) (n₀ : ℤ) (u n) y))
        = (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStarF (P.natDegree * U)) (P.eval (n₀ : ℤ)) (u n) y)) := by
      funext y
      refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
      rw [show Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
            (n₀ : ℤ) (u n) y
          = Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
            (P.eval (n₀ : ℤ)) (u n) y from rfl, hmU]
    rw [hfun]
    have hq1 : (1 : ℝ) ≤ p.toReal := by
      have h1 : ((1 : ENNReal)).toReal ≤ p.toReal := ENNReal.toReal_mono hptop' (le_of_lt hp)
      simpa using h1
    have h := Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass r hr1 ρ l₂ (P.natDegree * U)
      (P.eval (n₀ : ℤ)) u hKpos.le hq1 (hmass (P.eval (n₀ : ℤ)))
    exact h
  -- residue bookkeeping
  have hmain := eLpNorm_residueLp_le_of_forall_le p.toReal hp0 q
    (ENNReal.ofReal K * MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count)
    (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
        (n₀ : ℤ) (u n) y))
    (fun n₀ _ => hper n₀)
  rw [show ENNReal.ofReal p.toReal = p from hpe] at hmain
  have hlw : Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
    rw [Work.KMTAreas.A7.lossWeight]
    simp
  rw [hlw, mul_one]
  exact hmain

/-- **The bounded-scale (small `L`) case of the target** (`A = 0`, `ρ₀ = 1`): the corollary of
`fiberVarSamplingGRepSmallL_inner` with the given threshold function `B`. -/
theorem fiberVarSamplingGRepSmallLRep (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (B : ℝ → ℕ) (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
          Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ B ρ →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
              < Nat.floor (a n)) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree
                      (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₂
                      (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                        (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) x)) p
                  MeasureTheory.Measure.count :=
  ⟨0, le_rfl, 1, one_pos,
    fun p hp hptop ρ hρ hρ1 => fiberVarSamplingGRepSmallL_inner P hdeg B r hr ρ hρ hρ1 p hp hptop⟩

/-- **The bounded-input case of the target.**

Same statement as the target, with the extra hypothesis `∃ Bg, ∀ x, ‖g x‖ ≤ Bg`.  The proof is the
two-regime gluing of the *proved* pieces:

* bounded scale `Lnat l₁ l₂ k₁ k₂ ≤ B ρ`: the crude Young bound `fiberVarSamplingGRepSmallLRep`
  (a `ρ`-dependent constant, absorbed by `lossWeight A ≥ 1`);
* large scale: the repaired-window estimate `fiberVarSamplingGRepLargeBdd` (a constant independent
  of every parameter), whose Farey and non-aliasing hypotheses are supplied by
  `A7Hi.farey_and_strict_of_large_L_g` (from the target's `splitCut` hypothesis, in the large-`L`
  regime) and by `A7.exists_nonAliasing_uScale` (monotonicity in the scale, using `uRep ≥ uScale`).
  Off the clip `S` the free scale parameter is set to a huge `K`, so that both scale hypotheses
  hold there as well, while the clipped family is unchanged.

The constant is `A := 0` (`lossWeight 0 = 1`). -/
theorem fiberVarSamplingGRep_bdd (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
        ∀ (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
              < Nat.floor (a n)) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree
                      (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₂
                      (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                        (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) x)) p
                  MeasureTheory.Measure.count := by
  classical
  refine ⟨0, le_rfl, 1, one_pos, ?_⟩
  intro p hp hptop ρ hρ hρ1
  -- the two arithmetic inputs of the large-scale regime, at this `ρ`
  obtain ⟨Bfas, hBfas⟩ := Work.KMTAreas.A7Hi.farey_and_strict_of_large_L_g ρ hρ hρ1
  obtain ⟨Bna, hBna⟩ := Work.KMTAreas.A7.exists_nonAliasing_uScale ρ hρ hρ1
  -- the threshold function of the gluing, and the bounded-scale constant at it
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    fiberVarSamplingGRepSmallL_inner P hdeg (fun _ => max Bfas Bna + 1) r hr ρ hρ hρ1 p hp hptop
  obtain ⟨C₂, hC₂pos, hC₂⟩ := fiberVarSamplingGRepLargeBdd P hdeg r hr ρ hρ hρ1 p hp hptop
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g Bg hBg S _ ht hband hsplit
  by_cases hsmall : Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ max Bfas Bna + 1
  · -- bounded-scale regime: the crude bound, with `lossWeight 0 = 1`
    have hb := hC₁ a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g S hsmall ht hband hsplit
    refine hb.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [show Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by
      simp [Work.KMTAreas.A7.lossWeight]]
    linarith [le_max_left C₁ C₂]
  · -- large-scale regime
    push_neg at hsmall
    have hLdef : Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂) := rfl
    have hBfasLt : Bfas < max (max l₁ l₂) (max k₁ k₂) := by
      rw [hLdef] at hsmall
      omega
    have hBnaLt : Bna ≤ max (max l₁ l₂) (max k₁ k₂) := by
      rw [hLdef] at hsmall; omega
    have hl₂L : l₂ ≤ max (max l₁ l₂) (max k₁ k₂) := by omega
    -- the non-aliasing hypothesis, transferred from the `uScale` scale to the repaired one
    have hnaScale : Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
      hBna l₂ (max (max l₁ l₂) (max k₁ k₂)) hl₂L hBnaLt
    have hna : Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
      have hge : Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))
          ≤ Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ := by
        rw [Work.KMTAreas.A7.uRep]; exact le_max_left _ _
      have hle : -(2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))
          ≤ -(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)) := by
        have h : (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)
            ≤ (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ) := by exact_mod_cast hge
        linarith
      exact Work.KMTAreas.A7Hi.nonAliasing_mono_scale hle hnaScale
    -- the auxiliary scale sequence: the target's `⌊a·⌋` on the clip, a huge constant off it
    have hqpos : 0 < Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) :=
      Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)
    set N' : ℕ → ℕ := fun n => if S n then Nat.floor (a n)
      else 2 ^ (k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
        * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) + 1) with hN'
    have hstrict' : ∀ n : ℕ, k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 1
        ≤ (Work.Analysis.EndVar.logN (N' n)).toNat := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
        have h := hband n hn
        omega
      · rw [hN']; simp only [hn, if_false]
        set K : ℕ := 2 ^ (k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
          * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) + 1) with hK
        have hle : 2 ^ (k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) ≤ max K 2 := by
          rw [hK]
          refine le_trans ?_ (le_max_left _ _)
          exact Nat.le_mul_of_pos_right _
            (by omega : 0 < Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) + 1)
        have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hle
        have hlogN : (Work.Analysis.EndVar.logN K).toNat = Nat.log 2 (max K 2) := by
          rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
        rw [hlogN]
        omega
    have hfarey' : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂
        * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) ≤ (N' n : ℝ) := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
        exact (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (hsplit n hn) hBfasLt).1
      · rw [hN']; simp only [hn, if_false]
        have h8 : (8 : ℝ) ≤
            (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) := by
          have h : (8 : ℕ) ≤ 2 ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) := by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) :=
                  Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast h
        have hk0 : (0 : ℝ) < (2 : ℝ) ^ k₂ := by positivity
        have hq0 : (0 : ℝ) ≤ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) := Nat.cast_nonneg _
        have hsplitpow : (2 : ℝ) ^ (k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
            = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) := by
          rw [show k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4
            = k₂ + (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4) from by ring, pow_add]
        have hcast : (((2 ^ (k₂ + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
            * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) + 1) : ℕ) : ℝ))
            = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
              * ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) + 1) := by
          push_cast
          rw [hsplitpow]
        rw [hcast]
        calc 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ)
            = 8 * ((2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ)) := by ring
          _ ≤ (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
                * ((2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ)) :=
              mul_le_mul_of_nonneg_right h8 (mul_nonneg hk0.le hq0)
          _ = (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
                * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) := by ring
          _ ≤ (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
                * (2 : ℝ) ^ k₂ * ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ + 4)
                * ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) + 1) := by ring
    have hkey := hC₂ l₁ l₂ k₁ k₂ t g Bg hBg N' S ht hfarey' hstrict' hna
    have hwfn : ∀ n : ℕ, (if S n then Work.KMTAreas.A7.Tex ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N' n) k₂ t) g else 0)
        = (if S n then Work.KMTAreas.A7.Tex ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0) := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
      · simp only [hn, if_false]
    simp only [hwfn] at hkey
    refine hkey.trans ?_
    have hlw : Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
      simp [Work.KMTAreas.A7.lossWeight]
    rw [hlw, mul_one]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right C₁ C₂)) le_rfl

open MeasureTheory in
/-- **The remaining case of the target, as a named `Prop`**: the *large-scale, finite-variational*
case.  Here `B : ℝ → ℕ` is the threshold below which the crude bounded-scale bound
(`fiberVarSamplingGRepSmallL_inner`) applies; the extra hypothesis is the finiteness of the
`ℓᵖ`-norm of the variational norm of the clipped family, which makes the stored (junk-nulled)
family pointwise bounded.

The proof of the target from `fiberVarSamplingGRep_bdd` (bounded `g`) and this `Prop` is proved
below as `FiberVarSamplingGRep_of_bdd_and_finite`.

The content of the `Prop` is the `Vʳ`-valued packet-rotation bound for the *masked* families
`u n = 1_{E n}·(honest band-limited column)`: by the gate identity
`fiberOpP ρ P l₂ (mStargF d U) n₀ (Tex ρ l₂ φ̃_n g) = fiberOpP ρ P l₂ φ̃_n n₀ g` (available only
for bounded `g`), the fibre is the *comb packet* `Σ_{α ∈ (ℚ/ℤ)_{l₂}} e(P(n₀)·α)·P_α(u n)`; for a
junk-nulled `u` the spectrum of `u n` is the **torsion band** (a union of `q`-narrow arcs at the
`q`-torsion points, `q = arithQ ρ (max l₁ l₂)`), and the residue average over `n₀ < q` must be
controlled by `‖Vʳ u‖_{ℓᵖ}`.  This is the workspace's `Work.KMTAreas.A7Hi.PacketRotationResidueBoundTorsionBand`
(the `p = 2` half follows from the `q`-torsion orthogonality plus Bessel for the disjoint `uRep`-arcs;
the general-`p`/`Vʳ` half is the open input). -/
def FiberVarSamplingGRepFinite (P : Polynomial ℤ) (B : ℝ → ℕ) (r : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
        B ρ < Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ →
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
        (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
            < Nat.floor (a n)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g else 0) x)) p
          MeasureTheory.Measure.count < ⊤ →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree
                    (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                    (Nat.floor (a n)) k₂ t) g else 0) x)) p
                MeasureTheory.Measure.count

/-- **The target's statement, as a `Prop`** (the target is a `theorem`, so it cannot be used in
type position).  Verbatim. -/
def FiberVarSamplingGRepStatement (P : Polynomial ℤ) (r : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
        (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
            < Nat.floor (a n)) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree
                    (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                    (Nat.floor (a n)) k₂ t) g else 0) x)) p
                MeasureTheory.Measure.count

/-- **The reduction of the target to the bounded-input case and the finite-variational case.**

Given `FiberVarSamplingGRepFinite B r` for *any* threshold `B`, the target follows from the proved
bounded-input case `fiberVarSamplingGRep_bdd`.  The case split is

* `Lnat l₁ l₂ k₁ k₂ ≤ B ρ`: the crude bounded-scale bound (no boundedness hypothesis needed);
* `B ρ < Lnat …` and `g` bounded: `fiberVarSamplingGRep_bdd`;
* `B ρ < Lnat …` and `g` unbounded: if the variational norm of the clipped family is infinite the
  target is trivial, otherwise `FiberVarSamplingGRepFinite` applies.

All three constants are produced before the split, and each is absorbed by
`max (max C₁ C₂) C₃ · lossWeight A ρ …` (using `lossWeight ≥ 1`). -/
theorem FiberVarSamplingGRep_of_bdd_and_finite (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) (B : ℝ → ℕ) (hfin : FiberVarSamplingGRepFinite P B r) :
    FiberVarSamplingGRepStatement P r := by
  classical
  obtain ⟨A₁, hA₁, ρ₁, hρ₁, H₁⟩ := fiberVarSamplingGRep_bdd P hdeg r hr
  obtain ⟨A₂, hA₂, ρ₂, hρ₂, H₂⟩ := hfin
  refine ⟨max A₁ A₂, le_max_of_le_left hA₁, min (min ρ₁ ρ₂) 1,
    lt_min (lt_min hρ₁ hρ₂) one_pos, ?_⟩
  intro p hp hptop ρ hρ hρmin
  have hρ1 : ρ ≤ 1 := le_trans hρmin (min_le_right _ _)
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (le_trans hρmin (min_le_left _ _)) (min_le_left _ _)
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (le_trans hρmin (min_le_left _ _)) (min_le_right _ _)
  obtain ⟨C₁, hC₁pos, hC₁⟩ := H₁ p hp hptop ρ hρ hρρ₁
  obtain ⟨C₂, hC₂pos, hC₂⟩ := H₂ p hp hptop ρ hρ hρρ₂
  -- the crude bounded-scale constant at the threshold `B`
  obtain ⟨C₃, hC₃pos, hC₃⟩ :=
    fiberVarSamplingGRepSmallL_inner P hdeg B r hr ρ hρ hρ1 p hp hptop
  refine ⟨max (max C₁ C₂) C₃, lt_max_of_lt_left (lt_max_of_lt_left hC₁pos), ?_⟩
  intro a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g S _ ht hband hsplit
  have hlw₁ : Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ k₁ k₂ :=
    Work.KMTAreas.A7Hi.lossWeight_mono (le_max_left A₁ A₂) hA₁ hρ.le l₁ l₂ k₁ k₂
  have hlw₂ : Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ k₁ k₂ :=
    Work.KMTAreas.A7Hi.lossWeight_mono (le_max_right A₁ A₂) hA₂ hρ.le l₁ l₂ k₁ k₂
  have hlw0 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ k₁ k₂ :=
    Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg _ _ (le_max_of_le_left hA₁) hρ.le l₁ l₂ k₁ k₂
  have hlw0pos : 0 < Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ k₁ k₂ := lt_of_lt_of_le one_pos hlw0
  by_cases hsmall : Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ ≤ B ρ
  · -- bounded-scale regime: the crude bound (no boundedness of `g` needed)
    have hb := hC₃ a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g S hsmall ht hband hsplit
    refine hb.trans ?_
    rw [show Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by
      simp [Work.KMTAreas.A7.lossWeight]]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hC3le : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ _
    nlinarith [hC3le, hlw0, hC₃pos, hlw0pos]
  · push_neg at hsmall
    by_cases hg : ∃ Bg : ℝ, ∀ x : ℤ, ‖g x‖ ≤ Bg
    · -- bounded input: the bounded-input case of the target
      obtain ⟨Bg, hBg⟩ := hg
      have hb := hC₁ a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g Bg hBg S ht hband hsplit
      refine hb.trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact mul_le_mul (le_trans (le_max_left C₁ C₂) (le_max_left _ _)) hlw₁
        (Work.KMTAreas.A7.lossWeight_nonneg _ _ _ _ _ _) (by positivity)
    · -- unbounded input: the finite-variational case, or the trivial infinite case
      by_cases hW : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g else 0) x)) p
          MeasureTheory.Measure.count = ⊤
      · rw [hW]
        have hne : ENNReal.ofReal (max (max C₁ C₂) C₃
            * Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ k₁ k₂) ≠ 0 := by
          rw [ENNReal.ofReal_ne_zero_iff]
          exact mul_pos (lt_of_lt_of_le hC₃pos (le_max_right (max C₁ C₂) C₃)) hlw0pos
        rw [ENNReal.mul_top hne]
        exact le_top
      · have hWlt : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                (Nat.floor (a n)) k₂ t) g else 0) x)) p
            MeasureTheory.Measure.count < ⊤ := lt_of_le_of_ne le_top hW
        have hb := hC₂ a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t g S hsmall ht hband hsplit hWlt
        refine hb.trans ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact mul_le_mul (le_trans (le_max_right C₁ C₂) (le_max_left _ _)) hlw₂
          (Work.KMTAreas.A7.lossWeight_nonneg _ _ _ _ _ _) (by positivity)

theorem FiberVarSamplingGRep (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₂ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
              < Nat.floor (a n)) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree
                      (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₂
                      (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                        (Nat.floor (a n)) k₂ t) g else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                      (Nat.floor (a n)) k₂ t) g else 0) x)) p
                  MeasureTheory.Measure.count := by sorry

end

end Work.KMTAreas.A7Rescue
