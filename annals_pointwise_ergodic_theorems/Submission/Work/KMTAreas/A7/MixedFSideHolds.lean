import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedModel
import Submission.Work.KMTAreas.A7.variationalNorm_clip_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem monotone_of_lacunary_local {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- **Minkowski/Young for `ℝ≥0∞`-valued functions on the counting measure of `ℤ`.**  For `q ≥ 1`,
`K : ℤ → ℂ` and `W : ℤ → ℝ≥0∞`,

  `‖ x ↦ ∑'_j ‖K j‖ · W (x - j) ‖_{ℓ^q} ≤ (∑'_j ‖K j‖) · ‖W‖_{ℓ^q}`.

(Copied from `Work.KMTAreas.A7Hi.FiberOpCutBoundLevelOne`, where it is private.) -/
theorem eLpNorm_tsum_enorm_mul_sub_le_local {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ)
    (W : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := eLpNorm_tsum_le_tsum_eLpNorm (μ := Measure.count) (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable (fun x : ℤ => ‖K j‖ₑ * W (x - j))).aemeasurable)
  have hconst : ∀ j : ℤ,
      eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = ‖K j‖ₑ * eLpNorm W (ENNReal.ofReal q) Measure.count := by
    intro j
    rw [show eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q) Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := W) (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-- `Tm ρ 0 φ = Tle ρ 0 φ`: at arithmetic height `0` the `diffFreqs` convention and the
`iwArithFreqs` convention agree. -/
theorem Tm_zero_eq_Tle_local (ρ : ℝ) (φ : ℝ → ℂ) :
    Tm ρ 0 φ = Tle ρ 0 φ := by
  funext f
  rw [Tm, Tle, diffFreqs, if_pos rfl]

/-- **The `f`-side factor estimate of the mixed range** (paper `(lin-1)` at arithmetic height `0`
with the bounded window convolution `cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))` attached).

This is the `f`-side input `MixedFSideEstimate` of the mixed case of Area A7, proved from
`Work.KMTAreas.A7.LoLinVar`, the uniform kernel-mass bound
`Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le`, the variational Young inequality
(`Work.KMTAreas.A7Hi.variationalNorm_tsum_le`) with its `ℓ^p` form (Minkowski plus the translation
invariance of the counting measure, `eLpNorm_tsum_enorm_mul_sub_le_local`), and the clipping of the
guard (`Work.KMTAreas.A7.variationalNorm_clip_le`). -/
theorem MixedFSideHolds (P : Polynomial ℤ) (p₁ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) : Work.KMTAreas.A7.MixedFSideEstimate P p₁ := by
  classical
  obtain ⟨Cw, hCwpos, hCw⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  have hp1le : (1 : ENNReal) ≤ p₁ := le_of_lt hp₁
  have hp1real : (1 : ℝ) ≤ p₁.toReal := by
    have h := ENNReal.toReal_mono htp₁.ne hp1le
    rwa [ENNReal.toReal_one] at h
  have hcoe : ((Real.toNNReal Cw : NNReal) : ENNReal) = ENNReal.ofReal Cw := by
    have h : ENNReal.ofReal (↑(Real.toNNReal Cw) : ℝ) =
        ((Real.toNNReal Cw : NNReal) : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [Real.coe_toNNReal Cw hCwpos.le] at h
    exact h.symm
  intro C₀ r hC₀ hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have hlin := LoLinVar ρ hρ hρ1 p₁ hp₁ htp₁ r hr
  refine ⟨fun Λ => if h : 1 < Λ then
      2 * Real.toNNReal Cw * Classical.choose (hlin Λ h) + 1 else 1, ?_⟩
  intro a Λ l₂ k₁ k₂ t f hΛ ha ha1 hl₂ ht
  have hKdef : ((fun Λ => if h : 1 < Λ then
      2 * Real.toNNReal Cw * Classical.choose (hlin Λ h) + 1 else 1) Λ)
      = 2 * Real.toNNReal Cw * Classical.choose (hlin Λ hΛ) + 1 := dif_pos hΛ
  rw [hKdef]
  set Clin : NNReal := Classical.choose (hlin Λ hΛ) with hClindef
  have hClin : ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (hkN : ∀ n, 2 ^ k ≤ Nat.floor (a n))
      (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Tle ρ 0 (varphiNt (Nat.floor (a n)) k t) f x)) p₁ Measure.count
        ≤ (Clin : ENNReal) * ENNReal.ofReal ((1 + (k : ℝ)) ^ 2) *
            eLpNorm f p₁ Measure.count :=
    Classical.choose_spec (hlin Λ hΛ)
  have hamono : Monotone a := monotone_of_lacunary_local hΛ ha ha1
  by_cases hGne : ∃ n : ℕ, loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · -- ## the guard is nonempty: clip and reduce to a shifted, unclipped family
    obtain ⟨m, hm⟩ : ∃ m₀ : ℕ, ∀ n : ℕ, loGuard ρ C₀ a 0 l₂ k₁ k₂ n ↔ m₀ ≤ n := by
      refine ⟨Nat.find hGne, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hGne hcon hn
      · exact core_mono hamono hn (Nat.find_spec hGne)
    have hclip : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x) := by
      intro x
      have hfun : (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0)
          = (fun n : ℕ => if m ≤ n then
              convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0) := by
        funext n
        by_cases h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
        · rw [if_pos h, if_pos ((hm n).mp h)]
        · rw [if_neg h, if_neg (fun hc => h ((hm n).mpr hc))]
      rw [hfun]
      calc PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if m ≤ n then
                convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                  (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0)
          ≤ PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x) :=
            variationalNorm_clip_le r hr1 _ m
        _ = 2 * PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x) := by
            rw [two_mul]
    have hstep1 : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
          p₁ Measure.count
        ≤ 2 * eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x)) p₁ Measure.count :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]; exact hclip x)) p₁
    -- ## the Young/Minkowski step for the window convolution
    have hpt2 : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x)
        ≤ ∑' b : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) b‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f (x - b)) := by
      intro x
      have h := Work.KMTAreas.A7Hi.variationalNorm_tsum_le r hr1
        (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
        (fun b j => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f (x - b))
      simpa only [convOp] using h
    have htailX : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun j : ℕ => convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f) x)) p₁ Measure.count
        ≤ (∑' b : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) b‖ₑ) *
            eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
              p₁ Measure.count := by
      have h2 := eLpNorm_tsum_enorm_mul_sub_le_local (q := p₁.toReal) hp1real
        (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
        (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun j : ℕ => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
      rw [ENNReal.ofReal_toReal htp₁.ne] at h2
      exact (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
          rw [enorm_eq_self, enorm_eq_self]; exact hpt2 x)).trans h2
    -- ## the linear estimate for the shifted family
    have htail : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun j : ℕ => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
          p₁ Measure.count
        ≤ (Clin : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
            eLpNorm f p₁ Measure.count := by
      have h1 := hClin (fun j : ℕ => a (j + m))
        (by intro j
            have h := ha (j + m)
            have hidx : j + 1 + m = (j + m) + 1 := by omega
            show Λ < a (j + 1 + m) / a (j + m)
            rw [hidx]; exact h)
        (fun j => ha1 (j + m)) k₁
        (fun j => Work.KMTAreas.A7Hi.two_pow_le_floor_of_core
          ((hm (j + m)).mpr (Nat.le_add_left m j)))
        t ht f
      have h2 : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tm ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
            p₁ Measure.count
          ≤ (Clin : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
              eLpNorm f p₁ Measure.count := by
        simpa only [Tm_zero_eq_Tle_local] using h1
      refine h2.trans (mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl)
      exact ENNReal.ofReal_le_ofReal (by
        have hL := lmaxR_nonneg 0 l₂ k₁ k₂
        have hk : (k₁ : ℝ) ≤ lmaxR 0 l₂ k₁ k₂ := Work.KMTAreas.A7Hi.natCast_le_lmaxR_k₁ 0 l₂ k₁ k₂
        have h1 : (1 + (k₁ : ℝ)) ^ (2 : ℝ) ≤
            (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * lmaxR 0 l₂ k₁ k₂) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        have h3 : (1 + (k₁ : ℝ)) ^ (2 : ℝ) ≤
            (1 + lmaxR 0 l₂ k₁ k₂) ^ (2 : ℝ) * (2 : ℝ) ^ (2 * ρ * lmaxR 0 l₂ k₁ k₂) :=
          h1.trans (le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h2)
        rw [lossWeight, ← Real.rpow_natCast (1 + (k₁ : ℝ)) 2]
        exact h3)
    -- ## the mass bound of the window kernel
    have hmass : (∑' b : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) b‖ₑ)
        ≤ ((Real.toNNReal Cw : NNReal) : ENNReal) := by
      rw [hcoe]
      have hsum := (hCw (loMixedU ρ P.natDegree l₂ k₁ k₂)).1
      have h1 : (∑' j : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ₑ) =
          ENNReal.ofReal (∑' j : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsum]
        exact tsum_congr fun j => (ofReal_norm _).symm
      rw [h1]
      exact ENNReal.ofReal_le_ofReal (hCw (loMixedU ρ P.natDegree l₂ k₁ k₂)).2
    -- ## the assembly
    have hbound : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
          p₁ Measure.count
        ≤ 2 * ((∑' b : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) b‖ₑ) *
            ((Clin : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
              eLpNorm f p₁ Measure.count)) :=
      hstep1.trans (mul_le_mul' le_rfl (htailX.trans (mul_le_mul' le_rfl htail)))
    refine hbound.trans ?_
    calc 2 * ((∑' b : ℤ, ‖cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)) b‖ₑ) *
            ((Clin : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
              eLpNorm f p₁ Measure.count))
        ≤ 2 * (((Real.toNNReal Cw : NNReal) : ENNReal) *
            ((Clin : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
              eLpNorm f p₁ Measure.count)) :=
          mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)
      _ ≤ ((2 * Real.toNNReal Cw * Clin + 1 : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) * eLpNorm f p₁ Measure.count := by
          rw [show ((2 * Real.toNNReal Cw * Clin + 1 : NNReal) : ENNReal) =
              (2 * ((Real.toNNReal Cw : NNReal) : ENNReal) * (Clin : ENNReal) + 1) by
            push_cast; ring]
          calc 2 * (((Real.toNNReal Cw : NNReal) : ENNReal) *
                  ((Clin : ENNReal) * ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) *
                    eLpNorm f p₁ Measure.count))
              = (2 * ((Real.toNNReal Cw : NNReal) : ENNReal) * (Clin : ENNReal)) *
                  (ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) * eLpNorm f p₁ Measure.count) := by
                ring
            _ ≤ (2 * ((Real.toNNReal Cw : NNReal) : ENNReal) * (Clin : ENNReal) + 1) *
                  (ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) * eLpNorm f p₁ Measure.count) :=
                mul_le_mul' (le_add_right le_rfl) le_rfl
            _ = (2 * ((Real.toNNReal Cw : NNReal) : ENNReal) * (Clin : ENNReal) + 1) *
                  ENNReal.ofReal (lossWeight 2 ρ 0 l₂ k₁ k₂) * eLpNorm f p₁ Measure.count := by
                ring
  · -- ## the guard is empty: the family vanishes
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
      funext x
      have hf : (fun n : ℕ => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
              (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        rw [if_neg (fun hn => hGne ⟨n, hn⟩)]
      rw [hf]
    rw [hzero, Work.KMTAreas.A7Hi.eLpNorm_variationalNorm_zero hr1 p₁]
    exact bot_le

end

end Work.KMTAreas.A7
