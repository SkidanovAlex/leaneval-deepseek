import Mathlib
import Submission.Work.KMTAreas.A7Hi.VarphitildeSupportG
import Submission.Work.KMTAreas.A7Hi.NonAliasingMono
import Submission.Work.KMTAreas.A7.mStargF_band
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLoss_bdd
import Submission.Work.KMTAreas.A7.SmallKernMassBasics
import Submission.Work.KMTAreas.A7Hi.Gblock

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The `g`-side gate/clip identity

The wider cut `mStargF d U = η_{≤-2dU}` acts as the identity on the exact-height projection
`Tex ρ l₂ φ g` as long as `φ` is supported inside the *plateau half-ball* `|ξ| ≤ 2^{-2dU-1}` and
the arithmetic frequencies are non-aliasing at the scale `-2dU`.  This is the `g`-side analogue of
`Work.KMTAreas.A7.fiberOp_mStarF_Sclip` (which handles the first tensor factor `mStarF U`); the
identities are `mStargF d U = mStarF (d*U)` (`mStargF_band`) and the scale monotonicity of
`NonAliasing` (`nonAliasing_mono_scale`). -/
theorem fiberOp_mStargF_Sclip (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (l U : ℕ)
    (hU : 1 ≤ U) (hd : 1 ≤ P.natDegree)
    (hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l))
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1))
    (f : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (S : Prop) [Decidable S] (n₀ : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
        (if S then Work.KMTAreas.A7.Tex ρ l φ f else 0)
      = if S then Work.KMTAreas.A7.fiberOp ρ l φ n₀ f else 0 := by
  have hdU : 1 ≤ P.natDegree * U := by
    rcases Nat.eq_zero_or_pos U with h | h
    · omega
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hm : Work.KMTAreas.A7.mStargF P.natDegree U = Work.KMTAreas.A7.mStarF (P.natDegree * U) :=
    (Work.KMTAreas.A7.mStargF_band P.natDegree U hdU).1
  have hle : (U : ℤ) ≤ ((P.natDegree * U : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_left U (by omega : 0 < P.natDegree)
  have hna' : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (((P.natDegree * U : ℕ) : ℤ))))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l) :=
    nonAliasing_mono_scale (by omega) hna
  by_cases hS : S
  · rw [if_pos hS, if_pos hS, hm]
    exact Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd ρ hρ hρ1 l (P.natDegree * U) hdU hna'
      φ hφ hφsum hφsupp f B hB n₀
  · rw [if_neg hS, if_neg hS]
    funext y
    simp only [Work.KMTAreas.A7.fiberOp, Pi.zero_apply, mul_zero, tsum_zero]

/-! ## The `g`-side large-scale fibre sampling estimate, bounded input

This is the `g`-side analogue of `Work.KMTAreas.A7.fiberVarSamplingLargeLoss_bdd` (the `f`-side
estimate, which is PROVED), with the polynomial twist `P` in the residue index
(`fiberOpP ρ P l₂ m n₀ = fiberOp ρ l₂ m (P.eval n₀)`) and the `d`-fold bump `varphitildeNt`.
The proof is the same: the fibre is a kernel convolution with the profile `φ̃_{N,t}`, it is
rewritten on the residue class `r` mod `q` as the carrier-free slice (`fiberOp_residue_eq_slice`),
and the *coset comparison* `convSublatticeCosetCompareBdd` (quantitative Shannon sampling, using
Farey `βq ≤ 1/4`) compares the two cosets; the second end is the exact-height projection
`Tex ρ l₂ φ̃_{N,t} g` itself. -/
theorem fiberVarSamplingG_large_bdd (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
          ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂
              * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₂ + 2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℕ) + 1
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) y)) x)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
            p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  have hpne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hptop' : p ≠ ⊤ := hptop.ne
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hpne hptop'
  have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop'
  have hpr : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop').mpr hp
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  obtain ⟨Ccomp, hCcomp, hcomp⟩ := Work.KMTAreas.A7.convSublatticeCosetCompareBdd p.toReal hpr r hr1
  refine ⟨Ccomp ^ (1 / p.toReal), Real.rpow_pos_of_pos hCcomp _, ?_⟩
  intro l₁ l₂ k₁ k₂ t g Bg hBg N S hdec ht hfarey hstrict hna
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) with hU
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hq
  set φ : ℕ → ℝ → ℂ := fun n => Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t with hφ
  set κ : ℕ → ℤ → ℂ := fun n j => Work.KMTAreas.A7.cw (φ n) j with hκ
  set Hf : ℕ → ℤ → ℤ → ℂ :=
    fun n y z => if S n then Work.KMTAreas.A7.sliceInput
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) g y z else 0 with hHf
  set F : ℤ → ℕ → ENNReal := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
      (P.eval (n₀ : ℤ)) (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) y) with hF
  set W : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x) with hW
  have hφint : ∀ n : ℕ, Integrable (φ n) := by
    intro n
    simp only [hφ]
    exact Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree (N n) k₂ t
  have hφsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (φ n) j‖) := by
    intro n
    simp only [hφ]
    exact Work.KMTAreas.A7.summable_cw_varphitildeNt P P.natDegree (N n) k₂ t
  have hφsupp : ∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1) := by
    intro n ξ hξ
    exact varphitildeNt_support_strict_g P (by omega) (N n) k₂ U t (hstrict n) ξ (by
      simpa only [hφ] using hξ)
  have hU1 : 1 ≤ U := by
    simp only [hU]
    exact Work.KMTAreas.A7.one_le_uScale_bdd hρ.le _
  have hnaU : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
    simpa only [hU] using hna
  have hnaNew : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) :=
    Work.KMTAreas.A7.nonAliasing_subset hnaU
      (fun α hα => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
  have hqpos : 0 < q := by
    simp only [hq]
    exact Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)
  have hq1 : 1 ≤ q := hqpos
  have hq0 : (q : ENNReal) ≠ 0 := by positivity
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hfareyU : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N n : ℝ) := by
    intro n
    have h := hfarey n
    rw [hq]
    exact h
  have hqnsmul : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0 := by
    intro α hα
    rw [hq]
    exact Work.KMTAreas.A7.arithQ_nsmul_eq_zero
      (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂)
        (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα))
  have hβ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  have hβq : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have h : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      field_simp
    rw [h]
  have hκsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖κ n j‖) := by
    intro n
    simp only [hκ]
    exact hφsum n
  have hB0 : 0 ≤ Bg := le_trans (norm_nonneg (g 0)) (hBg 0)
  have hHfb : ∀ n : ℕ, ∀ y z : ℤ,
      ‖Hf n y z‖ ≤ Bg * ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ) := by
    intro n y z
    simp only [hHf]
    by_cases hSn : S n
    · simp only [hSn, if_true]
      simp only [Work.KMTAreas.A7.sliceInput]
      calc ‖g z * (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
              fourier (T := 1) (y + z) α)‖
          = ‖g z‖ * ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
              fourier (T := 1) (y + z) α‖ := norm_mul _ _
        _ ≤ Bg * ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ) := by
            refine mul_le_mul (hBg z) ?_ (norm_nonneg _) hB0
            calc ‖∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
                    fourier (T := 1) (y + z) α‖
                ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
                    ‖fourier (T := 1) (y + z) α‖ := norm_sum_le _ _
              _ = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, (1 : ℝ) := by
                  refine Finset.sum_congr rfl (fun α _ => ?_)
                  rw [fourier_apply]
                  exact Circle.norm_coe _
              _ = ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ) := by simp
    · simp only [hSn, if_false, norm_zero]
      exact mul_nonneg hB0 (Nat.cast_nonneg _)
  set kext : ℕ → ℝ → ℂ := fun n s => ∫ θ, φ n θ * Work.KMTAreas.A7.ee (-(s * θ)) with hkext
  have hkextdata : ∀ n : ℕ,
      Integrable (kext n) ∧ Continuous (kext n) ∧
        (∀ m : ℤ, kext n (m : ℝ) = κ n m) ∧
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (q : ℝ)))) (1 / (4 * (q : ℝ))) →
          FourierTransform.fourier (kext n) ξ = 0) := by
    intro n
    have hfun : kext n = fun s : ℝ =>
        ∫ θ, (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t : ℝ → ℂ) θ
          * Work.KMTAreas.A7.ee (-(s * θ)) := by
      funext s
      simp only [hkext, hφ, Work.KMTAreas.A7Hi.varphitildeNtSch_g_coe]
    have hfun2 : kext n
        = ⇑(𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t) :
            SchwartzMap ℝ ℂ) := by
      rw [hfun]
      funext s
      exact Work.KMTAreas.A7.cwR_eq_fourier _ s
    have hsupp : ∀ ξ : ℝ,
        (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t : ℝ → ℂ) ξ ≠ 0 →
        |ξ| ≤ 1 / (4 * (q : ℝ)) := by
      intro ξ hξ
      refine varphitildeNt_support_le_quarter_g P (by omega) q hq1 (N n) k₂ t (hfareyU n) ξ ?_
      simpa only [Work.KMTAreas.A7Hi.varphitildeNtSch_g_apply] using hξ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfun2]
      exact (𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t)).integrable
    · rw [hfun2]
      exact (𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t)).continuous
    · intro m
      rw [hfun]
      have h1 : (∫ θ, (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t :
              ℝ → ℂ) θ * Work.KMTAreas.A7.ee (-(((m : ℤ) : ℝ) * θ)))
          = Work.KMTAreas.A7.cw
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) m := by
        simp only [Work.KMTAreas.A7.cw, Work.KMTAreas.A7Hi.varphitildeNtSch_g_apply, neg_mul]
      simpa only [hκ, hφ] using h1
    · intro ξ hξ
      rw [hfun]
      exact Work.KMTAreas.A7.fourier_cwR_band (1 / (4 * (q : ℝ))) hβ
        (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t) hsupp ξ hξ
  have hpair : ∀ (n₀ r₀ : ℕ),
      (∑' u : ℤ, (F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal)
        ≤ ENNReal.ofReal Ccomp *
          (∑' u : ℤ, (W ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ)))) ^ p.toReal) := by
    intro n₀ r₀
    have hL : ∀ u : ℤ, F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, κ n j *
            Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + (r₀ : ℤ) - j)) := by
      intro u
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U) (P.eval (n₀ : ℤ))
            (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
            ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)))
          = fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ))
              ((q : ℤ) * u + (r₀ : ℤ) - j) := by
        funext n
        simp only [hκ, hHf]
        rw [fiberOp_mStargF_Sclip ρ hρ hρ1 P l₂ U hU1 (by omega) hnaNew (φ n)
          (hφint n) (hφsum n) (hφsupp n) g Bg hBg (S n) (P.eval (n₀ : ℤ))]
        simp only [ite_apply, Pi.zero_apply]
        have hpt : (r₀ : ℤ) + (u : ℤ) * (q : ℤ) = (q : ℤ) * (u : ℤ) + (r₀ : ℤ) := by ring
        rw [hpt]
        rw [Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg hqnsmul
          (P.eval (n₀ : ℤ)) (r₀ : ℤ) (u : ℤ)]
        exact (Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (φ n)
          (hφsum n) g Bg hBg (P.eval (n₀ : ℤ) - (r₀ : ℤ))
          ((q : ℤ) * (u : ℤ) + (r₀ : ℤ)) (S n)).symm
      simp only [hF]
      rw [hfun]
    have hR : ∀ u : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ))
              ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ)) - j))
        = W ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ))) := by
      intro u
      have hfun : (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ))
              ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ)) - j))
          = fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
              ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ))) := by
        funext n
        simp only [hκ, hHf]
        rw [Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (φ n) (hφsum n) g Bg hBg
          (P.eval (n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ))) (S n)]
        simp only [ite_apply, Pi.zero_apply]
        by_cases hSn : S n
        · simp only [hSn, if_true]
          rw [← Work.KMTAreas.A7.fiberOp_zero_eq_Tex ρ l₂ (φ n) (hφint n) g]
          have hy : (P.eval (n₀ : ℤ) - (r₀ : ℤ)) = 0 - ((r₀ : ℤ) - P.eval (n₀ : ℤ)) := by ring
          rw [hy]
          rw [← Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg
            hqnsmul 0 ((r₀ : ℤ) - P.eval (n₀ : ℤ)) (u : ℤ)]
        · simp only [hSn, if_false]
      simp only [hW]
      rw [hfun]
    calc (∑' u : ℤ, (F ((r₀ : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal)
        = ∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, κ n j *
            Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ)) ((q : ℤ) * u + (r₀ : ℤ) - j))) ^ p.toReal :=
          tsum_congr (fun u => by rw [hL u])
      _ ≤ ENNReal.ofReal Ccomp * ∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, κ n j *
              Hf n (P.eval (n₀ : ℤ) - (r₀ : ℤ))
                ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ)) - j))) ^ p.toReal :=
          hcomp (1 / (4 * (q : ℝ))) hβ q hqpos hβq κ kext hkextdata hκsum Hf
            (Bg * ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)) hHfb
            (P.eval (n₀ : ℤ) - (r₀ : ℤ)) (r₀ : ℤ) ((r₀ : ℤ) - P.eval (n₀ : ℤ))
      _ = ENNReal.ofReal Ccomp *
            (∑' u : ℤ, (W ((q : ℤ) * u + ((r₀ : ℤ) - P.eval (n₀ : ℤ)))) ^ p.toReal) := by
          rw [tsum_congr (fun u => by rw [hR u])]
  have hreindex : ∀ n₀ : ℕ,
      (∑ r ∈ Finset.range q,
          ∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - P.eval (n₀ : ℤ)))) ^ p.toReal)
        = ∑' x : ℤ, (W x) ^ p.toReal := by
    intro n₀
    rw [Work.KMTAreas.A7.tsum_int_split_shift_ennreal q hq1 (fun x : ℤ => (W x) ^ p.toReal)
      (-(P.eval (n₀ : ℤ)))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine tsum_congr (fun u => ?_)
    rw [show (q : ℤ) * u + ((r : ℤ) - P.eval (n₀ : ℤ))
        = (r : ℤ) + (u : ℤ) * (q : ℤ) + (-(P.eval (n₀ : ℤ))) from by ring]
  have hsplit : ∀ n₀ : ℕ,
      (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal
        = ∑ r ∈ Finset.range q,
            ∑' u : ℤ, (F ((r : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal := by
    intro n₀
    rw [Work.KMTAreas.A7.eLpNorm_pow_eq_tsum_int (fun y : ℤ => F y n₀) p hpne hptop]
    rw [Work.KMTAreas.A7.tsum_int_split_ennreal q hq1 (fun y : ℤ => (F y n₀) ^ p.toReal)]
  have hSum : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
        p MeasureTheory.Measure.count) ^ p.toReal)
      ≤ (q : ENNReal) * (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)) := by
    calc ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
            p MeasureTheory.Measure.count) ^ p.toReal
        = ∑ n₀ ∈ Finset.range q, ∑ r ∈ Finset.range q,
            ∑' u : ℤ, (F ((r : ℤ) + (u : ℤ) * (q : ℤ)) n₀) ^ p.toReal :=
          Finset.sum_congr rfl (fun n₀ _ => hsplit n₀)
      _ ≤ ∑ n₀ ∈ Finset.range q, ∑ r ∈ Finset.range q, ENNReal.ofReal Ccomp *
            (∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - P.eval (n₀ : ℤ)))) ^ p.toReal) :=
          Finset.sum_le_sum (fun n₀ _ => Finset.sum_le_sum (fun r _ => hpair n₀ r))
      _ = ∑ n₀ ∈ Finset.range q, ENNReal.ofReal Ccomp *
            (∑ r ∈ Finset.range q,
              ∑' u : ℤ, (W ((q : ℤ) * u + ((r : ℤ) - P.eval (n₀ : ℤ)))) ^ p.toReal) := by
          refine Finset.sum_congr rfl (fun n₀ _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ n₀ ∈ Finset.range q, ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal) := by
          refine Finset.sum_congr rfl (fun n₀ _ => ?_)
          rw [hreindex n₀]
      _ = (q : ENNReal) * (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hWpow : (MeasureTheory.eLpNorm W p MeasureTheory.Measure.count) ^ p.toReal
      = ∑' x : ℤ, (W x) ^ p.toReal :=
    Work.KMTAreas.A7.eLpNorm_pow_eq_tsum_int W p hpne hptop
  have hnorm : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q F x) p
        MeasureTheory.Measure.count
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
          (1 / p.toReal) := by
    have h := Work.KMTAreas.A7Hi.eLpNormResidueLpEq p.toReal hppos q F
    rw [hpo] at h
    change MeasureTheory.eLpNorm (Work.KMTAreas.A7.residueLp p.toReal q F) p
      MeasureTheory.Measure.count
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
          (1 / p.toReal)
    exact h
  have hfinal : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q F x) p
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ccomp ^ (1 / p.toReal)) *
        MeasureTheory.eLpNorm W p MeasureTheory.Measure.count := by
    have hrpow : ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ :=
      ENNReal.rpow_neg_one (q : ENNReal)
    calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q F x) p
          MeasureTheory.Measure.count
        = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
            (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p MeasureTheory.Measure.count) ^ p.toReal)
            (1 / p.toReal) := hnorm
      _ ≤ ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ((q : ENNReal) *
            (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal)))) (1 / p.toReal) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hSum) (by positivity)
      _ = ENNReal.rpow (ENNReal.ofReal Ccomp * (∑' x : ℤ, (W x) ^ p.toReal))
            (1 / p.toReal) := by
          rw [hrpow, ← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
      _ = ENNReal.ofReal Ccomp ^ (1 / p.toReal)
            * (∑' x : ℤ, (W x) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal (Ccomp ^ (1 / p.toReal)) *
            MeasureTheory.eLpNorm W p MeasureTheory.Measure.count := by
          rw [show (1 : ℝ) / p.toReal = (p.toReal)⁻¹ from one_div _]
          rw [← ENNReal.ofReal_rpow_of_nonneg hCcomp.le
            (by positivity : (0 : ℝ) ≤ (p.toReal)⁻¹)]
          rw [← hWpow]
          rw [ENNReal.rpow_rpow_inv hppos.ne'
            (MeasureTheory.eLpNorm W p MeasureTheory.Measure.count)]
  change ENNReal.ofReal (Ccomp ^ (1 / p.toReal)) *
      MeasureTheory.eLpNorm W p MeasureTheory.Measure.count ≥
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q F x) p
        MeasureTheory.Measure.count
  exact hfinal

end

end Work.KMTAreas.A7Hi
