/-
# `Work.A7MixedG.FiberLargeResidueHolds`

The per-residue large-scale fibre estimate of the mixed `g`-side (KMT §8), i.e.

`Work.KMTAreas.A7MixedG.FiberLargeResidue P p₂ hdeg hp₂ htp₂`.

## Route

* `fiberOp_var_shift_largeScales` — the **per-shift (per-residue) fibre sampling estimate**: for
  a bounded input `g`, a family of scales `N : ℕ → ℕ` and a clipping predicate `S`, the
  `ℓᵖ(Vʳ)`-norm of the *twisted* fibre `fiberOp ρ l₂ (mStargF d U) M (if S n then Tex ρ l₂ φ_n g else 0)`
  (an *arbitrary* shift `M : ℤ`) is bounded by the `ℓᵖ(Vʳ)`-norm of the family itself, with a
  constant independent of `l₂, k₂, U, t, g, N, S, M`.  This is the per-residue strengthening of
  `Work.KMTAreas.A7Hi.fiberVarSamplingG_large_bdd`; the proof is that proof (slice algebra →
  coset comparison `convSublatticeCosetCompareBdd` → re-summation of the matched cosets), with the
  residue *average* of the original replaced by the re-summation
  `∑_{r<q} ∑_z (fiberOp ... (qz + r))^p = ∑_x (fiberOp ... x)^p`.
* `fiberVarSamplingGShift_holds` — the `U := uScale ρ L` instance, i.e. verbatim
  `Work.KMTAreas.A7Hi.fiberVarSamplingGShift`.
* `fiberLargeResidueLargeScalesProp_holds` — the assembly (the `L ≤ T ρ` Young branch and the
  `L > T ρ` sampling branch) proving the crux `FiberLargeResidueLargeScalesProp`.
* `FiberLargeResidueHolds` — `FiberLargeResidueCore_of_largeScales` applied to the crux.
-/
import Mathlib
import Submission.Work.KMTAreas.A7MixedG.FiberLargeResidue

set_option maxHeartbeats 2000000

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

namespace Work.A7MixedG

open PointwiseErgodicTheorems

noncomputable section

/-! ## §1.  The per-shift fibre sampling estimate -/

/-- **The per-shift (per-residue) fibre sampling estimate of the `g`-side** (KMT §8, the
per-residue form of `fiberVarSamplingG_large_bdd`).

For `ρ ∈ (0,1]`, `p ∈ (1,∞)`, `r > 2` there is a constant `C` such that for every exact-height
`l₂`, every cut scale `U ≥ 1`, every `t`, every bounded `g`, every family of scales `N` and
clipping predicate `S` satisfying the quantitative Shannon hypotheses

* (Farey) `8·2^{k₂}·arithQ ρ l₂ ≤ N n` for all `n`,
* (strict main regime) `k₂ + 2U + 1 ≤ Log (N n)` for all `n`,
* (non-aliasing) `NonAliasing (-(2U)) (iwArithFreqs ρ l₂)`,

and every shift `M : ℤ`, the twisted fibre of the family
`(if S n then Tex ρ l₂ (φ̃_{N n, k₂, t}) g else 0)` is controlled by the family itself. -/
theorem fiberOp_var_shift_largeScales
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₂ k₂ U : ℕ), 1 ≤ U → ∀ (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ),
        (∀ x : ℤ, ‖g x‖ ≤ Bg) →
        ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₂ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          ∀ M : ℤ,
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                (Work.KMTAreas.A7.mStargF P.natDegree U) M
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
              p MeasureTheory.Measure.count := by
  classical
  set pR : ℝ := p.toReal with hpR
  have hpR1 : 1 < pR := by
    rw [hpR, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hpt)).mpr hp
  have hpR0 : 0 < pR := lt_trans zero_lt_one hpR1
  have hpof : ENNReal.ofReal pR = p := by
    rw [hpR]
    exact ENNReal.ofReal_toReal (ne_of_lt hpt)
  have h1pR : (0 : ℝ) ≤ 1 / pR := by positivity
  obtain ⟨Ceng, hCengpos, heng⟩ :=
    Work.KMTAreas.A7.convSublatticeCosetCompareBdd pR hpR1 r (le_of_lt (lt_trans (by norm_num) hr))
  refine ⟨Ceng ^ (1 / pR), Real.rpow_pos_of_pos hCengpos _, ?_⟩
  intro l₂ k₂ U hU t g Bg hBg N S _ hfarey hstrict hna M
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ l₂ with hq
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ with hA
  set φ : ℕ → ℝ → ℂ := fun n => Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t with hφ
  set κ : ℕ → ℤ → ℂ := fun n j => Work.KMTAreas.A7.cw (φ n) j with hκ
  set Hf : ℕ → ℤ → ℤ → ℂ :=
    fun n y z => if S n then Work.KMTAreas.A7.sliceInput A g y z else 0 with hHf
  set F : ℤ → ENNReal := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) M
      (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) y) with hF
  set W : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x) with hW
  have hqpos : 0 < q := by
    rw [hq]
    exact Work.KMTAreas.A7.arithQ_pos ρ l₂
  have hq1 : 1 ≤ q := hqpos
  have hnaNew : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) :=
    Work.KMTAreas.A7MixedG.NonAliasing_subset hna
      (fun α hα => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
  have hqnsmul : ∀ α ∈ A, q • α = 0 := by
    intro α hα
    have hα' : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ := hA ▸ hα
    have h1 : Work.KMTAreas.A7.arithQ ρ l₂ • α = 0 :=
      Work.KMTAreas.A7.arithQ_nsmul_eq_zero (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα')
    rw [hq]
    exact h1
  have hφint : ∀ n : ℕ, Integrable (φ n) := by
    intro n
    rw [hφ]
    exact Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree (N n) k₂ t
  have hφsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (φ n) j‖) := by
    intro n
    rw [hφ]
    exact Work.KMTAreas.A7.summable_cw_varphitildeNt P P.natDegree (N n) k₂ t
  have hφsupp : ∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1) := by
    intro n ξ hξ
    rw [hφ] at hξ
    exact Work.KMTAreas.A7Hi.varphitildeNt_support_strict_g P hd (N n) k₂ U t (hstrict n) ξ hξ
  have hfareyU : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N n : ℝ) := by
    intro n
    rw [hq]
    exact hfarey n
  have hβ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  have hβq : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have h : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      field_simp
    rw [h]
  have hφsuppq : ∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 → |ξ| ≤ 1 / (4 * (q : ℝ)) := by
    intro n ξ hξ
    rw [hφ] at hξ
    exact Work.KMTAreas.A7Hi.varphitildeNt_support_le_quarter_g P hd q hq1 (N n) k₂ t
      (hfareyU n) ξ hξ
  have hκsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖κ n j‖) := by
    intro n
    rw [hκ]
    exact hφsum n
  have hB0 : 0 ≤ Bg := le_trans (norm_nonneg (g 0)) (hBg 0)
  have hHfb : ∀ n : ℕ, ∀ y z : ℤ, ‖Hf n y z‖ ≤ Bg * (A.card : ℝ) := by
    intro n y z
    rw [hHf]
    by_cases hSn : S n
    · simp only [hSn, if_true]
      exact Work.KMTAreas.A7Hi.norm_sliceInput_le A g Bg hBg y z
    · simp only [hSn, if_false, norm_zero]
      exact mul_nonneg hB0 (Nat.cast_nonneg _)
  -- ### the band-`1/(4q)` continuous extension of the kernel `κ`
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
      rw [hkext, hφ]
      simp only [Work.KMTAreas.A7Hi.varphitildeNtSch_g_coe]
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
      refine hφsuppq n ξ ?_
      simp only [hφ]
      rwa [← Work.KMTAreas.A7Hi.varphitildeNtSch_g_apply]
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
  -- ### the per-coset comparison
  have hpair : ∀ r₀ : ℤ,
      (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        ≤ ENNReal.ofReal Ceng *
          (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
    intro r₀
    have hL : ∀ z : ℤ, F ((q : ℤ) * z + r₀)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j)) := by
      intro z
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U) M
            (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
            ((q : ℤ) * z + r₀))
          = fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7Hi.fiberOp_mStargF_Sclip ρ hρ hρ1 P l₂ U hU hd hnaNew (φ n)
          (hφint n) (hφsum n) (hφsupp n) g Bg hBg (S n) M]
        simp only [ite_apply, Pi.zero_apply]
        rw [Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg hqnsmul
          M r₀ z]
        exact (Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + r₀) (S n)).symm
      simp only [hF]
      rw [hfun]
    have hR : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
          κ n j * Hf n (M - r₀) ((q : ℤ) * z + (r₀ - M) - j))
        = W ((q : ℤ) * z + (r₀ - M)) := by
      intro z
      have hfun : (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))
          = fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
              ((q : ℤ) * z + (r₀ - M)) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + (r₀ - M)) (S n)]
        simp only [ite_apply, Pi.zero_apply]
        by_cases hSn : S n
        · simp only [hSn, if_true]
          rw [← Work.KMTAreas.A7Hi.fiberOp_zero_eq_Tex ρ l₂ (φ n) (hφint n) g]
          have hy : (M - r₀) = 0 - ((r₀ - M)) := by ring
          rw [hy]
          rw [← Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg
            hqnsmul 0 (r₀ - M) z]
        · simp only [hSn, if_false]
      simp only [hW]
      rw [hfun]
    calc (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        = ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j))) ^ pR :=
          tsum_congr (fun z => by rw [hL z])
      _ ≤ ENNReal.ofReal Ceng * ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))) ^ pR :=
          heng (1 / (4 * (q : ℝ))) hβ q hqpos hβq κ kext hkextdata hκsum Hf
            (Bg * (A.card : ℝ)) hHfb (M - r₀) r₀ (r₀ - M)
      _ = ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
          rw [tsum_congr (fun z => by rw [hR z])]
  -- ### the total-sum bound
  have hkey : (∑' x : ℤ, (F x) ^ pR) ≤ ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
    rw [Work.KMTAreas.A7Hi.periodDecompLocal q hqpos (fun x : ℤ => (F x) ^ pR)]
    calc ∑ r ∈ Finset.range q, ∑' z : ℤ, (F ((q : ℤ) * z + (r : ℤ))) ^ pR
        ≤ ∑ r ∈ Finset.range q, ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) :=
          Finset.sum_le_sum (fun r _ => hpair (r : ℤ))
      _ = ENNReal.ofReal Ceng * (∑ r ∈ Finset.range q,
            ∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
          rw [Work.KMTAreas.A7Hi.cosetShift_decomp q hqpos (fun x : ℤ => (W x) ^ pR) M]
  -- ### the norm comparison
  have hgoal : MeasureTheory.eLpNorm F (ENNReal.ofReal pR) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ceng ^ (1 / pR)) *
        MeasureTheory.eLpNorm W (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
    eLpNorm_le_of_tsum_rpow_le hpR0 hCengpos hkey
  rwa [← hpof]

/-! ## §2.  The `uScale` instance (the per-shift fibre sampling estimate of the mixed range) -/

/-- **The per-shift form of the mixed `g`-side fibre sampling estimate** — the statement of
`Work.KMTAreas.A7Hi.fiberVarSamplingGShift`, proved from `fiberOp_var_shift_largeScales` at the
cut scale `U := uScale ρ (max l₂ (max k₁ k₂))`. -/
theorem fiberVarSamplingGShift_holds (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
          ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S] (M : ℤ),
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₂ + 2 * (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)) : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                (Work.KMTAreas.A7.mStargF P.natDegree
                  (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)))) M
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
            p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hpt
  obtain ⟨C, hC, hmain⟩ :=
    fiberOp_var_shift_largeScales ρ hρ hρ1 P (by omega) p hp hpt r hr
  refine ⟨C, hC, ?_⟩
  intro l₂ k₁ k₂ t g Bg hBg N S _ M ht hfarey hstrict hna
  exact hmain l₂ k₂ (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)))
    (Work.KMTAreas.A7.one_le_uScale_bdd hρ.le _) t g Bg hBg N S hfarey hstrict hna M

end

end Work.A7MixedG

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## §3.  The large-scale crux `FiberLargeResidueLargeScalesProp`

This is the assembly of `Submission/Work/KMTAreas/A7/mixedGFibreLargeScalesCrux.lean` with its
per-shift input `Work.KMTAreas.A7Hi.fiberVarSamplingGShift` replaced by the proved
`Work.A7MixedG.fiberVarSamplingGShift_holds`. -/

/-- The loss weight at `c = 0` is `1`. -/
theorem lossWeight_zero_local (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
  rw [lossWeight]
  have h1 : (0 : ℝ) * ρ * lmaxR l₁ l₂ k₁ k₂ = 0 := by ring
  rw [h1, Real.rpow_zero, Real.rpow_zero, mul_one]

/-- **The guarded `g`-side family of the mixed range is the `l₁ = 0` instance of `Gcl`.** -/
theorem GmixedFam_eq_Gcl_local (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (hl₂ : l₂ ≠ 0) :
    GmixedFam ρ P C₀ a l₂ k₁ k₂ t g = Gcl ρ P C₀ a 0 l₂ k₁ k₂ t g := by
  funext n x
  simp only [GmixedFam, Gcl, loGuard, core, Tm, Tex, diffFreqs_eq_iwArithFreqsNew hl₂]

theorem fiberLargeResidueLargeScalesProp_holds (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) :
    Work.KMTAreas.A7MixedG.FiberLargeResidueLargeScalesProp P p₂ hdeg hp₂ htp₂ := by
  intro C₀ r hC₀ hr
  -- ### the `ρ`-dependent threshold packaging the three arithmetic inputs of the fibre estimate
  have h_ex : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ B : ℕ,
      (∀ (l₂ k₁ k₂ N : ℕ),
        splitCut ρ (max l₂ (max k₁ k₂)) < N → B < max l₂ (max k₁ k₂) →
          (8 * (2 : ℝ) ^ k₂ * (arithQ ρ l₂ : ℝ) ≤ (N : ℝ)) ∧
          (k₂ + 2 * (uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat)) ∧
      (∀ (l L : ℕ), l ≤ L → B ≤ L →
        Work.Analysis.IonescuWainger.NonAliasing (-(2 * (uScale ρ L : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) ∧
      (∀ (l₂ k₁ k₂ : ℕ), B ≤ max l₂ (max k₁ k₂) →
        loMixedU ρ P.natDegree l₂ k₁ k₂ = uScale ρ (max l₂ (max k₁ k₂))) := by
    intro ρ hρ hρ1
    obtain ⟨B₁, hB₁⟩ := Work.KMTAreas.A7Hi.farey_and_strict_of_large_L_g ρ hρ hρ1
    obtain ⟨B₂, hB₂⟩ := Work.KMTAreas.A7.exists_nonAliasing_uScale ρ hρ hρ1
    obtain ⟨B₃, hB₃⟩ := Work.KMTAreas.A7MixedG.loMixedU_eq_uScale_of_large ρ hρ P.natDegree
    refine ⟨max (B₁ + 1) (max B₂ B₃), ?_, ?_, ?_⟩
    · intro l₂ k₁ k₂ N hsplit hlt
      have hmax : max (max 0 l₂) (max k₁ k₂) = max l₂ (max k₁ k₂) := by omega
      have hB₁lt : B₁ < max l₂ (max k₁ k₂) := by
        have hle : B₁ + 1 ≤ max (B₁ + 1) (max B₂ B₃) := le_max_left _ _
        omega
      have hsplit' : splitCut ρ (max (max 0 l₂) (max k₁ k₂)) < N := by rw [hmax]; exact hsplit
      have h := hB₁ 0 l₂ k₁ k₂ N hsplit' (by rw [hmax]; exact hB₁lt)
      rw [hmax] at h
      refine ⟨?_, h.2⟩
      simpa only [max_eq_right (Nat.zero_le l₂)] using h.1
    · intro l L hl hL
      have h2 : B₂ ≤ L :=
        le_trans (le_trans (le_max_left B₂ B₃) (le_max_right (B₁ + 1) (max B₂ B₃))) hL
      exact hB₂ l L hl h2
    · intro l₂ k₁ k₂ hL
      have h3 : B₃ ≤ max l₂ (max k₁ k₂) :=
        le_trans (le_trans (le_max_right B₂ B₃) (le_max_right (B₁ + 1) (max B₂ B₃))) hL
      exact hB₃ l₂ k₁ k₂ h3
  classical
  -- ### the threshold as a *function* of `ρ`
  let T : ℝ → ℕ := fun ρ => if h : 0 < ρ ∧ ρ ≤ 1 then Classical.choose (h_ex ρ h.1 h.2) else 0
  have hTspec : ∀ ρ (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
      (∀ (l₂ k₁ k₂ N : ℕ),
        splitCut ρ (max l₂ (max k₁ k₂)) < N → T ρ < max l₂ (max k₁ k₂) →
          (8 * (2 : ℝ) ^ k₂ * (arithQ ρ l₂ : ℝ) ≤ (N : ℝ)) ∧
          (k₂ + 2 * (uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat)) ∧
      (∀ (l L : ℕ), l ≤ L → T ρ ≤ L →
        Work.Analysis.IonescuWainger.NonAliasing (-(2 * (uScale ρ L : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) ∧
      (∀ (l₂ k₁ k₂ : ℕ), T ρ ≤ max l₂ (max k₁ k₂) →
        loMixedU ρ P.natDegree l₂ k₁ k₂ = uScale ρ (max l₂ (max k₁ k₂))) := by
    intro ρ hρ hρ1
    have hchoose : T ρ = Classical.choose (h_ex ρ hρ hρ1) := by
      simp only [T]
      rw [dif_pos (show 0 < ρ ∧ ρ ≤ 1 from ⟨hρ, hρ1⟩)]
    rw [hchoose]
    exact Classical.choose_spec (h_ex ρ hρ hρ1)
  -- ### the Young constant of the small-scale branch
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num : (1 : NNReal) ≤ 2) hr)
  obtain ⟨Cyoung, hCyoungpos, hYoung⟩ :=
    Work.KMTAreas.A7MixedG.fiberOpP_young_bound P (by omega) r hr1 p₂ hp₂ htp₂ (Bfun := T)
  -- ### the fibre-sampling constant of the large-scale branch
  have hfib := Work.A7MixedG.fiberVarSamplingGShift_holds P hdeg r hr
  -- ### the existential constants of the target
  refine ⟨0, le_refl 0, 1, one_pos, 0, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨hTharf, hTna, hTu⟩ := hTspec ρ hρ hρ1
  obtain ⟨Cfib', hCfib'pos, hfib'⟩ := hfib ρ hρ hρ1 p₂ hp₂ htp₂
  set Cbig : NNReal := max (⌈Cyoung ρ⌉₊ : NNReal) (⌈Cfib'⌉₊ : NNReal) with hCbigdef
  have hCfle : ENNReal.ofReal (Cyoung ρ) ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) :=
    calc ENNReal.ofReal (Cyoung ρ) ≤ ((⌈Cyoung ρ⌉₊ : NNReal) : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCffle : ENNReal.ofReal Cfib' ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) :=
    calc ENNReal.ofReal Cfib' ≤ ((⌈Cfib'⌉₊ : NNReal) : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨fun _ : NNReal => (max 1 Cbig : NNReal), ?_⟩
  intro a Λ l₂ k₁ k₂ t g n₀ hΛ hlac ha hl₂ ht hgb hBL hna hguard
  have hl₂0 : l₂ ≠ 0 := by omega
  obtain ⟨Bg, hBg⟩ := hgb
  have hgB : ∀ y : ℤ, ‖g y‖ ≤ Bg := fun y => hBg ⟨y, rfl⟩
  set L : ℕ := max l₂ (max k₁ k₂) with hLdef
  set q : ℕ := arithQ ρ l₂ with hqdef
  set U : ℕ := uScale ρ (max l₂ (max k₁ k₂)) with hUdef
  have hlossW : lossWeight 0 ρ 0 l₂ k₁ k₂ = 1 := lossWeight_zero_local ρ 0 l₂ k₁ k₂
  have hlw1 : (1 : ENNReal) ≤ ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := by
    rw [hlossW, ENNReal.ofReal_one]
  have hE : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count := by
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
            * 1 := (mul_one _).symm
      _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := mul_le_mul_of_nonneg_left hlw1 bot_le
      _ = ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := mul_comm _ _
  by_cases hcase : L ≤ T ρ
  · -- ### Case 1: the small-scale (Young) branch
    have hl₂T : l₂ ≤ T ρ := by
      have h1 : l₂ ≤ L := by rw [hLdef]; exact le_max_left l₂ (max k₁ k₂)
      exact le_trans h1 hcase
    have hY := hYoung ρ hρ l₂ k₁ k₂ hl₂T n₀ (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g)
    refine hY.trans ?_
    calc ENNReal.ofReal (Cyoung ρ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right hCfle bot_le
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * (ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
                MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hE bot_le
      _ = ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := by
          rw [mul_assoc]
  · -- ### Case 2: the large-scale fibre estimate
    have hTlt : T ρ < L := lt_of_not_ge hcase
    have hTL : T ρ ≤ L := le_of_lt hTlt
    have hsplit : ∀ n : ℕ, loGuard ρ C₀ a 0 l₂ k₁ k₂ n → splitCut ρ L < Nat.floor (a n) := by
      intro n hn
      rw [hLdef]
      exact Work.KMTAreas.A7MixedG.splitCut_of_loGuard hn
    set S : ℕ → Prop := fun n => loGuard ρ C₀ a 0 l₂ k₁ k₂ n with hSdef
    haveI : DecidablePred S := by intro n; rw [hSdef]; infer_instance
    set K : ℕ := 2 ^ (k₂ + 2 * U + 4) * (q + 1) with hKdef
    set N' : ℕ → ℕ := fun n => if S n then Nat.floor (a n) else K with hNdef
    have hfareyN' : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N' n : ℝ) := by
      intro n
      by_cases hSn : S n
      · have hsplit' : splitCut ρ L < Nat.floor (a n) := hsplit n (by simpa only [hSdef] using hSn)
        have h := (hTharf l₂ k₁ k₂ (Nat.floor (a n))
          (by rw [← hLdef]; exact hsplit') hTlt).1
        rw [hNdef]
        simp only [hSn, if_true]
        simpa only [hqdef] using h
      · rw [hNdef]
        simp only [hSn, if_false]
        have hKge : 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (K : ℝ) := by
          rw [hKdef]
          push_cast
          have hpow : (2 : ℝ) ^ (k₂ + 2 * U + 4)
              = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4) := by
            rw [show k₂ + 2 * U + 4 = k₂ + (2 * U + 4) from by ring, pow_add]
          rw [hpow]
          have h3 : (3 : ℕ) ≤ 2 * U + 4 :=
            le_trans (by norm_num : (3 : ℕ) ≤ 4) (Nat.le_add_left 4 (2 * U))
          have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (2 * U + 4) := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num]
            exact pow_le_pow_right₀ (by norm_num) h3
          have hk : (0 : ℝ) < (2 : ℝ) ^ k₂ := by positivity
          have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          nlinarith [h8, hqnn, hk, mul_nonneg hk.le hqnn]
        exact hKge
    have hstrictN' : ∀ n : ℕ, k₂ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (N' n)).toNat := by
      intro n
      by_cases hSn : S n
      · have hsplit' : splitCut ρ L < Nat.floor (a n) := hsplit n (by simpa only [hSdef] using hSn)
        have h := (hTharf l₂ k₁ k₂ (Nat.floor (a n))
          (by rw [← hLdef]; exact hsplit') hTlt).2
        rw [hNdef]
        simp only [hSn, if_true]
        simpa only [hUdef] using h
      · rw [hNdef]
        simp only [hSn, if_false]
        have hle : 2 ^ (k₂ + 2 * U + 4) ≤ max K 2 := by
          rw [hKdef]
          refine le_trans ?_ (le_max_left _ _)
          exact Nat.le_mul_of_pos_right _ (by omega : 0 < q + 1)
        have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hle
        have hlogN : (Work.Analysis.EndVar.logN K).toNat = Nat.log 2 (max K 2) := by
          rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
        rw [hlogN]
        omega
    have hnaU : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
      have h := hTna l₂ L (by rw [hLdef]; exact le_max_left l₂ (max k₁ k₂)) hTL
      rw [hLdef] at h
      rw [hUdef]
      exact h
    have hcut : mStargF P.natDegree U = GmixedKer ρ P l₂ k₁ k₂ := by
      rw [Work.KMTAreas.A7MixedG.GmixedKer_eq,
        hTu l₂ k₁ k₂ (by rw [← hLdef]; exact hTL), ← hUdef]
    have hfam : ∀ n : ℕ, (if S n then Tex ρ l₂
          (varphitildeNt P P.natDegree (N' n) k₂ t) g else 0)
        = GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n := by
      intro n
      rw [GmixedFam_eq_Gcl_local ρ P C₀ a l₂ k₁ k₂ t g hl₂0]
      by_cases hn : S n
      · have hc : core ρ C₀ 0 l₂ k₁ k₂ a n := by
          simpa only [hSdef, loGuard, core] using hn
        have hNn : N' n = Nat.floor (a n) := by
          rw [hNdef]; simp only [hn, if_true]
        simp only [Gcl, hn, hc, if_true, hNn]
      · have hc : ¬ core ρ C₀ 0 l₂ k₁ k₂ a n := by
          simpa only [hSdef, loGuard, core] using hn
        simp only [Gcl, hn, hc, if_false]
    have hbdd := hfib' l₂ k₁ k₂ t g Bg hgB N' S (P.eval n₀) ht hfareyN' hstrictN' hnaU
    simp only [hfam] at hbdd
    have hfiber : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => fiberOp ρ l₂ (mStargF P.natDegree U) (P.eval n₀)
            (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => fiberOpP ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂) n₀
            (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x)) := by
      funext x
      refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
      show fiberOp ρ l₂ (mStargF P.natDegree U) (P.eval n₀)
          (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x
        = fiberOp ρ l₂ (GmixedKer ρ P l₂ k₁ k₂) (P.eval n₀)
          (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x
      rw [hcut]
    rw [hfiber] at hbdd
    refine hbdd.trans ?_
    calc ENNReal.ofReal Cfib' * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right hCffle bot_le
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * (ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
                MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hE bot_le
      _ = ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := by
          rw [mul_assoc]

end

end Work.KMTAreas.A7

namespace Work.A7MixedG

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The per-residue large-scale fibre estimate of the mixed range (KMT §8), obtained from its
large-scale branch (`FiberLargeResidueLargeScalesProp`). -/
theorem FiberLargeResidueHolds (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) :
    Work.KMTAreas.A7MixedG.FiberLargeResidue P p₂ hdeg hp₂ htp₂ :=
  Work.KMTAreas.A7MixedG.FiberLargeResidueCore_of_largeScales P p₂ hdeg hp₂ htp₂
    (Work.KMTAreas.A7.fiberLargeResidueLargeScalesProp_holds P p₂ hdeg hp₂ htp₂)

end Work.A7MixedG
