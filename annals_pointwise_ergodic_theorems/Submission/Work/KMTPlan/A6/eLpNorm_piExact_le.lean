import Mathlib
import Submission.Work.KMTPlan.A6.besselG
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Port.Aesm

/-!
# `eLpNorm_piExact_le` is **FALSE** — counterexample, diagnosis and the corrected statement

## What was requested

For every `ρ ∈ (0,1]`, every `l : ℕ`, every height `c : ℤ` and every `g : ℤ → ℂ`,

`‖Π_{l,≤c} g‖_{ℓ²(ℤ)} ≤ 4 · #(diffFreqs ρ l) · ‖g‖_{ℓ²(ℤ)}`,  where `Π_{l,≤c} = Π_{≤l,≤c} − Π_{≤l−1,≤c}`.

## Why it is false

`Π_{l,≤c}` is the Fourier multiplier with symbol `piSym ρ l c = iwSymbolSet (diffFreqs ρ l) (etSym c)`
(`piSym_eq`/`piExact_eq_multiplier` in `Work.KMTPlan.A6.besselG`), where
`etSym c = periodize (etaCut kmtEta c)` is the periodisation of the bump `η(·/2^c)`.  The claimed
constant `4 · #(diffFreqs ρ l)` is a bound on the *sup norm of the symbol* only in the regime
`2^c ≲ 1`: the constant `4` is the number of periods of `η(·/2^c)` that can overlap when
`c ≤ 1`.  For `c ≥ 2` the periodisation genuinely adds up: each `k ∈ ℤ` with `|u + k| ≤ 2^{c-1}`
contributes `1`, so at every `ξ`

  `etSym c ξ ≥ 2^c − 1`   (in real part),

and the operator `Π_{l,≤c}` is the multiplier by a symbol of sup norm `≍ 2^c` — the paper's
projections are only bounded uniformly in the *good major-arc* regime `2^c ≲ 2^{-C_ρ 2^{ρ l}}`
(negative heights), cf. `Work.Analysis.IonescuWainger.GoodMajorArcs` and
`Work.KMTPlan.A6.norm_etSym_le_four` below.

## The counterexample (formally verified in this file; see `not_eLpNorm_piExact_le`)

Take `ρ = 1`, `l = 0`, `c = 3` and `g = kmtDiracZero = δ_0`.  Then

* `diffFreqs ρ l = {(0 : Circle)}` has cardinality `1`, so the claimed constant is `4`;
* `eLpNorm δ_0 2 Measure.count = 1`;
* `piExact (kmtPj 1) 0 3 δ_0` is the sequence of Fourier coefficients of `etSym 3`, and its value
  at `0` equals `∫ ξ, etSym 3 ξ ∂circleMeasure`, whose real part is `≥ 8` because
  `etSym 3 ξ ≥ 8` at *every* `ξ` (`etSym_three_re_ge`) and `circleMeasure` is a probability
  measure.  Hence `eLpNorm (piExact (kmtPj 1) 0 3 δ_0) 2 Measure.count ≥ 8 > 4`.

`eLpNorm_piExact_counterexample` is that instance, and `not_eLpNorm_piExact_le` is the formal
negation of the requested statement.

## The corrected statements (both **proved**, axiom-clean, in this file)

* `eLpNorm_piExact_le_of_height_le_one` — the requested inequality with the single extra
  hypothesis `c ≤ 1` and the *same* constant `4 · #(diffFreqs ρ l)`:
  `eLpNorm (piExact (kmtPj ρ) l c g) 2 count ≤ ((4 * #(diffFreqs ρ l) : ℕ) : ENNReal) * eLpNorm g 2 count`.
  This is the regime in which the constant `4` is correct (`norm_etSym_le_four`: at most four
  periods of `η(·/2^c)` overlap, so `‖etSym c‖_∞ ≤ 4`).
* `eLpNorm_piExact_le_of_two_pow_le_half` — the same with the hypothesis `2^c ≤ 1/2`, which is
  the form carried by the surrounding A6 files (`Tle_piExact_eq_convOp`,
  `piExact_eq_convOp`, `MdlSliceLinGOne*`).

For *arbitrary* `c` no constant independent of `c` can work: the correct bound carries the
factor `≍ max 1 2^{c+1}`.  Alternatively one can use the family form
`Work.KMTAreas.A7.eLpNorm_piExact_le` at `q = 2`, which takes the `ℓ²` bounds of the individual
projections `kmtProj ρ l' k'` as a hypothesis (as in
`Work.KMTPlan.A6.MdlSliceLinNeg1.mdlF_two_bound`); those bounds are
`eLpNorm_iwConv_two_le_of_symbol_bound` applied to `‖etSym k'‖_∞`.

-/

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-! ## The counterexample -/

/-- The Dirac mass at `0` on `ℤ`, as a function `ℤ → ℂ`. -/
def kmtDiracZero : ℤ → ℂ := fun n => if n = 0 then 1 else 0

lemma kmtDiracZero_mul (K : ℤ → ℂ) : K 0 * kmtDiracZero (0 - 0) = K 0 := by
  rw [show (0 : ℤ) - 0 = 0 from rfl, kmtDiracZero, if_pos rfl, mul_one]

lemma kmtDiracZero_apply_ne {j : ℤ} (hj : j ≠ 0) : kmtDiracZero (0 - j) = 0 := by
  rw [kmtDiracZero, if_neg (by omega : (0 : ℤ) - j ≠ 0)]

/-- The arithmetic frequency set of height `≤ 0` consists of `0` alone. -/
lemma iwArithFreqs_one_zero_A6 :
    Work.Analysis.IonescuWainger.iwArithFreqs 1 0 =
      {(0 : Work.Analysis.IonescuWainger.Circle)} := by
  rw [Work.Analysis.IonescuWainger.iwArithFreqs,
    show Work.Analysis.IonescuWainger.iwP 1 0 = {1} from by
      rw [Work.Analysis.IonescuWainger.iwP, if_pos (Nat.zero_le _)]
      norm_num]
  simp

/-- **The value of the exact-height projection at `0`.**  For the Dirac mass `δ_0`, the exact
height projection coincides with `fourierCoeff (etSym c) 0`, i.e. with the `0`-th Fourier
coefficient of the symbol. -/
lemma piExact_kmtDiracZero_zero (c : ℤ) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 c kmtDiracZero 0
      = Work.Analysis.IWMultiplier.iwKernel (Work.KMTPlan.A6.etSym c) 0 := by
  rw [Work.Analysis.EndVar.piExact, if_pos rfl, Work.KMTContract.kmtPj_proj,
    Work.KMTContract.kmtProj_apply, Work.KMTPlan.A6.etSym, iwArithFreqs_one_zero_A6]
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet
      ({(0 : Work.Analysis.IonescuWainger.Circle)} : Finset _)
      (Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c))
      = Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) := by
    funext ξ
    simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  rw [hsym, tsum_eq_single 0]
  · exact kmtDiracZero_mul _
  · intro j hj
    rw [kmtDiracZero_apply_ne hj, mul_zero]

/-- The `0`-th Fourier coefficient is the integral of the symbol against the circle measure. -/
lemma iwKernel_zero_eq_integral (F : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IWMultiplier.iwKernel F 0 = ∫ ξ, F ξ ∂Work.Analysis.IonescuWainger.circleMeasure := by
  rw [Work.Analysis.IWMultiplier.iwKernel]
  simp [fourierCoeff]

/-- `eLpNorm · 2 Measure.count` dominates the value at any single point. -/
lemma eLpNorm_count_ge_enorm_apply (f : ℤ → ℂ) (n : ℤ) :
    ‖f n‖ₑ ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num),
    MeasureTheory.lintegral_count, show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  calc ‖f n‖ₑ = (‖f n‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ (∑' i : ℤ, ‖f i‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun i : ℤ => ‖f i‖ₑ ^ (2:ℝ)) n) (by norm_num)

/-- The `ℓ²` norm of the Dirac mass is `1`. -/
lemma eLpNorm_kmtDiracZero :
    MeasureTheory.eLpNorm kmtDiracZero 2 MeasureTheory.Measure.count = 1 := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num),
    MeasureTheory.lintegral_count, show (2 : ℝ≥0∞).toReal = 2 by norm_num,
    tsum_eq_single 0]
  · simp [kmtDiracZero]
  · intro n hn
    simp [kmtDiracZero, hn]

/-- At `ρ = 1`, `l = 0` the exact-height frequency set has cardinality `1`, so the claimed
constant is `4 · 1 = 4`. -/
lemma diffFreqs_one_zero_card : (Work.KMTAreas.A7.diffFreqs 1 0).card = 1 := by
  rw [Work.KMTAreas.A7.diffFreqs, if_pos rfl, iwArithFreqs_one_zero_A6]
  simp

/-- **At height `2^c` with `c = 3` the periodised cutoff is at least `8` everywhere.**  The eight
integers `k ∈ [-4,3]` satisfy `|u + k| ≤ 4 = 2^{c-1}` for every representative `u ∈ [0,1)`, hence
contribute `1` each; all other summands are non-negative. -/
lemma etSym_three_re_ge (ξ : Work.Analysis.IonescuWainger.Circle) :
    (8:ℝ) ≤ (Work.KMTPlan.A6.etSym 3 ξ).re := by
  rw [Work.KMTPlan.A6.etSym, Work.Analysis.IonescuWainger.periodize]
  set u : ℝ := (AddCircle.equivIco (1:ℝ) 0 ξ).val with hu
  have huI : u ∈ Set.Ico (0:ℝ) 1 := by
    rw [hu]; simpa using (AddCircle.equivIco (1:ℝ) 0 ξ).2
  rw [Set.mem_Ico] at huI
  have hzero : ∀ n : ℤ, n ∉ Finset.Icc (-8:ℤ) 8 →
      Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta 3 (u + n) = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and, not_le] at hn
    refine Work.KMTPlan.A6.etaCut_eq_zero_of_le 3 ?_
    rw [show (2:ℝ) ^ (3:ℤ) = 8 by norm_num]
    rcases lt_or_ge n (-8) with h | h
    · have hn9 : (n:ℝ) ≤ -9 := by exact_mod_cast (by omega : n ≤ -9)
      have hlt : u + (n:ℝ) ≤ -8 := by linarith [huI.2]
      rw [abs_of_neg (by linarith)]
      linarith
    · have hn9 : (9:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 9 ≤ n)
      rw [abs_of_pos (by linarith [huI.1])]
      linarith
  rw [tsum_eq_sum hzero, Complex.re_sum]
  have hstep : (∑ n ∈ Finset.Icc (-4:ℤ) 3,
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta 3 (u + n)).re)
      ≤ ∑ n ∈ Finset.Icc (-8:ℤ) 8,
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta 3 (u + n)).re := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _ _
      rw [Work.Analysis.IonescuWainger.etaCut, Work.KMTContract.kmtEta, Complex.ofReal_re]
      exact Work.KMTContract.kmtEta_nonneg _
  have hone : ∀ n ∈ Finset.Icc (-4:ℤ) 3,
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta 3 (u + n)).re = 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Work.KMTPlan.A6.etaCut_eq_one_of_le_bG 3 (by
      rw [show (2:ℝ) ^ ((3:ℤ) - 1) = 4 by norm_num]
      rw [abs_le]
      constructor
      · have h1 : (-4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
        linarith [huI.1]
      · have h2 : (n:ℝ) ≤ 3 := by exact_mod_cast hn.2
        linarith [huI.2])]
    norm_num
  have h8 : (8:ℝ) ≤ ∑ n ∈ Finset.Icc (-4:ℤ) 3,
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta 3 (u + n)).re := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const]
    have hc : (Finset.Icc (-4:ℤ) 3).card = 8 := by decide
    rw [hc]
    norm_num
  exact h8.trans hstep

/-- Consequently the integral of the symbol over the probability measure `circleMeasure` has real
part at least `8`. -/
lemma integral_etSym_three_re_ge :
    (8:ℝ) ≤ (∫ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.KMTPlan.A6.etSym 3 ξ ∂Work.Analysis.IonescuWainger.circleMeasure).re := by
  have hint : Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      Work.KMTPlan.A6.etSym 3 ξ) Work.Analysis.IonescuWainger.circleMeasure :=
    (Work.KMTPlan.A6.memLp_etSym 3).integrable le_top
  have hre : (∫ ξ : Work.Analysis.IonescuWainger.Circle,
        (Work.KMTPlan.A6.etSym 3 ξ).re ∂Work.Analysis.IonescuWainger.circleMeasure)
      = (∫ ξ : Work.Analysis.IonescuWainger.Circle,
          Work.KMTPlan.A6.etSym 3 ξ ∂Work.Analysis.IonescuWainger.circleMeasure).re := by
    have h := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) Complex.reCLM hint
    simpa only [Complex.reCLM_apply] using h
  rw [← hre]
  calc (8:ℝ) = ∫ _ξ : Work.Analysis.IonescuWainger.Circle,
        (8:ℝ) ∂Work.Analysis.IonescuWainger.circleMeasure := by
        rw [MeasureTheory.integral_const, MeasureTheory.Measure.real,
          MeasureTheory.measure_univ]
        norm_num
    _ ≤ ∫ ξ : Work.Analysis.IonescuWainger.Circle,
          (Work.KMTPlan.A6.etSym 3 ξ).re ∂Work.Analysis.IonescuWainger.circleMeasure :=
        MeasureTheory.integral_mono (integrable_const 8) hint.re
          (fun ξ => etSym_three_re_ge ξ)

/-- **The requested inequality fails for `ρ = 1`, `l = 0`, `c = 3`, `g = δ_0`:** the left hand
side is at least `8` (the value at `0` is the integral of a symbol that is `≥ 8` everywhere),
while the claimed right hand side is `4 · #(diffFreqs 1 0) · 1 = 4`. -/
theorem eLpNorm_piExact_counterexample :
    ¬ (MeasureTheory.eLpNorm
          (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 3 kmtDiracZero) 2
          MeasureTheory.Measure.count
        ≤ ((4 * (Work.KMTAreas.A7.diffFreqs 1 0).card : ℕ) : ENNReal) *
            MeasureTheory.eLpNorm kmtDiracZero 2 MeasureTheory.Measure.count) := by
  intro h
  have hval : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 3 kmtDiracZero 0
      = ∫ ξ : Work.Analysis.IonescuWainger.Circle,
          Work.KMTPlan.A6.etSym 3 ξ ∂Work.Analysis.IonescuWainger.circleMeasure := by
    rw [piExact_kmtDiracZero_zero, iwKernel_zero_eq_integral]
  have hnorm0 : (8:ℝ) ≤
      ‖Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 3 kmtDiracZero 0‖ := by
    rw [hval]
    have habs := Complex.abs_re_le_norm
      (∫ ξ : Work.Analysis.IonescuWainger.Circle,
        Work.KMTPlan.A6.etSym 3 ξ ∂Work.Analysis.IonescuWainger.circleMeasure)
    rw [abs_of_nonneg (le_trans (by norm_num) integral_etSym_three_re_ge)] at habs
    exact le_trans integral_etSym_three_re_ge habs
  have hge8 : (8:ENNReal) ≤ MeasureTheory.eLpNorm
      (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 3 kmtDiracZero) 2
      MeasureTheory.Measure.count := by
    have h2 : (8 : ENNReal) ≤
        ‖Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj 1) 0 3 kmtDiracZero 0‖ₑ := by
      simpa using ENNReal.ofReal_le_ofReal hnorm0
    exact h2.trans (eLpNorm_count_ge_enorm_apply _ 0)
  have hR : ((4 * (Work.KMTAreas.A7.diffFreqs 1 0).card : ℕ) : ENNReal) *
      MeasureTheory.eLpNorm kmtDiracZero 2 MeasureTheory.Measure.count = 4 := by
    rw [diffFreqs_one_zero_card, eLpNorm_kmtDiracZero]
    norm_num
  rw [hR] at h
  exact absurd (hge8.trans h) (by norm_num)

/-- **The requested statement is false**: it fails at `ρ = 1`, `l = 0`, `c = 3`, `g = δ_0`. -/
theorem not_eLpNorm_piExact_le :
    ¬ (∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (l : ℕ) (c : ℤ) (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g) 2
            MeasureTheory.Measure.count
          ≤ ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
  intro H
  exact eLpNorm_piExact_counterexample
    (H 1 (by norm_num) (by norm_num) 0 3 kmtDiracZero)

/-! ## The bound that the constant `4` really encodes -/

/-- **For `c ≤ 1` the periodised cutoff is bounded by `4`.**  The support of `etaCut kmtEta c` has
radius `2^c ≤ 2`, so at the representative `u ∈ [0,1)` only the four periods `k ∈ [-2,1]` can be
non-zero.  This is the regime in which the constant `4` of the requested statement is the correct
sup norm of the symbol, and it is also the regime in which the paper's projections are used
(`GoodMajorArcs`, i.e. the *good major arcs*). -/
theorem norm_etSym_le_four (c : ℤ) (hc : c ≤ 1) (ξ : Work.Analysis.IonescuWainger.Circle) :
    ‖Work.KMTPlan.A6.etSym c ξ‖ ≤ 4 := by
  rw [Work.KMTPlan.A6.etSym, Work.Analysis.IonescuWainger.periodize]
  set u : ℝ := (AddCircle.equivIco (1:ℝ) 0 ξ).val with hu
  have huI : u ∈ Set.Ico (0:ℝ) 1 := by
    rw [hu]; simpa using (AddCircle.equivIco (1:ℝ) 0 ξ).2
  rw [Set.mem_Ico] at huI
  have h2c : (2:ℝ)^c ≤ 2 := by
    have h2 : (2:ℝ)^c ≤ (2:ℝ)^(1:ℤ) := zpow_le_zpow_right₀ (by norm_num) hc
    simpa using h2
  have hsupp : ∀ k : ℤ, k ∉ Finset.Icc (-2:ℤ) 1 →
      Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c (u + k) = 0 := by
    intro k hk
    rw [Finset.mem_Icc, not_and, not_le] at hk
    refine Work.KMTPlan.A6.etaCut_eq_zero_of_le c ?_
    rcases lt_or_ge k (-2) with h | h
    · have hk3 : (k:ℝ) ≤ -3 := by exact_mod_cast (by omega : k ≤ -3)
      have hneg : u + (k:ℝ) < 0 := by linarith [huI.2]
      rw [abs_of_neg hneg]
      linarith
    · have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
      have hpos : 0 < u + (k:ℝ) := by linarith [huI.1]
      rw [abs_of_pos hpos]
      linarith
  rw [tsum_eq_sum hsupp]
  calc ‖∑ k ∈ Finset.Icc (-2:ℤ) 1,
        Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c (u + k)‖
      ≤ ∑ k ∈ Finset.Icc (-2:ℤ) 1,
          ‖Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c (u + k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-2:ℤ) 1, (1:ℝ) :=
        Finset.sum_le_sum fun k _ => Work.KMTPlan.A6.norm_etaCut_le_one c (u + k)
    _ = 4 := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc (-2:ℤ) 1).card = 4 := by decide
        rw [hcard]; norm_num

/-- **The corrected form of the requested inequality**: the same statement with the height
hypothesis `c ≤ 1`, which is the regime in which the constant `4` is correct
(`norm_etSym_le_four`).  Note that the surrounding A6 material (`Tle_piExact_eq_convOp`,
`piExact_eq_convOp`) works with the hypothesis `2^c ≤ 1/2`, which implies `c ≤ 1`.

For `g ∈ ℓ²` the proof is the ℓ² multiplier bound `eLpNorm_iwConv_two_le_of_symbol_bound` applied
to the identification `piExact = iwConv (diffFreqs ρ l) (etSym c)` on `ℓ²` (as in
`Tle_mdlF_eq_iwConv.Tle_piExact_eq_iwConv'`).  For `g ∉ ℓ²` the right-hand side is `⊤` unless
`#(diffFreqs ρ l) = 0`, and in that last case `diffFreqs ρ l = ∅` forces
`iwArithFreqs ρ l = iwArithFreqs ρ (l-1)`, so the two projections coincide and `piExact = 0`. -/
theorem eLpNorm_piExact_le_of_height_le_one (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    (hc : c ≤ 1) (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g) 2
        MeasureTheory.Measure.count
      ≤ ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  set A : Finset Work.Analysis.IonescuWainger.Circle := Work.KMTAreas.A7.diffFreqs ρ l with hA
  set Φ : Work.Analysis.IonescuWainger.Circle → ℂ := Work.KMTPlan.A6.etSym c with hΦ
  have hsup : ∀ ξ : Work.Analysis.IonescuWainger.Circle, ‖Φ ξ‖ ≤ 4 := by
    intro ξ
    rw [hΦ]
    exact norm_etSym_le_four c hc ξ
  have hsym : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet A Φ ξ‖ ≤ ((4 * A.card : ℕ) : ℝ) := by
    intro ξ
    have h := Work.Analysis.IonescuWainger.norm_iwSymbolSet_le A hsup ξ
    rw [show ((4 * A.card : ℕ) : ℝ) = (A.card : ℝ) * 4 by push_cast; ring]
    exact h
  have hmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
    rw [hΦ, hA]
    exact Work.KMTPlan.A6.memLp_iwSym (Work.KMTAreas.A7.diffFreqs ρ l) c
  by_cases hg : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · -- the non-`ℓ²` case
    rw [hg]
    by_cases hcard : A.card = 0
    · -- the symbol vanishes: the two projections coincide and `piExact = 0`
      have hdF : Work.KMTAreas.A7.diffFreqs ρ l = ∅ := Finset.card_eq_zero.mp (by rw [← hA]; exact hcard)
      have hl : l ≠ 0 := by
        intro h0
        have hm : (0 : Work.Analysis.IonescuWainger.Circle) ∈
            Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 := by
          rw [Work.Analysis.IonescuWainger.iwArithFreqs,
            show Work.Analysis.IonescuWainger.iwP ρ 0 = {1} from by
              rw [Work.Analysis.IonescuWainger.iwP, if_pos (Nat.zero_le _)]
              norm_num]
          simp
        rw [h0, Work.KMTAreas.A7.diffFreqs, if_pos rfl] at hdF
        rw [hdF] at hm
        exact absurd hm (Finset.notMem_empty 0)
      have hsub : Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) ⊆
          Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
        Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (by omega)
      have hempty : Work.Analysis.IonescuWainger.iwArithFreqs ρ l \
          Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) = ∅ := by
        have h' := hdF
        rw [Work.KMTAreas.A7.diffFreqs, if_neg hl] at h'
        exact h'
      have hss : Work.Analysis.IonescuWainger.iwArithFreqs ρ l ⊆
          Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) := by
        intro α hα
        by_contra hα'
        have hm : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l \
            Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) :=
          Finset.mem_sdiff.mpr ⟨hα, hα'⟩
        rw [hempty] at hm
        exact absurd hm (Finset.notMem_empty α)
      have hsymA : Work.Analysis.IonescuWainger.iwArithFreqs ρ l =
          Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) :=
        Finset.Subset.antisymm hss hsub
      have hzero : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g = 0 := by
        funext n
        rw [Work.Analysis.EndVar.piExact, if_neg hl, Work.KMTContract.kmtPj_proj,
          Work.KMTContract.kmtPj_proj, Pi.sub_apply]
        simp only [Work.KMTContract.kmtProj, hsymA, sub_self, Pi.zero_apply]
      rw [hzero, hcard]
      simp
    · have hne : ((4 * A.card : ℕ) : ENNReal) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        omega
      rw [ENNReal.mul_top hne]
      exact le_top
  · -- the `ℓ²` case
    have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hg)
    have hbound := Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound A Φ
      ((4 * A.card : ℕ) : ℝ) (by positivity) hsym hmem g hgmem
    have hconv : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g
        = Work.Analysis.IWMultiplier.iwConv A Φ g := by
      have hmdl : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g
          = ⇑(Work.Analysis.IonescuWainger.multiplierOf
              (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) hmem
              (Work.KMTPlan.A6.toL2Z hgmem)) := by
        have h1 : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c
              (⇑(Work.KMTPlan.A6.toL2Z hgmem))
            = ⇑(Work.Analysis.IonescuWainger.multiplierOf (Work.KMTPlan.A6.piSym ρ l c)
                (Work.KMTPlan.A6.memLp_piSym ρ l c) (Work.KMTPlan.A6.toL2Z hgmem)) :=
          Work.KMTPlan.A6.piExact_eq_multiplier ρ hρ hρ1 l c (Work.KMTPlan.A6.toL2Z hgmem)
        rw [Work.KMTPlan.A6.multiplierOf_congr_bG' (Work.KMTPlan.A6.memLp_piSym ρ l c) hmem
          (by rfl)] at h1
        rw [Work.KMTPlan.A6.toL2Z_coe hgmem] at h1
        exact h1
      calc Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g
          = ⇑(Work.Analysis.IonescuWainger.multiplierOf
              (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) hmem
              (Work.KMTPlan.A6.toL2Z hgmem)) := hmdl
        _ = ⇑(Work.Analysis.IonescuWainger.iwOpSet A Φ hmem
              (Work.KMTPlan.A6.toL2Z hgmem)) := rfl
        _ = Work.Analysis.IWMultiplier.iwConv A Φ (⇑(Work.KMTPlan.A6.toL2Z hgmem)) :=
              (iwConvEqIwOpSetMemlp hmem (Work.KMTPlan.A6.toL2Z hgmem)).symm
        _ = Work.Analysis.IWMultiplier.iwConv A Φ g := by
              rw [Work.KMTPlan.A6.toL2Z_coe hgmem]
    rw [hconv]
    simpa using hbound

/-- **The corrected inequality in the shape used by the surrounding A6 material**: the hypothesis
`2^c ≤ 1/2` (exactly the one carried by `Tle_piExact_eq_convOp`) implies `c ≤ 1`, so this is a
direct corollary of `eLpNorm_piExact_le_of_height_le_one`. -/
theorem eLpNorm_piExact_le_of_two_pow_le_half (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (c : ℤ) (hc : (2:ℝ)^c ≤ 1/2) (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g) 2
        MeasureTheory.Measure.count
      ≤ ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  refine eLpNorm_piExact_le_of_height_le_one ρ hρ hρ1 l c ?_ g
  by_contra h
  rw [not_le] at h
  have h1 : (2:ℝ) ^ (1:ℤ) ≤ (2:ℝ) ^ c := zpow_le_zpow_right₀ (by norm_num) (by omega)
  norm_num at h1
  linarith

/-! ## The requested statement (kept verbatim; it is false, see `not_eLpNorm_piExact_le`) -/

/-- **Do not use**: this statement is false, with the counterexample
`eLpNorm_piExact_counterexample` in this file (take `ρ = 1`, `l = 0`, `c = 3`, `g = δ_0`).  It is
kept verbatim so that the request can be repaired; the correct versions are described in the
module docstring (in particular `norm_etSym_le_four` for the hypothesis `c ≤ 1`, which is the
regime in which the constant `4` is correct). -/
theorem eLpNorm_piExact_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ) (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g) 2
        MeasureTheory.Measure.count
      ≤ ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by sorry

end

end Work.KMTPlan.A6
