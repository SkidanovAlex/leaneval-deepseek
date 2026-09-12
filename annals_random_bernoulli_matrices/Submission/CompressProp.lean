/-
Proposition `l: compress` — probability assembly (Tikhomirov 2020, arXiv:1812.09016).

The deterministic core lives in `Submission.Compress`; the volumetric slice nets in
`Commons.LinearAlgebra.Net.compress_slice_net`; the per-net-point small ball estimate is
`Submission.AuxOfLKR.aux_single_vector`; the spectral event is supplied by the caller
(`Commons.Probability.RandomMatrix.rect_spectral_norm_bounded_entries`), abstracted here as
a measurable sub-event on which the rectangular `∀ x` bound holds.

Main deliverable: `compress_main_bound` — for a `(n−1)×n` Bernoulli(p) family `B` and a shift
`s` with `s+p ≠ 0`,

    P{ ∃ x compressible(ε̃, ν), actSq(B· + s) x ≤ (γ/2)²·n }
        ≤ 2^{-n} + N_slices · Bnet · auxb

where `γ := γa·√ε̃`, `ν := γ/(32L)`, `R := γ/(8L)`, `w := γ/(4|s+p|)`,
`N_slices := 2·⌈8(L+γ)/γ+1⌉ + 1` is a bound on the number of relevant slices,
`Bnet` bounds each slice-net cardinality, and `auxb` is the per-point auxiliary estimate.
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.Compress
import Submission.AuxOfLKR
import Submission.Commons.LinearAlgebra.Net.compress_slice_net
import Submission.Commons.Probability.RandomMatrix.rect_spectral_measurable
import Submission.Commons.Probability.Compress.layer0_choose
import ChallengeDeps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.CompressProp

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

noncomputable section

universe u

/-! ## 1. Small measure / arithmetic bridges -/

/-- Expectation of a Bernoulli(p)-law variable equals `p`. -/
lemma bernoulli_integral {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I} {X : Ω → ℝ}
    (hX : HasLaw X (bernoulliMeasure 1 0 p) P) : ∫ ω, X ω ∂P = (p : ℝ) := by
  have hmap : Measure.map X P = bernoulliMeasure 1 0 p := hX.map_eq
  have hme : AEMeasurable X P := hX.aemeasurable
  have h1 : ∫ ω, X ω ∂P = ∫ y : ℝ, y ∂(Measure.map X P) := by
    symm
    exact MeasureTheory.integral_map hme (by fun_prop)
  rw [h1, hmap]
  have hber : ∫ y : ℝ, y ∂(bernoulliMeasure 1 0 p) = (p : ℝ) • (1 : ℝ) + (1 - (p : ℝ)) • (0 : ℝ) := by
    exact ProbabilityTheory.integral_bernoulliMeasure 1 0 p (fun y : ℝ => y)
  rw [hber]
  simp

/-- Expectation of the centered Bernoulli variable is zero. -/
lemma centered_integral_zero {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I}
    {X : Ω → ℝ} (hX : HasLaw X (bernoulliMeasure 1 0 p) P) :
    ∫ ω, (X ω - (p : ℝ)) ∂P = 0 := by
  have hmap : Measure.map X P = bernoulliMeasure 1 0 p := hX.map_eq
  have hme : AEMeasurable X P := hX.aemeasurable
  have h1 : ∫ ω, (X ω - (p : ℝ)) ∂P = ∫ y : ℝ, (y - (p : ℝ)) ∂(Measure.map X P) := by
    symm
    exact MeasureTheory.integral_map hme (by fun_prop)
  rw [h1, hmap]
  have hber : ∫ y : ℝ, (y - (p : ℝ)) ∂(bernoulliMeasure 1 0 p) =
      (p : ℝ) • (1 - (p : ℝ)) + (1 - (p : ℝ)) • (0 - (p : ℝ)) := by
    exact ProbabilityTheory.integral_bernoulliMeasure 1 0 p (fun y : ℝ => y - (p : ℝ))
  rw [hber]
  ring

/-- Subtracting a constant preserves independence of the flat family. -/
lemma iIndepFun_sub_const {m n : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Fin m → Fin n → Ω → ℝ) (hB : ProbabilityTheory.iIndepFun (fun kj : Fin m × Fin n => B kj.1 kj.2) P)
    (c : ℝ) : ProbabilityTheory.iIndepFun (fun kj : Fin m × Fin n => (fun ω => B kj.1 kj.2 ω - c)) P := by
  have hg : ∀ i : Fin m × Fin n, Measurable (fun t : ℝ => t - c) := fun i =>
    measurable_id.sub measurable_const
  have hc := ProbabilityTheory.iIndepFun.comp hB (fun _ : Fin m × Fin n => fun t : ℝ => t - c) hg
  convert hc using 1
  funext i ω
  rfl

/-- Measurable entries minus a constant stay measurable. -/
lemma measurable_sub_const {Ω : Type u} [MeasurableSpace Ω] {p : I} {m n : ℕ}
    (B : Fin m → Fin n → Ω → ℝ)
    (hB : ∀ k : Fin m, ∀ j : Fin n, Measurable (B k j)) :
    ∀ k : Fin m, ∀ j : Fin n, Measurable (fun ω => B k j ω - (p : ℝ)) := by
  intro k j
  exact (hB k j).sub measurable_const

/-- `exp(-n) ≤ 2^{-n}`. -/
lemma exp_neg_nat_le_two_pow_neg (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  rw [Real.exp_neg]
  have he : Real.exp 1 ^ n = Real.exp (n : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  rw [← he]
  have hpow : (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt Real.exp_one_gt_two) n
  have h1e : 0 < (Real.exp 1) ^ n := pow_pos (Real.exp_pos 1) n
  have h2e : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hinv : ((Real.exp 1) ^ n)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := (inv_le_inv₀ h1e h2e).2 hpow
  calc
    ((Real.exp 1) ^ n)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := hinv
    _ = (1 / 2 : ℝ) ^ n := by
      rw [← inv_pow (2 : ℝ) n]
      norm_num

/-- Probability of a measurable sub-event's complement is at most `2^{-n}`
given the sub-event has probability at least `1 - 2^{-n}`. -/
lemma measureReal_compl_le_two_pow_neg {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} {S : Set Ω} (hM : MeasurableSet S)
    (hP : P.real S ≥ 1 - (1 / 2 : ℝ) ^ n) : P.real Sᶜ ≤ (1 / 2 : ℝ) ^ n := by
  have hfin : P S ≠ ∞ := MeasureTheory.measure_ne_top P S
  have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := P) (s := S) hM
  have huniv : P.real Set.univ = 1 := by
    simp [Measure.real]
  have hsum' : P.real S + P.real Sᶜ = 1 := by
    rw [hsum, huniv]
  nlinarith

/-- complement measure of an event is `1 − measure`. -/
lemma measureReal_compl_eq {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {S : Set Ω} (hM : MeasurableSet S) :
    P.real Sᶜ = 1 - P.real S := by
  have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := P) (s := S) hM
  have huniv : P.real Set.univ = 1 := by simp [Measure.real]
  linarith

open Submission.Compress

/-! ## 2. Square-root / actSq bridges -/

/-- `actSq ≤ a² ⟺ sqrtAct ≤ a` for nonnegative `a`. -/
lemma sqrtAct_le_iff {m n : ℕ} (A : Fin m → Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) (x : Fin n → ℝ) :
    sqrtAct A x ≤ a ↔ actSq A x ≤ a ^ 2 := by
  constructor
  · intro h
    exact (Real.sqrt_le_iff (x := actSq A x) (y := a)).mp h |>.2
  · intro h
    exact (Real.sqrt_le_iff (x := actSq A x) (y := a)).mpr ⟨ha, h⟩

/-- `actSq ≤ a²` gives `sqrtAct ≤ a` (a ≥ 0). -/
lemma sqrtAct_le_of_actSq_le_sq {m n : ℕ} (A : Fin m → Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) (x : Fin n → ℝ)
    (h : actSq A x ≤ a ^ 2) : sqrtAct A x ≤ a := by
  exact (sqrtAct_le_iff A ha x).2 h

/-- `sqrtAct ≤ a` gives `actSq ≤ a²`. -/
lemma actSq_le_sq_of_sqrtAct_le {m n : ℕ} (A : Fin m → Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) (x : Fin n → ℝ)
    (h : sqrtAct A x ≤ a) : actSq A x ≤ a ^ 2 := by
  exact (sqrtAct_le_iff A ha x).1 h

/-- `actSq (Mω) x ≤ (γ/2)²·n` with γ > 0 and n ≥ 1 implies `sqrtAct (Mω) x < γ·√n`. -/
lemma sqrtAct_lt_of_actSq_half {m n : ℕ} (A : Fin m → Fin n → ℝ) {γ : ℝ} (hγ : 0 < γ) (x : Fin n → ℝ)
    (hn : 0 < (n : ℝ)) (h : actSq A x ≤ (γ / 2) ^ 2 * (n : ℝ)) : sqrtAct A x < γ * Real.sqrt (n : ℝ) := by
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn
  have h1 : sqrtAct A x ≤ Real.sqrt ((γ / 2) ^ 2 * (n : ℝ)) := by
    unfold sqrtAct
    exact Real.sqrt_le_sqrt h
  have hs2 : Real.sqrt ((γ / 2) ^ 2 * (n : ℝ)) = γ / 2 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (sq_nonneg (γ / 2)) ((n : ℝ))]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ γ / 2)]
  calc
    sqrtAct A x ≤ Real.sqrt ((γ / 2) ^ 2 * (n : ℝ)) := h1
    _ = γ / 2 * Real.sqrt (n : ℝ) := hs2
    _ < γ * Real.sqrt (n : ℝ) := by
      exact mul_lt_mul_of_pos_right (by linarith : γ / 2 < γ) hsn




/-! ### 3. Deterministic per-slice reduction -/

/-- `sqrtAct ≤ γ·√n` implies `actSq ≤ γ²·n` (γ ≥ 0). -/
lemma actSq_le_sq_nat_of_sqrtAct_le {m n : ℕ} (A : Fin m → Fin n → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (x : Fin n → ℝ)
    (h : sqrtAct A x ≤ γ * Real.sqrt (n : ℝ)) : actSq A x ≤ γ ^ 2 * (n : ℝ) := by
  have hγn : 0 ≤ γ * Real.sqrt (n : ℝ) := mul_nonneg hγ (Real.sqrt_nonneg _)
  have h1 : actSq A x ≤ (γ * Real.sqrt (n : ℝ)) ^ 2 :=
    actSq_le_sq_of_sqrtAct_le A hγn x h
  have hsq : (γ * Real.sqrt (n : ℝ)) ^ 2 = γ ^ 2 * (n : ℝ) := by
    rw [mul_pow]
    have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [hsqn]
  rw [hsq] at h1
  exact h1

/-- On the spectral event, a `(γ/2)·√n`-small ball of `x` propagates to scale `γ·√n`
at a net point `y` with `‖y−x‖ ≤ γ/(8L)` and matched coordinate sum. -/
lemma slice_reduce {n : ℕ} (A : Fin (n - 1) → Fin n → ℝ) (c L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hc : c ≠ 0)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {x y : Fin n → ℝ}
    (hd : sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2)
    (hs : |vecSum (y - x)| ≤ γ / (4 * |c|))
    (hball : actSq (shiftRows A c) x ≤ (γ / 2) ^ 2 * (n : ℝ)) :
    actSq (shiftRows A c) y ≤ γ ^ 2 * (n : ℝ) := by
  have hsq : ((γ / 2) ^ 2 * (n : ℝ)) = ((γ / 2) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [mul_pow]
    have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [hsqn]
  have hb : sqrtAct (shiftRows A c) x ≤ (γ / 2) * Real.sqrt (n : ℝ) := by
    rw [hsq] at hball
    exact sqrtAct_le_of_actSq_le_sq (shiftRows A c)
      (mul_nonneg (by positivity : 0 ≤ γ / 2) (Real.sqrt_nonneg _)) x hball
  have hred := event_reduction A c L γ hL hγ hc hE hb hd hs
  exact actSq_le_sq_nat_of_sqrtAct_le (shiftRows A c) (le_of_lt hγ) y hred

/-- Two numbers in the same slice window differ by less than the window width. -/
lemma vecSum_sub_lt_of_same_slice {n : ℕ} {w : ℝ} (hw : 0 < w) (ℓ : ℤ) {x y : Fin n → ℝ}
    (hx : w * (ℓ : ℝ) ≤ vecSum x ∧ vecSum x < w * ((ℓ : ℝ) + 1))
    (hy : w * (ℓ : ℝ) ≤ vecSum y ∧ vecSum y < w * ((ℓ : ℝ) + 1)) :
    |vecSum (y - x)| < w := by
  have h2 : vecSum (y - x) = vecSum y - vecSum x := vecSum_sub y x
  rw [h2]
  have hvx : |vecSum y - vecSum x| < w := by
    rw [abs_lt]
    constructor
    · nlinarith [hx.1, hy.2]
    · nlinarith [hy.1, hx.2]
  -- note: from hx.1: wℓ ≤ vx, hy.2: vy < w(ℓ+1) ⟹ vy - vx < w; and hy.1: wℓ ≤ vy, hx.2: vx < w(ℓ+1) ⟹ -(w) < vy - vx? 
  -- we need (vy - vx) - (-w) > 0: vy - vx > -w: hy.1 - hx.2: wℓ ≤ vy and vx < wℓ + w ⟹ vx < vy + w ⟹ vy - vx > -w ✓ ; and vy - vx < w: hy.2 - hx.1: vy < wℓ + w and wℓ ≤ vx ⟹ vy < vx + w ✓
  exact hvx

/-- Given a slice-window position and a bound on `|vecSum x|`, the slice index is bounded. -/
lemma slice_index_lt_of_vecSum {n : ℕ} {w T0 : ℝ} (hw : 0 < w) {ℓ : ℤ} {x : Fin n → ℝ}
    (hx : w * (ℓ : ℝ) ≤ vecSum x ∧ vecSum x < w * ((ℓ : ℝ) + 1))
    (hv : |vecSum x| < T0) : |(ℓ : ℝ)| < T0 / w + 1 := by
  have hwin : |vecSum x - w * (ℓ : ℝ)| < w := by
    rw [abs_lt]
    constructor
    · nlinarith [hx.1]  -- -(w) < v - wℓ: from hx.1 : wℓ ≤ v ⟹ v - wℓ ≥ 0 > -w ✓ (needs w>0)
    · nlinarith [hx.2, hw]  -- v - wℓ < w from v < wℓ + w
  have hv' : -(T0) < vecSum x ∧ vecSum x < T0 := abs_lt.mp hv
  have hwin' : -(w) < vecSum x - w * (ℓ : ℝ) ∧ vecSum x - w * (ℓ : ℝ) < w := abs_lt.mp hwin
  have hmain : |w * (ℓ : ℝ)| < T0 + w := by
    rw [abs_lt]
    constructor
    · nlinarith [hwin'.2, hv'.1]
    · nlinarith [hwin'.1, hv'.2]
  have hwℓ : |w * (ℓ : ℝ)| = w * |(ℓ : ℝ)| := by
    rw [abs_mul]
    rw [abs_of_pos hw]
  rw [hwℓ] at hmain
  have hdiv : |(ℓ : ℝ)| < (T0 + w) / w :=
    (lt_div_iff₀ hw).2 (by simpa [mul_comm] using hmain)
  have hdiv2 : (T0 + w) / w = T0 / w + 1 := by
    field_simp [hw.ne']
  rwa [hdiv2] at hdiv



/-! ## 4. Home slice of a small-ball vector -/

/-- Given compressible (unit) `x` with a small ball on the spectral event,
find its home slice with bounded index. -/
lemma exists_home_slice {n : ℕ} (hn₂ : 2 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (c L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hc : c ≠ 0)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {δ ν : ℝ} {x : Fin n → ℝ} (hxc : Commons.LinearAlgebra.Net.compressible δ ν x)
    (hball : actSq (shiftRows A c) x ≤ (γ / 2) ^ 2 * (n : ℝ)) :
    ∃ ℓ : ℤ, Commons.LinearAlgebra.Net.slice δ ν (γ / (4 * |c|)) ℓ x ∧
      |(ℓ : ℝ)| < 8 * (L + γ) / γ + 1 := by
  have hx1 : sqNorm x = 1 := by
    rcases hxc with ⟨hx1', hz⟩
    change Commons.LinearAlgebra.Net.sqNorm x = 1 at hx1'
    simpa [sqNorm, Commons.LinearAlgebra.Net.sqNorm] using hx1'
  have hn0 : 0 < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂
    linarith
  have hstrict : sqrtAct (shiftRows A c) x < γ * Real.sqrt (n : ℝ) :=
    sqrtAct_lt_of_actSq_half (shiftRows A c) hγ x hn0 hball
  have hvsum : |vecSum x| < (2 * L + 2 * γ) / |c| :=
    sum_lt_of_ball_lt hn₂ A c L γ hL hγ hc hE hx1 hstrict
  let w : ℝ := γ / (4 * |c|)
  have hw : 0 < w := by
    dsimp [w]
    have hc0 : 0 < |c| := abs_pos.mpr hc
    positivity
  let ℓ₀ : ℤ := Int.floor (vecSum x / w)
  have hwin : w * (ℓ₀ : ℝ) ≤ vecSum x ∧ vecSum x < w * ((ℓ₀ : ℝ) + 1) := by
    dsimp [ℓ₀]
    constructor
    · have h1 := Int.floor_le (vecSum x / w)
      have hm := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
      field_simp [hw.ne'] at hm
      exact hm
    · have h2 := Int.lt_floor_add_one (vecSum x / w)
      have hm := mul_lt_mul_of_pos_left h2 hw
      field_simp [hw.ne'] at hm
      exact hm
  have hslice : Commons.LinearAlgebra.Net.slice δ ν w ℓ₀ x := by
    exact ⟨hxc, hwin.1, hwin.2⟩
  have hℓ : |(ℓ₀ : ℝ)| < 8 * (L + γ) / γ + 1 := by
    have hb := slice_index_lt_of_vecSum (w := w) hw (ℓ := ℓ₀) hwin hvsum
    have hT : ((2 * L + 2 * γ) / |c|) / w = 8 * (L + γ) / γ := by
      dsimp [w]
      have hc0 : |c| ≠ 0 := abs_ne_zero.mpr hc
      have hγ0 : γ ≠ 0 := ne_of_gt hγ
      field_simp [hc0, hγ0]
      ring
    rwa [hT] at hb
  exact ⟨ℓ₀, hslice, hℓ⟩


/-! ## 5. Main assembly bound -/

lemma int_mem_Icc_of_abs_lt_real {M : ℝ} {ℓ : ℤ} (h : |(ℓ : ℝ)| < M) :
    ℓ ∈ Finset.Icc (-(Int.ceil M)) (Int.ceil M) := by
  have hlt : |(ℓ : ℝ)| < (Int.ceil M : ℝ) := by
    exact lt_of_lt_of_le h (Int.le_ceil M)
  have hℓ : -(Int.ceil M : ℝ) < (ℓ : ℝ) ∧ (ℓ : ℝ) < (Int.ceil M : ℝ) := abs_lt.mp hlt
  have h1 : -(Int.ceil M) ≤ ℓ := by
    have h1' : (-(Int.ceil M) : ℝ) < (ℓ : ℝ) := hℓ.1
    have h1'' : (-(Int.ceil M) : ℤ) < ℓ := by exact_mod_cast h1'
    omega
  have h2 : ℓ ≤ Int.ceil M := by
    have h2' : ((ℓ : ℝ) < (Int.ceil M : ℝ)) := hℓ.2
    have h2'' : ℓ < Int.ceil M := by exact_mod_cast h2'
    omega
  exact Finset.mem_Icc.mpr ⟨h1, h2⟩

/-- Cardinality bound for the slice-index window. -/
lemma card_slice_window_le {M : ℝ} (hM : 0 ≤ M) :
    ((Finset.Icc (-(Int.ceil M)) (Int.ceil M) : Finset ℤ).card : ℝ) ≤ 2 * M + 3 := by
  let k : ℤ := Int.ceil M
  have hk : 0 ≤ k := Int.ceil_nonneg hM
  have hcard : (Finset.Icc (-k) k : Finset ℤ).card = (2 * k + 1).toNat := by
    rw [Int.card_Icc]
    congr
    omega
  have h2k : 0 ≤ 2 * k + 1 := by omega
  have htoNat : (((2 * k + 1 : ℤ).toNat : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (a := (2 * k + 1 : ℤ)) h2k)
  have hkM : (k : ℝ) ≤ M + 1 := by
    have hceil : (Int.ceil M : ℤ) ≤ Int.floor M + 1 := Int.ceil_le_floor_add_one M
    have hc : ((Int.ceil M : ℤ) : ℝ) ≤ ((Int.floor M + 1 : ℤ) : ℝ) := by exact_mod_cast hceil
    have hfloor : (Int.floor M : ℝ) ≤ M := Int.floor_le M
    calc
      (k : ℝ) = ((Int.ceil M : ℤ) : ℝ) := rfl
      _ ≤ ((Int.floor M + 1 : ℤ) : ℝ) := hc
      _ = (Int.floor M : ℝ) + 1 := by norm_num
      _ ≤ M + 1 := by linarith
  calc
    ((Finset.Icc (-k) k : Finset ℤ).card : ℝ) = (((2 * k + 1 : ℤ).toNat : ℕ) : ℝ) := by
      rw [hcard]
    _ = ((2 * k + 1 : ℤ) : ℝ) := htoNat
    _ = 2 * (k : ℝ) + 1 := by norm_num
    _ ≤ 2 * M + 3 := by nlinarith [hkM]


theorem compress_main_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {n : ℕ} (hn₂ : 2 ≤ n)
    (L γ : ℝ) (hL₁ : 1 ≤ L) (hγ : 0 < γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (B : Fin (n - 1) → Fin n → Ω → ℝ)
    (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
    (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
    (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
    (s : ℝ) (hss : s + (p : ℝ) ≠ 0)
    (Sspec : Set Ω) (hSpecM : MeasurableSet Sspec)
    (hSpecP : P.real Sspec ≥ 1 - (1 / 2 : ℝ) ^ n)
    (hSpecOn : ∀ ⦃ω : Ω⦄, ω ∈ Sspec → ∀ x : Fin n → ℝ,
        actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x)
    (Bnet : ℝ) (hBnet0 : 0 ≤ Bnet)
    (hnet : ∀ ℓ : ℤ, ∃ Net : Finset (Fin n → ℝ),
        (∀ x : Fin n → ℝ,
            Commons.LinearAlgebra.Net.slice eps (γ / (32 * L)) (γ / (4 * |s + (p : ℝ)|)) ℓ x →
            ∃ y ∈ Net, Commons.LinearAlgebra.Net.slice eps (γ / (32 * L)) (γ / (4 * |s + (p : ℝ)|)) ℓ y ∧
              Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2) ∧
        ((Net.card : ℝ) ≤ Bnet))
    (hauxb : ℝ) (hauxb0 : 0 ≤ hauxb)
    (hpt : ∀ y : Fin n → ℝ, (∑ j : Fin n, (y j) ^ 2) = 1 →
        P.real {ω : Ω | actSq (fun k j => B k j ω + s) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb) :
    P.real {ω : Ω | ∃ x : Fin n → ℝ,
        Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) x ∧
        actSq (fun k j => B k j ω + s) x ≤ (γ / 2) ^ 2 * (n : ℝ)}
      ≤ (1 / 2 : ℝ) ^ n + (((2 * Int.ceil (8 * (L + γ) / γ + 1) + 1 : ℤ) : ℝ) * Bnet) * hauxb := by
  classical
  let c : ℝ := s + (p : ℝ)
  let δ : ℝ := eps
  let ν : ℝ := γ / (32 * L)
  let w : ℝ := γ / (4 * |c|)
  let M₀ : ℝ := 8 * (L + γ) / γ + 1
  let k : ℤ := Int.ceil M₀
  let Cω : Ω → Fin (n - 1) → Fin n → ℝ := fun ω k j => B k j ω - (p : ℝ)
  let Mtr : Ω → Fin (n - 1) → Fin n → ℝ := fun ω k j => B k j ω + s
  let S : Set Ω := {ω : Ω | ∀ x : Fin n → ℝ, actSq (Cω ω) x ≤ L ^ 2 * (n : ℝ) * sqNorm x}
  let T : Set Ω := {ω : Ω | ∃ x : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν x ∧
      actSq (Mtr ω) x ≤ (γ / 2) ^ 2 * (n : ℝ)}
  let Aℓ : ℤ → Set Ω := fun ℓ => {ω : Ω | ω ∈ S ∧ ∃ x : Fin n → ℝ,
      Commons.LinearAlgebra.Net.slice δ ν w ℓ x ∧ actSq (Mtr ω) x ≤ (γ / 2) ^ 2 * (n : ℝ)}
  let Net₀ : ℤ → Finset (Fin n → ℝ) := fun ℓ => Classical.choose (hnet ℓ)
  let Gℓ : ℤ → Finset (Fin n → ℝ) := fun ℓ =>
    (Net₀ ℓ).filter (fun y => Commons.LinearAlgebra.Net.slice δ ν w ℓ y)
  let E : (Fin n → ℝ) → Set Ω := fun y => {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL₁
  have hcne : c ≠ 0 := by simpa [c] using hss
  have hw : 0 < w := by
    dsimp [w]
    have hc0 : 0 < |c| := abs_pos.mpr hcne
    positivity
  have hnℝ : 0 < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₂
    linarith
  have hMtr : ∀ ω : Ω, shiftRows (Cω ω) c = Mtr ω := by
    intro ω
    funext k j
    dsimp [shiftRows, Cω, Mtr, c]
    ring
  -- Sspec ⊆ S
  have hSSpec : Sspec ⊆ S := by
    intro ω hω x
    have hh := hSpecOn (ω := ω) hω x
    change actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x
    exact hh
  -- complement bound
  have hSpecComp : P.real Sᶜ ≤ (1 / 2 : ℝ) ^ n := by
    have hSspecC : Sᶜ ⊆ Sspecᶜ := by
      intro ω hω
      exact fun hωs => hω (hSSpec hωs)
    calc
      P.real Sᶜ ≤ P.real Sspecᶜ := by
        exact MeasureTheory.measureReal_mono (s₁ := Sᶜ) (s₂ := Sspecᶜ) hSspecC
          (measure_ne_top P Sspecᶜ)
      _ = 1 - P.real Sspec := measureReal_compl_eq P hSpecM
      _ ≤ (1 / 2 : ℝ) ^ n := by linarith [hSpecP]
  -- For each ℓ, A_ℓ ⊆ ⋃_{y ∈ G_ℓ} E y
  have hB : ∀ ℓ : ℤ, Aℓ ℓ ⊆ {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)} := by
    intro ℓ ω hω
    rcases hω with ⟨hSω, x, hxsl, hxball⟩
    rcases (Classical.choose_spec (hnet ℓ)) with ⟨hcover, hcard⟩
    rcases hcover x hxsl with ⟨y, hyNet, hysl, hyx⟩
    have hd : sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2 := by
      change Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2
      simpa [sqNorm, Commons.LinearAlgebra.Net.sqNorm] using hyx
    have hwinx : w * (ℓ : ℝ) ≤ vecSum x ∧ vecSum x < w * ((ℓ : ℝ) + 1) := by
      simpa [w, c, vecSum, Commons.LinearAlgebra.Net.vecSum] using hxsl.2
    have hwiny : w * (ℓ : ℝ) ≤ vecSum y ∧ vecSum y < w * ((ℓ : ℝ) + 1) := by
      simpa [w, c, vecSum, Commons.LinearAlgebra.Net.vecSum] using hysl.2
    have hd2 : |vecSum (y - x)| ≤ γ / (4 * |c|) := by
      have hlt : |vecSum (y - x)| < w := vecSum_sub_lt_of_same_slice (w := w) hw ℓ hwinx hwiny
      dsimp [w] at hlt
      exact le_of_lt hlt
    have hb' : actSq (shiftRows (Cω ω) c) x ≤ (γ / 2) ^ 2 * (n : ℝ) := by
      rw [hMtr ω]
      exact hxball
    have hred := slice_reduce (A := Cω ω) (c := c) (L := L) (γ := γ) hL0 hγ hcne hSω hd hd2 hb'
    have hyE : actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ) := by
      rw [hMtr ω] at hred
      exact hred
    exact ⟨y, Finset.mem_filter.mpr ⟨hyNet, hysl⟩, hyE⟩
  -- per-ℓ probability bound
  have hperℓ : ∀ ℓ : ℤ, P.real (Aℓ ℓ) ≤ Bnet * hauxb := by
    intro ℓ
    have hseteq : {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}
        = (⋃ y ∈ (Gℓ ℓ : Finset (Fin n → ℝ)), {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}) := by
      ext ω
      constructor
      · rintro ⟨y, hyG, hyE⟩
        exact Set.mem_iUnion₂.mpr ⟨y, hyG, hyE⟩
      · intro h
        rcases Set.mem_iUnion₂.mp h with ⟨y, hyG, hyE⟩
        exact ⟨y, hyG, hyE⟩
    have hpart1 : P.real (Aℓ ℓ) ≤ P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)} := by
      exact MeasureTheory.measureReal_mono (s₁ := Aℓ ℓ)
        (s₂ := {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}) (hB ℓ)
        (measure_ne_top P {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)})
    have hpart2 : P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}
        ≤ ∑ y ∈ Gℓ ℓ, P.real {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)} := by
      rw [hseteq]
      exact MeasureTheory.measureReal_biUnion_finset_le (Gℓ ℓ)
        (fun y => {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)})
    have hpart3 : (∑ y ∈ Gℓ ℓ, P.real {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)})
        ≤ (Gℓ ℓ).card • hauxb := by
      apply Finset.sum_le_card_nsmul (Gℓ ℓ) (fun y => P.real {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}) hauxb
      intro y hyG
      have hysl : Commons.LinearAlgebra.Net.slice δ ν w ℓ y := (Finset.mem_filter.mp hyG).2
      have hyunit : (∑ j : Fin n, (y j) ^ 2) = 1 := by
        have hc1 : Commons.LinearAlgebra.Net.sqNorm y = 1 := hysl.1.1
        simpa [Commons.LinearAlgebra.Net.sqNorm] using hc1
      have hsub : {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)}
          = {ω : Ω | actSq (fun k j => B k j ω + s) y ≤ γ ^ 2 * (n : ℝ)} := by
        dsimp [Mtr]
      rw [hsub]
      exact hpt y hyunit
    have hcardG : ((Gℓ ℓ).card : ℝ) ≤ Bnet := by
      have h1 : (Gℓ ℓ).card ≤ (Net₀ ℓ).card := Finset.card_filter_le _ _
      have h2 : (Net₀ ℓ).card ≤ Bnet := (Classical.choose_spec (hnet ℓ)).2
      calc
        ((Gℓ ℓ).card : ℝ) ≤ ((Net₀ ℓ).card : ℝ) := by exact_mod_cast h1
        _ ≤ Bnet := h2
    have hpart4 : (Gℓ ℓ).card • hauxb ≤ Bnet * hauxb := by
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcardG hauxb0
    calc
      P.real (Aℓ ℓ) ≤ P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ Gℓ ℓ ∧ actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)} := hpart1
      _ ≤ ∑ y ∈ Gℓ ℓ, P.real {ω : Ω | actSq (Mtr ω) y ≤ γ ^ 2 * (n : ℝ)} := hpart2
      _ ≤ (Gℓ ℓ).card • hauxb := hpart3
      _ ≤ Bnet * hauxb := hpart4
  -- T ∩ S ⊆ ⋃_{ℓ ∈ Icc} A_ℓ
  have hTS : T ∩ S ⊆ (⋃ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Aℓ ℓ) := by
    intro ω hω
    rcases hω with ⟨hTω, hSω⟩
    rcases hTω with ⟨x, hxc, hxball⟩
    have hball' : actSq (shiftRows (Cω ω) c) x ≤ (γ / 2) ^ 2 * (n : ℝ) := by
      rw [hMtr ω]
      exact hxball
    have hhome := exists_home_slice (n := n) hn₂ (A := Cω ω) (c := c) (L := L) (γ := γ) hL0 hγ hcne
      (hE := hSω) (hxc := hxc) hball'
    rcases hhome with ⟨ℓ, hslice, hℓabs⟩
    have hA : ω ∈ Aℓ ℓ := by
      refine ⟨hSω, x, ?_, hxball⟩
      simpa [δ, ν, w, c] using hslice
    have hℓmem : ℓ ∈ (Finset.Icc (-k) k : Finset ℤ) := by
      dsimp [k, M₀]
      exact int_mem_Icc_of_abs_lt_real hℓabs
    exact Set.mem_iUnion₂.mpr ⟨ℓ, hℓmem, hA⟩
  -- measure step
  have hpartA : P.real (T ∩ S) ≤ P.real (⋃ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Aℓ ℓ) := by
    exact MeasureTheory.measureReal_mono (s₁ := T ∩ S)
      (s₂ := ⋃ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Aℓ ℓ) hTS
      (measure_ne_top P (⋃ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Aℓ ℓ))
  have hpartB : P.real (⋃ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Aℓ ℓ)
      ≤ ∑ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), P.real (Aℓ ℓ) := by
    exact MeasureTheory.measureReal_biUnion_finset_le (Finset.Icc (-k) k : Finset ℤ) (fun ℓ => Aℓ ℓ)
  have hpartC : (∑ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), P.real (Aℓ ℓ))
      ≤ (∑ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Bnet * hauxb) := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    exact hperℓ ℓ
  have hk0 : 0 ≤ k := by
    dsimp [k]
    apply Int.ceil_nonneg
    dsimp [M₀]
    positivity
  have hcard : ((Finset.Icc (-k) k : Finset ℤ).card : ℝ) ≤ ((2 * k + 1 : ℤ) : ℝ) := by
    have hcardEq : (Finset.Icc (-k) k : Finset ℤ).card = (2 * k + 1).toNat := by
      rw [Int.card_Icc]
      congr
      omega
    rw [hcardEq]
    have h2k : 0 ≤ 2 * k + 1 := by omega
    have htn : (((2 * k + 1 : ℤ).toNat : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (a := (2 * k + 1 : ℤ)) h2k)
    exact le_of_eq htn
  have hprod0 : 0 ≤ Bnet * hauxb := mul_nonneg hBnet0 hauxb0
  have hpartD : (∑ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Bnet * hauxb)
      ≤ (((2 * k + 1 : ℤ) : ℝ) * Bnet) * hauxb := by
    calc
      (∑ ℓ ∈ (Finset.Icc (-k) k : Finset ℤ), Bnet * hauxb)
          = ((Finset.Icc (-k) k : Finset ℤ).card : ℝ) * (Bnet * hauxb) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((2 * k + 1 : ℤ) : ℝ)) * (Bnet * hauxb) := by
            exact mul_le_mul_of_nonneg_right hcard hprod0
      _ = (((2 * k + 1 : ℤ) : ℝ) * Bnet) * hauxb := by ring
  -- total P(T) ≤ 2^{-n} + Σ
  have hTsub : T ⊆ (T ∩ S) ∪ Sᶜ := by
    intro ω hω
    by_cases hSω : ω ∈ S
    · exact Or.inl ⟨hω, hSω⟩
    · exact Or.inr hSω
  have hmeasure : P.real T ≤ P.real (T ∩ S) + P.real Sᶜ := by
    calc
      P.real T ≤ P.real ((T ∩ S) ∪ Sᶜ) := by
        exact MeasureTheory.measureReal_mono (s₁ := T) (s₂ := (T ∩ S) ∪ Sᶜ) hTsub
          (measure_ne_top P ((T ∩ S) ∪ Sᶜ))
      _ ≤ P.real (T ∩ S) + P.real Sᶜ := by
        exact MeasureTheory.measureReal_union_le (T ∩ S) Sᶜ
  have hfinal : P.real T ≤ (((2 * k + 1 : ℤ) : ℝ) * Bnet) * hauxb + (1 / 2 : ℝ) ^ n := by
    nlinarith [hmeasure, hpartA, hpartB, hpartC, hpartD, hSpecComp]
  -- T defeq to the theorem event; k := ⌈M₀⌉ with M₀ := 8(L+γ)/γ+1
  have hTdef : T = {ω : Ω | ∃ x : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) x ∧
      actSq (fun k j => B k j ω + s) x ≤ (γ / 2) ^ 2 * (n : ℝ)} := by
    dsimp [T, Mtr, δ, ν]
  rw [← hTdef]
  have hkdef : Int.ceil (8 * (L + γ) / γ + 1) = k := by
    dsimp [k, M₀]
  rw [hkdef]
  nlinarith [hfinal]



/-! ## 6. Aux-index and scale bookkeeping -/

/- (i) ceil lemmas for r := ⌈ee·(n−1)⌉₊ -/
lemma aux_r_pos {ee : ℝ} (hee0 : 0 < ee) {n : ℕ} (hn₂ : 2 ≤ n) :
    0 < Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) := by
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by
    have h : 1 ≤ n - 1 := by omega
    have hr : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  exact Nat.ceil_pos.mpr (mul_pos hee0 hn1)

lemma aux_r_le {ee : ℝ} (hee1 : ee ≤ 1) {n : ℕ} (hn₂ : 2 ≤ n) :
    Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) ≤ n - 1 := by
  apply Nat.ceil_le.mpr
  have hnn : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have hm : ee * ((n - 1 : ℕ) : ℝ) ≤ 1 * ((n - 1 : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_right hee1 hnn
  nlinarith

lemma aux_r_ge (ee : ℝ) {n : ℕ} :
    ee * ((n - 1 : ℕ) : ℝ) ≤ (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ) := by
  exact Nat.le_ceil _

/- (ii) scale identity -/
lemma scale_sq {γa ee : ℝ} (hee0 : 0 ≤ ee) :
    (γa * Real.sqrt ee) ^ 2 = γa ^ 2 * ee := by
  have hsq : (Real.sqrt ee) ^ 2 = ee := Real.sq_sqrt hee0
  rw [mul_pow, hsq]

/- (iii) slice factor bound: (2⌈M⌉+1) ≤ (16L/γa + 21)/√ee,  M := 8(L+γ)/γ + 1, γ := γa√ee -/
lemma slice_factor_le {γa L ee : ℝ} (hγa : 0 < γa) (hL : 0 < L) (hee0 : 0 < ee) (hee1 : ee ≤ 1) :
    (((2 * Int.ceil (8 * (L + γa * Real.sqrt ee) / (γa * Real.sqrt ee) + 1) + 1 : ℤ) : ℝ))
      ≤ (16 * L / γa + 21) / Real.sqrt ee := by
  let M : ℝ := 8 * (L + γa * Real.sqrt ee) / (γa * Real.sqrt ee) + 1
  have hγ : 0 < γa * Real.sqrt ee := mul_pos hγa (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < ee))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hceil : (Int.ceil M : ℤ) ≤ Int.floor M + 1 := Int.ceil_le_floor_add_one M
  have hfl : (Int.floor M : ℝ) ≤ M := Int.floor_le M
  have hc1 : ((Int.ceil M : ℤ) : ℝ) ≤ M + 1 := by
    have h1 : ((Int.ceil M : ℤ) : ℝ) ≤ ((Int.floor M + 1 : ℤ) : ℝ) := by exact_mod_cast hceil
    calc
      ((Int.ceil M : ℤ) : ℝ) ≤ ((Int.floor M + 1 : ℤ) : ℝ) := h1
      _ = (Int.floor M : ℝ) + 1 := by norm_num
      _ ≤ M + 1 := by linarith
  have hfac : (((2 * Int.ceil M + 1 : ℤ) : ℝ)) ≤ 2 * M + 3 := by
    -- (2⌈M⌉+1) = 2⌈M⌉+1 ≤ 2(M+1)+1 = 2M + 3
    have h2 : ((2 * Int.ceil M + 1 : ℤ) : ℝ) = 2 * ((Int.ceil M : ℤ) : ℝ) + 1 := by norm_num
    rw [h2]
    nlinarith [hc1]
  have hM' : 2 * M + 3 ≤ (16 * L / γa + 21) / Real.sqrt ee := by
    -- M = 8L/(γa√ee) + 8 + 1
    have hM2 : M = 8 * L / (γa * Real.sqrt ee) + 9 := by
      dsimp [M]
      have h8 : 8 * (L + γa * Real.sqrt ee) / (γa * Real.sqrt ee) = 8 * L / (γa * Real.sqrt ee) + 8 := by
        field_simp [hγ.ne']
      rw [h8]
      ring
    rw [hM2]
    have hse_pos : 0 < Real.sqrt ee := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < ee)
    have hse1 : Real.sqrt ee ≤ 1 := by
      have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      simpa using h1sq
    have h21 : 21 ≤ 21 / Real.sqrt ee := by
      exact (le_div_iff₀ hse_pos).2 (by nlinarith [hse1])
    have hsplit : (16 * L / γa + 21) / Real.sqrt ee = 16 * L / (γa * Real.sqrt ee) + 21 / Real.sqrt ee := by
      calc
        (16 * L / γa + 21) / Real.sqrt ee = (16 * L / γa) / Real.sqrt ee + 21 / Real.sqrt ee := by
          rw [add_div]
        _ = 16 * L / (γa * Real.sqrt ee) + 21 / Real.sqrt ee := by
          rw [div_div]
    calc
      2 * (8 * L / (γa * Real.sqrt ee) + 9) + 3 = 16 * L / (γa * Real.sqrt ee) + 21 := by ring
      _ ≤ 16 * L / (γa * Real.sqrt ee) + 21 / Real.sqrt ee := by linarith
      _ = (16 * L / γa + 21) / Real.sqrt ee := hsplit.symm
  exact le_trans (le_trans hfac hM') (le_rfl)




/-! ## 7. Proposition `l: compress` (paper form). -/

/-- Proposition `l: compress` (paper form). -/
theorem compress_theorem {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Fin (n - 1) → Fin n → Ω → ℝ)
        (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
        (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
        (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ k : Fin (n - 1), ∀ j : Fin n, ∀ ω : Ω, |B k j ω - (p : ℝ)| ≤ 1),
        ∀ s : ℝ, s + (p : ℝ) ≠ 0 →
          P.real {ω : Ω | ∃ x : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν x ∧
            actSq (fun k j => B k j ω + s) x ≤ γ₀ ^ 2 * (n : ℝ)} ≤ (1 - (p : ℝ) + ε) ^ n := by
  classical
  rcases Commons.Probability.RandomMatrix.rect_spectral_measurable (L := 1) (K := 1)
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) with ⟨Csp, hCsp1, hRect⟩
  rcases Submission.AuxOfLKR.aux_single_vector hp₀ hp₁ with ⟨γa, hγa, hAux⟩
  rcases Commons.LinearAlgebra.Net.compress_slice_net with ⟨C₀, hC₀₁, hSliceNet⟩
  let L : ℝ := max Csp (γa / 8)
  have hLgeC : Csp ≤ L := by dsimp [L]; exact le_max_left _ _
  have hLgeg : γa / 8 ≤ L := by dsimp [L]; exact le_max_right _ _
  have hL1 : 1 ≤ L := le_trans hCsp1 hLgeC
  let A₀ : ℝ := 16 * L / γa + 21
  have hA₀1 : 1 ≤ A₀ := by
    dsimp [A₀]
    have hpos : 0 < 16 * L / γa := div_pos (by positivity) hγa
    nlinarith
  rcases Commons.Probability.Compress.layer0_choose hp₀ hp₁ hε₀ hγa hL1 hC₀₁ hA₀1 with ⟨ee, n₀, hee0, hee1, hn₀2, hL0⟩
  let γ : ℝ := γa * Real.sqrt ee
  have hγ0 : 0 < γ := mul_pos hγa (Real.sqrt_pos.2 hee0)
  let γ₀ : ℝ := γ / 2
  have hγ₀0 : 0 < γ₀ := by dsimp [γ₀]; positivity
  refine ⟨n₀, hn₀2, γ₀, hγ₀0, ee, hee0, hee1, γ / (32 * L), ?_, ?_⟩
  · -- 0 < ν
    dsimp [γ]
    positivity
  · -- ν < 1 ∧ main body
    constructor
    · -- ν < 1
      have hγle : γ ≤ γa := by
        dsimp [γ]
        have hs : Real.sqrt ee ≤ 1 := by
          have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (le_of_lt hee1)
          simpa using h1sq
        nlinarith
      have hle : γ / (32 * L) ≤ 1 / 4 := by
        have hLpos : 0 < L := by linarith
        have hnum : γ ≤ 8 * L := by
          calc
            γ ≤ γa := hγle
            _ = 8 * (γa / 8) := by ring
            _ ≤ 8 * L := mul_le_mul_of_nonneg_left hLgeg (by norm_num)
        have hstep : γ / (32 * L) ≤ (8 * L) / (32 * L) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 32 * L)
        have hsim : (8 * L) / (32 * L) = 1 / 4 := by
          have hLne : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
          field_simp [hLne]
          ring
        rwa [hsim] at hstep
      nlinarith
    · -- main body: ∀ n ≥ n₀, data, s
      intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt s hss
      have hn2n : 2 ≤ n := le_trans hn₀2 hn
      let Aω : Ω → Fin (n - 1) → Fin n → ℝ := fun ω k j => B k j ω - (p : ℝ)
      have hAmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (fun ω => Aω ω k j) := by
        intro k j
        dsimp [Aω]
        exact (hBmeas k j).sub measurable_const
      have hAind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => (Aω · kj.1 kj.2)) P := by
        have hg : ∀ i : Fin (n - 1) × Fin n, Measurable (fun t : ℝ => t - (p : ℝ)) := fun i =>
          measurable_id.sub measurable_const
        have hc := ProbabilityTheory.iIndepFun.comp hBind
          (fun _ : Fin (n - 1) × Fin n => fun t : ℝ => t - (p : ℝ)) hg
        convert hc using 1
        funext i ω
        dsimp [Aω]
      have hAb : ∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω), |Aω ω k j| ≤ 1 := by
        intro k j ω
        dsimp [Aω]
        exact hBpt k j ω
      have hAm : ∀ k : Fin (n - 1), ∀ j : Fin n, ∫ ω, Aω ω k j ∂P = 0 := by
        intro k j
        dsimp [Aω]
        exact centered_integral_zero P (hBlaw k j)
      have hn1 : 1 ≤ n := by omega
      rcases hRect n hn1 (Ω := Ω) P Aω hAmeas hAind hAb hAm with ⟨G, hGm, hGP, hGsub⟩
      have hGP2 : P.real G ≥ 1 - (1 / 2 : ℝ) ^ n := by
        have he := exp_neg_nat_le_two_pow_neg n
        have hle : Real.exp (-1 * (n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
          simpa using he
        linarith
      have hGon : ∀ ⦃ω : Ω⦄, ω ∈ G → ∀ x : Fin n → ℝ,
          actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x := by
        intro ω hω x
        have hh := hGsub hω x
        change actSq (Aω ω) x ≤ L ^ 2 * (n : ℝ) * sqNorm x
        have hA : actSq (Aω ω) x = (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2) := rfl
        rw [hA]
        change (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2)
            ≤ L ^ 2 * (n : ℝ) * (∑ i : Fin n, (x i) ^ 2)
        have hC2 : (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ L ^ 2 * (n : ℝ) := by
          have hC0 : 0 ≤ Csp := by positivity
          have hL0' : 0 ≤ L := by positivity
          have hcl : Csp * Real.sqrt (n : ℝ) ≤ L * Real.sqrt (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hLgeC (Real.sqrt_nonneg _)
          have hsqb : (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ (L * Real.sqrt (n : ℝ)) ^ 2 := by
            exact sq_le_sq.mpr (by
              rw [abs_of_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)),
                  abs_of_nonneg (mul_nonneg hL0' (Real.sqrt_nonneg _))]
              exact hcl)
          calc
            (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ (L * Real.sqrt (n : ℝ)) ^ 2 := hsqb
            _ = L ^ 2 * (n : ℝ) := by
              rw [mul_pow]
              have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
              rw [hsqn]
        have hsqx : 0 ≤ (∑ i : Fin n, (x i) ^ 2) := by positivity
        have hhh : (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2)
            ≤ (Csp * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (x i) ^ 2) := by
          simpa using hh
        have hC2s : (Csp * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (x i) ^ 2)
            ≤ L ^ 2 * (n : ℝ) * (∑ i : Fin n, (x i) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hC2 hsqx
        exact le_trans hhh hC2s
      -- per-ℓ slice nets
      have hγle2 : γ ≤ γa := by
        dsimp [γ]
        have hs : Real.sqrt ee ≤ 1 := by
          have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (le_of_lt hee1)
          simpa using h1sq
        nlinarith
      have hRle1 : γ / (8 * L) ≤ 1 := by
        have hLpos : 0 < L := by linarith
        have hnum : γ ≤ 8 * L := by
          calc
            γ ≤ γa := hγle2
            _ = 8 * (γa / 8) := by ring
            _ ≤ 8 * L := mul_le_mul_of_nonneg_left hLgeg (by norm_num)
        have hstep : γ / (8 * L) ≤ (8 * L) / (8 * L) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 8 * L)
        have hsim : (8 * L) / (8 * L) = 1 := by
          have hLne : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
          field_simp [hLne]
        rwa [hsim] at hstep
      have hw0 : 0 < γ / (4 * |s + (p : ℝ)|) := by
        have hc0 : 0 < |s + (p : ℝ)| := abs_pos.mpr hss
        positivity
      have hνpos : 0 < γ / (32 * L) := by positivity
      have hνR : γ / (32 * L) ≤ (γ / (8 * L)) / 4 := by
        have hLpos : 0 < L := by linarith
        have hLne : L ≠ 0 := ne_of_gt hLpos
        have hsim : γ / (32 * L) = (γ / (8 * L)) / 4 := by
          field_simp [hLne]
          ring
        rw [hsim]
      have hnet : ∀ ℓ : ℤ, ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ,
              Commons.LinearAlgebra.Net.slice ee (γ / (32 * L)) (γ / (4 * |s + (p : ℝ)|)) ℓ x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.slice ee (γ / (32 * L)) (γ / (4 * |s + (p : ℝ)|)) ℓ y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2) ∧
          ((Net.card : ℝ) ≤ (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
              (C₀ / (γ / (8 * L))) ^ Nat.floor (ee * (n : ℝ))) := by
        intro ℓ
        rcases hSliceNet n hn1 (δ := ee) (ν := γ / (32 * L)) (R := γ / (8 * L)) hee0 (le_of_lt hee1)
          hνpos hνR (by positivity : 0 < γ / (8 * L)) hRle1 (w := γ / (4 * |s + (p : ℝ)|)) hw0 ℓ
          with ⟨Net, hcov, hcard⟩
        exact ⟨Net, hcov, hcard⟩
      let r₀ : ℕ := Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))
      let hauxb : ℝ := (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r₀ : ℝ)) ^ r₀ *
          (1 - (p : ℝ)) ^ ((n - 1) - r₀)
      have hAuxB0 : 0 ≤ hauxb := by
        dsimp [hauxb]
        have hr0 : 0 < (r₀ : ℝ) := by
          dsimp [r₀]
          exact_mod_cast (aux_r_pos hee0 hn2n)
        have hpart1 : 0 ≤ Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r₀ : ℝ) := by
          exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos 1)) (by positivity)) (le_of_lt hr0)
        have hpp : (p : ℝ) ≤ 1 := (p.property).2
        have hpart2 : 0 ≤ (1 - (p : ℝ)) ^ ((n - 1) - r₀) := by
          exact pow_nonneg (by linarith) _
        exact mul_nonneg (pow_nonneg hpart1 _) hpart2
      have hpt : ∀ y : Fin n → ℝ, (∑ j : Fin n, (y j) ^ 2) = 1 →
          P.real {ω : Ω | actSq (fun k j => B k j ω + s) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb := by
        intro y hyunit
        have hle_e : ee * ((n - 1 : ℕ) : ℝ) ≤ (r₀ : ℝ) := by
          dsimp [r₀]
          exact Nat.le_ceil _
        have hrpos : 0 < r₀ := by
          dsimp [r₀]
          exact aux_r_pos hee0 hn2n
        have hrle : r₀ ≤ n - 1 := by
          dsimp [r₀]
          exact aux_r_le (le_of_lt hee1) hn2n
        have hmain := hAux ee hee0 n hn2n (Ω := Ω) P B hBmeas hBind hBlaw (s := s) (x := y) hyunit
          (r := r₀) hrpos hrle hle_e
        have hscale : γa ^ 2 * ee * (n : ℝ) = γ ^ 2 * (n : ℝ) := by
          dsimp [γ]
          rw [scale_sq (le_of_lt hee0)]
        have heq : {ω : Ω |
              (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * y j))^2) ≤ γa ^ 2 * ee * (n : ℝ)}
            = {ω : Ω |
              (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * y j))^2) ≤ γ ^ 2 * (n : ℝ)} := by
          ext ω
          rw [hscale]
        rw [heq] at hmain
        have hev2 : {ω : Ω | actSq (fun k j => B k j ω + s) y ≤ γ ^ 2 * (n : ℝ)}
            = {ω : Ω |
              (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * y j))^2) ≤ γ ^ 2 * (n : ℝ)} := by
          ext ω
          rfl
        rw [hev2]
        dsimp [hauxb, r₀]
        exact hmain
      let Bnet : ℝ := (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
          (C₀ / (γ / (8 * L))) ^ Nat.floor (ee * (n : ℝ))
      have hBnet0 : 0 ≤ Bnet := by
        dsimp [Bnet]
        positivity
      have hmainb := compress_main_bound (p := p) hp₀ hp₁ (eps := ee) hee0 (le_of_lt hee1)
        (n := n) hn2n (L := L) (γ := γ) hL1 hγ0 (Ω := Ω) P B hBmeas hBind hBlaw (s := s) hss
        (Sspec := G) hGm hGP2 hGon Bnet hBnet0 hnet hauxb hAuxB0 hpt
      have hg₀ : γ₀ ^ 2 * (n : ℝ) = (γ / 2) ^ 2 * (n : ℝ) := by
        dsimp [γ₀]
      rw [show {ω : Ω | ∃ x : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) x ∧
          actSq (fun k j => B k j ω + s) x ≤ γ₀ ^ 2 * (n : ℝ)}
        = {ω : Ω | ∃ x : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) x ∧
          actSq (fun k j => B k j ω + s) x ≤ (γ / 2) ^ 2 * (n : ℝ)} by
        ext ω
        rw [hg₀]]
      have hfac := slice_factor_le (γa := γa) (L := L) (ee := ee) hγa (by linarith : 0 < L) hee0 (le_of_lt hee1)
      have hpref : (((2 * Int.ceil (8 * (L + γ) / γ + 1) + 1 : ℤ) : ℝ) * Bnet) * hauxb
          ≤ (A₀ / Real.sqrt ee) * Bnet * hauxb := by
        have hf : (((2 * Int.ceil (8 * (L + γ) / γ + 1) + 1 : ℤ) : ℝ))
            ≤ (16 * L / γa + 21) / Real.sqrt ee := by
          simpa [γ] using hfac
        have hchain : (((2 * Int.ceil (8 * (L + γ) / γ + 1) + 1 : ℤ) : ℝ)) ≤ A₀ / Real.sqrt ee := by
          dsimp [A₀]
          exact hf
        have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchain hBnet0) hAuxB0
        simpa [mul_assoc] using hmul
      have hstep2 : (1 / 2 : ℝ) ^ n +
          (((2 * Int.ceil (8 * (L + γ) / γ + 1) + 1 : ℤ) : ℝ) * Bnet) * hauxb
          ≤ (1 / 2 : ℝ) ^ n + (A₀ / Real.sqrt ee) * Bnet * hauxb := by
        nlinarith
      have h2 := le_trans hmainb hstep2
      have hL0n := hL0 n hn
      have hL0match : (1 / 2 : ℝ) ^ n + (A₀ / Real.sqrt ee) * Bnet * hauxb ≤ (1 - (p : ℝ) + ε) ^ n := by
        have hb2 : C₀ / ((γa * Real.sqrt ee) / (8 * L)) = C₀ * (8 * L) / (γa * Real.sqrt ee) := by
          have hgne : γa * Real.sqrt ee ≠ 0 := by positivity
          field_simp [hgne]
        calc
          (1 / 2 : ℝ) ^ n + (A₀ / Real.sqrt ee) * Bnet * hauxb
              = (1 / 2 : ℝ) ^ n + (A₀ / Real.sqrt ee) *
                  (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
                  (C₀ * (8 * L) / (γa * Real.sqrt ee)) ^ Nat.floor (ee * (n : ℝ)) *
                  (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
                      (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^
                        Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))) *
                    (1 - (p : ℝ)) ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)))) := by
            dsimp [Bnet, hauxb, r₀, A₀, γ]
            rw [hb2]
            ring
          _ ≤ (1 - (p : ℝ) + ε) ^ n := by
            simpa [mul_assoc] using hL0n
      exact le_trans h2 hL0match

end

end Submission.CompressProp