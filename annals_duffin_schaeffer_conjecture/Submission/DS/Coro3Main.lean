import Mathlib
import Submission.DS.Coro3Sum

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

namespace Submission.DS

noncomputable section

/-- The ENNReal cover sum at level `n`: sum of `(diameter)^b` over all cover pairs. -/
def coverSum (ψ : ℕ+ → ℝ≥0) (b : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑' p : CovSigma n, (Metric.ediam ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ)) ^ b

/-- Sigma-cover condition. -/
lemma covSigma_cover_eventually (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    ∀ᶠ n in atTop, 𝒜 ψ ⊆ ⋃ p : CovSigma n, ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ) := by
  filter_upwards with n
  intro x hx
  exact mem_covSigma_iUnion ψ hx hψ n

/-- A cover pair's interval has `diameter^b ≤ ((2ψ(q)/q)^b)` (as ENNReal). -/
lemma covSigma_ediam_rpow_le (ψ : ℕ+ → ℝ≥0) {b : ℝ} (hb0 : 0 ≤ b) {n : ℕ} (p : CovSigma n) :
    (Metric.ediam ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ)) ^ b ≤
      ((((2 : NNReal) * (ψ p.1.1 / p.1.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞) := by
  let q : ℕ+ := p.1.1
  let a : ℕ := p.2.1
  have hd : Metric.ediam ({y : ℝ | inequality_1_7 ψ y a q} : Set ℝ) ≤
      ENNReal.ofReal (2 * ((ψ q / q : NNReal) : ℝ)) := by
    have hh := ediam_covInterval_le ψ (covPairOfSigma p)
    simpa [q, a, covInterval, covPairOfSigma] using hh
  have hd' : (Metric.ediam ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ)) ^ b ≤
      (ENNReal.ofReal (2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ))) ^ b := by
    simpa [q, a] using (ENNReal.rpow_le_rpow hd hb0)
  have h2r : 0 ≤ 2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ) := by positivity
  have hbase : (NNReal.mk (2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ)) h2r) =
      (2 : NNReal) * (ψ p.1.1 / p.1.1 : NNReal) := by
    ext <;> simp [NNReal.coe_mul]
  have heq : (ENNReal.ofReal (2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ))) ^ b =
      ((((2 : NNReal) * (ψ p.1.1 / p.1.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal h2r]
    rw [← ENNReal.coe_rpow_of_nonneg (NNReal.mk (2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ)) h2r) hb0]
    rw [hbase]
  exact hd'.trans_eq heq

/-- Bound `coverSum` by the `(φ+1)`-weighted tail. -/
lemma coverSum_le_phiWeightedTail (ψ : ℕ+ → ℝ≥0) {b : ℝ} (hb0 : 0 ≤ b) (n : ℕ) :
    coverSum ψ b n ≤
      ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
        (((φ q.1 + 1 : ℕ) : ℝ≥0∞) *
          ((((2 : NNReal) * (ψ q.1 / q.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞)) := by
  calc
    coverSum ψ b n ≤ ∑' p : CovSigma n, ((((2 : NNReal) * (ψ p.1.1 / p.1.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞) := by
      unfold coverSum
      exact ENNReal.tsum_le_tsum (fun p => covSigma_ediam_rpow_le ψ hb0 p)
    _ ≤ ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
        (((φ q.1 + 1 : ℕ) : ℝ≥0∞) *
          ((((2 : NNReal) * (ψ q.1 / q.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞)) := by
      exact covSigma_sum_le_tail (G := fun q : ℕ+ =>
        ((((2 : NNReal) * (ψ q / q : NNReal)) ^ b : NNReal) : ℝ≥0∞)) n

/-- `(φ(q)+1)·(2x)^b ≤ C·φ(q)·x^b` when `ψ(q) ≤ 1/2` (so `φ(q) ≥ 1`). -/
lemma phi_times_two_rpow_le (ψ : ℕ+ → ℝ≥0) {q : ℕ+} (hψ : ψ q ≤ (1 / 2 : ℝ≥0)) (b : ℝ) :
    ((φ q + 1 : ℕ) : NNReal) * ((2 : NNReal) * (ψ q / q : NNReal)) ^ b ≤
      ((2 : NNReal) * ((2 : NNReal) ^ b)) * ((φ q : NNReal) * ((ψ q / q : NNReal) ^ b)) := by
  let x : NNReal := ψ q / q
  have hφ : (1 : NNReal) ≤ (φ q : NNReal) := by
    have hφn : 1 ≤ φ q := by
      have h0 : 0 < φ q := totient_pos_pnat q
      omega
    exact_mod_cast hφn
  have hφ2 : ((φ q + 1 : ℕ) : NNReal) ≤ (2 : NNReal) * (φ q : NNReal) := by
    norm_num [NNReal.coe_natCast]
    nlinarith
  calc
    ((φ q + 1 : ℕ) : NNReal) * ((2 : NNReal) * x) ^ b
        = ((φ q + 1 : ℕ) : NNReal) * ((2 : NNReal) ^ b * x ^ b) := by rw [NNReal.mul_rpow]
    _ ≤ ((2 : NNReal) * (φ q : NNReal)) * ((2 : NNReal) ^ b * x ^ b) :=
          mul_le_mul' hφ2 le_rfl
    _ = ((2 : NNReal) * ((2 : NNReal) ^ b)) * ((φ q : NNReal) * x ^ b) := by ring
    _ = ((2 : NNReal) * ((2 : NNReal) ^ b)) * ((φ q : NNReal) * ((ψ q / q : NNReal) ^ b)) := by
      rfl

/-- `coverSum` is bounded by the tail of `C · w` where `w q = φ(q)·(ψ(q)/q)^b` and
`C = 2·2^b`. -/
lemma coverSum_le_Cw_tail (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0))
    (b : ℝ) (hb0 : 0 ≤ b) (n : ℕ) :
    coverSum ψ b n ≤
      tailSum (fun q : ℕ+ =>
        ((2 : NNReal) * ((2 : NNReal) ^ b)) * ((φ q : NNReal) * ((ψ q / q : NNReal) ^ b))) n := by
  let C : NNReal := (2 : NNReal) * ((2 : NNReal) ^ b)
  let w : ℕ+ → ℝ≥0 := fun q => (φ q : NNReal) * ((ψ q / q : NNReal) ^ b)
  calc
    coverSum ψ b n ≤
        ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
          (((φ q.1 + 1 : ℕ) : ℝ≥0∞) *
            ((((2 : NNReal) * (ψ q.1 / q.1 : NNReal)) ^ b : NNReal) : ℝ≥0∞)) :=
      coverSum_le_phiWeightedTail ψ hb0 n
    _ ≤ ∑' q : {q : ℕ+ // ((n : ℕ) + 1) ≤ (q : ℕ)},
        (((C * w q.1 : NNReal) : ℝ≥0∞)) := by
      refine ENNReal.tsum_le_tsum (fun q => ?_)
      rw [← ENNReal.coe_natCast]
      rw [← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr (phi_times_two_rpow_le ψ (hψ q.1) b)
    _ = tailSum (fun q : ℕ+ => C * w q) n := by
      rfl

/-- Summability of the dominating weight `C·w`. -/
lemma summable_Cw (ψ : ℕ+ → ℝ≥0) (b : ℝ)
    (hb : Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ b))) :
    Summable (fun q : ℕ+ =>
      ((2 : NNReal) * ((2 : NNReal) ^ b)) * ((φ q : NNReal) * ((ψ q / q : NNReal) ^ b))) := by
  classical
  let w : ℕ+ → ℝ≥0 := fun q => (φ q : NNReal) * ((ψ q / q : NNReal) ^ b)
  let C : NNReal := (2 : NNReal) * ((2 : NNReal) ^ b)
  have hfinW : (∑' q : ℕ+, ((w q : NNReal) : ℝ≥0∞)) ≠ ∞ := by
    rw [ENNReal.tsum_coe_ne_top_iff_summable]
    exact hb
  have hfinCW : (∑' q : ℕ+, (((C * w q : NNReal) : NNReal) : ℝ≥0∞)) ≠ ∞ := by
    have hstep : (∑' q : ℕ+, (((C * w q : NNReal) : NNReal) : ℝ≥0∞)) =
        ((C : NNReal) : ℝ≥0∞) * (∑' q : ℕ+, ((w q : NNReal) : ℝ≥0∞)) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro q
      rw [← ENNReal.coe_mul]
    rw [hstep]
    exact ENNReal.mul_ne_top (by simp) hfinW
  exact (ENNReal.tsum_coe_ne_top_iff_summable).1 (by simpa [C, w] using hfinCW)

/-- The main measure-theoretic input: for every `b ≥ 0` with the `b`-series convergent,
the `b`-dimensional Hausdorff measure of `𝒜 ψ` vanishes. -/
lemma hausdorffMeasure_A_eq_zero (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hb : Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ b))) :
    MeasureTheory.Measure.hausdorffMeasure b (𝒜 ψ) = 0 := by
  classical
  let w : ℕ+ → ℝ≥0 := fun q => (φ q : NNReal) * ((ψ q / q : NNReal) ^ b)
  let C : NNReal := (2 : NNReal) * ((2 : NNReal) ^ b)
  have hCw : Summable (fun q : ℕ+ => C * w q) := by
    simpa [C, w] using summable_Cw ψ b hb
  have htail : Tendsto (fun n : ℕ => tailSum (fun q : ℕ+ => C * w q) n) atTop (𝓝 0) :=
    tailSum_tendsto_zero (fun q : ℕ+ => C * w q) hCw
  have hSle : ∀ n : ℕ, coverSum ψ b n ≤ tailSum (fun q : ℕ+ => C * w q) n := by
    intro n
    simpa [C, w] using coverSum_le_Cw_tail ψ hψ b hb0 n
  have hlim : liminf (fun n : ℕ => coverSum ψ b n) atTop = 0 := by
    apply le_antisymm
    · calc
        liminf (fun n : ℕ => coverSum ψ b n) atTop ≤
            liminf (fun n : ℕ => tailSum (fun q : ℕ+ => C * w q) n) atTop := by
              exact liminf_le_liminf (by filter_upwards with n; exact hSle n)
        _ = 0 := htail.liminf_eq
    · exact bot_le
  let t : ∀ n : ℕ, CovSigma n → Set ℝ := fun n p =>
    ({y : ℝ | inequality_1_7 ψ y p.2.1 p.1.1} : Set ℝ)
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hMain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := ℝ) (d := b)
    (s := 𝒜 ψ) (l := atTop) (r := r) (t := t) (hr := tendsto_cov_diam_cap)
    (ht := covSigma_diam_eventually ψ hψ) (hst := covSigma_cover_eventually ψ hψ)
  have hle0 : MeasureTheory.Measure.hausdorffMeasure b (𝒜 ψ) ≤ 0 := by
    calc
      MeasureTheory.Measure.hausdorffMeasure b (𝒜 ψ) ≤
          liminf (fun n : ℕ => ∑' p : CovSigma n, (Metric.ediam (t n p)) ^ b) atTop := hMain
      _ = liminf (fun n : ℕ => coverSum ψ b n) atTop := by
        apply congrArg (fun u : ℕ → ℝ≥0∞ => liminf u atTop)
        funext n
        unfold coverSum t
        rfl
      _ = 0 := hlim
  exact le_antisymm hle0 bot_le

/-- The set of exponents whose moment series converges (its infimum is `s_inf ψ`). -/
def sumSet (ψ : ℕ+ → ℝ≥0) : Set ℝ≥0 :=
  {β : ℝ≥0 | Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ (β : ℝ)))}

/-- `s_inf` is the infimum of `sumSet`. -/
lemma s_inf_eq_sInf (ψ : ℕ+ → ℝ≥0) : s_inf ψ = sInf (sumSet ψ) := by
  unfold s_inf sumSet
  apply congrArg sInf
  ext β
  rfl

/-- The real moment series at exponent 4 is summable (as a real series). -/
lemma real_moment_four_summable (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    Summable (fun q : ℕ+ => (φ q : ℝ) * (((ψ q / q : NNReal) : ℝ) ^ (4 : ℝ))) := by
  classical
  let x : ℕ+ → ℝ := fun q => ((ψ q / q : NNReal) : ℝ)
  have hx0 : ∀ q : ℕ+, 0 ≤ x q := fun q => NNReal.coe_nonneg _
  have hxle : ∀ q : ℕ+, x q ≤ (1 : ℝ) / (q : ℝ) := by
    intro q
    have hψR : (ψ q : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hψ q
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
    have hmain : (ψ q : ℝ) / (q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hψR (le_of_lt hq0)
    have hstep : (1 / 2 : ℝ) / (q : ℝ) ≤ (1 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) (le_of_lt hq0)
    calc
      x q = (ψ q : ℝ) / (q : ℝ) := by
        simpa [x, NNReal.coe_div]
      _ ≤ (1 / 2 : ℝ) / (q : ℝ) := hmain
      _ ≤ (1 : ℝ) / (q : ℝ) := hstep
  let f0 : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2
  have hf0 : Summable f0 :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hout : ∀ m : ℕ, m ∉ Set.range (fun q : ℕ+ => (q : ℕ)) → f0 m = 0 := by
    intro m hm
    have hm0 : m = 0 := by
      by_contra h
      exact hm ⟨⟨m, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [f0, hm0]
  have hfc : Summable (fun q : ℕ+ => f0 (q : ℕ)) := by
    simpa [Function.comp_def] using
      ((Function.Injective.summable_iff (f := f0) (g := fun q : ℕ+ => (q : ℕ))
        PNat.coe_injective hout).2 hf0)
  have hle : ∀ q : ℕ+, (φ q : ℝ) * (x q ^ (4 : ℝ)) ≤ f0 (q : ℕ) := by
    intro q
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (PNat.pos q) : (1 : ℕ) ≤ (q : ℕ))
    have hφle : (φ q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le (q : ℕ)
    have hxpow : x q ^ (4 : ℝ) ≤ ((1 : ℝ) / (q : ℝ)) ^ (4 : ℝ) :=
      Real.rpow_le_rpow (hx0 q) (hxle q) (by norm_num)
    have hb1 : (φ q : ℝ) * (x q ^ (4 : ℝ)) ≤ (q : ℝ) * (x q ^ (4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hφle (Real.rpow_nonneg (hx0 q) (4 : ℝ))
    have hb2 : (q : ℝ) * (x q ^ (4 : ℝ)) ≤ (q : ℝ) * ((1 : ℝ) / (q : ℝ)) ^ (4 : ℝ) :=
      mul_le_mul_of_nonneg_left hxpow (le_of_lt hq0)
    have hb3 : (q : ℝ) * ((1 : ℝ) / (q : ℝ)) ^ (4 : ℝ) ≤ (1 : ℝ) / ((q : ℝ) ^ 2) := by
      have h4real : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
      rw [h4real, Real.rpow_natCast]
      have hq4 : (q : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hq0.ne'
      field_simp [hq4]
      have hqq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hq1 hq0.le]
      nlinarith
    calc
      (φ q : ℝ) * (x q ^ (4 : ℝ)) ≤ (q : ℝ) * (x q ^ (4 : ℝ)) := hb1
      _ ≤ (q : ℝ) * ((1 : ℝ) / (q : ℝ)) ^ (4 : ℝ) := hb2
      _ ≤ (1 : ℝ) / ((q : ℝ) ^ 2) := hb3
      _ = f0 (q : ℕ) := by
        simp [f0]
  have hge0 : ∀ q : ℕ+, 0 ≤ (φ q : ℝ) * (x q ^ (4 : ℝ)) := fun q =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hx0 q) (4 : ℝ))
  have hsum := Summable.of_nonneg_of_le hge0 hle hfc
  simpa [x, f0] using hsum

/-- NNReal version of the real-to-NNReal conversion at exponent 4. -/
lemma nnreal_mul_rpow_eq_toNNReal (a b : ℝ≥0) :
    a * (b ^ (4 : ℝ)) = ((a : ℝ) * ((b : ℝ) ^ (4 : ℝ))).toNNReal := by
  apply Subtype.ext
  change (a : ℝ) * (((b ^ (4 : ℝ)) : NNReal) : ℝ) = max ((a : ℝ) * ((b : ℝ) ^ (4 : ℝ))) 0
  rw [NNReal.coe_rpow]
  rw [max_eq_left (mul_nonneg (NNReal.coe_nonneg a) (Real.rpow_nonneg (NNReal.coe_nonneg b) (4 : ℝ)))]

/-- `4` lies in the exponent set, so `sumSet ψ` is nonempty. -/
lemma four_mem_sumSet (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    (4 : ℝ≥0) ∈ sumSet ψ := by
  unfold sumSet
  have hR := real_moment_four_summable ψ hψ
  have hT := Summable.toNNReal hR
  have hL : Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ (4 : ℝ))) := by
    have hEq : (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ (4 : ℝ))) =
        (fun q : ℕ+ => ((φ q : ℝ) * (((ψ q / q : NNReal) : ℝ) ^ (4 : ℝ))).toNNReal) := by
      funext q
      exact nnreal_mul_rpow_eq_toNNReal (φ q) (ψ q / q : NNReal)
    rw [hEq.symm] at hT
    exact hT
  simpa using hL

/-- `dimH (𝒜 ψ) ≤ s_inf ψ`. -/
lemma dimH_A_le_sInf (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    dimH (𝒜 ψ) ≤ ((s_inf ψ : ℝ≥0) : ℝ≥0∞) := by
  classical
  have h4 : (4 : ℝ≥0) ∈ sumSet ψ := four_mem_sumSet ψ hψ
  rw [s_inf_eq_sInf]
  refine dimH_le ?_
  intro d'
  intro hdinfty
  apply ENNReal.coe_le_coe.mpr
  by_contra hnot
  have hgt : sInf (sumSet ψ) < d' := lt_of_not_ge hnot
  rcases exists_lt_of_csInf_lt ⟨4, h4⟩ hgt with ⟨β, hβmem, hβlt⟩
  have hb0 : 0 ≤ (β : ℝ) := β.2
  have hμ0 : MeasureTheory.Measure.hausdorffMeasure (β : ℝ) (𝒜 ψ) = 0 :=
    hausdorffMeasure_A_eq_zero ψ hψ (β : ℝ) hb0 (by simpa [sumSet] using hβmem)
  have hmono : MeasureTheory.Measure.hausdorffMeasure (d' : ℝ) (𝒜 ψ) ≤
      MeasureTheory.Measure.hausdorffMeasure (β : ℝ) (𝒜 ψ) :=
    MeasureTheory.Measure.hausdorffMeasure_mono (by exact_mod_cast (le_of_lt hβlt)) (𝒜 ψ)
  have hd0 : MeasureTheory.Measure.hausdorffMeasure (d' : ℝ) (𝒜 ψ) = 0 :=
    le_antisymm (by simpa [hμ0] using hmono) bot_le
  rw [hd0] at hdinfty
  exact ENNReal.zero_ne_top hdinfty

/-- `dimH (𝒜 ψ) ≤ 1`. -/
lemma dimH_A_le_one (ψ : ℕ+ → ℝ≥0) : dimH (𝒜 ψ) ≤ 1 := by
  calc
    dimH (𝒜 ψ) ≤ dimH (Set.univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = 1 := Real.dimH_univ

/-- The Jarník-type upper bound of Corollary 3:
`dimH (𝒜 ψ) ≤ min (s_inf ψ) 1`. -/
lemma dimH_A_le_min (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n : ℕ+, ψ n ∈ Set.Icc 0 (1 / 2 : ℝ≥0)) :
    dimH (𝒜 ψ) ≤ ((min (s_inf ψ) 1 : ℝ≥0) : ℝ≥0∞) := by
  have hhalf : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0) := fun q => (hψ q).2
  rw [ENNReal.coe_min]
  exact le_min (dimH_A_le_sInf ψ hhalf) (by simpa using dimH_A_le_one ψ)

end

end Submission.DS
