import Mathlib
import Submission.DS.Theorem1

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# Corollary 3 upper bound: `dimH (𝒜 ψ) ≤ min (s_inf ψ) 1`

For `ψ : ℕ+ → ℝ≥0` with `ψ(q) ≤ 1/2` for all `q`, the Hausdorff dimension of the
Duffin–Schaeffer approximable set `𝒜 ψ ⊆ [0,1]` is at most `min (s_inf ψ) 1` where

    s_inf ψ = sInf {β | Summable fun q ↦ φ q * (ψ q / q) ^ β.1}

This is the *upper* half of the Beresnevich–Velani corollary (Jarník-type covering
argument); it is elementary and does not need the Duffin–Schaeffer theorem.

## Strategy

* (measure layer) For every `β ≥ 0` with `Σ_q φ(q)·(ψ(q)/q)^β < ∞` we show
  `μH[β] (𝒜 ψ) = 0` by covering `𝒜 ψ` with the intervals
  `{x | |x - a/q| ≤ ψ(q)/q}` (coprime `a ≤ q`, `q` large): the diameter-power sums
  are controlled by tails of the convergent `β`-series (`hausdorffMeasure_A_eq_zero`).
* (dimension layer) `dimH ≤ sInf` via `dimH_le` + `hausdorffMeasure_mono`
  (`dimH_A_le_sInf`); `dimH ≤ 1` since `𝒜 ψ ⊆ ℝ` (`dimH_A_le_one`).
-/

namespace Submission.DS

/-- Cover pairs at level `n`: reduced fractions `a/q` with `q ≥ n+1`, `a ≤ q`,
`gcd(a,q)=1`. The first component is the denominator `q`, the second the numerator `a`. -/
def CovPairs (n : ℕ) : Type :=
  {p : ℕ+ × ℕ // ((n : ℕ) + 1 ≤ (p.1 : ℕ)) ∧ Nat.Coprime p.2 (p.1 : ℕ) ∧ p.2 ≤ (p.1 : ℕ)}

/-- The solution interval of a cover pair. -/
def covInterval (ψ : ℕ+ → ℝ≥0) {n : ℕ} (p : CovPairs n) : Set ℝ :=
  {x : ℝ | inequality_1_7 ψ x p.1.2 p.1.1}

instance covPairs_countable (n : ℕ) : Countable (CovPairs n) := by
  unfold CovPairs
  infer_instance

/-- The solution set of `a/q` is an interval of diameter `2ψ(q)/q`. -/
lemma ediam_covInterval_le (ψ : ℕ+ → ℝ≥0) {n : ℕ} (p : CovPairs n) :
    Metric.ediam (covInterval ψ p) ≤
      ENNReal.ofReal (2 * ((ψ p.1.1 / p.1.1 : NNReal) : ℝ)) := by
  unfold covInterval
  rw [solInterval_eq_Icc ψ p.1.2 p.1.1]
  rw [Real.ediam_Icc]
  apply le_of_eq
  congr 1
  ring

/-- `x ∈ 𝒜 ψ` lies in the `q ≥ n+1` cover, for every `n`. -/
lemma mem_cov_iUnion (ψ : ℕ+ → ℝ≥0) {x : ℝ} (hx : x ∈ 𝒜 ψ)
    (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) (n : ℕ) :
    x ∈ ⋃ p : CovPairs n, covInterval ψ p := by
  rw [A_eq_Icc_inter_limsup] at hx
  rcases hx with ⟨hx01, hxlim⟩
  have hinf : ({q : ℕ+ | x ∈ Acopr ψ q}).Infinite := by
    simpa [limsupDenoms] using hxlim
  rcases (infinite_iff_forall_ge {q : ℕ+ | x ∈ Acopr ψ q}).1 hinf (n + 1) with ⟨q, hq, hqge⟩
  have hxq : x ∈ Acopr ψ q := hq
  rcases hxq with ⟨a, hc, hineq⟩
  have hale : a ≤ (q : ℕ) := num_le_q_of_half_radius (hψ q) hx01.2 hineq
  refine mem_iUnion.mpr ⟨⟨(q, a), ⟨hqge, hc, hale⟩⟩, ?_⟩
  simpa [covInterval] using hineq

/-- The eventual-diameter cap tends to zero. -/
lemma tendsto_cov_diam_cap : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    atTop (𝓝 0) := by
  simpa using (ENNReal.tendsto_ofReal (m := fun n : ℕ => 1 / ((n : ℝ) + 1)) (a := (0 : ℝ))
    tendsto_one_div_add_atTop_nhds_zero_nat)

/-- Diameter condition for the level-`n` cover. -/
lemma cov_diam_eventually (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    ∀ᶠ n in atTop, ∀ p : CovPairs n,
      Metric.ediam (covInterval ψ p) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  filter_upwards with n
  intro p
  rcases p with ⟨⟨q, a⟩, hrest⟩
  rcases hrest with ⟨hqge, hcop, hale⟩
  have hd1 : Metric.ediam (covInterval ψ ⟨(q, a), ⟨hqge, hcop, hale⟩⟩) ≤
      ENNReal.ofReal (2 * ((ψ q / q : NNReal) : ℝ)) := by
    simpa [covInterval] using ediam_covInterval_le ψ ⟨(q, a), ⟨hqge, hcop, hale⟩⟩
  have hle1 : 2 * ((ψ q / q : NNReal) : ℝ) ≤ 1 / (q : ℝ) := by
    have hψR : (ψ q : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hψ q
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
    have hmain : (ψ q : ℝ) / (q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hψR (le_of_lt hqpos)
    have hmain2 : 2 * ((ψ q : ℝ) / (q : ℝ)) ≤ 1 / (q : ℝ) := by
      have hstep : 2 * ((1 / 2 : ℝ) / (q : ℝ)) = 1 / (q : ℝ) := by
        field_simp [hqpos.ne']
      calc
        2 * ((ψ q : ℝ) / (q : ℝ)) ≤ 2 * ((1 / 2 : ℝ) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = 1 / (q : ℝ) := hstep
    simpa [NNReal.coe_div] using hmain2
  have hle2 : 1 / (q : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    have hden : ((n : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hqge
    exact one_div_le_one_div_of_le hpos hden
  have hmain : Metric.ediam (covInterval ψ ⟨(q, a), ⟨hqge, hcop, hale⟩⟩) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    hd1.trans (ENNReal.ofReal_le_ofReal (le_trans hle1 hle2))
  simpa [covInterval] using hmain

/-- Cover condition for the level-`n` cover: every point of `𝒜 ψ` lies in some interval
with `q ≥ n+1`. -/
lemma cov_cover_eventually (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0)) :
    ∀ᶠ n in atTop, 𝒜 ψ ⊆ ⋃ p : CovPairs n, covInterval ψ p := by
  filter_upwards with n
  intro x hx
  exact mem_cov_iUnion ψ hx hψ n

end Submission.DS
