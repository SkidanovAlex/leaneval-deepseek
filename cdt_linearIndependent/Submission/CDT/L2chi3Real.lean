import Submission.CDT.TheoremA_leaf

/-!
# Sub-leaf (1) of CDT Theorem A: `L(2,χ₋₃)` is a positive real number

Proved here from the absolutely convergent residue series (see
`Submission.Helpers.LFunction_chi3_two_eq_tsum_residues`):

```lean
noncomputable def chi3Real (n : ℕ) : ℝ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0
noncomputable def L2chi3Real : ℝ := ∑' n : ℕ, chi3Real n / (n : ℝ) ^ 2
theorem LFunction_chi3_two_eq_L2chi3Real : ZMod.LFunction chi3 2 = (L2chi3Real : ℂ)
theorem L2chi3Real_pos : 0 < L2chi3Real
```

The character takes only the values `0, 1, -1`, so the real summand is bounded
by `1/n²` and the series converges absolutely (`fterm_summable`, by comparison
with `Σ 1/n²`).  Regrouping the terms into the pairs
`(1/(3n+1)² − 1/(3n+2)²)` (each strictly positive — `pairSum_pos`) gives
`L2chi3Real = Σ'ₙ pairSum n` (`L2chi3Real_eq_pair_tsum`), hence positivity.
The bridge to the analytic `L`-value is `Complex.cpow_natCast`
(`(n:ℂ)^(2:ℂ) = (n:ℂ)^2`), `Complex.ofReal_div` and `Complex.ofReal_tsum`.
The integral `∫₀¹ x^k·log x = −1/(k+1)²` (`integral_pow_mul_log`, improper
FTC with primitive `x^{k+1}(log x)/(k+1) − x^{k+1}/(k+1)²` and the limits
`x^{k+1}log x → 0` at `0⁺`) is here too; the paired summands are therefore
period integrals (`pairSum_eq_integral`, module
`Submission.CDT.L2chi3Real_period`) and summing them against the geometric
expansion yields the paper's period identity
`L(2,χ₋₃) = −∫₀¹ log x/(1+x+x²) dx`
(`L2chi3Real_eq_integral_period`, module `Submission.CDT.L2chi3Real_integral`).

Everything here is fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators
open scoped Complex
open scoped Topology
open scoped Interval
open Filter

noncomputable section

namespace Submission.CDT

open Submission.Helpers

/-- The character `χ₋₃(n)` (values in `ℝ`, one of `0, 1, -1`). -/
def chi3Real (n : ℕ) : ℝ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

lemma chi3Real_mul (n : ℕ) : chi3Real (3 * n) = 0 := by
  dsimp [chi3Real]
  have h : (3 * n) % 3 = 0 := by omega
  simp [h]

lemma chi3Real_add_one (n : ℕ) : chi3Real (3 * n + 1) = 1 := by
  dsimp [chi3Real]
  have h1 : (3 * n + 1) % 3 = 1 := by omega
  have h2 : (3 * n + 1) % 3 ≠ 2 := by omega
  simp [h1, h2]

lemma chi3Real_add_two (n : ℕ) : chi3Real (3 * n + 2) = -1 := by
  dsimp [chi3Real]
  have h1 : (3 * n + 2) % 3 ≠ 1 := by omega
  have h2 : (3 * n + 2) % 3 = 2 := by omega
  simp [h1, h2]

/-- complex character equals the cast of the real one -/
lemma chi3_eq_ofReal (n : ℕ) : Submission.Helpers.chi3 (n : ZMod 3) = (chi3Real n : ℂ) := by
  rw [chi3_apply_nat_mod]
  dsimp [chi3Real]
  by_cases h1 : n % 3 = 1
  · simp [h1]
  · by_cases h2 : n % 3 = 2
    · simp [h1, h2]
    · simp [h1, h2]

/-- the real L-series summand -/
def fterm (n : ℕ) : ℝ := chi3Real n / ((n : ℕ) : ℝ) ^ 2

/-- the real value of `L(2,χ₋₃)` as an absolutely convergent real series -/
def L2chi3Real : ℝ := ∑' n : ℕ, fterm n

lemma fterm_mul (n : ℕ) : fterm (3 * n) = 0 := by
  dsimp [fterm]
  rw [chi3Real_mul]
  simp

lemma fterm_add_one (n : ℕ) : fterm (3 * n + 1) = 1 / (((3 * n + 1 : ℕ) : ℝ) ^ 2) := by
  dsimp [fterm]
  rw [chi3Real_add_one]

lemma fterm_add_two (n : ℕ) : fterm (3 * n + 2) = -1 / (((3 * n + 2 : ℕ) : ℝ) ^ 2) := by
  dsimp [fterm]
  rw [chi3Real_add_two]

/-- `‖χ₋₃(n)‖ ≤ 1` -/
lemma chi3Real_abs_le_one (n : ℕ) : |chi3Real n| ≤ 1 := by
  dsimp [chi3Real]
  by_cases h1 : n % 3 = 1 <;> by_cases h2 : n % 3 = 2 <;> simp [h1, h2]

/-- the real series is absolutely convergent (dominated by `Σ 1/n²`) -/
lemma fterm_summable : Summable fterm := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ?_ ?_
  · exact (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  · intro n
    by_cases hn : n = 0
    · simp [fterm, hn]
    · have hdenpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
      have hχ : |chi3Real n| ≤ 1 := chi3Real_abs_le_one n
      calc
        ‖fterm n‖ = |chi3Real n / (n : ℝ) ^ 2| := rfl
        _ = |chi3Real n| / |(n : ℝ) ^ 2| := by rw [abs_div]
        _ = |chi3Real n| / (n : ℝ) ^ 2 := by
              rw [abs_of_nonneg (le_of_lt hdenpos)]
        _ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := (div_le_div_of_nonneg_right hχ (le_of_lt hdenpos))

/-- the paired summand (term at `3n+1` plus term at `3n+2`) -/
def pairSum (k : ℕ) : ℝ := fterm (3 * k + 1) + fterm (3 * k + 2)

/-- the paired summand is `1/(3k+1)² − 1/(3k+2)²` (the period-summand of
the paper's display for `L(2,χ₋₃)`) -/
lemma pairSum_eq_sq (k : ℕ) :
    pairSum k = (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
      - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
  unfold pairSum
  rw [fterm_add_one, fterm_add_two]
  ring

/-- pair partial sums over `k < M` equal the full partial sums over `n < 3M`
(the terms at `3k` vanish). -/
lemma sum_range_3M (M : ℕ) :
    (∑ n ∈ Finset.range (3 * M), fterm n) = ∑ k ∈ Finset.range M, pairSum k := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hM : 3 * (M + 1) = 3 * M + 3 := by ring
      calc
        (∑ n ∈ Finset.range (3 * (M + 1)), fterm n)
            = ∑ n ∈ Finset.range (3 * M + 3), fterm n := by rw [hM]
        _ = (∑ n ∈ Finset.range (3 * M), fterm n) + fterm (3 * M + 1) + fterm (3 * M + 2) := by
              simp [Finset.sum_range_succ, fterm_mul]
        _ = (∑ k ∈ Finset.range M, pairSum k) + fterm (3 * M + 1) + fterm (3 * M + 2) := by rw [ih]
        _ = ∑ k ∈ Finset.range (M + 1), pairSum k := by
              rw [Finset.sum_range_succ]
              simp [add_assoc, pairSum]

/-- explicit paired summand -/
lemma pairSum_eq (k : ℕ) :
    pairSum k = 1 / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - 1 / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by
  dsimp [pairSum]
  rw [fterm_add_one, fterm_add_two]
  ring

/-- each paired summand is positive -/
lemma pairSum_pos (k : ℕ) : 0 < pairSum k := by
  rw [pairSum_eq]
  have hlt : ((3 * k + 1 : ℕ) : ℝ) < ((3 * k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 3 * k + 1 < 3 * k + 2)
  have hpos : 0 < ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 3 * k + 1)
  have hsq1 : 0 < ((3 * k + 1 : ℕ) : ℝ) ^ 2 := sq_pos_of_pos hpos
  have hlt' : ((3 * k + 1 : ℕ) : ℝ) ^ 2 < ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hlt (le_of_lt hpos) (n := 2) (by norm_num)
  have hle : 1 / (((3 * k + 2 : ℕ) : ℝ) ^ 2) < 1 / (((3 * k + 1 : ℕ) : ℝ) ^ 2) := by
    exact one_div_lt_one_div_of_lt hsq1 hlt'
  linarith

/-- paired summands are bounded by `1/(k+1)²` -/
lemma pairSum_le (k : ℕ) : pairSum k ≤ (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  rw [pairSum_eq]
  have h2 : (1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - 1 / (((3 * k + 2 : ℕ) : ℝ) ^ 2)
      ≤ 1 / (((3 * k + 1 : ℕ) : ℝ) ^ 2) := by
    have hle : 0 ≤ 1 / (((3 * k + 2 : ℕ) : ℝ) ^ 2) := by positivity
    linarith
  exact le_trans h2 (by
    -- 1/(3k+1)^2 ≤ 1/(k+1)^2  since (k+1) ≤ (3k+1)
    have hpos : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 := by
      exact sq_pos_of_pos (by exact_mod_cast (by omega : 0 < k + 1))
    have hle' : ((k + 1 : ℕ) : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : k + 1 ≤ 3 * k + 1)
    have hsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ ((3 * k + 1 : ℕ) : ℝ) ^ 2 := by
      have hpos0 : 0 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      exact pow_le_pow_left₀ hpos0 hle' 2
    exact one_div_le_one_div_of_le hpos hsq)

/-- the pair series is summable -/
lemma pairSum_summable : Summable pairSum := by
  have hg : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (k := 1)).mpr hs
  exact Summable.of_nonneg_of_le (fun k => le_of_lt (pairSum_pos k)) pairSum_le hg

/-- the partial sums of the pair series converge to `L2chi3Real` -/
lemma pair_partial_tendsto :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, pairSum k) atTop (𝓝 L2chi3Real) := by
  -- partial sums of fterm over range n tend to tsum fterm = L2chi3Real
  have hpt : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, fterm i) atTop (𝓝 L2chi3Real) := by
    exact HasSum.tendsto_sum_nat (Summable.hasSum fterm_summable)
  -- compose with M ↦ 3M
  have hmul : Tendsto (fun M : ℕ => 3 * M) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    refine ⟨b + 1, ?_⟩
    intro a ha
    nlinarith
  have hpt3 : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (3 * M), fterm i) atTop (𝓝 L2chi3Real) := by
    change Tendsto ((fun n : ℕ => ∑ i ∈ Finset.range n, fterm i) ∘ (fun M : ℕ => 3 * M)) atTop (𝓝 L2chi3Real)
    exact hpt.comp hmul
  -- pointwise equality with the pair partial sums
  have hcong : (fun M : ℕ => ∑ i ∈ Finset.range (3 * M), fterm i)
      =ᶠ[atTop] (fun M : ℕ => ∑ k ∈ Finset.range M, pairSum k) := by
    exact Eventually.of_forall (fun M => sum_range_3M M)
  exact hpt3.congr' hcong

/-- `L(2,χ₋₃)` (real series) equals the sum of the positive pairs -/
lemma L2chi3Real_eq_pair_tsum : L2chi3Real = ∑' k : ℕ, pairSum k := by
  have hsum := Summable.hasSum_iff_tendsto_nat (f := pairSum) (m := L2chi3Real) pairSum_summable
  have hh : HasSum pairSum L2chi3Real := hsum.mpr pair_partial_tendsto
  exact (HasSum.tsum_eq hh).symm

/-- `L(2,χ₋₃)` (real series) is positive -/
lemma L2chi3Real_pos : 0 < L2chi3Real := by
  rw [L2chi3Real_eq_pair_tsum]
  have h0 : 0 < pairSum 0 := pairSum_pos 0
  have hsum := Summable.hasSum pairSum_summable
  have hle : pairSum 0 ≤ ∑' k : ℕ, pairSum k := by
    exact le_hasSum hsum 0 (fun j hj => le_of_lt (pairSum_pos j))
  linarith

/-- per-term bridge: the complex `cpow`-form equals the real-term cast -/
lemma term_eq_ofReal (n : ℕ) : Submission.Helpers.chi3 (n : ZMod 3) / ((n : ℂ) ^ (2 : ℂ)) =
    ((chi3Real n / ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hcp : (n : ℂ) ^ (2 : ℂ) = (n : ℂ) ^ 2 := by
    change (n : ℂ) ^ ((2 : ℕ) : ℂ) = (n : ℂ) ^ 2
    rw [Complex.cpow_natCast]
  rw [chi3_eq_ofReal n, hcp]
  rw [Complex.ofReal_div]
  congr 1
  norm_num

/-- **`L(2,χ₋₃)` equals the positive real series** (as complex). -/
theorem LFunction_chi3_two_eq_L2chi3Real :
    ZMod.LFunction (Submission.Helpers.chi3) 2 = (L2chi3Real : ℂ) := by
  rw [LFunction_chi3_two_eq_tsum]
  calc
    (∑' n : ℕ, (Submission.Helpers.chi3 (n : ZMod 3)) / ((n : ℂ) ^ (2 : ℂ)))
        = ∑' n : ℕ, ((chi3Real n / ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
          apply tsum_congr
          intro n
          exact term_eq_ofReal n
    _ = (L2chi3Real : ℂ) := by
          rw [← Complex.ofReal_tsum]
          rfl

/-- **Sub-leaf (1): `L(2,χ₋₃)` is a positive real number.** -/
theorem LFunction_chi3_two_pos_real :
    ∃ r : ℝ, 0 < r ∧ ZMod.LFunction (Submission.Helpers.chi3) 2 = (r : ℂ) := by
  refine ⟨L2chi3Real, L2chi3Real_pos, LFunction_chi3_two_eq_L2chi3Real⟩

/-- equivalently, its imaginary part is zero and real part positive -/
lemma LFunction_chi3_two_re_pos : 0 < (ZMod.LFunction (Submission.Helpers.chi3) 2).re := by
  rcases LFunction_chi3_two_pos_real with ⟨r, hr0, hr⟩
  rw [hr]
  simpa using hr0


/-! ## Sub-leaf (2) part 1: `∫₀¹ xᵏ·log x = −1/(k+1)²`

The classical logarithmic power integral (improper at `0`), proved with the
improper FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`
using the primitive `(x^{k+1}·log x)/(k+1) − x^{k+1}/(k+1)²` (derivative
`xᵏ·log x` on `(0,1)`) and the limit `x^{k+1}·log x → 0` as `x → 0⁺`
(`tendsto_log_mul_rpow_nhdsGT_zero`). This is the first analytic block of
the *period identity* sub-leaf (2).
-/
lemma deriv_pow_log {k : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ (k + 1) * Real.log x)
      ((k + 1 : ℝ) * (x ^ k) * Real.log x + x ^ k) x := by
  have hlog := Real.hasDerivAt_log hx
  have hpow := hasDerivAt_pow (k + 1) x
  have hpow' : HasDerivAt (fun x : ℝ => x ^ (k + 1)) ((k + 1 : ℝ) * x ^ k) x := by
    simpa [Nat.cast_add, Nat.cast_one] using hpow
  have hp := hpow'.mul hlog
  have hcancel : x ^ (k + 1) * x⁻¹ = x ^ k := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
  have hval : ((k + 1 : ℝ) * x ^ k) * Real.log x + x ^ (k + 1) * x⁻¹ =
      (k + 1 : ℝ) * (x ^ k) * Real.log x + x ^ k := by
    rw [hcancel]
  exact hp.congr_deriv hval

-- P := (x^{k+1} log x)/(k+1) − x^{k+1}/(k+1)²  has derivative x^k log x
lemma deriv_P {k : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)
        - x ^ (k + 1) / ((k + 1 : ℝ) ^ 2))
      (x ^ k * Real.log x) x := by
  have hk : (k + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have h1 := deriv_pow_log (k := k) hx
  have hA : HasDerivAt (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ))
      ((x ^ k * Real.log x) + x ^ k / (k + 1 : ℝ)) x := by
    have h1' : HasDerivAt (fun x : ℝ => (1 / (k + 1 : ℝ)) * (x ^ (k + 1) * Real.log x))
        ((1 / (k + 1 : ℝ)) * ((k + 1 : ℝ) * x ^ k * Real.log x + x ^ k)) x :=
      h1.const_mul (1 / (k + 1 : ℝ))
    have hfun : (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ))
        = fun x : ℝ => (1 / (k + 1 : ℝ)) * (x ^ (k + 1) * Real.log x) := by
      funext x
      rw [div_eq_mul_inv]
      ring
    have hval : (1 / (k + 1 : ℝ)) * ((k + 1 : ℝ) * x ^ k * Real.log x + x ^ k)
        = x ^ k * Real.log x + x ^ k / (k + 1 : ℝ) := by
      field_simp [hk]
    exact (hfun ▸ h1').congr_deriv hval
  have hB : HasDerivAt (fun x : ℝ => x ^ (k + 1) / ((k + 1 : ℝ) ^ 2))
      (x ^ k / (k + 1 : ℝ)) x := by
    have h2 := (hasDerivAt_pow (k + 1) x).div_const ((k + 1 : ℝ) ^ 2)
    have hpow2' : HasDerivAt (fun x : ℝ => x ^ (k + 1)) ((k + 1 : ℝ) * x ^ k) x := by
      simpa [Nat.cast_add, Nat.cast_one] using (hasDerivAt_pow (k + 1) x)
    have h2' := hpow2'.div_const ((k + 1 : ℝ) ^ 2)
    have hval : ((k + 1 : ℝ) * x ^ k) / ((k + 1 : ℝ) ^ 2) = x ^ k / (k + 1 : ℝ) := by
      field_simp [hk]
    exact h2'.congr_deriv hval
  have hd := hA.sub hB
  have hval2 : (x ^ k * Real.log x + x ^ k / (k + 1 : ℝ)) - x ^ k / (k + 1 : ℝ)
      = x ^ k * Real.log x := by ring
  exact hd.congr_deriv hval2

lemma tendsto_pow_log_zero {k : ℕ} :
    Tendsto (fun x : ℝ => x ^ (k + 1) * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmain := tendsto_log_mul_rpow_nhdsGT_zero (r := ((k + 1 : ℕ) : ℝ)) (by positivity : 0 < ((k + 1 : ℕ) : ℝ))
  have hrw : (fun x : ℝ => x ^ (k + 1) * Real.log x)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun x : ℝ => Real.log x * x ^ ((k + 1 : ℕ) : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    dsimp
    rw [← Real.rpow_natCast]
    ring
  exact hmain.congr' hrw.symm

lemma tendsto_P_zero {k : ℕ} :
    Tendsto (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)
        - x ^ (k + 1) / ((k + 1 : ℝ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := tendsto_pow_log_zero (k := k)
  have hpow0 : Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun x : ℝ => x ^ (k + 1)) 0 :=
      (continuous_pow (k + 1) : Continuous (fun x : ℝ => x ^ (k + 1))).continuousAt
    simpa using hc.tendsto
  have hA : Tendsto (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => (1 / (k + 1 : ℝ)) * (x ^ (k + 1) * Real.log x))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / (k + 1 : ℝ)) * 0)) := ht.const_mul (1 / (k + 1 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hc
  have hB : Tendsto (fun x : ℝ => x ^ (k + 1) / ((k + 1 : ℝ) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => (1 / ((k + 1 : ℝ) ^ 2)) * x ^ (k + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / ((k + 1 : ℝ) ^ 2)) * 0)) := hpow0.const_mul (1 / ((k + 1 : ℝ) ^ 2))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hc
  simpa using (hA.sub hB)

lemma continuousAt_P_one (k : ℕ) :
    ContinuousAt (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)
        - x ^ (k + 1) / ((k + 1 : ℝ) ^ 2)) 1 := by
  have hc1 : ContinuousAt (fun x : ℝ => x ^ (k + 1)) 1 := (continuous_pow (k + 1)).continuousAt
  have hc2 : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
  have hprod : ContinuousAt (fun x : ℝ => x ^ (k + 1) * Real.log x) 1 := hc1.mul hc2
  have hA : ContinuousAt (fun x : ℝ => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)) 1 := by
    simpa using hprod.div_const (k + 1 : ℝ)
  have hB : ContinuousAt (fun x : ℝ => x ^ (k + 1) / ((k + 1 : ℝ) ^ 2)) 1 := by
    simpa using hc1.div_const ((k + 1 : ℝ) ^ 2)
  exact hA.sub hB

lemma P_at_one (k : ℕ) :
    ((1 : ℝ) ^ (k + 1) * Real.log 1) / (k + 1 : ℝ) - (1 : ℝ) ^ (k + 1) / ((k + 1 : ℝ) ^ 2)
      = -(1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hk : (k + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  simp
  field_simp [hk]

lemma integral_pow_mul_log (k : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ k * Real.log x = -(1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  let P : ℝ → ℝ := fun x => (x ^ (k + 1) * Real.log x) / (k + 1 : ℝ)
      - x ^ (k + 1) / ((k + 1 : ℝ) ^ 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := P) (f' := fun x => x ^ k * Real.log x) (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) < 1)
    (fa := (0 : ℝ)) (fb := P 1) ?hderiv ?hint ?ha ?hb
  · have hfin : ∫ x in (0 : ℝ)..1, x ^ k * Real.log x = P 1 := by
      simpa [P] using hFTC
    rw [hfin]
    simp [P, P_at_one k]
  · intro x hx
    exact deriv_P (k := k) (ne_of_gt hx.1)
  · have hlogI : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have hcont : ContinuousOn (fun x : ℝ => x ^ k) [[(0 : ℝ), 1]] := by fun_prop
    -- log * x^k integrable; x^k·log x: product commutes
    have hmi : IntervalIntegrable (fun x : ℝ => Real.log x * x ^ k) MeasureTheory.volume (0 : ℝ) 1 :=
      hlogI.mul_continuousOn hcont
    simpa [mul_comm] using hmi
  · simpa [P] using (tendsto_P_zero (k := k))
  · have hc := continuousAt_P_one k
    simpa [P] using (tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto)

end Submission.CDT
