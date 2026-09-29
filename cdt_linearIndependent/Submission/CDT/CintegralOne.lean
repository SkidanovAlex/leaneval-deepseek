import Mathlib
import Submission.CDT.L2chi3Cintegral
import Submission.Commons.Analysis.Integral.integral_tsum_interval
import Submission.Commons.Analysis.Integral.integral_mul_integral_interval
import Submission.Commons.Analysis.Summation.sum_cintegralOne_core

/-!
# The `(Cintegral)` case `n = 1`: the double-integral evaluation `J₁ = Σₘ W(m)`

Target (the analytic leaf recorded in `L2chi3Cintegral`):

```lean
lemma cintegralJ_one_eq_sum_W : cintegralJ 1 = ∑' m : ℕ, cOneW m
```

Mathematical route (mirroring the commons proof of the `n = 0` square
identity `squareInverseKernelDoubleIntegral`, but with the binomial
expansion `(1−u³)⁻³ = Σₘ C(m+2,2)·u^{3m}` in place of the geometric
series):

kernel₁(s,t) = 9st(1−s³)(1−t³)/(1+st+s²t²)³,  u = st,
1+u+u² = (1−u³)/(1−u),  so
kernel₁(s,t) = (1−s³)(1−t³)·9u(1−u)³·Σₘ C(m+2,2)u^{3m}
             = Σₘ Aₘ(s,t),
Aₘ(s,t) = 9·((m+1)(m+2)/2)·(st)^{3m+1}·(1−st)³·(1−s³)(1−t³).

Two 1D Bochner interchanges (`integral_tsum_interval`, first in `t` for
a.e. `s`, then in `s`) reduce `J₁` to `Σₘ ∫∫Aₘ`; expanding `(1−st)³ =
Σᵢ₌₀³(−1)ⁱ C(3,i)(st)ⁱ` and using the monomial integrals
`∫₀¹ x^q(1−x³)dx = 3/((q+1)(q+4))` gives `∫∫Aₘ = W(m)` with the rational
summand `W(m)` of the commons identity `sum_cintegralOne_core`
(`Σₘ W(m) = 3·L(2,χ₋₃) − 2`).

Everything here is fully proved (no axioms, no `sorry`).

**Deliverables of this module** (all zero-`sorry`, in `Submission.CDT`):

* `cintegralJ_one_eq_sum_W : cintegralJ 1 = ∑' m, cOneW m` — the analytic
  leaf of the `(Cintegral)` `n = 1` evaluation, with `cOneW` the rational
  summand of the commons identity (equal to `Commons.Analysis.Summation.Tm`);
* `cintegralJ_one_eq_sum_W_inline` — the same with the summand written out;
* `cintegral_identity_one : CintegralIdentityOne` — the `(Cintegral)`
  coefficient identity at `n = 1` (`3·L(2,χ₋₃) − 2 = J₁`), assembled from
  `cintegralJ_one_eq_sum_W` + `squareSum_eq_L2chi3` +
  `sum_cintegralOne_core`;
* `cintegral_identity_le_one : ∀ n ≤ 1, CintegralIdentityAt n` — the first
  instances of the full `CintegralIdentity` (`L2chi3Cintegral`);
* `cintegralIdentity_iff_tail : CintegralIdentity ↔ CintegralIdentityTail` —
  since `n = 0, 1` are proved, the whole `(Cintegral)` identity is
  equivalent to its remaining tail (`n ≥ 2`).

(With the previously-proved `CintegralIdentity_zero` this closes the
`(Cintegral)` identity at `n = 0, 1` — the analytic-B route of node (2) of
`mainA` now needs only the general-`n` Beukers evaluation
`CintegralIdentity` (`n ≥ 2`) to discharge `OverconvergesUnit
eichlerDiffB` via `overconvergesB_of_cintegral`; the remaining layers of
`cdt_theoremA_leaf_gap` are recorded in `TheoremA_leaf`'s missing-lemma
ledger.)
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Interval

namespace Submission.CDT

/-! ## Definitions -/

/-- the `(Cintegral)` `n = 1` coefficient `9·(m+1)(m+2)/2` -/
def cOneCoef (m : ℕ) : ℝ := ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * 9

/-- the `(Cintegral)` `n = 1` kernel `9st(1−s³)(1−t³)/(1+st+s²t²)³` -/
def cOneKernel (s t : ℝ) : ℝ :=
  (9 : ℝ) * s * t * (1 - s ^ 3) * (1 - t ^ 3) / (1 + s * t + s ^ 2 * t ^ 2) ^ 3

/-- the `m`-th summand `Aₘ` of the binomial expansion of the kernel -/
def cOneAm (m : ℕ) (s t : ℝ) : ℝ :=
  cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3 * (1 - s ^ 3) * (1 - t ^ 3)

/-- the rational `m`-th term `W(m)` (equal to the commons summand `Tm m`) -/
def cOneW (m : ℕ) : ℝ := Commons.Analysis.Summation.Tm m

/-! ## elementary algebra -/

/-- `C(m+2,2) = (m+1)(m+2)/2` (real) -/
lemma cOne_choose (m : ℕ) :
    (Nat.choose (m + 2) 2 : ℝ) = ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) := by
  have h := Nat.cast_choose_two (K := ℝ) (m + 2)
  have hsub : ((m + 2 : ℕ) : ℝ) - 1 = ((m + 1 : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hsub] at h
  rw [mul_comm] at h
  exact h

/-- `(1−x)³ = Σᵢ₌₀³ (−1)ⁱ·C(3,i)·xⁱ` -/
lemma cube_sum_expand (x : ℝ) :
    (1 - x) ^ 3 = ∑ i ∈ Finset.range 4, (-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ) * x ^ i := by
  norm_num [Finset.sum_range_succ]
  ring

/-- pointwise expansion of `Aₘ` in powers of `st` -/
lemma cOneAm_expand (m : ℕ) (s t : ℝ) :
    cOneAm m s t = ∑ i ∈ Finset.range 4,
      cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (s * t) ^ (3 * m + 1 + i)
        * (1 - s ^ 3) * (1 - t ^ 3) := by
  unfold cOneAm
  calc
    cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3 * (1 - s ^ 3) * (1 - t ^ 3)
        = cOneCoef m * (1 - s ^ 3) * (1 - t ^ 3) * (s * t) ^ (3 * m + 1)
            * (1 - s * t) ^ 3 := by ring
    _ = cOneCoef m * (1 - s ^ 3) * (1 - t ^ 3) * (s * t) ^ (3 * m + 1)
            * (∑ i ∈ Finset.range 4, (-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ) * (s * t) ^ i) := by
          rw [← cube_sum_expand (s * t)]
    _ = ∑ i ∈ Finset.range 4, cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
            * (s * t) ^ (3 * m + 1 + i) * (1 - s ^ 3) * (1 - t ^ 3) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          calc
            cOneCoef m * (1 - s ^ 3) * (1 - t ^ 3) * (s * t) ^ (3 * m + 1)
                * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ) * (s * t) ^ i)
                = cOneCoef m * (1 - s ^ 3) * (1 - t ^ 3) * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                    * ((s * t) ^ (3 * m + 1) * (s * t) ^ i) := by ring
            _ = cOneCoef m * (1 - s ^ 3) * (1 - t ^ 3) * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                    * (s * t) ^ (3 * m + 1 + i) := by
                  rw [← pow_add]
            _ = cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (s * t) ^ (3 * m + 1 + i)
                    * (1 - s ^ 3) * (1 - t ^ 3) := by ring

/-! ## the binomial `(1−u³)⁻³ = Σₘ ((m+1)(m+2)/2)·u^{3m}` series -/

/-- `Σₘ ((m+1)(m+2)/2)·rᵐ = (1−r)⁻³` for `‖r‖ < 1` -/
lemma cOne_pow3_series {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * r ^ m) =
      1 / (1 - r) ^ 3 := by
  calc
    (∑' m : ℕ, ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * r ^ m)
        = ∑' m : ℕ, (Nat.choose (m + 2) 2 : ℝ) * r ^ m := by
          apply tsum_congr
          intro m
          rw [cOne_choose m]
    _ = 1 / (1 - r) ^ 3 := by
          simpa using (tsum_choose_mul_geometric_of_norm_lt_one (k := 2) (r := r) hr)

/-- summability of the same series -/
lemma cOne_pow3_summable {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * r ^ m) := by
  have h := summable_choose_mul_geometric_of_norm_lt_one (k := 2) (r := r) hr
  refine h.congr ?_
  intro m
  rw [cOne_choose m]

/-! ## the single-variable kernel series -/

/-- `Σₘ cOneCoef(m)·u^{3m+1}·(1−u)³ = 9u/(1+u+u²)³` for `0 ≤ u < 1` -/
lemma cOne_series (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' m : ℕ, cOneCoef m * u ^ (3 * m + 1) * (1 - u) ^ 3) = 9 * u / (1 + u + u ^ 2) ^ 3 := by
  have hu3 : ‖u ^ 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 3)]
    exact pow_lt_one₀ hu0 hu1 (by norm_num : (3 : ℕ) ≠ 0)
  have hpow3 := cOne_pow3_series (r := u ^ 3) hu3
  have hrew : ∀ m : ℕ, cOneCoef m * u ^ (3 * m + 1) * (1 - u) ^ 3 =
      (9 * u * (1 - u) ^ 3) * (((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * (u ^ 3) ^ m) := by
    intro m
    unfold cOneCoef
    have hu : u ^ (3 * m + 1) = u * (u ^ 3) ^ m := by
      calc
        u ^ (3 * m + 1) = u ^ (3 * m) * u := by rw [pow_succ]
        _ = (u ^ 3) ^ m * u := by rw [pow_mul u 3 m]
        _ = u * (u ^ 3) ^ m := by rw [mul_comm]
    rw [hu]
    ring
  calc
    (∑' m : ℕ, cOneCoef m * u ^ (3 * m + 1) * (1 - u) ^ 3)
        = ∑' m : ℕ, (9 * u * (1 - u) ^ 3)
            * (((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * (u ^ 3) ^ m) := by
          exact tsum_congr hrew
    _ = (9 * u * (1 - u) ^ 3) * (∑' m : ℕ,
            ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * (u ^ 3) ^ m) := by
          rw [tsum_mul_left]
    _ = (9 * u * (1 - u) ^ 3) * (1 / (1 - u ^ 3) ^ 3) := by rw [hpow3]
    _ = 9 * u / (1 + u + u ^ 2) ^ 3 := by
          have h1u : 1 - u ≠ 0 := by linarith
          have hden : 1 + u + u ^ 2 ≠ 0 := by
            have hsq : 0 ≤ u ^ 2 := sq_nonneg u
            nlinarith
          have hfac : 1 - u ^ 3 = (1 - u) * (1 + u + u ^ 2) := by ring
          have h1u3 : 1 - u ^ 3 ≠ 0 := by
            rw [hfac]
            exact mul_ne_zero h1u hden
          rw [hfac]
          field_simp [h1u, hden, h1u3]

/-! ## the pointwise kernel identity `Σₘ Aₘ = kernel₁` -/

/-- `Σₘ Aₘ(s,t) = kernel₁(s,t)` pointwise for `0 ≤ s, t`, `st < 1` -/
lemma cOneAm_tsum (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hst : s * t < 1) :
    (∑' m : ℕ, cOneAm m s t) = cOneKernel s t := by
  have hu0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hser := cOne_series (s * t) hu0 hst
  calc
    (∑' m : ℕ, cOneAm m s t)
        = ∑' m : ℕ, (1 - s ^ 3) * (1 - t ^ 3) * (cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3) := by
          apply tsum_congr
          intro m
          unfold cOneAm
          ring
    _ = (1 - s ^ 3) * (1 - t ^ 3) * (∑' m : ℕ,
          cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3) := by
          rw [tsum_mul_left]
    _ = (1 - s ^ 3) * (1 - t ^ 3) * (9 * (s * t) / (1 + s * t + (s * t) ^ 2) ^ 3) := by
          rw [hser]
    _ = cOneKernel s t := by
          unfold cOneKernel
          rw [← mul_pow s t 2]
          have hden : 1 + s * t + (s * t) ^ 2 ≠ 0 := by
            have hu : 0 ≤ s * t := mul_nonneg hs0 ht0
            have hsq : 0 ≤ (s * t) ^ 2 := sq_nonneg (s * t)
            nlinarith
          field_simp [hden]


/-! ## nonnegativity of the summands -/

/-- `cOneCoef m ≥ 0` -/
lemma cOneCoef_nonneg (m : ℕ) : 0 ≤ cOneCoef m := by
  unfold cOneCoef
  positivity

/-- `Aₘ(s,t) ≥ 0` on `[0,1]²` -/
lemma cOneAm_nonneg (m : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ cOneAm m s t := by
  have h1st : 0 ≤ 1 - s * t := sub_nonneg.mpr (mul_le_one₀ hs1 ht0 ht1)
  have h1s : 0 ≤ 1 - s ^ 3 := sub_nonneg.mpr (pow_le_one₀ hs0 hs1)
  have h1t : 0 ≤ 1 - t ^ 3 := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  have hpow : 0 ≤ (s * t) ^ (3 * m + 1) := pow_nonneg (mul_nonneg hs0 ht0) (3 * m + 1)
  have hpow3 : 0 ≤ (1 - s * t) ^ 3 := pow_nonneg h1st 3
  dsimp [cOneAm]
  have h1 : 0 ≤ cOneCoef m * (s * t) ^ (3 * m + 1) :=
    mul_nonneg (cOneCoef_nonneg m) hpow
  have h2 : 0 ≤ (cOneCoef m * (s * t) ^ (3 * m + 1)) * (1 - s * t) ^ 3 :=
    mul_nonneg h1 hpow3
  have h3 : 0 ≤ (cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3) * (1 - s ^ 3) :=
    mul_nonneg h2 h1s
  exact mul_nonneg h3 h1t

/-- the inner `t`-integral of `Aₘ(s,·)` is nonnegative for `s ∈ [0,1]` -/
lemma cOneInner_nonneg (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (∫ t in (0 : ℝ)..1, cOneAm m s t) := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact cOneAm_nonneg m hs0 hs1 ht.1 ht.2

/-- the norm of the inner integral equals the inner integral for `s ∈ [0,1]` -/
lemma cOneInner_norm_eq (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(∫ t in (0 : ℝ)..1, cOneAm m s t)‖ = ∫ t in (0 : ℝ)..1, cOneAm m s t := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cOneInner_nonneg m hs0 hs1)]

/-! ## the monomial integrals -/

/-- `∫₀¹ x^q·(1−x³) dx = 3/((q+1)(q+4))` -/

lemma cOne_int_one_sub_cube (q : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3)) =
      3 / (((q : ℝ) + 1) * ((q : ℝ) + 4)) := by
  have hpow : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, x ^ n) = 1 / (((n : ℝ) + 1)) :=
    Commons.Analysis.Integral.intervalIntegral_pow_zero_one
  calc
    (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3))
        = ∫ x in (0 : ℝ)..1, (x ^ q - x ^ (q + 3)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          calc
            x ^ q * (1 - x ^ 3) = x ^ q - x ^ q * x ^ 3 := by ring
            _ = x ^ q - x ^ (q + 3) := by
                  rw [← pow_add]
    _ = (∫ x in (0 : ℝ)..1, x ^ q) - (∫ x in (0 : ℝ)..1, x ^ (q + 3)) := by
          rw [intervalIntegral.integral_sub]
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
          · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = 1 / ((q : ℝ) + 1) - 1 / (((q + 3 : ℕ) : ℝ) + 1) := by
          rw [hpow q, hpow (q + 3)]
    _ = 1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 4) := by
          have hq34 : (((q + 3 : ℕ) : ℝ) + 1) = ((q : ℝ) + 4) := by norm_num; ring
          rw [hq34]
    _ = 3 / (((q : ℝ) + 1) * ((q : ℝ) + 4)) := by
          have h1 : (q : ℝ) + 1 ≠ 0 := by positivity
          have h4 : (q : ℝ) + 4 ≠ 0 := by positivity
          field_simp [h1, h4]
          ring

/-- the separable double monomial `∫₀¹∫₀¹ (xy)^p(1−x³)(1−y³) = `(3/((p+1)(p+4)))²` -/
lemma cOne_int_p_sq (p : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (x * y) ^ p * (1 - x ^ 3) * (1 - y ^ 3)) =
      (3 / (((p : ℝ) + 1) * ((p : ℝ) + 4))) ^ 2 := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (x * y) ^ p * (1 - x ^ 3) * (1 - y ^ 3))
        = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
            (x ^ p * (1 - x ^ 3)) * (y ^ p * (1 - y ^ 3)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply intervalIntegral.integral_congr
          intro y hy
          change (x * y) ^ p * (1 - x ^ 3) * (1 - y ^ 3) =
            x ^ p * (1 - x ^ 3) * (y ^ p * (1 - y ^ 3))
          rw [mul_pow]
          ring
    _ = (∫ x in (0 : ℝ)..1, x ^ p * (1 - x ^ 3))
          * (∫ y in (0 : ℝ)..1, y ^ p * (1 - y ^ 3)) := by
          exact (Commons.Analysis.Integral.integral_mul_integral_interval
            (fun x : ℝ => x ^ p * (1 - x ^ 3)) (fun y : ℝ => y ^ p * (1 - y ^ 3))
            (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)
            (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)).symm
    _ = (3 / (((p : ℝ) + 1) * ((p : ℝ) + 4))) ^ 2 := by
          rw [cOne_int_one_sub_cube p]
          ring

/-! ## the closed form of the inner integral -/

/-- the inner integral `∫₀¹ Aₘ(x,·)` is a polynomial in `x`:
`cOneCoef·(1−x³)·Σᵢ (−1)ⁱC(3,i)x^{3m+1+i}·(3/((3m+1+i:ℝ)+1)((3m+1+i:ℝ)+4))` -/
lemma cOneInnerClosed (m : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, cOneAm m x y) =
      cOneCoef m * (1 - x ^ 3) * (∑ i ∈ Finset.range 4,
        ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
          * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) := by
  have hterm (i : ℕ) : ∀ y : ℝ,
      cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (x * y) ^ (3 * m + 1 + i)
          * (1 - x ^ 3) * (1 - y ^ 3) =
        (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3) * x ^ (3 * m + 1 + i))
          * (y ^ (3 * m + 1 + i) * (1 - y ^ 3)) := by
    intro y
    have hxy : (x * y) ^ (3 * m + 1 + i) = x ^ (3 * m + 1 + i) * y ^ (3 * m + 1 + i) :=
      mul_pow x y (3 * m + 1 + i)
    rw [hxy]
    ring
  calc
    (∫ y in (0 : ℝ)..1, cOneAm m x y)
        = ∫ y in (0 : ℝ)..1, (∑ i ∈ Finset.range 4,
            cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (x * y) ^ (3 * m + 1 + i)
              * (1 - x ^ 3) * (1 - y ^ 3)) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact cOneAm_expand m x y
    _ = ∑ i ∈ Finset.range 4, (∫ y in (0 : ℝ)..1,
            cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (x * y) ^ (3 * m + 1 + i)
              * (1 - x ^ 3) * (1 - y ^ 3)) := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = ∑ i ∈ Finset.range 4,
          (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3) * x ^ (3 * m + 1 + i))
            * (∫ y in (0 : ℝ)..1, y ^ (3 * m + 1 + i) * (1 - y ^ 3)) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∫ y in (0 : ℝ)..1, cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                * (x * y) ^ (3 * m + 1 + i) * (1 - x ^ 3) * (1 - y ^ 3))
                = ∫ y in (0 : ℝ)..1,
                    (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3)
                        * x ^ (3 * m + 1 + i)) * (y ^ (3 * m + 1 + i) * (1 - y ^ 3)) := by
                  apply intervalIntegral.integral_congr
                  intro y hy
                  exact hterm i y
            _ = (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3)
                    * x ^ (3 * m + 1 + i))
                  * (∫ y in (0 : ℝ)..1, y ^ (3 * m + 1 + i) * (1 - y ^ 3)) := by
                  rw [intervalIntegral.integral_const_mul]
    _ = ∑ i ∈ Finset.range 4,
          cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3) * x ^ (3 * m + 1 + i)
            * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hq := cOne_int_one_sub_cube (3 * m + 1 + i)
          -- hq : ∫x x^q(1−x³) = 3/(((q:ℝ)+1)((q:ℝ)+4)) with q := 3m+1+i: the y-integral: rw [hq]
          rw [show (∫ y in (0 : ℝ)..1, y ^ (3 * m + 1 + i) * (1 - y ^ 3)) =
              3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)) by
            simpa using hq]
    _ = cOneCoef m * (1 - x ^ 3) * (∑ i ∈ Finset.range 4,
          ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
            * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) := by
          calc
            (∑ i ∈ Finset.range 4, cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * (1 - x ^ 3)
                * x ^ (3 * m + 1 + i)
                * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                = ∑ i ∈ Finset.range 4, (cOneCoef m * (1 - x ^ 3))
                    * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
                      * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = cOneCoef m * (1 - x ^ 3) * (∑ i ∈ Finset.range 4,
                    ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
                      * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) := by
                  rw [← Finset.mul_sum]


/-! ## the double integral equals the rational `W(m)` -/

/-- the `i`-th term of the double-monomial form (real denominators) -/
def cOneIntTerm (m : ℕ) (i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) *
    (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) ^ 2

/-- the `i`-th term of the `W(m)`-form (nat-cast denominators) -/
def cOneIntTerm' (m : ℕ) (i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) *
    (3 / ((((3 * m + 2 + i : ℕ) : ℝ) * ((3 * m + 5 + i : ℕ) : ℝ)))) ^ 2

/-- `cOneW m` unfolds to its explicit rational body -/
lemma cOneW_eq (m : ℕ) : cOneW m =
    ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * 9 *
      ((3 / ((((3 * m + 2 : ℕ) : ℝ) * ((3 * m + 5 : ℕ) : ℝ)))) ^ 2
        - 3 * (3 / ((((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 6 : ℕ) : ℝ)))) ^ 2
        + 3 * (3 / ((((3 * m + 4 : ℕ) : ℝ) * ((3 * m + 7 : ℕ) : ℝ)))) ^ 2
        - (3 / ((((3 * m + 5 : ℕ) : ℝ) * ((3 * m + 8 : ℕ) : ℝ)))) ^ 2) := by
  rfl

/-- the 4-term sum equals the explicit body of `cOneW m` -/
lemma cOne_sum_eq_W (m : ℕ) :
    (∑ i ∈ Finset.range 4, cOneIntTerm' m i) =
      ((3 / ((((3 * m + 2 : ℕ) : ℝ) * ((3 * m + 5 : ℕ) : ℝ)))) ^ 2
        - 3 * (3 / ((((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 6 : ℕ) : ℝ)))) ^ 2
        + 3 * (3 / ((((3 * m + 4 : ℕ) : ℝ) * ((3 * m + 7 : ℕ) : ℝ)))) ^ 2
        - (3 / ((((3 * m + 5 : ℕ) : ℝ) * ((3 * m + 8 : ℕ) : ℝ)))) ^ 2) := by
  simp [Finset.sum_range_succ, cOneIntTerm']
  ring

/-- `cOneCoef · Σᵢ term' = cOneW m` -/
lemma cOneCoef_sum_eq_W (m : ℕ) :
    cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm' m i) = cOneW m := by
  rw [cOneW_eq]
  rw [cOne_sum_eq_W]
  unfold cOneCoef
  ring


/-- the two denominator forms of the `i`-th monomial term agree -/
lemma cOneIntTerm_eq (m i : ℕ) : cOneIntTerm m i = cOneIntTerm' m i := by
  unfold cOneIntTerm cOneIntTerm'
  have h1 : (((3 * m + 1 + i : ℕ) : ℝ) + 1) = ((3 * m + 2 + i : ℕ) : ℝ) := by
    rw [show ((3 * m + 1 + i : ℕ) : ℝ) + 1 = ((3 * m + 1 + i + 1 : ℕ) : ℝ) by
      rw [Nat.cast_add]
      norm_num]
    congr 1
    omega
  have h4 : (((3 * m + 1 + i : ℕ) : ℝ) + 4) = ((3 * m + 5 + i : ℕ) : ℝ) := by
    rw [show ((3 * m + 1 + i : ℕ) : ℝ) + 4 = ((3 * m + 1 + i + 4 : ℕ) : ℝ) by
      rw [Nat.cast_add]
      norm_num]
    congr 1
    omega
  rw [h1, h4]

/-- the double integral equals the 4-term monomial form -/
lemma cOneDoubleInt_form (m : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y) =
      cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm m i) := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y)
        = ∫ x in (0 : ℝ)..1, cOneCoef m * (1 - x ^ 3)
            * (∑ i ∈ Finset.range 4, ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
              * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact cOneInnerClosed m x
    _ = ∫ x in (0 : ℝ)..1, (∑ i ∈ Finset.range 4,
          (cOneCoef m * (1 - x ^ 3))
            * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
              * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change cOneCoef m * (1 - x ^ 3) * (∑ i ∈ Finset.range 4,
                ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
                  * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))) =
              ∑ i ∈ Finset.range 4,
                (cOneCoef m * (1 - x ^ 3))
                  * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
                    * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range 4, (∫ x in (0 : ℝ)..1,
          (cOneCoef m * (1 - x ^ 3))
            * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
              * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))) := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = ∑ i ∈ Finset.range 4,
          (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
            * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
          * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hq := cOne_int_one_sub_cube (3 * m + 1 + i)
          calc
            (∫ x in (0 : ℝ)..1, (cOneCoef m * (1 - x ^ 3))
                * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
                  * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)))))
                = ∫ x in (0 : ℝ)..1, (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                    * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                    * (x ^ (3 * m + 1 + i) * (1 - x ^ 3)) := by
                  apply intervalIntegral.integral_congr
                  intro x hx
                  ring
            _ = (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                    * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                  * (∫ x in (0 : ℝ)..1, x ^ (3 * m + 1 + i) * (1 - x ^ 3)) := by
                  rw [intervalIntegral.integral_const_mul]
            _ = (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                    * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                  * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) := by
                  rw [show (∫ x in (0 : ℝ)..1, x ^ (3 * m + 1 + i) * (1 - x ^ 3)) =
                      3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4)) by
                    simpa using hq]
    _ = cOneCoef m * (∑ i ∈ Finset.range 4,
          ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
            * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) ^ 2) := by
          calc
            (∑ i ∈ Finset.range 4, (cOneCoef m * ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))
                = ∑ i ∈ Finset.range 4, cOneCoef m
                    * (((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                      * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = cOneCoef m * (∑ i ∈ Finset.range 4,
                    ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ))
                      * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))) ^ 2) := by
                  rw [← Finset.mul_sum]
    _ = cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm m i) := by rfl

/-- the double integral in `W(m)`-form -/
lemma cOneDoubleInt_form' (m : ℕ) :
    cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm m i) =
      cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm' m i) := by
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact cOneIntTerm_eq m i

/-- **the monomial evaluation** `∫₀¹∫₀¹ Aₘ = W(m)` -/
lemma cOneDoubleInt (m : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y) = cOneW m := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y)
        = cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm m i) := cOneDoubleInt_form m
    _ = cOneCoef m * (∑ i ∈ Finset.range 4, cOneIntTerm' m i) := cOneDoubleInt_form' m
    _ = cOneW m := cOneCoef_sum_eq_W m


/-! ## the interchanges -/

/-- for `s ∈ [0,1]` the `t`-integral of the kernel equals the `t`-integral of
its binomial expansion (they agree a.e. in `t`) -/
lemma cOneInnerKernel_geom {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t in (0 : ℝ)..1, cOneKernel s t) =
      ∫ t in (0 : ℝ)..1, (∑' m : ℕ, cOneAm m s t) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with t ht
  intro htI
  have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htI
  have ht0 : 0 ≤ t := le_of_lt ht'.1
  have ht1 : t ≤ 1 := ht'.2
  have htlt : t < 1 := lt_of_le_of_ne ht1 ht
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hstlt : s * t < 1 := by
    rcases lt_or_eq_of_le hs1 with hslt | hseq
    · calc
        s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht1 hs0
        _ = s := by rw [mul_one]
        _ < 1 := hslt
    · rw [hseq, one_mul]
      exact htlt
  exact (cOneAm_tsum s t hs0 ht0 hstlt).symm

/-- `Aₘ(s,t) ≤ cOneCoef·(st)^{3m+1}` on `[0,1]²` -/
lemma cOneAm_le_pow (m : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : cOneAm m s t ≤ cOneCoef m * (s * t) ^ (3 * m + 1) := by
  have h01 : 0 ≤ 1 - s * t := sub_nonneg.mpr (mul_le_one₀ hs1 ht0 ht1)
  have h11 : 1 - s * t ≤ 1 := by nlinarith [mul_nonneg hs0 ht0]
  have h1 : (1 - s * t) ^ 3 ≤ 1 := pow_le_one₀ h01 h11
  have h1s0 : 0 ≤ 1 - s ^ 3 := sub_nonneg.mpr (pow_le_one₀ hs0 hs1)
  have h1s1 : 1 - s ^ 3 ≤ 1 := by nlinarith [pow_nonneg hs0 3]
  have h1t0 : 0 ≤ 1 - t ^ 3 := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  have h1t1 : 1 - t ^ 3 ≤ 1 := by nlinarith [pow_nonneg ht0 3]
  have hprod : (1 - s * t) ^ 3 * (1 - s ^ 3) * (1 - t ^ 3) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ h1 h1s0 h1s1) h1t0 h1t1
  have hnon : 0 ≤ cOneCoef m * (s * t) ^ (3 * m + 1) :=
    mul_nonneg (cOneCoef_nonneg m) (pow_nonneg (mul_nonneg hs0 ht0) (3 * m + 1))
  unfold cOneAm
  rw [show cOneCoef m * (s * t) ^ (3 * m + 1) * (1 - s * t) ^ 3 * (1 - s ^ 3) * (1 - t ^ 3)
      = (cOneCoef m * (s * t) ^ (3 * m + 1))
          * ((1 - s * t) ^ 3 * (1 - s ^ 3) * (1 - t ^ 3)) by ring]
  simpa using (mul_le_mul_of_nonneg_left hprod hnon)

/-- the inner `t`-integral interchanges with the series for `0 ≤ s < 1` -/
lemma cOneInnerInterchange {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ t in (0 : ℝ)..1, (∑' m : ℕ, cOneAm m s t)) =
      (∑' m : ℕ, ∫ t in (0 : ℝ)..1, cOneAm m s t) := by
  have hs3 : ‖s ^ 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs0 3)]
    exact pow_lt_one₀ hs0 hs1 (by norm_num : (3 : ℕ) ≠ 0)
  have hsm1 : s ≤ 1 := le_of_lt hs1
  have hle : ∀ m : ℕ, (∫ t in (0 : ℝ)..1, ‖cOneAm m s t‖) ≤
      (9 * s) * (((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * (s ^ 3) ^ m) := by
    intro m
    calc
      (∫ t in (0 : ℝ)..1, ‖cOneAm m s t‖)
          ≤ ∫ t in (0 : ℝ)..1, cOneCoef m * (s * t) ^ (3 * m + 1) := by
            apply intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
            · exact Continuous.intervalIntegrable (by unfold cOneAm cOneCoef; fun_prop) (0 : ℝ) 1
            · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            have ht0 : 0 ≤ t := ht.1
            have ht1 : t ≤ 1 := ht.2
            have hnon : 0 ≤ cOneAm m s t := cOneAm_nonneg m hs0 hsm1 ht0 ht1
            rw [Real.norm_eq_abs, abs_of_nonneg hnon]
            exact cOneAm_le_pow m hs0 hsm1 ht0 ht1
      _ = cOneCoef m * s ^ (3 * m + 1) * (∫ t in (0 : ℝ)..1, t ^ (3 * m + 1)) := by
            calc
              (∫ t in (0 : ℝ)..1, cOneCoef m * (s * t) ^ (3 * m + 1))
                  = ∫ t in (0 : ℝ)..1, (cOneCoef m * s ^ (3 * m + 1)) * (t ^ (3 * m + 1)) := by
                    apply intervalIntegral.integral_congr
                    intro t ht
                    change cOneCoef m * (s * t) ^ (3 * m + 1) =
                      (cOneCoef m * s ^ (3 * m + 1)) * (t ^ (3 * m + 1))
                    rw [mul_pow]
                    ring
              _ = (cOneCoef m * s ^ (3 * m + 1)) * (∫ t in (0 : ℝ)..1, t ^ (3 * m + 1)) := by
                    rw [intervalIntegral.integral_const_mul]
      _ ≤ cOneCoef m * s ^ (3 * m + 1) := by
            have hint : (∫ t in (0 : ℝ)..1, t ^ (3 * m + 1)) ≤ 1 := by
              have hv := Commons.Analysis.Integral.intervalIntegral_pow_zero_one (3 * m + 1)
              rw [hv]
              apply (div_le_one (by positivity : 0 < (((3 * m + 1 : ℕ) : ℝ) + 1))).2
              have h0 : (0 : ℝ) ≤ ((3 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
              nlinarith
            have hnon : 0 ≤ cOneCoef m * s ^ (3 * m + 1) :=
              mul_nonneg (cOneCoef_nonneg m) (pow_nonneg hs0 _)
            simpa using (mul_le_mul_of_nonneg_left hint hnon)
      _ = (9 * s) * (((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * (s ^ 3) ^ m) := by
            unfold cOneCoef
            have hs_pow : s ^ (3 * m + 1) = s * (s ^ 3) ^ m := by
              calc
                s ^ (3 * m + 1) = s ^ (3 * m) * s := by rw [pow_succ]
                _ = (s ^ 3) ^ m * s := by rw [pow_mul s 3 m]
                _ = s * (s ^ 3) ^ m := by rw [mul_comm]
            rw [hs_pow]
            ring
  have hsum : Summable (fun m : ℕ => ∫ t in (0 : ℝ)..1, ‖cOneAm m s t‖) := by
    refine Summable.of_nonneg_of_le ?_ hle ?_
    · intro m
      exact intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
        (fun t => norm_nonneg (cOneAm m s t))
    · exact (cOne_pow3_summable (r := s ^ 3) hs3).mul_left (9 * s)
  exact (Commons.Analysis.Integral.integral_tsum_interval (f := fun m t => cOneAm m s t)
    (fun m => Continuous.intervalIntegrable (by unfold cOneAm cOneCoef; fun_prop) (0 : ℝ) 1) hsum).symm

/-- `x ↦ ∫₀¹ Aₘ(x,·)` is continuous -/
lemma cOneInner_continuous (m : ℕ) :
    Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, cOneAm m x y) := by
  have heq : (fun x : ℝ => ∫ y in (0 : ℝ)..1, cOneAm m x y) =
      (fun x : ℝ => cOneCoef m * (1 - x ^ 3) * (∑ i ∈ Finset.range 4,
        ((-1 : ℝ) ^ i * (Nat.choose 3 i : ℝ)) * x ^ (3 * m + 1 + i)
          * (3 / ((((3 * m + 1 + i : ℕ) : ℝ) + 1) * (((3 * m + 1 + i : ℕ) : ℝ) + 4))))) := by
    funext x
    exact cOneInnerClosed m x
  rw [heq]
  fun_prop

/-- `Σₘ W(m)` converges (commons: `hasSum_Tm`) -/
lemma cOneW_summable : Summable cOneW := by
  exact Commons.Analysis.Summation.hasSum_Tm.summable

/-- summability of the outer sequence of norms of inner integrals -/
lemma cOneOuterSummable : Summable (fun m : ℕ =>
    ∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, cOneAm m x y)‖) := by
  refine (cOneW_summable.congr ?_)
  intro m
  calc
    cOneW m = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y) := (cOneDoubleInt m).symm
    _ = ∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, cOneAm m x y)‖ := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
          exact (cOneInner_norm_eq m hx'.1 hx'.2).symm

/-- the outer `x`-integral interchanges with the series over `m` -/
lemma cOneOuterInterchange :
    (∫ x in (0 : ℝ)..1, (∑' m : ℕ, (∫ y in (0 : ℝ)..1, cOneAm m x y))) =
      (∑' m : ℕ, ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y) := by
  exact (Commons.Analysis.Integral.integral_tsum_interval
    (f := fun m x => ∫ y in (0 : ℝ)..1, cOneAm m x y)
    (fun m => Continuous.intervalIntegrable (cOneInner_continuous m) (0 : ℝ) 1)
    cOneOuterSummable).symm

/-! ## the main theorem -/

/-- **the `(Cintegral)` `n = 1` double-integral evaluation**:
`J₁ = Σₘ W(m)` -/
theorem cintegralJ_one_eq_sum_W : cintegralJ 1 = ∑' m : ℕ, cOneW m := by
  calc
    cintegralJ 1 = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneKernel x y) := by
      rw [cintegralJ_one_unfold]
      rfl
    _ = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (∑' m : ℕ, cOneAm m x y)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact cOneInnerKernel_geom hx'.1 hx'.2
    _ = (∫ x in (0 : ℝ)..1, (∑' m : ℕ, (∫ y in (0 : ℝ)..1, cOneAm m x y))) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with x hx
      intro hxI
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxI
      have hx0 : 0 < x := hx'.1
      have hxle : x ≤ 1 := hx'.2
      have hxlt : x < 1 := lt_of_le_of_ne hxle hx
      exact cOneInnerInterchange (le_of_lt hx0) hxlt
    _ = ∑' m : ℕ, (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, cOneAm m x y) := cOneOuterInterchange
    _ = ∑' m : ℕ, cOneW m := by
      apply tsum_congr
      intro m
      exact cOneDoubleInt m

/-! ## the `(Cintegral)` instance `n = 1` -/

/-- **`CintegralIdentityOne` is proved**: `3·L(2,χ₋₃) − 2 = J₁` -/
theorem cintegral_identity_one : CintegralIdentityOne := by
  rw [CintegralIdentityOne_eq]
  calc
    (3 : ℝ) * L2chi3Real - 2 = 3 * (∑' k : ℕ,
        ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2) - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) - 2 := by
          rw [← squareSum_eq_L2chi3]
    _ = (∑' m : ℕ, cOneW m) := by
          exact (Commons.Analysis.Summation.sum_cintegralOne_core).symm
    _ = cintegralJ 1 := by
          exact cintegralJ_one_eq_sum_W.symm


/-- **the same evaluation with the rational summand written out** (the
displayed form of the paper / of the `L2chi3Cintegral` docstring): -/
theorem cintegralJ_one_eq_sum_W_inline : cintegralJ 1 = ∑' m : ℕ,
    ((((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) / 2) * 9 *
      ((3 / ((((3 * m + 2 : ℕ) : ℝ) * ((3 * m + 5 : ℕ) : ℝ)))) ^ 2
        - 3 * (3 / ((((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 6 : ℕ) : ℝ)))) ^ 2
        + 3 * (3 / ((((3 * m + 4 : ℕ) : ℝ) * ((3 * m + 7 : ℕ) : ℝ)))) ^ 2
        - (3 / ((((3 * m + 5 : ℕ) : ℝ) * ((3 * m + 8 : ℕ) : ℝ)))) ^ 2) := by
  rw [cintegralJ_one_eq_sum_W]
  apply tsum_congr
  intro m
  exact cOneW_eq m


/-! ## first instances of `CintegralIdentity` (all `n`) -/

/-- **the `(Cintegral)` instances at `n = 0` and `n = 1`**:
`CintegralIdentityAt n` for every `n ≤ 1` (the analytic-B route of node (2)
of `mainA` needs the general-`n` Beukers evaluation `CintegralIdentity`
for `n ≥ 8` to discharge `OverconvergesUnit eichlerDiffB` via
`overconvergesB_of_cintegral`; the instances at `n ≤ 7` are closed in
`CintegralOne`–`CintegralSeven`/`CintegralAssembled`). -/
theorem cintegral_identity_le_one : ∀ n : ℕ, n ≤ 1 → CintegralIdentityAt n := by
  intro n hn
  interval_cases n
  · change L2chi3Real * (HA_coeff 0 : ℝ) - 2 * (HB_coeff 0 : ℝ) = cintegralJ 0
    exact CintegralIdentity_zero
  · change L2chi3Real * (HA_coeff 1 : ℝ) - 2 * (HB_coeff 1 : ℝ) = cintegralJ 1
    exact cintegral_identity_one

/-- **`CintegralIdentity` ⟺ its tail** (`n ≥ 2`): the `n = 0, 1`
instances are proved (and in fact every `n ≤ 7`, see
`cintegral_identity_le_seven`), so the whole identity is equivalent to the
remaining general-`n` Beukers evaluation `CintegralIdentityTail`. -/
lemma cintegralIdentity_iff_tail : CintegralIdentity ↔ CintegralIdentityTail := by
  constructor
  · intro h n hn2
    exact h n
  · intro h n
    by_cases hn0 : n = 0
    · subst n
      change L2chi3Real * (HA_coeff 0 : ℝ) - 2 * (HB_coeff 0 : ℝ) = cintegralJ 0
      exact CintegralIdentity_zero
    · by_cases hn1 : n = 1
      · subst n
        exact cintegral_identity_one
      · have hn2 : 2 ≤ n := by omega
        exact h n hn2


end Submission.CDT
