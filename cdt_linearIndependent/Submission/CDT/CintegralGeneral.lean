import Mathlib
import Submission.CDT.L2chi3Cintegral
import Submission.Commons.Analysis.Integral.integral_tsum_interval
import Submission.Commons.Analysis.Integral.integral_mul_integral_interval
import Submission.Commons.Analysis.Integral.int_pow_mul_one_sub_cube_general

/-!
# The general-`n` Beukers expansion of the `(Cintegral)` double integral

The per-degree modules `CintegralOne`–`CintegralTwentyOne` prove, one
degree at a time, the Beukers double-integral evaluation

```lean
theorem cintegralJ_n_eq_sum_W : cintegralJ n = ∑' m : ℕ, Wₙ(m)
```

of the `(Cintegral)` period integrals `Jₙ = ∫₀¹∫₀¹ Kₙ` with

`Kₙ(s,t) = 9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}`.

This module proves the **same evaluation for all `n` at once** — i.e. the
general-`n` Beukers expansion of the period integral:

```lean
theorem cintegralJ_eq_sum_W_gen (n : ℕ) : cintegralJ n = ∑' m : ℕ, genW n m
```

with the parametric summand

`genW n m = 9ⁿ·C(m+2n,2n)·Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)·(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²`

(`genW`, `genMono`, `genProd` below).  This is exactly the paper's display
`(Cintegral)` (CDT, arXiv:2408.15403, remark after Prop. `functionsH`) —
one half of the coefficient identity
`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` (`CintegralIdentityAt n`); the other half is the
evaluation `Σₘ Wₙ(m) = aₙ·L(2,χ₋₃) − 2·bₙ` of the `m`-sum, which the
commons creative-telescoping cores provide degree by degree
(`Commons.Analysis.Summation.sum_cintegral{One,..,TwentyOne}_core`).

**Method** (the per-degree template, parametrized in `n`).
`1/(1+st+s²t²) = (1−st)/(1−(st)³)` turns the kernel into the binomial
series `Σₘ C(m+2n,2n)(st)^{3m}`, so `Kₙ = Σₘ Aₘ⁽ⁿ⁾` with

`Aₘ⁽ⁿ⁾(s,t) = 9ⁿC(m+2n,2n)(st)^{3m+n}(1−st)^{2n+1}(1−s³)ⁿ(1−t³)ⁿ`.

Two one-dimensional Bochner interchanges (dominated by the geometric
series, `gen_pow3_summable`) reduce `Jₙ` to `Σₘ ∫∫Aₘ⁽ⁿ⁾`; expanding
`(1−st)^{2n+1}` (`one_sub_pow_eq_sum`) and using the general monomial
integral `∫₀¹x^q(1−x³)ⁿ dx = 3ⁿn!/∏_{k≤n}(q+1+3k)` (commons
`int_pow_mul_one_sub_cube_general`) gives `∫∫Aₘ⁽ⁿ⁾ = genW n m`.

Everything here is fully proved (no axioms, no `sorry`).

## What remains of the `(Cintegral)` route, and how it can be attacked

By `CintegralIdentity_of_genW_sum` the *whole* coefficient identity
`CintegralIdentity` follows from the single parametric `m`-sum evaluation

```lean
∀ n, (∑' m : ℕ, genW n m) = L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ)
```

(equivalently, by `CintegralAssembled.CintegralIdentity_of_recurrence`, from
the Zagier recurrence `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}` for the
double integrals).  The per-degree commons creative-telescoping cores
`sum_cintegral<N>_core` supply this one degree at a time (the light
per-degree modules combine them with `cintegralJ_eq_sum_W_gen`).

Three routes to the parametric statement, with what is known about each:

* **2-D creative telescoping / Almkvist–Zeilberger** on the hyperexponential
  family `Kₙ = 9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}` (this is what the
  paper cites `[AZ]`, Almkvist–Zeilberger, *The method of differentiating
  under the integral sign*, for).  Writing `R = 1+st+s²t²`,
  `W = st(1−s³)(1−t³)`, `u = W/R²` (so `Kₙ = (9u)ⁿ/R`, `max 9u = 1` at
  `s = t = 1/2`), the recurrence is equivalent to a *pointwise* identity
  `∂_s(uP) + ∂_t(uQ) = G(n,u)/R` with `G(n,u) = 9(n+1)²u² − (10n²+10n+3)u + n²`
  and the boundary terms of `(9u)ⁿ(P,Q)` cancelling (`u` vanishes on
  `{s ∈ {0,1}} ∪ {t ∈ {0,1}}`, so `n ≥ 1` kills them automatically).  A
  recorded **obstruction**: with `P, Q` *polynomials in `n`* the `n`-powers
  separate, forcing each component `g_k(u)/R` (`g₂ = 9u²−10u+1`,
  `g₁ = 18u²−10u`, `g₀ = 9u²−3u`) to integrate to `0`; but
  `∫∫g₂(u)/R = J₂/9 − 10J₁/9 + J₀ = 17/18 − 2L/3 ≠ 0` (from the proved
  instances).  So the certificate must be genuinely `x`-dependent (e.g. the
  ODE form `L_x f_x = ∂_sA + ∂_tB` with `f_x = R/(R²−9Wx)`, denominators
  `(R² − 9Wx)`), or act on the `m`-summands;
* **Griffiths–Dwork / Milnor-ring reduction**: work in `ℚ[s,t]/(∂_sF, ∂_tF)`
  for `F = 9u`, reducing `F^{n+1}ω` modulo exact forms to get the
  Picard–Fuchs-type recurrence — finite linear algebra, no explicit
  certificate, but needs the Gauss–Manin setup;
* **the `m`-summand route**: evaluate `Sₙ(m) = Σᵢ(−1)ⁱC(2n+1,i)Mₙ(3m+n+i)²`
  by residues/finite differences (an alternating sum of order `2n+1` over a
  rational function with `n+1` double poles) and telescope in `m`; this is
  presumably the paper's "a little effort by hand", but the closed form of
  `Sₙ(m)` is not recorded anywhere in the repository yet.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Interval

namespace Submission.CDT

/-! ## The parametric data -/

/-- the `(Cintegral)` degree-`n` coefficient `9ⁿ·C(m+2n,2n)` -/
def genCoef (n m : ℕ) : ℝ := (Nat.choose (m + 2 * n) (2 * n) : ℝ) * (9 : ℝ) ^ n

/-- the `(Cintegral)` kernel `Kₙ = 9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}` -/
def genKernel (n : ℕ) (s t : ℝ) : ℝ :=
  (9 : ℝ) ^ n * (s * t) ^ n * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
    / (1 + s * t + s ^ 2 * t ^ 2) ^ (2 * n + 1)

/-- the `m`-th summand `Aₘ⁽ⁿ⁾` of the binomial expansion of the kernel -/
def genAm (n m : ℕ) (s t : ℝ) : ℝ :=
  genCoef n m * (s * t) ^ (3 * m + n) * (1 - s * t) ^ (2 * n + 1)
    * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n

/-- the general monomial integral value `∫₀¹ x^q (1−x³)ⁿ dx = 3ⁿn!/∏_{k≤n}(q+1+3k)` -/
def genMono (n q : ℕ) : ℝ :=
  ((3 : ℝ) ^ n * (n.factorial : ℝ))
    / ∏ k ∈ Finset.range (n + 1), ((q : ℝ) + 1 + 3 * (k : ℝ))

/-- the nat-cast product `∏_{k≤n}(3m+n+1+3k+i)` (real) -/
def genProd (n m i : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (((3 * m + n + 1 + 3 * k + i : ℕ)) : ℝ)

/-- the `i`-th monomial term of the double-integral form, in `M`-notation -/
def genIntTerm (n m i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (genMono n (3 * m + n + i)) ^ 2

/-- the `i`-th monomial term of the `Wₙ(m)`-form (nat-cast denominators) -/
def genIntTerm' (n m i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
    * (((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i) ^ 2

/-- the rational `m`-th term
`Wₙ(m) = 9ⁿ·C(m+2n,2n)·Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)·(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²` -/
def genW (n m : ℕ) : ℝ := genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i)

/-! ## the binomial series `(1−r)^{-(2n+1)} = Σₘ C(m+2n,2n) rᵐ` -/

lemma gen_pow3_series (n : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' m : ℕ, (Nat.choose (m + 2 * n) (2 * n) : ℝ) * r ^ m)
      = 1 / (1 - r) ^ ((2 * n : ℕ) + 1) :=
  tsum_choose_mul_geometric_of_norm_lt_one (k := 2 * n) (r := r) hr

lemma gen_pow3_summable (n : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => (Nat.choose (m + 2 * n) (2 * n) : ℝ) * r ^ m) :=
  summable_choose_mul_geometric_of_norm_lt_one (k := 2 * n) (r := r) hr

/-! ## the `(2n+1)`-st power expansion -/

/-- `(1−x)^N = Σᵢ₌₀^N (−1)ⁱ·C(N,i)·xⁱ` -/
lemma one_sub_pow_eq_sum (N : ℕ) (x : ℝ) :
    (1 - x) ^ N = ∑ i ∈ Finset.range (N + 1), (-1 : ℝ) ^ i * (Nat.choose N i : ℝ) * x ^ i := by
  have h := add_pow (1 : ℝ) (-x) N
  rw [show (1 : ℝ) + -x = 1 - x by ring] at h
  rw [h, ← Finset.sum_range_reflect
    (fun j => (1 : ℝ) ^ j * (-x) ^ (N - j) * (N.choose j : ℝ)) (N + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ N := by
    have := Finset.mem_range.mp hi
    omega
  have h1 : N + 1 - 1 - i = N - i := by omega
  have h2 : N - (N - i) = i := by omega
  rw [h1, h2, Nat.choose_symm hi']
  ring

/-! ## the single-variable kernel series -/

/-- `Σₘ genCoef(n,m)·u^{3m+n}·(1−u)^{2n+1} = 9ⁿuⁿ/(1+u+u²)^{2n+1}` for `0 ≤ u < 1` -/
lemma gen_series (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' m : ℕ, genCoef n m * u ^ (3 * m + n) * (1 - u) ^ (2 * n + 1))
      = (9 : ℝ) ^ n * u ^ n / (1 + u + u ^ 2) ^ (2 * n + 1) := by
  have hu3 : ‖u ^ 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 3)]
    exact pow_lt_one₀ hu0 hu1 (by norm_num : (3 : ℕ) ≠ 0)
  have hser := gen_pow3_series n (r := u ^ 3) hu3
  have hrew : ∀ m : ℕ, genCoef n m * u ^ (3 * m + n) * (1 - u) ^ (2 * n + 1) =
      ((9 : ℝ) ^ n * u ^ n * (1 - u) ^ (2 * n + 1))
        * ((Nat.choose (m + 2 * n) (2 * n) : ℝ) * (u ^ 3) ^ m) := by
    intro m
    unfold genCoef
    have hu : u ^ (3 * m + n) = u ^ n * (u ^ 3) ^ m := by
      calc
        u ^ (3 * m + n) = u ^ (3 * m) * u ^ n := by rw [pow_add]
        _ = (u ^ 3) ^ m * u ^ n := by rw [pow_mul]
        _ = u ^ n * (u ^ 3) ^ m := by rw [mul_comm]
    rw [hu]
    ring
  calc
    (∑' m : ℕ, genCoef n m * u ^ (3 * m + n) * (1 - u) ^ (2 * n + 1))
        = ∑' m : ℕ, ((9 : ℝ) ^ n * u ^ n * (1 - u) ^ (2 * n + 1))
            * ((Nat.choose (m + 2 * n) (2 * n) : ℝ) * (u ^ 3) ^ m) :=
          tsum_congr hrew
    _ = ((9 : ℝ) ^ n * u ^ n * (1 - u) ^ (2 * n + 1))
          * (∑' m : ℕ, (Nat.choose (m + 2 * n) (2 * n) : ℝ) * (u ^ 3) ^ m) := by
          rw [tsum_mul_left]
    _ = ((9 : ℝ) ^ n * u ^ n * (1 - u) ^ (2 * n + 1))
          * (1 / (1 - u ^ 3) ^ ((2 * n : ℕ) + 1)) := by rw [hser]
    _ = (9 : ℝ) ^ n * u ^ n / (1 + u + u ^ 2) ^ (2 * n + 1) := by
          have h1u : 1 - u ≠ 0 := by linarith
          have hden : 1 + u + u ^ 2 ≠ 0 := by nlinarith [sq_nonneg u]
          have hfac : 1 - u ^ 3 = (1 - u) * (1 + u + u ^ 2) := by ring
          have h1u3 : 1 - u ^ 3 ≠ 0 := by
            rw [hfac]
            exact mul_ne_zero h1u hden
          rw [hfac, mul_pow]
          field_simp [h1u, hden, h1u3]

/-! ## nonnegativity and domination of the summands -/

lemma genCoef_nonneg (n m : ℕ) : 0 ≤ genCoef n m := by
  unfold genCoef
  exact mul_nonneg (by exact_mod_cast (Nat.zero_le (Nat.choose (m + 2 * n) (2 * n))))
    (by positivity)

lemma genAm_nonneg (n m : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ genAm n m s t := by
  have h1st : 0 ≤ 1 - s * t := sub_nonneg.mpr (mul_le_one₀ hs1 ht0 ht1)
  have hpow : 0 ≤ (s * t) ^ (3 * m + n) := pow_nonneg (mul_nonneg hs0 ht0) _
  have hpowN : 0 ≤ (1 - s * t) ^ (2 * n + 1) := pow_nonneg h1st _
  dsimp [genAm]
  have h1 : 0 ≤ genCoef n m * (s * t) ^ (3 * m + n) :=
    mul_nonneg (genCoef_nonneg n m) hpow
  have h2 : 0 ≤ (genCoef n m * (s * t) ^ (3 * m + n)) * (1 - s * t) ^ (2 * n + 1) :=
    mul_nonneg h1 hpowN
  have h3 : 0 ≤ (genCoef n m * (s * t) ^ (3 * m + n) * (1 - s * t) ^ (2 * n + 1))
      * (1 - s ^ 3) ^ n :=
    mul_nonneg h2 (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ hs0 hs1)) n)
  exact mul_nonneg h3 (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ ht0 ht1)) n)

lemma genInner_nonneg (n m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (∫ t in (0 : ℝ)..1, genAm n m s t) := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact genAm_nonneg n m hs0 hs1 ht.1 ht.2

lemma genInner_norm_eq (n m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(∫ t in (0 : ℝ)..1, genAm n m s t)‖ = ∫ t in (0 : ℝ)..1, genAm n m s t := by
  rw [Real.norm_eq_abs, abs_of_nonneg (genInner_nonneg n m hs0 hs1)]

lemma genAm_le_pow (n m : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : genAm n m s t ≤ genCoef n m * (s * t) ^ (3 * m + n) := by
  have h01 : 0 ≤ 1 - s * t := sub_nonneg.mpr (mul_le_one₀ hs1 ht0 ht1)
  have h11 : 1 - s * t ≤ 1 := by nlinarith [mul_nonneg hs0 ht0]
  have h1 : (1 - s * t) ^ (2 * n + 1) ≤ 1 := pow_le_one₀ h01 h11
  have h1s0 : 0 ≤ 1 - s ^ 3 := sub_nonneg.mpr (pow_le_one₀ hs0 hs1)
  have h1s1 : 1 - s ^ 3 ≤ 1 := by nlinarith [pow_nonneg hs0 3]
  have h1t0 : 0 ≤ 1 - t ^ 3 := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  have h1t1 : 1 - t ^ 3 ≤ 1 := by nlinarith [pow_nonneg ht0 3]
  have hs3 : (1 - s ^ 3) ^ n ≤ 1 := pow_le_one₀ h1s0 h1s1
  have ht3 : (1 - t ^ 3) ^ n ≤ 1 := pow_le_one₀ h1t0 h1t1
  have hprod : (1 - s * t) ^ (2 * n + 1) * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ h1 (pow_nonneg h1s0 n) hs3) (pow_nonneg h1t0 n) ht3
  have hnon : 0 ≤ genCoef n m * (s * t) ^ (3 * m + n) :=
    mul_nonneg (genCoef_nonneg n m) (pow_nonneg (mul_nonneg hs0 ht0) _)
  dsimp [genAm]
  rw [show genCoef n m * (s * t) ^ (3 * m + n) * (1 - s * t) ^ (2 * n + 1)
        * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
      = (genCoef n m * (s * t) ^ (3 * m + n))
          * ((1 - s * t) ^ (2 * n + 1) * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n) by ring]
  simpa using (mul_le_mul_of_nonneg_left hprod hnon)

/-! ## the pointwise kernel identity `Σₘ Aₘ⁽ⁿ⁾ = Kₙ` -/

lemma genAm_tsum (n : ℕ) (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hst : s * t < 1) :
    (∑' m : ℕ, genAm n m s t) = genKernel n s t := by
  have hu0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hser := gen_series n (s * t) hu0 hst
  calc
    (∑' m : ℕ, genAm n m s t)
        = ∑' m : ℕ, (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
            * (genCoef n m * (s * t) ^ (3 * m + n) * (1 - s * t) ^ (2 * n + 1)) := by
          apply tsum_congr
          intro m
          unfold genAm
          ring
    _ = (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
          * (∑' m : ℕ, genCoef n m * (s * t) ^ (3 * m + n) * (1 - s * t) ^ (2 * n + 1)) := by
          rw [tsum_mul_left]
    _ = (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
          * ((9 : ℝ) ^ n * (s * t) ^ n / (1 + s * t + (s * t) ^ 2) ^ (2 * n + 1)) := by
          rw [hser]
    _ = genKernel n s t := by
          unfold genKernel
          have hsq : (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
          rw [hsq]
          have hden : 1 + s * t + s ^ 2 * t ^ 2 ≠ 0 := by
            nlinarith [sq_nonneg (s * t)]
          field_simp [hden]

/-! ## the general monomial integrals -/

/-- the general monomial integral `∫₀¹x^q(1−x³)ⁿ dx = genMono n q`
(commons `int_pow_mul_one_sub_cube_general`) -/
lemma gen_int (n q : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3) ^ n) = genMono n q := by
  simpa [genMono] using (Commons.Analysis.Integral.int_pow_mul_one_sub_cube_general q n)

/-- the separable double monomial `∫₀¹∫₀¹ (xy)^p(1−x³)ⁿ(1−y³)ⁿ = (genMono n p)²` -/
lemma gen_int_p (n p : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (x * y) ^ p * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n) = (genMono n p) ^ 2 := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (x * y) ^ p * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n)
        = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
            (x ^ p * (1 - x ^ 3) ^ n) * (y ^ p * (1 - y ^ 3) ^ n) := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply intervalIntegral.integral_congr
          intro y hy
          change (x * y) ^ p * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n =
            x ^ p * (1 - x ^ 3) ^ n * (y ^ p * (1 - y ^ 3) ^ n)
          rw [mul_pow]
          ring
    _ = (∫ x in (0 : ℝ)..1, x ^ p * (1 - x ^ 3) ^ n)
          * (∫ y in (0 : ℝ)..1, y ^ p * (1 - y ^ 3) ^ n) := by
          exact (Commons.Analysis.Integral.integral_mul_integral_interval
            (fun x : ℝ => x ^ p * (1 - x ^ 3) ^ n)
            (fun y : ℝ => y ^ p * (1 - y ^ 3) ^ n)
            (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)
            (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)).symm
    _ = (genMono n p) ^ 2 := by
          rw [gen_int n p]
          ring

/-! ## pointwise expansion of the summand -/

lemma genAm_expand (n m : ℕ) (x y : ℝ) :
    genAm n m x y = ∑ i ∈ Finset.range (2 * n + 2),
      genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (x * y) ^ (3 * m + n + i)
        * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n := by
  have hexp := one_sub_pow_eq_sum (2 * n + 1) (x * y)
  rw [show (2 * n + 1) + 1 = 2 * n + 2 by omega] at hexp
  unfold genAm
  calc
    genCoef n m * (x * y) ^ (3 * m + n) * (1 - x * y) ^ (2 * n + 1)
        * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n
        = genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n * (x * y) ^ (3 * m + n)
            * (1 - x * y) ^ (2 * n + 1) := by ring
    _ = genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n * (x * y) ^ (3 * m + n)
            * (∑ i ∈ Finset.range (2 * n + 2),
                (-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ) * (x * y) ^ i) := by
          rw [← hexp]
    _ = ∑ i ∈ Finset.range (2 * n + 2), genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n
            * (x * y) ^ (3 * m + n)
            * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ) * (x * y) ^ i) := by
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (2 * n + 2), genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
            * (x * y) ^ (3 * m + n + i) * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n * (x * y) ^ (3 * m + n)
                * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ) * (x * y) ^ i)
                = genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n
                    * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * ((x * y) ^ (3 * m + n) * (x * y) ^ i) := by ring
            _ = genCoef n m * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n
                    * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * (x * y) ^ (3 * m + n + i) := by
                  rw [← pow_add]
            _ = genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * (x * y) ^ (3 * m + n + i) * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n := by ring

/-- the monomial index identity `genMono n (3m+n+i) = 3ⁿn!/genProd n m i` -/
lemma genMono_eq (n m i : ℕ) :
    genMono n (3 * m + n + i) = ((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i := by
  unfold genMono genProd
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  push_cast
  ring

/-! ## the closed form of the inner integral -/

lemma genInnerClosed (n m : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, genAm n m x y) =
      genCoef n m * (1 - x ^ 3) ^ n * (∑ i ∈ Finset.range (2 * n + 2),
        ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
          * genMono n (3 * m + n + i)) := by
  calc
    (∫ y in (0 : ℝ)..1, genAm n m x y)
        = ∫ y in (0 : ℝ)..1, (∑ i ∈ Finset.range (2 * n + 2),
            genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (x * y) ^ (3 * m + n + i)
              * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact genAm_expand n m x y
    _ = ∑ i ∈ Finset.range (2 * n + 2), (∫ y in (0 : ℝ)..1,
            genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (x * y) ^ (3 * m + n + i)
              * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n) := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = ∑ i ∈ Finset.range (2 * n + 2),
          (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (1 - x ^ 3) ^ n
            * x ^ (3 * m + n + i))
          * (∫ y in (0 : ℝ)..1, y ^ (3 * m + n + i) * (1 - y ^ 3) ^ n) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∫ y in (0 : ℝ)..1, genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                * (x * y) ^ (3 * m + n + i) * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n)
                = ∫ y in (0 : ℝ)..1,
                    (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (1 - x ^ 3) ^ n
                      * x ^ (3 * m + n + i)) * (y ^ (3 * m + n + i) * (1 - y ^ 3) ^ n) := by
                  apply intervalIntegral.integral_congr
                  intro y hy
                  change genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                      * (x * y) ^ (3 * m + n + i) * (1 - x ^ 3) ^ n * (1 - y ^ 3) ^ n =
                    (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (1 - x ^ 3) ^ n
                      * x ^ (3 * m + n + i)) * (y ^ (3 * m + n + i) * (1 - y ^ 3) ^ n)
                  rw [mul_pow]
                  ring
            _ = (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (1 - x ^ 3) ^ n
                    * x ^ (3 * m + n + i))
                  * (∫ y in (0 : ℝ)..1, y ^ (3 * m + n + i) * (1 - y ^ 3) ^ n) := by
                  rw [intervalIntegral.integral_const_mul]
    _ = ∑ i ∈ Finset.range (2 * n + 2),
          genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (1 - x ^ 3) ^ n
            * x ^ (3 * m + n + i) * genMono n (3 * m + n + i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hq := gen_int n (3 * m + n + i)
          rw [show (∫ y in (0 : ℝ)..1, y ^ (3 * m + n + i) * (1 - y ^ 3) ^ n) =
              genMono n (3 * m + n + i) by
            simpa using hq]
    _ = genCoef n m * (1 - x ^ 3) ^ n * (∑ i ∈ Finset.range (2 * n + 2),
          ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
            * genMono n (3 * m + n + i)) := by
          calc
            (∑ i ∈ Finset.range (2 * n + 2), genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                * (1 - x ^ 3) ^ n * x ^ (3 * m + n + i) * genMono n (3 * m + n + i))
                = ∑ i ∈ Finset.range (2 * n + 2), (genCoef n m * (1 - x ^ 3) ^ n)
                    * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                        * genMono n (3 * m + n + i)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = genCoef n m * (1 - x ^ 3) ^ n * (∑ i ∈ Finset.range (2 * n + 2),
                    ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                      * genMono n (3 * m + n + i)) := by
                  rw [← Finset.mul_sum]

lemma genInner_continuous (n m : ℕ) :
    Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, genAm n m x y) := by
  have heq : (fun x : ℝ => ∫ y in (0 : ℝ)..1, genAm n m x y) =
      (fun x : ℝ => genCoef n m * (1 - x ^ 3) ^ n * (∑ i ∈ Finset.range (2 * n + 2),
        ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
          * genMono n (3 * m + n + i))) := by
    funext x
    exact genInnerClosed n m x
  rw [heq]
  fun_prop

/-! ## the double integral equals the rational `Wₙ(m)` -/

lemma genIntTerm_eq (n m i : ℕ) : genIntTerm n m i = genIntTerm' n m i := by
  unfold genIntTerm genIntTerm'
  rw [genMono_eq n m i]

lemma genDoubleInt_form (n m : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y) =
      genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm n m i) := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y)
        = ∫ x in (0 : ℝ)..1, genCoef n m * (1 - x ^ 3) ^ n
            * (∑ i ∈ Finset.range (2 * n + 2),
                ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                  * genMono n (3 * m + n + i)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact genInnerClosed n m x
    _ = ∫ x in (0 : ℝ)..1, (∑ i ∈ Finset.range (2 * n + 2),
          (genCoef n m * (1 - x ^ 3) ^ n)
            * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
              * genMono n (3 * m + n + i))) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change genCoef n m * (1 - x ^ 3) ^ n * (∑ i ∈ Finset.range (2 * n + 2),
                ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                  * genMono n (3 * m + n + i)) =
              ∑ i ∈ Finset.range (2 * n + 2), (genCoef n m * (1 - x ^ 3) ^ n)
                * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                  * genMono n (3 * m + n + i))
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (2 * n + 2), (∫ x in (0 : ℝ)..1,
          (genCoef n m * (1 - x ^ 3) ^ n)
            * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
              * genMono n (3 * m + n + i))) := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
    _ = ∑ i ∈ Finset.range (2 * n + 2),
          (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
              * genMono n (3 * m + n + i)) * genMono n (3 * m + n + i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hq := gen_int n (3 * m + n + i)
          calc
            (∫ x in (0 : ℝ)..1, (genCoef n m * (1 - x ^ 3) ^ n)
                * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * x ^ (3 * m + n + i)
                  * genMono n (3 * m + n + i)))
                = ∫ x in (0 : ℝ)..1, (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * genMono n (3 * m + n + i)) * (x ^ (3 * m + n + i) * (1 - x ^ 3) ^ n) := by
                  apply intervalIntegral.integral_congr
                  intro x hx
                  ring
            _ = (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * genMono n (3 * m + n + i))
                  * (∫ x in (0 : ℝ)..1, x ^ (3 * m + n + i) * (1 - x ^ 3) ^ n) := by
                  rw [intervalIntegral.integral_const_mul]
            _ = (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                    * genMono n (3 * m + n + i)) * genMono n (3 * m + n + i) := by
                  rw [show (∫ x in (0 : ℝ)..1, x ^ (3 * m + n + i) * (1 - x ^ 3) ^ n) =
                      genMono n (3 * m + n + i) by simpa using hq]
    _ = genCoef n m * (∑ i ∈ Finset.range (2 * n + 2),
          ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (genMono n (3 * m + n + i)) ^ 2) := by
          calc
            (∑ i ∈ Finset.range (2 * n + 2), (genCoef n m * ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ))
                * genMono n (3 * m + n + i)) * genMono n (3 * m + n + i))
                = ∑ i ∈ Finset.range (2 * n + 2), genCoef n m
                    * (((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (genMono n (3 * m + n + i)) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = genCoef n m * (∑ i ∈ Finset.range (2 * n + 2),
                    ((-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)) * (genMono n (3 * m + n + i)) ^ 2) := by
                  rw [← Finset.mul_sum]
    _ = genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm n m i) := rfl

lemma genDoubleInt_form' (n m : ℕ) :
    genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm n m i) =
      genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i) := by
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact genIntTerm_eq n m i

/-- **the monomial evaluation** `∫₀¹∫₀¹ Aₘ⁽ⁿ⁾ = Wₙ(m)` -/
lemma genDoubleInt (n m : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y) = genW n m := by
  calc
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y)
        = genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm n m i) :=
          genDoubleInt_form n m
    _ = genCoef n m * (∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i) :=
          genDoubleInt_form' n m
    _ = genW n m := rfl

/-! ## the inner (`t`) interchange -/

lemma genInnerKernel_geom (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t in (0 : ℝ)..1, genKernel n s t) =
      ∫ t in (0 : ℝ)..1, (∑' m : ℕ, genAm n m s t) := by
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
  exact (genAm_tsum n s t hs0 ht0 hstlt).symm

lemma genInnerInterchange (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ t in (0 : ℝ)..1, (∑' m : ℕ, genAm n m s t)) =
      (∑' m : ℕ, ∫ t in (0 : ℝ)..1, genAm n m s t) := by
  have hs3 : ‖s ^ 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs0 3)]
    exact pow_lt_one₀ hs0 hs1 (by norm_num : (3 : ℕ) ≠ 0)
  have hsm1 : s ≤ 1 := le_of_lt hs1
  have hle : ∀ m : ℕ, (∫ t in (0 : ℝ)..1, ‖genAm n m s t‖) ≤
      ((9 : ℝ) ^ n * s ^ n) * ((Nat.choose (m + 2 * n) (2 * n) : ℝ) * (s ^ 3) ^ m) := by
    intro m
    calc
      (∫ t in (0 : ℝ)..1, ‖genAm n m s t‖)
          ≤ ∫ t in (0 : ℝ)..1, genCoef n m * (s * t) ^ (3 * m + n) := by
            apply intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1)
            · exact Continuous.intervalIntegrable (by unfold genAm genCoef; fun_prop) (0 : ℝ) 1
            · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            have ht0 : 0 ≤ t := ht.1
            have ht1 : t ≤ 1 := ht.2
            have hnon : 0 ≤ genAm n m s t := genAm_nonneg n m hs0 hsm1 ht0 ht1
            rw [Real.norm_eq_abs, abs_of_nonneg hnon]
            exact genAm_le_pow n m hs0 hsm1 ht0 ht1
      _ = genCoef n m * s ^ (3 * m + n) * (∫ t in (0 : ℝ)..1, t ^ (3 * m + n)) := by
            calc
              (∫ t in (0 : ℝ)..1, genCoef n m * (s * t) ^ (3 * m + n))
                  = ∫ t in (0 : ℝ)..1, (genCoef n m * s ^ (3 * m + n)) * (t ^ (3 * m + n)) := by
                    apply intervalIntegral.integral_congr
                    intro t ht
                    change genCoef n m * (s * t) ^ (3 * m + n) =
                      (genCoef n m * s ^ (3 * m + n)) * (t ^ (3 * m + n))
                    rw [mul_pow]
                    ring
              _ = (genCoef n m * s ^ (3 * m + n)) * (∫ t in (0 : ℝ)..1, t ^ (3 * m + n)) := by
                    rw [intervalIntegral.integral_const_mul]
      _ ≤ genCoef n m * s ^ (3 * m + n) := by
            have hint : (∫ t in (0 : ℝ)..1, t ^ (3 * m + n)) ≤ 1 := by
              have hv := Commons.Analysis.Integral.intervalIntegral_pow_zero_one (3 * m + n)
              rw [hv]
              apply (div_le_one (by positivity : 0 < (((3 * m + n : ℕ) : ℝ) + 1))).2
              have h0 : (0 : ℝ) ≤ ((3 * m + n : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
              nlinarith
            have hnon : 0 ≤ genCoef n m * s ^ (3 * m + n) :=
              mul_nonneg (genCoef_nonneg n m) (pow_nonneg hs0 _)
            simpa using (mul_le_mul_of_nonneg_left hint hnon)
      _ = ((9 : ℝ) ^ n * s ^ n) * ((Nat.choose (m + 2 * n) (2 * n) : ℝ) * (s ^ 3) ^ m) := by
            unfold genCoef
            have hs_pow : s ^ (3 * m + n) = s ^ n * (s ^ 3) ^ m := by
              calc
                s ^ (3 * m + n) = s ^ (3 * m) * s ^ n := by rw [pow_add]
                _ = (s ^ 3) ^ m * s ^ n := by rw [pow_mul]
                _ = s ^ n * (s ^ 3) ^ m := by rw [mul_comm]
            rw [hs_pow]
            ring
  have hsum : Summable (fun m : ℕ => ∫ t in (0 : ℝ)..1, ‖genAm n m s t‖) := by
    refine Summable.of_nonneg_of_le ?_ hle ?_
    · intro m
      exact intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
        (fun t => norm_nonneg (genAm n m s t))
    · exact (gen_pow3_summable n (r := s ^ 3) hs3).mul_left ((9 : ℝ) ^ n * s ^ n)
  exact (Commons.Analysis.Integral.integral_tsum_interval (f := fun m t => genAm n m s t)
    (fun m => Continuous.intervalIntegrable (by unfold genAm genCoef; fun_prop) (0 : ℝ) 1)
    hsum).symm

/-! ## summability of `genW` (crude comparison with `Σ 1/(m+1)²`) -/

/-- the denominator-clearing helper
`genY n m = (3ⁿn!/∏_{k≤n}(3m+1+3k))²`-scale -/
def genY (n m : ℕ) : ℝ :=
  (((3 : ℝ) ^ n * (n.factorial : ℝ)) / (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1)) ^ 2

/-- the constant in the crude bound `|Wₙ(m)| ≤ genBoundConst n/(m+1)²` -/
def genBoundConst (n : ℕ) : ℝ :=
  (9 : ℝ) ^ n * (((3 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)
    * (((2 * n + 1 : ℕ)) : ℝ) ^ (2 * n) * 2 ^ (2 * n + 1)

lemma genProd_ge (n m i : ℕ) :
    (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1) ≤ genProd n m i := by
  have hprod : (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1)
      = ∏ k ∈ Finset.range (n + 1), (((3 * m + 1 : ℕ)) : ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hprod]
  unfold genProd
  apply Finset.prod_le_prod₀
  · intro k hk
    positivity
  · intro k hk
    exact_mod_cast (show (3 * m + 1 : ℕ) ≤ 3 * m + n + 1 + 3 * k + i by omega)

/-- the `i`-th term of `Wₙ(m)` is bounded by the `i`-th binomial times `genY n m` -/
lemma genIntTerm'_abs_le (n m i : ℕ) :
    |genIntTerm' n m i| ≤ (Nat.choose (2 * n + 1) i : ℝ) * genY n m := by
  have hge := genProd_ge n m i
  have hpos : 0 < (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1) := by positivity
  have hposp : 0 < genProd n m i := lt_of_lt_of_le hpos hge
  have hle : ((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i
      ≤ ((3 : ℝ) ^ n * (n.factorial : ℝ)) / (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1) :=
    div_le_div_of_nonneg_left (by positivity) hpos hge
  have hsq : (((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i) ^ 2
      ≤ (((3 : ℝ) ^ n * (n.factorial : ℝ)) / (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have habs : |(-1 : ℝ) ^ i * (Nat.choose (2 * n + 1) i : ℝ)|
      = (Nat.choose (2 * n + 1) i : ℝ) := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
    exact_mod_cast Nat.zero_le _
  have hX : |(((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i) ^ 2|
      = (((3 : ℝ) ^ n * (n.factorial : ℝ)) / genProd n m i) ^ 2 :=
    abs_of_nonneg (pow_nonneg (div_nonneg (by positivity) (le_of_lt hposp)) 2)
  unfold genIntTerm' genY
  rw [abs_mul, habs, hX]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- the `i`-sum of `Wₙ(m)` is bounded by `2^{2n+1}·genY n m` -/
lemma genW_sum_bound (n m : ℕ) :
    |∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i| ≤ 2 ^ (2 * n + 1) * genY n m := by
  have hY : (0 : ℝ) ≤ genY n m := by unfold genY; positivity
  calc
    |∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i|
        ≤ ∑ i ∈ Finset.range (2 * n + 2), |genIntTerm' n m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2 * n + 2), (Nat.choose (2 * n + 1) i : ℝ) * genY n m :=
          Finset.sum_le_sum (fun i hi => genIntTerm'_abs_le n m i)
    _ = (∑ i ∈ Finset.range (2 * n + 2), (Nat.choose (2 * n + 1) i : ℝ)) * genY n m := by
          rw [Finset.sum_mul]
    _ = 2 ^ (2 * n + 1) * genY n m := by
          have h : (∑ i ∈ Finset.range (2 * n + 2), (Nat.choose (2 * n + 1) i : ℝ))
              = (2 : ℝ) ^ (2 * n + 1) := by
            have hnat : (∑ i ∈ Finset.range (2 * n + 2), Nat.choose (2 * n + 1) i)
                = 2 ^ (2 * n + 1) := by
              rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
              exact Nat.sum_range_choose (2 * n + 1)
            exact_mod_cast hnat
          rw [h]

/-- `genCoef n m ≤ 9ⁿ·(2n+1)^{2n}·(m+1)^{2n}` -/
lemma genCoef_le (n m : ℕ) :
    genCoef n m ≤ (9 : ℝ) ^ n * (((2 * n + 1 : ℕ)) : ℝ) ^ (2 * n) * ((m : ℝ) + 1) ^ (2 * n) := by
  have h1 : (Nat.choose (m + 2 * n) (2 * n) : ℝ) ≤ ((m + 2 * n : ℕ) : ℝ) ^ (2 * n) := by
    exact_mod_cast Nat.choose_le_pow (m + 2 * n) (2 * n)
  have h2 : ((m + 2 * n : ℕ) : ℝ) ≤ (((2 * n + 1 : ℕ)) : ℝ) * ((m : ℝ) + 1) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity, show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have h3 : ((m + 2 * n : ℕ) : ℝ) ^ (2 * n)
      ≤ ((((2 * n + 1 : ℕ)) : ℝ) * ((m : ℝ) + 1)) ^ (2 * n) :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((m + 2 * n : ℕ) : ℝ)) h2 (2 * n)
  calc
    genCoef n m = (Nat.choose (m + 2 * n) (2 * n) : ℝ) * (9 : ℝ) ^ n := by
      unfold genCoef; ring
    _ ≤ ((((2 * n + 1 : ℕ)) : ℝ) * ((m : ℝ) + 1)) ^ (2 * n) * (9 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (le_trans h1 h3) (by positivity)
    _ = (9 : ℝ) ^ n * (((2 * n + 1 : ℕ)) : ℝ) ^ (2 * n) * ((m : ℝ) + 1) ^ (2 * n) := by
          rw [mul_pow]; ring

/-- `genY n m ≤ (3ⁿn!)²/(m+1)^{2n+2}` -/
lemma genY_le (n m : ℕ) :
    genY n m ≤ ((3 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2 / ((m : ℝ) + 1) ^ (2 * n + 2) := by
  have hge : ((m : ℝ) + 1) ≤ (((3 * m + 1 : ℕ)) : ℝ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hp : ((m : ℝ) + 1) ^ (n + 1) ≤ (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1)) hge (n + 1)
  have hpos1 : 0 < ((m : ℝ) + 1) ^ (n + 1) := by positivity
  have hle : ((3 : ℝ) ^ n * (n.factorial : ℝ)) / (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1)
      ≤ ((3 : ℝ) ^ n * (n.factorial : ℝ)) / ((m : ℝ) + 1) ^ (n + 1) :=
    div_le_div_of_nonneg_left (by positivity) hpos1 hp
  calc
    genY n m
        = (((3 : ℝ) ^ n * (n.factorial : ℝ)) / (((3 * m + 1 : ℕ)) : ℝ) ^ (n + 1)) ^ 2 := by
          unfold genY; ring
    _ ≤ (((3 : ℝ) ^ n * (n.factorial : ℝ)) / ((m : ℝ) + 1) ^ (n + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hle 2
    _ = ((3 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2 / ((m : ℝ) + 1) ^ (2 * n + 2) := by
          rw [div_pow, ← pow_mul, show (n + 1) * 2 = 2 * n + 2 by omega]

/-- the crude bound `|Wₙ(m)| ≤ genBoundConst n/(m+1)²` -/
lemma genW_abs_le (n m : ℕ) : |genW n m| ≤ genBoundConst n / ((m : ℝ) + 1) ^ 2 := by
  have hsum := genW_sum_bound n m
  have hYle := genY_le n m
  have hcoef := genCoef_le n m
  have hstep : |genW n m|
      ≤ ((9 : ℝ) ^ n * (((2 * n + 1 : ℕ)) : ℝ) ^ (2 * n) * ((m : ℝ) + 1) ^ (2 * n))
        * (2 ^ (2 * n + 1)
            * (((3 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2 / ((m : ℝ) + 1) ^ (2 * n + 2))) := by
    unfold genW
    rw [abs_mul, abs_of_nonneg (genCoef_nonneg n m)]
    have h1 : |∑ i ∈ Finset.range (2 * n + 2), genIntTerm' n m i| ≤ 2 ^ (2 * n + 1) * genY n m := hsum
    have h2 : 2 ^ (2 * n + 1) * genY n m
        ≤ 2 ^ (2 * n + 1)
            * (((3 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2 / ((m : ℝ) + 1) ^ (2 * n + 2)) :=
      mul_le_mul_of_nonneg_left hYle (by positivity)
    exact mul_le_mul hcoef (le_trans h1 h2) (abs_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  unfold genBoundConst
  have hne : ((m : ℝ) + 1) ^ (2 * n) ≠ 0 := by positivity
  rw [pow_add]
  field_simp [hne]
  ring

lemma genW_summable (n : ℕ) : Summable (genW n) := by
  have hbase : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    have h2 : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow (p := 2) |>.mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr h2
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => genBoundConst n * ((m : ℝ) + 1)⁻¹ ^ 2) ?_ ?_
  · refine (hbase.mul_left (genBoundConst n)).congr (fun m => ?_)
    rw [div_eq_mul_inv, inv_pow]
    ring
  · intro m
    rw [Real.norm_eq_abs]
    refine le_trans (genW_abs_le n m) (le_of_eq ?_)
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-! ## the outer (`s`) interchange and the main theorem -/

/-- the kernel coincides with `cintegralKernel` -/
lemma genKernel_eq_cintegral (n : ℕ) (s t : ℝ) : cintegralKernel n s t = genKernel n s t := by
  unfold cintegralKernel genKernel
  rw [mul_pow]
  ring

lemma genOuterSummable (n : ℕ) : Summable (fun m : ℕ =>
    ∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, genAm n m x y)‖) := by
  refine (genW_summable n).congr ?_
  intro m
  calc
    genW n m = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y) :=
      (genDoubleInt n m).symm
    _ = ∫ x in (0 : ℝ)..1, ‖(∫ y in (0 : ℝ)..1, genAm n m x y)‖ := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
          exact (genInner_norm_eq n m hx'.1 hx'.2).symm

lemma genOuterInterchange (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (∑' m : ℕ, (∫ y in (0 : ℝ)..1, genAm n m x y))) =
      (∑' m : ℕ, ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y) := by
  exact (Commons.Analysis.Integral.integral_tsum_interval
    (f := fun m x => ∫ y in (0 : ℝ)..1, genAm n m x y)
    (fun m => Continuous.intervalIntegrable (genInner_continuous n m) (0 : ℝ) 1)
    (genOuterSummable n)).symm

/-- **the general-`n` Beukers expansion of the `(Cintegral)` double integral**:
`Jₙ = Σₘ Wₙ(m)` for every `n`. -/
theorem cintegralJ_eq_sum_W_gen (n : ℕ) : cintegralJ n = ∑' m : ℕ, genW n m := by
  calc
    cintegralJ n = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genKernel n x y) := by
      rw [show cintegralJ n = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          cintegralKernel n x y by rfl]
      apply intervalIntegral.integral_congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      exact genKernel_eq_cintegral n x y
    _ = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (∑' m : ℕ, genAm n m x y)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact genInnerKernel_geom n hx'.1 hx'.2
    _ = (∫ x in (0 : ℝ)..1, (∑' m : ℕ, (∫ y in (0 : ℝ)..1, genAm n m x y))) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with x hx
      intro hxI
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxI
      have hx0 : 0 < x := hx'.1
      have hxle : x ≤ 1 := hx'.2
      have hxlt : x < 1 := lt_of_le_of_ne hxle hx
      exact genInnerInterchange n (le_of_lt hx0) hxlt
    _ = ∑' m : ℕ, (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, genAm n m x y) :=
      genOuterInterchange n
    _ = ∑' m : ℕ, genW n m := by
      apply tsum_congr
      intro m
      exact genDoubleInt n m

/-- **the coefficient identity from the parametric `m`-sum evaluation**: if the
`m`-sum of `genW n ·` evaluates to `L(2,χ₋₃)·aₙ − 2·bₙ` for every `n`, then the
whole `(Cintegral)` identity follows (via the general Beukers expansion
`cintegralJ_eq_sum_W_gen`). -/
theorem CintegralIdentity_of_genW_sum
    (hW : ∀ n : ℕ, (∑' m : ℕ, genW n m)
      = L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ)) :
    CintegralIdentity := by
  intro n
  rw [CintegralIdentityAt, ← hW n, ← cintegralJ_eq_sum_W_gen n]

end Submission.CDT
