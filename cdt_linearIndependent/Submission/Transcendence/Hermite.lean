import Mathlib

/-!
# Hermite's theorem: the transcendence of `e`

First transcendence theorem of this development: `e = Complex.exp 1` is
transcendental over `ℚ` (Hermite 1873).

Proof sketch (classical Hermite proof in integer-polynomial form; details in
the lemmas below). Suppose `q ∈ ℤ[X]`, `q ≠ 0`, `q.eval 0 ≠ 0`, with
`aeval e q = 0`.  For a prime `p` and `N = q.natDegree` define

`fₚ(x) = x^(p-1) · (∏_{i=1}^N (x − i))^p ∈ ℤ[X]`,  `Fₚ = sumIDeriv fₚ`,

`J = Σ_{k=0}^{N} cₖ · Fₚ(k) / (p-1)!` where `cₖ = q.coeff k`.

* **Arithmetic**: each `Fₚ(k)/(p−1)!` is an integer; divisible by `p` for
  `k ≥ 1`; and `Fₚ(0)/(p−1)! ≡ ±(N!)ᵖ (mod p)`.  Hence for prime
  `p > max N |c₀|`, `J` is an integer not divisible by `p`, so `|J| ≥ 1`.
* **Identity**: `d/dx (e⁻ˣF(x)) = −e⁻ˣ f(x)` gives
  `F(k) − eᵏF(0) = −eᵏ∫₀ᵏ e⁻ᵗf(t)dt`; summing against `cₖ` and using
  `Σ cₖ eᵏ = 0` yields `J = −Σₖ cₖ P(fₚ,k) / (p−1)!`.
* **Estimate**: `|P(fₚ,k)| ≤ Cᵖ` for `k ≤ N` (analytic part), so
  `|J| ≤ Cᵖ/(p−1)! < 1` for large `p`, contradicting `|J| ≥ 1`.

The analytic ingredient is reproduced as public lemmas below (the same facts
in `Lindemann.AnalyticalPart` are private); the arithmetic ingredient is
developed from scratch.  This is the template for Lindemann's theorem
(`e^α` transcendental for algebraic `α ≠ 0`), needed for the `m = n` corner of
Theorem C of Calegari–Dimitrov–Tang, and eventually Lindemann–Weierstrass.
-/

/-!
# Status (build progress, session by session)

All lemmas below are **fully proved** (no axioms, no `sorry`).

* §1 (P machinery, analytic bound): the exact integral representation
  `P_eq_integral_exp_mul_eval` and the exponential bound `P_le` — public
  restatements of the (private) lemmas in `Lindemann.AnalyticalPart`.
* §2 (Hermite polynomial): `hermitePoly N p = X^(p-1)·(∏_{i=1}^N (X−i))^p`
  and its pointwise bound `‖fₚ(z)‖ ≤ (N·(2N)^N)^p` for `‖z‖ ≤ N`.
* §3 (arithmetic core): `sumIDeriv_hermite_zero` and
  `sumIDeriv_hermite_pos`, i.e. `Fₚ(0) = (p−1)!·h(0)ᵖ + p!·u₀` and
  `Fₚ(k) = p!·uₖ` for `1 ≤ k ≤ N`, from `aeval_sumIDeriv(_of_pos)`.
* §4 (bridges to ℂ): `sumIDerivAt`, `sumIDeriv_cval`, `exp_natCast`.
* §5a (algebraic setup): `exists_minimal_int_poly` — from
  `IsAlgebraic ℚ x`, `x ≠ 0`, a nonzero `q : ℤ[X]` killing `x` with
  `q.eval 0 ≠ 0` (minimal degree).  Key input: Mathlib's
  `IsFractionRing.isAlgebraic_iff` (clearing denominators for free).
* §5b (integer quotients): `quotAt`, `quotAt_zero` (`A₀ ≡ h(0)ᵖ (mod p)`),
  `quotAt_pos` (`p | Aₖ` for `1 ≤ k ≤ N`).
* §5c (`J` and its nonzero-ness): `hermJ`, `hermJ_mod`
  (`J ≡ c₀·h(0)ᵖ (mod p)`), `hermJ_ne_zero` (prime `p > N`, `p ∤ c₀` ⟹
  `J ≠ 0`), plus the factorial-value facts `natAbs_hermProd_eval_zero` etc.
* §5d (the exact identity): `aeval_sum_exp`, `hermJ_eq_sum_range`/
  `hermJ_cval`, the factorial-divisibility of all `sₖ` and quotient casts,
  the generic `hermite_identity` (`Σₖ cₖ·Fₖ = −Σₖ cₖ·Pₖ` from
  `Σₖ cₖ·eᵏ = 0`), and the main `hermJ_mul_factorial`:
  `(J:ℂ)·(p−1)! = −Σₖ (cₖ:ℂ)·P(fₚ,(k:ℂ))`.
* §5e (analytic bound and contradiction): `P_le_explicit`,
  `P_hermite_bound` (uniform `‖P(fₚ,(k:ℂ))‖ ≤ B(N)ᵖ`),
  `Psum_bound` (`‖Σₖ cₖPₖ‖ ≤ (S·B)ᵖ`), the eventual factorial bound
  `pow_div_factorial_pred_eventually_lt`, and the main theorem
  **`exp_one_transcendental : Transcendental ℚ (cexp 1)`** (Hermite).
* §6 (transfer to the reals): `isAlgebraic_complex_of_isAlgebraic_real`
  (algebraicity over ℚ transfers along ℝ → ℂ, via
  `isIntegral_algebraMap_iff`) and
  **`real_exp_one_transcendental : Transcendental ℚ (Real.exp 1)`
  (name chosen without the `Real.` prefix to avoid colliding with the ℝ
  namespace inside `Submission.Transcendence`)**.

**Next steps (future sessions):** generalize the §5 development to
Lindemann's theorem — `Transcendental ℚ (cexp z)` for algebraic `z ≠ 0` —
replacing only the algebraic setup §5a (the root polynomial of `z` and its
conjugates, via `minpoly`/the denominator machinery, instead of `X·∏(X−i)`)
and the final “exponentials ℚ-independent” wrapper (a polynomial relation
`Σ cₖ·e^{k·z} = 0` from `eᶻ` algebraic of degree `N`); this is what the
`m = n` corner of Theorem C of Calegari–Dimitrov–Tang needs
(`Irrational (log(1+1/m))²`).

Target applications beyond this file (same §-structure, replace the
algebraic-setup step):
* Lindemann: `Transcendental ℚ (cexp z)` for algebraic `z ≠ 0` — the `m = n`
  corner of Theorem C of Calegari–Dimitrov–Tang needs it for `z = log(1+1/m)`.
* Lindemann–Weierstrass via `exp_polynomial_approx` (linear-independence form).
-/

noncomputable section

open Complex Polynomial
open scoped BigOperators

namespace Submission.Transcendence

/-! ## 1.  The functional `P` and its analytic bound -/

/-- `P f s = eˢ·(Σ derivatives of f)(0) − (Σ derivatives of f)(s)`, the
exponential-polynomial expression whose size is controlled by the analytic
part of Lindemann–Weierstrass. -/
def P (f : ℂ[X]) (s : ℂ) : ℂ :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

/-- Derivative of `-(e^{-xs} · (Σ derivatives of p)(xs))` in `x` (inlined: the Mathlib
version became module-private in v4.35). -/
private theorem hasDerivAt_cexp_mul_sumIDeriv' (p : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert! (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

private theorem integral_exp_mul_eval' (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in 0..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_cexp_mul_sumIDeriv' p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

/-- The exact integral representation of `P`. -/
theorem P_eq_integral_exp_mul_eval (f : ℂ[X]) (s : ℂ) :
    P f s = exp s * (s * ∫ x in 0..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [integral_exp_mul_eval', mul_add, mul_neg, exp_neg,
    mul_inv_cancel_left₀ (exp_ne_zero s), neg_add_eq_sub]
  rfl

/-- Auxiliary bound: with `c` controlling `fₚ(xs)` for `x ∈ Ioc 0 1`,
`P(fₚ,s)` is controlled by `Real.exp s.re * (Real.exp ‖s‖ * |c|ᵖ * ‖s‖)`. -/
theorem P_le_aux (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p : ℕ,
      ‖P (f p) s‖ ≤
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

/-- Main analytic bound: if `|fₚ(xs)| ≤ cᵖ` for all `p` and `x ∈ Ioc 0 1`,
then for some nonnegative constant `c'`, `|P(fₚ,s)| ≤ c'ᵖ` for all nonzero
`p`. -/
theorem P_le (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p ≠ 0, ‖P (f p) s‖ ≤ c' ^ p := by
  obtain ⟨c', hc', h'⟩ := P_le_aux f s c hc
  clear c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  use c₁ * (c₂ * c' * c₃), by positivity
  intro p hp
  refine (h' p).trans ?_
  simp_rw [mul_pow]
  have le_max_one_pow {x : ℝ} : x ≤ max x 1 ^ p :=
    (max_cases x 1).elim (fun h => h.1.symm ▸ le_self_pow₀ h.2 hp)
      fun h => by rw [h.1, one_pow]; exact h.2.le
  gcongr <;> exact le_max_one_pow

/-! ## 2.  The Hermite polynomial and its pointwise bound -/

/-- `hermitePoly N p = X^(p-1) · (∏_{i=1}^{N} (X − i))^p ∈ ℤ[X]`, the auxiliary
polynomial of Hermite's proof of the transcendence of `e`. -/
def hermitePoly (N : ℕ) (p : ℕ) : ℤ[X] :=
  X ^ (p - 1) * (∏ i ∈ Finset.Icc 1 N, (X - C (i : ℤ))) ^ p

/-- Evaluation of the mapped Hermite polynomial at `z` agrees with the
direct complex expression `z^(p-1) · (∏ (z − i))^p`. -/
lemma eval_hermitePoly (N p : ℕ) (z : ℂ) :
    ((hermitePoly N p).map (Int.castRingHom ℂ)).eval z
      = z ^ (p - 1) * (∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ))) ^ p := by
  simp only [hermitePoly]
  rw [Polynomial.map_mul]
  rw [Polynomial.map_pow]
  rw [Polynomial.eval_mul]
  rw [Polynomial.eval_pow]
  congr 1
  · rw [Polynomial.map_X, Polynomial.eval_X]
  · rw [Polynomial.map_pow, Polynomial.eval_pow]
    congr 1
    rw [Polynomial.map_prod]
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    rfl

/-- Size of the product factor `∏_{i=1}^N (X − i)` at a point `z` with
`‖z‖ ≤ N`: at most `(2N)^N`. -/
lemma hermiteProd_bound (N : ℕ) (hN : 0 < N) {z : ℂ} (hz : ‖z‖ ≤ N) :
    ‖(∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ)))‖ ≤ (2 * N : ℝ) ^ N := by
  calc
    ‖(∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ)))‖ = ∏ i ∈ Finset.Icc 1 N, ‖z - (i : ℂ)‖ := by
      rw [norm_prod]
    _ ≤ ∏ i ∈ Finset.Icc 1 N, ((2 * N : ℝ)) := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro i hi
        positivity
      · intro i hi
        have hi1 : (1 : ℕ) ≤ i := (Finset.mem_Icc.mp hi).1
        have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2
        have hiz : (i : ℝ) ≤ N := by exact_mod_cast hiN
        calc
          ‖z - (i : ℂ)‖ ≤ ‖z‖ + ‖(i : ℂ)‖ := norm_sub_le z (i : ℂ)
          _ ≤ (N : ℝ) + (N : ℝ) := by
            rw [Complex.norm_natCast]
            nlinarith [hz]
          _ = (2 * N : ℝ) := by ring
    _ = ((2 * N : ℝ)) ^ N := by
      rw [Finset.prod_const]
      congr 1
      rw [Nat.card_Icc]
      omega

/-- Pointwise bound for the Hermite polynomial: if `‖z‖ ≤ N` (and `0 < N`)
then `‖hermitePoly N p (z)‖ ≤ (N · (2N)^N) ^ p`. -/
lemma hermitePoly_eval_bound (N p : ℕ) (hN : 0 < N) {z : ℂ} (hz : ‖z‖ ≤ N) :
    ‖((hermitePoly N p).map (Int.castRingHom ℂ)).eval z‖ ≤ (N * (2 * N) ^ N) ^ p := by
  rw [eval_hermitePoly]
  have hprod := hermiteProd_bound N hN hz
  have hprod_p : ‖(∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ))) ^ p‖ ≤ ((2 * N : ℝ) ^ N) ^ p := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hprod p
  have hzpow : ‖z ^ (p - 1)‖ ≤ (N : ℝ) ^ (p - 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg z) hz (p - 1)
  have hN₁ : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (p - 1) ≤ (N : ℝ) ^ p :=
    pow_le_pow_right₀ hN₁ (Nat.sub_le _ _)
  calc
    ‖z ^ (p - 1) * (∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ))) ^ p‖
        = ‖z ^ (p - 1)‖ * ‖(∏ i ∈ Finset.Icc 1 N, (z - (i : ℂ))) ^ p‖ := by
          rw [norm_mul]
    _ ≤ (N : ℝ) ^ (p - 1) * ((2 * N : ℝ) ^ N) ^ p := by
          exact mul_le_mul hzpow hprod_p (norm_nonneg _) (by positivity)
    _ ≤ (N : ℝ) ^ p * ((2 * N : ℝ) ^ N) ^ p := by
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (N * (2 * N) ^ N) ^ p := by
          rw [← mul_pow]



/-! ## 3.  Arithmetic core: integrality and `p`-adic properties -/

/-- The product factor `∏_{i=1}^N (X − i)` of the Hermite polynomial (its
roots are `1,…,N`). -/
def hermProd (N : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.Icc 1 N, (X - C (i : ℤ))

/-- `hermitePoly N p = X^(p-1) · (hermProd N)^p`. -/
lemma hermitePoly_eq (N p : ℕ) :
    hermitePoly N p = X ^ (p - 1) * (hermProd N) ^ p := by
  rfl

/-- Removing the factor `(X − k)` from `hermProd N`, valid for `k ∈ [1, N]`. -/
lemma hermProd_erase_mul (N : ℕ) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    (∏ i ∈ (Finset.Icc 1 N).erase k, (X - C (i : ℤ))) * (X - C (k : ℤ)) = hermProd N := by
  simpa [hermProd] using
    Finset.prod_erase_mul (Finset.Icc 1 N) (fun i => X - C (i : ℤ)) hk

/-- Evaluation at `0` of the sum of the iterated derivatives of the Hermite
polynomial: `(p−1)!` divides it, and its quotient is congruent to
`(hermProd N)(0)ᵖ` modulo `p`.  Precisely:

`Fₚ(0) = (p−1)!·h(0)ᵖ + p!·u₀` for some integer `u₀`. -/
lemma sumIDeriv_hermite_zero (N p : ℕ) (hp : 0 < p) :
    ∃ u : ℤ,
      (sumIDeriv (hermitePoly N p)).eval 0 =
        ((p - 1).factorial : ℤ) * ((hermProd N).eval 0) ^ p + (p.factorial : ℤ) * u := by
  have hinj : Function.Injective (algebraMap ℤ ℤ) := by
    intro a b h
    simpa using h
  obtain ⟨gp, _hdeg, hgp⟩ :=
    Polynomial.aeval_sumIDeriv_of_pos (R := ℤ) (A := ℤ) (p := hermitePoly N p) (q := p) hp hinj
  -- apply at r = 0 with p' = hermProd^p :  hermitePoly N p = X^(p-1) * hermProd^p
  have h0 : (hermitePoly N p) = (X - C (0 : ℤ)) ^ (p - 1) * (hermProd N) ^ p := by
    rw [hermitePoly_eq]
    simp
  have hmain := hgp (0 : ℤ) (p' := (hermProd N) ^ p) (by simpa using h0)
  have hmain' : (sumIDeriv (hermitePoly N p)).eval 0 =
      ((p - 1).factorial : ℤ) * ((hermProd N) ^ p).eval 0 + (p.factorial : ℤ) * gp.eval 0 := by
    simpa [nsmul_eq_mul] using hmain
  refine ⟨gp.eval 0, ?_⟩
  rw [hmain', eval_pow]

/-- Evaluation at a root `k ∈ [1, N]` of the sum of the iterated derivatives
of the Hermite polynomial is divisible by `p!` (so its quotient by `(p−1)!`
is divisible by `p`). -/
lemma sumIDeriv_hermite_pos (N p : ℕ) (hp : 0 < p) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    ∃ u : ℤ,
      (sumIDeriv (hermitePoly N p)).eval (k : ℤ) = (p.factorial : ℤ) * u := by
  have hinj : Function.Injective (algebraMap ℤ ℤ) := by
    intro a b h
    simpa using h
  obtain ⟨gp, _hdeg, hgp⟩ :=
    Polynomial.aeval_sumIDeriv (R := ℤ) (A := ℤ) (p := hermitePoly N p) (q := p)
  -- divisibility (X − k)^p ∣ hermitePoly N p
  let hk' : ℤ[X] := ∏ i ∈ (Finset.Icc 1 N).erase k, (X - C (i : ℤ))
  have herm_eq : hermProd N = (X - C (k : ℤ)) * hk' := by
    rw [← hermProd_erase_mul N hk]
    ring
  have hdiv_raw : (X - C (k : ℤ)) ^ p ∣ hermitePoly N p := by
    refine ⟨X ^ (p - 1) * hk' ^ p, ?_⟩
    rw [hermitePoly_eq, herm_eq, mul_pow]
    ring
  have hdiv : (X - C (k : ℤ)) ^ p ∣ Polynomial.map (algebraMap ℤ ℤ) (hermitePoly N p) := by
    simpa using hdiv_raw
  have hmain := hgp (k : ℤ) hdiv
  have hmain' : (sumIDeriv (hermitePoly N p)).eval (k : ℤ) =
      (p.factorial : ℤ) * gp.eval (k : ℤ) := by
    simpa [nsmul_eq_mul] using hmain
  exact ⟨gp.eval (k : ℤ), hmain'⟩



/-! ## 4.  Bridges to `ℂ`: integer values, and powers of `e` -/

/-- Value of `sumIDeriv (hermitePoly N p)` at the integer point `k`, as an
integer.  (The arithmetic core §3 controls its factorial divisibility.) -/
def sumIDerivAt (N p : ℕ) (k : ℤ) : ℤ :=
  (sumIDeriv (hermitePoly N p)).eval k

/-- The complex value of `sumIDeriv (hermitePoly N p)` at `(k : ℂ)` is the
cast of the integer `sumIDerivAt N p k`. -/
lemma sumIDeriv_cval (N p : ℕ) (k : ℤ) :
    ((sumIDeriv (hermitePoly N p)).map (Int.castRingHom ℂ)).eval (k : ℂ)
      = (sumIDerivAt N p k : ℂ) := by
  rw [sumIDerivAt]
  rw [← Polynomial.eval₂_eq_eval_map]
  simpa using (Polynomial.eval₂_at_apply (f := (Int.castRingHom ℂ))
    (p := sumIDeriv (hermitePoly N p)) (r := (k : ℤ)))

/-- `eⁿ = e^n` (complex exponential of the natural-number cast). -/
lemma exp_natCast (n : ℕ) : cexp (n : ℂ) = cexp 1 ^ n := by
  simpa using (Complex.exp_nsmul (1 : ℂ) n)



/-! ## 5.  Algebraic setup for the contradiction -/

/-- Evaluating a `ℤ`-polynomial at `0` gives its constant coefficient. -/
lemma eval_zero_eq_coeff (q : ℤ[X]) : q.eval 0 = q.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    have hz : (0 : ℤ) ^ b = 0 := by
      exact zero_pow hb0
    simp [hz]
  · intro hb
    exact False.elim (hb (by simp))

/-- If `x ≠ 0` is algebraic over `ℚ`, there is a *minimal-degree* nonzero
integer polynomial killing `x` whose value at `0` is nonzero.  (Minimality is
only needed to force `q.eval 0 ≠ 0`; the degree itself is not returned.) -/
lemma exists_minimal_int_poly {x : ℂ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    ∃ q : ℤ[X], q ≠ 0 ∧ Polynomial.aeval x q = 0 ∧ q.eval 0 ≠ 0 := by
  classical
  have hxZ : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℂ)).mpr hx
  obtain ⟨p, hp0, hpx⟩ := hxZ
  let Pdeg : ℕ → Prop := fun n => ∃ q : ℤ[X], q ≠ 0 ∧ Polynomial.aeval x q = 0 ∧ q.natDegree = n
  have hex : ∃ n, Pdeg n := ⟨p.natDegree, ⟨p, hp0, hpx, rfl⟩⟩
  let n₀ : ℕ := Nat.find hex
  have hmin : Pdeg n₀ := Nat.find_spec hex
  obtain ⟨q, hq0, hqx, hqdeg⟩ := hmin
  have hminimal : ∀ m : ℕ, Pdeg m → n₀ ≤ m := by
    intro m hm
    exact Nat.find_min' hex hm
  refine ⟨q, hq0, hqx, ?_⟩
  by_contra hq0eval
  have hcoeff : q.coeff 0 = 0 := by
    rw [← eval_zero_eq_coeff q]
    exact hq0eval
  have hXdvd : X ∣ q := (Polynomial.X_dvd_iff).2 hcoeff
  obtain ⟨q₁, hq₁⟩ := hXdvd
  have hq₁nz : q₁ ≠ 0 := by
    intro h
    apply hq0
    rw [hq₁, h]
    simp
  have hq₁x : Polynomial.aeval x q₁ = 0 := by
    have : Polynomial.aeval x (X * q₁) = 0 := by simpa [hq₁] using hqx
    rw [Polynomial.aeval_mul, Polynomial.aeval_X] at this
    exact (mul_eq_zero.mp this).resolve_left hx0
  have hsmall : q₁.natDegree < q.natDegree := by
    rw [hq₁, Polynomial.natDegree_X_mul hq₁nz]
    omega
  have hP₁ : Pdeg q₁.natDegree := ⟨q₁, hq₁nz, hq₁x, rfl⟩
  have : n₀ ≤ q₁.natDegree := hminimal q₁.natDegree hP₁
  omega

/-- The integer polynomial killing `e = cexp 1` whose existence §5 starts from.
(The next session builds the contradiction from it.) -/
lemma exists_minimal_int_poly_exp :
    IsAlgebraic ℚ (cexp 1) →
      ∃ q : ℤ[X], q ≠ 0 ∧ Polynomial.aeval (cexp 1) q = 0 ∧ q.eval 0 ≠ 0 :=
  fun hx => exists_minimal_int_poly hx (Complex.exp_ne_zero 1)



/-! ## 5b. Integer quotients `sₖ/(p−1)!` and their `p`-adic structure -/

/-- `(sumIDeriv (hermitePoly N p)).eval k` divided by `(p−1)!` — an integer
by §3 — as an integer. -/
def quotAt (N p : ℕ) (k : ℤ) : ℤ :=
  sumIDerivAt N p k / ((p - 1).factorial : ℤ)

/-- The quotient at `0` is congruent to `h(0)ᵖ` modulo `p`. -/
lemma quotAt_zero (N p : ℕ) (hp : 0 < p) :
    ∃ t : ℤ, quotAt N p 0 = (hermProd N).eval 0 ^ p + (p : ℤ) * t := by
  obtain ⟨u, hu⟩ := sumIDeriv_hermite_zero N p hp
  have hnat : p.factorial = p * (p - 1).factorial := by
    cases hp' : p with
    | zero =>
        omega
    | succ q =>
        rw [Nat.factorial_succ]
        rw [show q + 1 - 1 = q by omega]
  have hfac : (p.factorial : ℤ) = (p : ℤ) * ((p - 1).factorial : ℤ) := by
    exact_mod_cast hnat
  have hc : sumIDerivAt N p 0 =
      ((hermProd N).eval 0 ^ p + (p : ℤ) * u) * (((p - 1).factorial : ℤ)) := by
    rw [sumIDerivAt, hu, hfac]
    ring
  unfold quotAt
  refine ⟨u, ?_⟩
  exact Int.ediv_eq_of_eq_mul_left (by exact_mod_cast (Nat.factorial_ne_zero (p - 1))) hc

/-- At a root `k ∈ [1, N]` the quotient `sₖ/(p−1)!` is divisible by `p`. -/
lemma quotAt_pos (N p : ℕ) (hp : 0 < p) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    ∃ t : ℤ, quotAt N p (k : ℤ) = (p : ℤ) * t := by
  obtain ⟨u, hu⟩ := sumIDeriv_hermite_pos N p hp hk
  have hnat : p.factorial = p * (p - 1).factorial := by
    cases hp' : p with
    | zero =>
        omega
    | succ q =>
        rw [Nat.factorial_succ]
        rw [show q + 1 - 1 = q by omega]
  have hfac : (p.factorial : ℤ) = ((p - 1).factorial : ℤ) * (p : ℤ) := by
    rw [mul_comm]
    exact_mod_cast hnat
  have hc : sumIDerivAt N p (k : ℤ) = ((p : ℤ) * u) * (((p - 1).factorial : ℤ)) := by
    rw [sumIDerivAt, hu, hfac]
    ring
  unfold quotAt
  refine ⟨u, ?_⟩
  exact Int.ediv_eq_of_eq_mul_left (by exact_mod_cast (Nat.factorial_ne_zero (p - 1))) hc



/-! ## 5c. `J` and its nonzero-ness -/

/-- The value `h(0) = ∏_{i=1}^N (−i)` of the Hermite product factor at `0`. -/
lemma hermProd_eval_zero (N : ℕ) : (hermProd N).eval 0 = ∏ i ∈ Finset.Icc 1 N, (-(i : ℤ)) := by
  simp [hermProd, eval_prod]

/-- The absolute value of `∏ i` (as integers) is the natural product. -/
lemma natAbs_prod_natCast (s : Finset ℕ) : ((∏ i ∈ s, (i : ℤ)).natAbs) = ∏ i ∈ s, i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has, Int.natAbs_mul, Int.natAbs_natCast a, ih]

/-- `∏_{i=1}^N i = N!`. -/
lemma prod_Icc_id_factorial (N : ℕ) : (∏ i ∈ Finset.Icc 1 N, i) = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega) (fun i : ℕ => i)]
      rw [ih, Nat.factorial_succ]
      ring

/-- The absolute value of `∏ (−i)` (as integers) is the natural product. -/
lemma natAbs_prod_neg_natCast (s : Finset ℕ) :
    ((∏ i ∈ s, (-(i : ℤ))).natAbs) = ∏ i ∈ s, i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has]
    rw [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast a, ih]

/-- `|h(0)| = N!`, so a prime `p > N` does not divide `h(0)`. -/
lemma natAbs_hermProd_eval_zero (N : ℕ) : ((hermProd N).eval 0).natAbs = N.factorial := by
  rw [hermProd_eval_zero, natAbs_prod_neg_natCast, prod_Icc_id_factorial]



/-- The integer `J = Σₖ cₖ·(Fₚ(k)/(p−1)!)` of Hermite's proof (coefficient
`cₖ` of the polynomial `c`, summed over the roots `k = 1,…,N` plus `k = 0`). -/
def hermJ (N p : ℕ) (c : ℤ[X]) : ℤ :=
  c.coeff 0 * quotAt N p 0 + ∑ k ∈ Finset.Icc 1 N, c.coeff k * quotAt N p (k : ℤ)

/-- `J ≡ c₀·h(0)ᵖ (mod p)`: the terms at roots `k ≥ 1` are divisible by `p`,
and the `k = 0` quotient is congruent to `h(0)ᵖ`. -/
lemma hermJ_mod (N p : ℕ) (c : ℤ[X]) (hp : 0 < p) :
    ∃ t : ℤ, hermJ N p c = c.coeff 0 * (hermProd N).eval 0 ^ p + (p : ℤ) * t := by
  obtain ⟨u₀, hu₀⟩ := quotAt_zero N p hp
  let tf : ℕ → ℤ := fun k =>
    if hk : k ∈ Finset.Icc 1 N then Classical.choose (quotAt_pos N p hp hk) else 0
  have htf : ∀ k ∈ Finset.Icc 1 N, quotAt N p (k : ℤ) = (p : ℤ) * tf k := by
    intro k hk
    have hspec := Classical.choose_spec (quotAt_pos N p hp hk)
    simp only [tf, dif_pos hk]
    exact hspec
  refine ⟨c.coeff 0 * u₀ + ∑ k ∈ Finset.Icc 1 N, c.coeff k * tf k, ?_⟩
  have hsum : (∑ k ∈ Finset.Icc 1 N, c.coeff k * quotAt N p (k : ℤ)) =
      (p : ℤ) * (∑ k ∈ Finset.Icc 1 N, c.coeff k * tf k) := by
    rw [Finset.mul_sum (Finset.Icc 1 N) (fun k => c.coeff k * tf k) (p : ℤ)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [htf k hk]
    ring
  unfold hermJ
  rw [hu₀, hsum]
  ring



/-- For a prime `p > N` with `p ∤ c₀`, the integer `J` is not zero:
`J ≡ c₀·h(0)ᵖ (mod p)` and neither factor is divisible by `p`. -/
lemma hermJ_ne_zero (N p : ℕ) (c : ℤ[X]) (hp : Nat.Prime p) (hpN : N < p)
    (hc0 : c.eval 0 ≠ 0) (hcp : (c.eval 0).natAbs < p) :
    hermJ N p c ≠ 0 := by
  have hp0 : 0 < p := Nat.Prime.pos hp
  obtain ⟨t, hJ⟩ := hermJ_mod N p c hp0
  -- p does not divide h(0) (its absolute value is N!)
  have hnotdN : ¬ p ∣ N.factorial := by
    intro hd
    have : p ≤ N := (hp.dvd_factorial).1 hd
    omega
  have hnotd_h0nat : ¬ p ∣ ((hermProd N).eval 0).natAbs := by
    intro hd
    apply hnotdN
    rwa [natAbs_hermProd_eval_zero] at hd
  have hnotd_h0 : ¬ (p : ℤ) ∣ (hermProd N).eval 0 := by
    intro hd
    exact hnotd_h0nat (Int.ofNat_dvd_left.mp hd)
  -- p does not divide c₀
  have hc0' : c.coeff 0 ≠ 0 := by
    rw [eval_zero_eq_coeff] at hc0
    exact hc0
  have hcp' : (c.coeff 0).natAbs < p := by
    rw [eval_zero_eq_coeff] at hcp
    exact hcp
  have hnotd_c0nat : ¬ p ∣ (c.coeff 0).natAbs := by
    intro hd
    have hpos : 0 < (c.coeff 0).natAbs := Int.natAbs_pos.mpr hc0'
    exact (Nat.not_dvd_of_pos_of_lt hpos hcp') hd
  by_contra hJ0
  have hd : (p : ℤ) ∣ c.coeff 0 * (hermProd N).eval 0 ^ p := by
    refine ⟨-t, ?_⟩
    have hlin : c.coeff 0 * (hermProd N).eval 0 ^ p + (p : ℤ) * t = 0 := by
      rw [← hJ]
      exact hJ0
    have hA : c.coeff 0 * (hermProd N).eval 0 ^ p = -(p : ℤ) * t := by
      nlinarith
    calc
      c.coeff 0 * (hermProd N).eval 0 ^ p = -(p : ℤ) * t := hA
      _ = (p : ℤ) * (-t) := by ring
  rcases (Int.Prime.dvd_mul hp hd) with hc | hhp
  · exact hnotd_c0nat hc
  · have hh' : p ∣ ((hermProd N).eval 0).natAbs := by
      rw [Int.natAbs_pow] at hhp
      exact Nat.Prime.dvd_of_dvd_pow hp hhp
    exact hnotd_h0nat hh'



/-! ## 5d. The exact identity relating `J` to the `P` values -/

/-- Expanding `aeval e q` over the powers of `e = cexp 1`:
`aeval e q = Σₖ (q.coeff k : ℂ)·eᵏ` with `eᵏ = cexp (k : ℂ)`. -/
lemma aeval_sum_exp (q : ℤ[X]) :
    Polynomial.aeval (cexp 1) q =
      ∑ k ∈ Finset.range (q.natDegree + 1), (q.coeff k : ℂ) * cexp (k : ℂ) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [Polynomial.eval_eq_sum_range']
  · refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Polynomial.coeff_map]
    rw [← exp_natCast k]
    simp
  · exact Nat.lt_succ_iff.mpr Polynomial.natDegree_map_le



/-- `{0,…,N} = {0} ∪ [1,N]` as finsets. -/
lemma range_eq_insert (N : ℕ) : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
  ext k
  constructor
  · intro hk
    have hk' : k ≤ N := by
      have : k < N + 1 := Finset.mem_range.mp hk
      omega
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk1 : 1 ≤ k := by omega
      simp [hk0, hk1, hk']
  · intro hk
    simp at hk
    rcases hk with hk0 | hkIcc
    · simp [hk0]
    · rw [Finset.mem_range]
      omega

/-- The two-part definition of `J` is the full sum over `k = 0,…,N`. -/
lemma hermJ_eq_sum_range (N p : ℕ) (c : ℤ[X]) :
    hermJ N p c = ∑ k ∈ Finset.range (N + 1), c.coeff k * quotAt N p (k : ℤ) := by
  unfold hermJ
  rw [range_eq_insert N]
  rw [Finset.sum_insert (by simp)]
  rfl



/-- `p! = p·(p−1)!` for `0 < p`. -/
lemma factorial_eq_mul_pred {p : ℕ} (hp : 0 < p) : p.factorial = p * (p - 1).factorial := by
  cases hp' : p with
  | zero => omega
  | succ q =>
      rw [Nat.factorial_succ]
      rw [show q + 1 - 1 = q by omega]

/-- `(p−1)! ∣ s₀` (at the point `k = 0`). -/
lemma factorial_dvd_sumIDerivAt_zero (N p : ℕ) (hp : 0 < p) :
    ((p - 1).factorial : ℤ) ∣ sumIDerivAt N p 0 := by
  obtain ⟨u, hu⟩ := sumIDeriv_hermite_zero N p hp
  refine ⟨(hermProd N).eval 0 ^ p + (p : ℤ) * u, ?_⟩
  rw [sumIDerivAt, hu]
  have hfac : (p.factorial : ℤ) = ((p - 1).factorial : ℤ) * (p : ℤ) := by
    rw [mul_comm]
    exact_mod_cast factorial_eq_mul_pred hp
  rw [hfac]
  ring

/-- `(p−1)! ∣ sₖ` at a root `k ∈ [1, N]`. -/
lemma factorial_dvd_sumIDerivAt_pos (N p : ℕ) (hp : 0 < p) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    ((p - 1).factorial : ℤ) ∣ sumIDerivAt N p (k : ℤ) := by
  obtain ⟨u, hu⟩ := sumIDeriv_hermite_pos N p hp hk
  refine ⟨(p : ℤ) * u, ?_⟩
  rw [sumIDerivAt, hu]
  have hfac : (p.factorial : ℤ) = ((p - 1).factorial : ℤ) * (p : ℤ) := by
    rw [mul_comm]
    exact_mod_cast factorial_eq_mul_pred hp
  rw [hfac]
  ring

/-- `(p−1)!` divides every `sₖ` for `0 ≤ k ≤ N`. -/
lemma factorial_dvd_sumIDerivAt_range (N p : ℕ) (hp : 0 < p) {k : ℕ}
    (hk : k ∈ Finset.range (N + 1)) :
    ((p - 1).factorial : ℤ) ∣ sumIDerivAt N p (k : ℤ) := by
  by_cases hk0 : k = 0
  · subst k
    exact factorial_dvd_sumIDerivAt_zero N p hp
  · have hk' : k < N + 1 := Finset.mem_range.mp hk
    have hkIcc : k ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    exact factorial_dvd_sumIDerivAt_pos N p hp hkIcc

/-- The complex value of the quotient `Aₖ = sₖ/(p−1)!` is the fraction
`sₖ/(p−1)!` in `ℂ`. -/
lemma quotAt_range_cval (N p : ℕ) (hp : 0 < p) {k : ℕ}
    (hk : k ∈ Finset.range (N + 1)) :
    (quotAt N p (k : ℤ) : ℂ) =
      (sumIDerivAt N p (k : ℤ) : ℂ) / (((p - 1).factorial : ℤ) : ℂ) := by
  unfold quotAt
  exact Int.cast_div (factorial_dvd_sumIDerivAt_range N p hp hk)
    (by exact_mod_cast (Nat.factorial_ne_zero (p - 1)))

/-- Casting `J` to `ℂ` turns the quotients into the corresponding fractions. -/
lemma hermJ_eq_frac (N p : ℕ) (c : ℤ[X]) (hp : 0 < p) :
    (hermJ N p c : ℂ) =
      ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) *
        ((sumIDerivAt N p (k : ℤ) : ℂ) / (((p - 1).factorial : ℤ) : ℂ)) := by
  rw [hermJ_eq_sum_range]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Int.cast_mul]
  rw [quotAt_range_cval N p hp hk]



/-- The generic `P`-identity: from the exponential relation
`Σₖ cₖ·eᵏ = 0`, the sum of the iterated-derivative values equals the negative
sum of the `P` values. -/
lemma hermite_identity (fp : ℂ[X]) (c : ℤ[X]) (N : ℕ)
    (hrel : ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * cexp (k : ℂ) = 0) :
    (∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (sumIDeriv fp).eval (k : ℂ)) =
      -∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * P fp (k : ℂ) := by
  let F : ℂ[X] := sumIDeriv fp
  have hP : ∀ k : ℕ, F.eval (k : ℂ) = cexp (k : ℂ) * F.eval 0 - P fp (k : ℂ) := by
    intro k
    unfold P F
    ring
  calc
    (∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (sumIDeriv fp).eval (k : ℂ))
        = ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * F.eval (k : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rfl
    _ = ∑ k ∈ Finset.range (N + 1),
            (((c.coeff k : ℂ) * cexp (k : ℂ)) * F.eval 0 - (c.coeff k : ℂ) * P fp (k : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hP k]
          ring
    _ = -∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * P fp (k : ℂ) := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.sum_mul (Finset.range (N + 1))
            (fun k : ℕ => (c.coeff k : ℂ) * cexp (k : ℂ)) (F.eval 0)]
          rw [hrel]
          simp

/-- Casting `J` to `ℂ` as the full sum over `k = 0,…,N` (quotient form). -/
lemma hermJ_cval (N p : ℕ) (c : ℤ[X]) :
    (hermJ N p c : ℂ) =
      ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (quotAt N p (k : ℤ) : ℂ) := by
  rw [hermJ_eq_sum_range]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Int.cast_mul]

/-- The exact identity of Hermite's proof, multiplied by `(p−1)!`:

`(J:ℂ)·(p−1)! = −Σₖ cₖ·P(fₚ,(k:ℂ))`,

using only the algebraic relation `aeval e q = 0` (with `q` of degree `N`). -/
lemma hermJ_mul_factorial (N p : ℕ) (c : ℤ[X]) (hp : 0 < p) (hdeg : c.natDegree = N)
    (hrel : Polynomial.aeval (cexp 1) c = 0) :
    (hermJ N p c : ℂ) * (((p - 1).factorial : ℤ) : ℂ) =
      -∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) *
        P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ) := by
  let fp : ℂ[X] := (hermitePoly N p).map (Int.castRingHom ℂ)
  let d : ℂ := (((p - 1).factorial : ℤ) : ℂ)
  have hrel0 : ∑ k ∈ Finset.range (c.natDegree + 1), (c.coeff k : ℂ) * cexp (k : ℂ) = 0 := by
    rwa [← aeval_sum_exp c]
  have hrel' : ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * cexp (k : ℂ) = 0 := by
    rwa [hdeg] at hrel0
  have hid := hermite_identity fp c N hrel'
  calc
    (hermJ N p c : ℂ) * (((p - 1).factorial : ℤ) : ℂ)
        = (∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (quotAt N p (k : ℤ) : ℂ)) * d := by
          rw [hermJ_cval]
    _ = ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (quotAt N p (k : ℤ) : ℂ) * d := by
          rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * ((quotAt N p (k : ℤ) : ℂ) * d) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (sumIDerivAt N p (k : ℤ) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          congr 1
          have hd' : quotAt N p (k : ℤ) * ((p - 1).factorial : ℤ) = sumIDerivAt N p (k : ℤ) := by
            unfold quotAt
            exact Int.ediv_mul_cancel (factorial_dvd_sumIDerivAt_range N p hp hk)
          have hc1 : (quotAt N p (k : ℤ) : ℂ) * d = (sumIDerivAt N p (k : ℤ) : ℂ) := by
            dsimp [d]
            rw [← Int.cast_mul, hd']
          simpa using hc1
    _ = ∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * (sumIDeriv fp).eval (k : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          congr 1
          rw [show ((sumIDerivAt N p (k : ℤ) : ℂ)) =
              ((sumIDeriv (hermitePoly N p)).map (Int.castRingHom ℂ)).eval (k : ℂ) by
                exact (sumIDeriv_cval N p (k : ℤ)).symm]
          dsimp [fp]
          rw [Polynomial.sumIDeriv_map]
    _ = -∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) * P fp (k : ℂ) := hid
    _ = -∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) *
        P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ) := by
          dsimp [fp]


/-! ## 5e. Analytic bound and final contradiction -/

/-- Explicit version of `P_le_aux`: the bound with the constant made visible
(`|c|` instead of an existential). -/
theorem P_le_explicit (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∀ p : ℕ, ‖P (f p) s‖ ≤ Real.exp s.re * (Real.exp ‖s‖ * |c| ^ p * ‖s‖) := by
  intro p
  rw [P_eq_integral_exp_mul_eval (f p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert! MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

/-- `P` vanishes at `s = 0`. -/
lemma P_zero (f : ℂ[X]) : P f 0 = 0 := by
  simp [P]

/-- Uniform analytic bound: for `1 ≤ N`, `p ≠ 0` and `0 ≤ k ≤ N`,
`‖P(fₚ,(k:ℂ))‖ ≤ B(N)ᵖ` with `B(N) = exp(N)²·N·(N·(2N)^N)`. -/
lemma P_hermite_bound (N : ℕ) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) {p : ℕ} (hp : p ≠ 0) :
    ‖P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖ ≤
      ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ)) ^ N)) ^ p := by
  have hc' : ∀ q : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      ‖(((hermitePoly N q).map (Int.castRingHom ℂ))).eval (x • (k : ℂ))‖ ≤
        ((N : ℝ) * (2 * (N : ℝ)) ^ N) ^ q := by
    intro q x hx
    have hz : ‖x • (k : ℂ)‖ ≤ (N : ℝ) := by
      have h1 : ‖x • (k : ℂ)‖ = x * (k : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1.le]
        simp
      rw [h1]
      have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
      have hx1 : x ≤ 1 := hx.2
      nlinarith
    exact hermitePoly_eval_bound N q hN hz
  have hb := P_le_explicit (f := fun q : ℕ => (hermitePoly N q).map (Int.castRingHom ℂ))
    (s := (k : ℂ)) (c := (N : ℝ) * (2 * (N : ℝ)) ^ N) hc'
  let c : ℝ := (N : ℝ) * (2 * (N : ℝ)) ^ N
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hExp : Real.exp (k : ℝ) ≤ Real.exp (N : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast hk)
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have h1 : Real.exp (k : ℝ) * (Real.exp (k : ℝ) * c ^ p * (k : ℝ)) ≤
      Real.exp (N : ℝ) * (Real.exp (N : ℝ) * c ^ p * (N : ℝ)) := by
    dsimp [c]
    gcongr
  have hA1 : 1 ≤ (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) := by
    have he1 : 1 ≤ Real.exp (N : ℝ) := Real.one_le_exp_iff.mpr (by positivity)
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg (Real.exp (N : ℝ)), he1]
  have hAp : (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) ≤ ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ)) ^ p :=
    le_self_pow₀ hA1 hp
  have h2 : Real.exp (N : ℝ) * (Real.exp (N : ℝ) * c ^ p * (N : ℝ)) ≤
      ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * c) ^ p := by
    calc
      Real.exp (N : ℝ) * (Real.exp (N : ℝ) * c ^ p * (N : ℝ))
          = (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * c ^ p := by ring
      _ ≤ ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ)) ^ p * c ^ p := by
            exact mul_le_mul_of_nonneg_right hAp (pow_nonneg hc0 p)
      _ = ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * c) ^ p := by rw [← mul_pow]
  calc
    ‖P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖
        ≤ Real.exp (k : ℝ) * (Real.exp (k : ℝ) * |c| ^ p * (k : ℝ)) := by
            simpa [show ‖(k : ℂ)‖ = (k : ℝ) by simp, show ((k : ℂ).re) = (k : ℝ) by simp,
              abs_of_nonneg hc0] using hb p
    _ ≤ Real.exp (N : ℝ) * (Real.exp (N : ℝ) * c ^ p * (N : ℝ)) := by
            have habs : |c| = c := abs_of_nonneg hc0
            simpa [habs] using h1
    _ ≤ ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * c) ^ p := h2
    _ = ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ)) ^ N)) ^ p := by
          dsimp [c]

/-- The complex norm of a nonzero integer is at least `1`. -/
lemma norm_intCast_ge_one {z : ℤ} (hz : z ≠ 0) : 1 ≤ ‖(z : ℂ)‖ := by
  rcases Int.eq_nat_or_neg z with ⟨n, hn | hn⟩
  · subst z
    have hnz : n ≠ 0 := by
      intro h
      apply hz
      simp [h]
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hnz)
    have hn : ‖(((n : ℕ) : ℤ) : ℂ)‖ = (n : ℝ) := by simp
    simpa [hn] using hn1
  · subst z
    have hnz : n ≠ 0 := by
      intro h
      apply hz
      simp [h]
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hnz)
    have hn : ‖((-(((n : ℕ) : ℤ)) : ℂ))‖ = (n : ℝ) := by simp
    simpa [hn] using hn1

/-- If `c` is nonzero of degree `N`, the sum of the norms of its first
`N+1` coefficients is at least `1`. -/
lemma sum_abs_coeff_ge_one (N : ℕ) (c : ℤ[X]) (hc : c ≠ 0) (hdeg : c.natDegree = N) :
    1 ≤ ∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ)‖ := by
  have hcN : c.coeff N ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hc
  have h1 : 1 ≤ ‖(c.coeff N : ℂ)‖ := norm_intCast_ge_one hcN
  have hmem : N ∈ Finset.range (N + 1) := by simp
  have hs := Finset.single_le_sum
    (s := Finset.range (N + 1)) (f := fun k : ℕ => ‖(c.coeff k : ℂ)‖)
    (by intro i hi; exact norm_nonneg _) hmem
  exact le_trans h1 hs

/-- Sum bound: `‖Σₖ cₖ·P(fₚ,(k:ℂ))‖ ≤ (S·B)ᵖ` with `S = Σₖ‖cₖ‖` and
`B = exp(N)²·N·(N·(2N)^N)` (the constant of `P_hermite_bound`). -/
lemma Psum_bound (N : ℕ) (c : ℤ[X]) (hN : 0 < N) (hdeg : c.natDegree = N) (hc : c ≠ 0)
    {p : ℕ} (hp : p ≠ 0) :
    ‖∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) *
        P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖ ≤
      ((∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ)‖) *
        ((Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ)) ^ N))) ^ p := by
  let B : ℝ := (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ)) ^ N)
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ)‖
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hA1 : 1 ≤ (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) := by
      have he1 : 1 ≤ Real.exp (N : ℝ) := Real.one_le_exp_iff.mpr (by positivity)
      nlinarith [sq_nonneg (Real.exp (N : ℝ)), he1]
    have hc1 : 1 ≤ (N : ℝ) * (2 * (N : ℝ)) ^ N := by
      have h2 : 1 ≤ (2 : ℝ) * (N : ℝ) := by nlinarith
      have : 1 ≤ (2 * (N : ℝ)) ^ N := one_le_pow₀ h2
      nlinarith
    nlinarith
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hS1 : 1 ≤ S := sum_abs_coeff_ge_one N c hc hdeg
  have hP : ∀ k ∈ Finset.range (N + 1), ‖P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖ ≤ B ^ p := by
    intro k hk
    have hkN : k ≤ N := by
      have : k < N + 1 := Finset.mem_range.mp hk
      omega
    exact (P_hermite_bound N hN hkN hp).trans (by
      dsimp [B]
      exact le_rfl)
  calc
    ‖∑ k ∈ Finset.range (N + 1), (c.coeff k : ℂ) *
        P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖
        ≤ ∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ) *
            P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ)‖ * ‖P ((hermitePoly N p).map (Int.castRingHom ℂ)) (k : ℂ)‖ := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [norm_mul]
    _ ≤ ∑ k ∈ Finset.range (N + 1), ‖(c.coeff k : ℂ)‖ * (B ^ p) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact mul_le_mul_of_nonneg_left (hP k hk) (norm_nonneg _)
    _ = S * B ^ p := by
          dsimp [S]
          rw [Finset.sum_mul]
    _ ≤ (S * B) ^ p := by
          have hSp : S ≤ S ^ p := le_self_pow₀ hS1 hp
          calc
            S * B ^ p ≤ S ^ p * B ^ p := by
              exact mul_le_mul_of_nonneg_right hSp (pow_nonneg hB0 p)
            _ = (S * B) ^ p := by rw [← mul_pow]
    _ ≤ (S * B) ^ p := by rfl

/-- Factorials eventually dominate powers: for every real `C`, all sufficiently
large `p` satisfy `Cᵖ/(p−1)! < 1`. -/
lemma pow_div_factorial_pred_eventually_lt (C : ℝ) :
    ∀ᶠ p in Filter.atTop, C ^ p / ((p - 1).factorial : ℝ) < 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => C ^ n / (n.factorial : ℝ)) Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop (K := ℝ) C
  let D : ℝ := |C| + 1
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hmem : Set.Ioo (-(1 / D) : ℝ) (1 / D) ∈ nhds (0 : ℝ) := isOpen_Ioo.mem_nhds (by
    dsimp [D]
    constructor
    · exact neg_lt_zero.mpr (one_div_pos.mpr (by positivity))
    · exact one_div_pos.mpr (by positivity))
  have hev : ∀ᶠ n in Filter.atTop, C ^ n / (n.factorial : ℝ) ∈ Set.Ioo (-(1 / D)) (1 / D) := ht hmem
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hev
  refine Filter.mem_atTop_sets.mpr ⟨N + 1, ?_⟩
  intro p hp
  have hp1 : 1 ≤ p := by omega
  have hpp : N ≤ p - 1 := by omega
  have hap := hN (p - 1) hpp
  have hpow : C ^ p = C * C ^ (p - 1) := by
    have hpow2 : C ^ p = C ^ ((p - 1) + 1) := by
      congr 1
      omega
    rw [hpow2, pow_succ]
    rw [mul_comm]
  change C ^ p / ((p - 1).factorial : ℝ) < 1
  have hf : C ^ p / ((p - 1).factorial : ℝ) = C * (C ^ (p - 1) / ((p - 1).factorial : ℝ)) := by
    rw [hpow]
    ring
  rw [hf]
  have ha : |C ^ (p - 1) / ((p - 1).factorial : ℝ)| < 1 / D := by
    exact abs_lt.mpr ⟨hap.1, hap.2⟩
  have hlt : |C| * |C ^ (p - 1) / ((p - 1).factorial : ℝ)| < 1 := by
    have h1 : |C| * |C ^ (p - 1) / ((p - 1).factorial : ℝ)| ≤ |C| * (1 / D) :=
      mul_le_mul_of_nonneg_left (le_of_lt ha) (abs_nonneg C)
    have h2 : |C| * (1 / D) < 1 := by
      dsimp [D]
      have hpos : 0 < |C| + 1 := by positivity
      have h3 : |C| * (1 / (|C| + 1)) = |C| / (|C| + 1) := by ring
      rw [h3]
      rw [div_lt_one hpos]
      linarith [abs_nonneg C]
    exact lt_of_le_of_lt h1 h2
  have habs : |C * (C ^ (p - 1) / ((p - 1).factorial : ℝ))| < 1 := by
    rw [abs_mul]
    exact hlt
  exact (abs_lt.mp habs).2

/-- **Hermite's theorem**: `e = cexp 1` is transcendental over `ℚ`. -/
theorem exp_one_transcendental : Transcendental ℚ (cexp 1) := by
  rw [Transcendental]
  intro hx
  obtain ⟨q, hq0, hqx, hq00⟩ := exists_minimal_int_poly_exp hx
  let N : ℕ := q.natDegree
  have hNpos : 0 < N := by
    by_contra hN0
    have hdeg0 : q.natDegree = 0 := by omega
    have hcq : q.coeff 0 ≠ 0 := by
      have hconst : ∃ a : ℤ, C a = q := (Polynomial.natDegree_eq_zero).1 hdeg0
      rcases hconst with ⟨a, ha⟩
      have : a ≠ 0 := by
        intro h
        apply hq0
        simpa [h] using ha.symm
      rw [← ha]
      simp [this]
    have hcv : Polynomial.aeval (cexp 1) q = (q.coeff 0 : ℂ) := by
      have hconst : ∃ a : ℤ, C a = q := (Polynomial.natDegree_eq_zero).1 hdeg0
      rcases hconst with ⟨a, ha⟩
      rw [← ha]
      simp
    have : (q.coeff 0 : ℂ) = 0 := by
      simpa [hcv] using hqx
    exact hcq (by exact_mod_cast this)
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), ‖(q.coeff k : ℂ)‖
  let B : ℝ := (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) * ((N : ℝ) * (2 * (N : ℝ)) ^ N)
  let C0 : ℝ := S * B
  have hS1 : 1 ≤ S := sum_abs_coeff_ge_one N q hq0 (by rfl)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hA1 : 1 ≤ (Real.exp (N : ℝ)) ^ 2 * (N : ℝ) := by
      have he1 : 1 ≤ Real.exp (N : ℝ) := Real.one_le_exp_iff.mpr (by positivity)
      nlinarith [sq_nonneg (Real.exp (N : ℝ)), he1]
    have hc1 : 1 ≤ (N : ℝ) * (2 * (N : ℝ)) ^ N := by
      have h2 : 1 ≤ (2 : ℝ) * (N : ℝ) := by nlinarith
      have : 1 ≤ (2 * (N : ℝ)) ^ N := one_le_pow₀ h2
      nlinarith
    nlinarith
  have hC1 : 1 ≤ C0 := by
    dsimp [C0]
    nlinarith
  obtain ⟨P0, hP0⟩ := Filter.mem_atTop_sets.mp (pow_div_factorial_pred_eventually_lt C0)
  let M : ℕ := max P0 (max (N + 1) ((q.eval 0).natAbs + 1))
  obtain ⟨p, hpM, hpp⟩ := Nat.exists_infinite_primes M
  have hpN : N < p := by
    have h1' : N + 1 ≤ M := by
      dsimp [M]
      exact le_trans (le_max_left (N + 1) ((q.eval 0).natAbs + 1))
        (le_max_right P0 (max (N + 1) ((q.eval 0).natAbs + 1)))
    omega
  have hpabs : (q.eval 0).natAbs < p := by
    have h2' : (q.eval 0).natAbs + 1 ≤ M := by
      dsimp [M]
      exact le_trans (le_max_right (N + 1) ((q.eval 0).natAbs + 1))
        (le_max_right P0 (max (N + 1) ((q.eval 0).natAbs + 1)))
    omega
  have hb0 : C0 ^ p / ((p - 1).factorial : ℝ) < 1 := hP0 p (by omega)
  have hJ0 : hermJ N p q ≠ 0 := hermJ_ne_zero N p q hpp hpN hq00 hpabs
  have hJ1 : 1 ≤ ‖(hermJ N p q : ℂ)‖ := norm_intCast_ge_one hJ0
  have hid := hermJ_mul_factorial N p q hpp.pos (rfl : q.natDegree = N) hqx
  have hsum := Psum_bound N q hNpos (rfl : q.natDegree = N) hq0 hpp.ne_zero
  have hJd : ‖(hermJ N p q : ℂ) * (((p - 1).factorial : ℤ) : ℂ)‖ ≤ C0 ^ p := by
    rw [hid]
    rw [norm_neg]
    dsimp [C0, S, B] at hsum ⊢
    exact hsum
  have hnormd : ‖(hermJ N p q : ℂ) * (((p - 1).factorial : ℤ) : ℂ)‖ =
      ‖(hermJ N p q : ℂ)‖ * ((p - 1).factorial : ℝ) := by
    rw [norm_mul]
    simp
  have hmain : ‖(hermJ N p q : ℂ)‖ * ((p - 1).factorial : ℝ) ≤ C0 ^ p := by
    rw [← hnormd]
    exact hJd
  have hfact0 : 0 < ((p - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (p - 1)
  have hJ2 : ‖(hermJ N p q : ℂ)‖ ≤ C0 ^ p / ((p - 1).factorial : ℝ) := by
    exact (le_div_iff₀ hfact0).mpr hmain
  exact (not_lt_of_ge hJ1) (lt_of_le_of_lt hJ2 hb0)

/-! ## 6.  Transfer to the reals -/

/-- Algebraicity over `ℚ` transfers along the inclusion `ℝ → ℂ`. -/
lemma isAlgebraic_complex_of_isAlgebraic_real {x : ℝ} (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (x : ℂ) := by
  rw [isAlgebraic_iff_isIntegral]
  have hxi : IsIntegral ℚ x := isAlgebraic_iff_isIntegral.mp hx
  have hmap : IsIntegral ℚ ((x : ℂ)) :=
    (isIntegral_algebraMap_iff (R := ℚ) (A := ℝ) (B := ℂ) (x := x)).mpr hxi
  simpa using hmap

/-- **Hermite's theorem over the reals**: `e = Real.exp 1` is transcendental
over `ℚ`. -/
theorem real_exp_one_transcendental : Transcendental ℚ (Real.exp 1) := by
  rw [Transcendental]
  intro hx
  exact exp_one_transcendental (by
    simpa [Complex.ofReal_exp] using (isAlgebraic_complex_of_isAlgebraic_real hx))


/-- The generic Hermite identity at arbitrary points `s : ℕ → ℂ`: if
`Σₖ bₖ·cexp(sₖ) = 0` then `Σₖ bₖ·F(sₖ) = −Σₖ bₖ·P fp (sₖ)` where
`F = sumIDeriv fp`.  (Specializes to `hermite_identity` for
`sₖ = (k : ℂ)`, and to the Lindemann exponent points for `sₖ = k·z`.) -/
lemma hermite_identity_at (fp : ℂ[X]) (b : ℕ → ℂ) (m : ℕ) (s : ℕ → ℂ)
    (hrel : ∑ k ∈ Finset.range (m + 1), b k * cexp (s k) = 0) :
    (∑ k ∈ Finset.range (m + 1), b k * (sumIDeriv fp).eval (s k)) =
      -∑ k ∈ Finset.range (m + 1), b k * P fp (s k) := by
  let F : ℂ[X] := sumIDeriv fp
  have hP : ∀ k : ℕ, F.eval (s k) = cexp (s k) * F.eval 0 - P fp (s k) := by
    intro k
    unfold P F
    ring
  calc
    (∑ k ∈ Finset.range (m + 1), b k * (sumIDeriv fp).eval (s k))
        = ∑ k ∈ Finset.range (m + 1), b k * F.eval (s k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rfl
    _ = ∑ k ∈ Finset.range (m + 1),
            (((b k * cexp (s k)) * F.eval 0) - b k * P fp (s k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hP k]
          ring
    _ = -∑ k ∈ Finset.range (m + 1), b k * P fp (s k) := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.sum_mul (Finset.range (m + 1))
            (fun k : ℕ => b k * cexp (s k)) (F.eval 0)]
          rw [hrel]
          simp


end Submission.Transcendence
