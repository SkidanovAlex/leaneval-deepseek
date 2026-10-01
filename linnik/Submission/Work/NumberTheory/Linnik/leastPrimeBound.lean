import Mathlib
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
import Submission.Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt

/-!
# `leastPrimeBound` — Linnik's theorem with L = 5.5 (Heath-Brown 1992, Theorem 6)

The requested lemma is exactly Heath-Brown's *P(a,q) ≪ q^{11/2}* (Proc. LMS (3) 64
(1992) 265–338).  When `a < d`, every prime `p ≡ a [MOD d]` is of the form `a + kd`
with `k ≥ 0`, so the clause `a ≤ p` is automatic.

## Roadmap (see `DEPENDENCY_TREE.md` in this directory for the full tree with citations)

The paper proves Theorem 6 through the weighted prime sum of §13–§15
(`Σ = Σ_{p ≡ a (mod q)} (log p)/p · f(L^{-1} log p)`, tent weight `f` supported on
`[L−2K, L]`, `L = 5.5, K = 0.3` in the large-λ₁ case; `L = 4.9, K = 0.25` in the
Siegel-zero case), showing `Σ ≫ L/φ(q)`, whence a prime `p ≤ q^{5.5}` exists in the
class.  The layers, bottom-up:

* **Leaves (delegated, in flight):** `Commons.NumberTheory.Linnik.primePowerTail` and
  `.primePowerVonMangoldtTail` — the §13 p.79 prime-power tail bounds
  `Σ'_{n ≥ N} 1/n ≪ N^{-1/2}` (and with `Λ(n)/n`), used to pass from the prime sum
  `Σ` to the von-Mangoldt sum.
* **§2 Burgess layer** (character sums / `L(σ+it,χ)` bounds, Lemmas 2.1–2.5).
* **§3–§4** partial-fraction expansion of `L′/L` and derivative bounds — requires
  functional-equation/Hadamard-product infrastructure for Dirichlet L-functions
  (Mathlib has continuation + pointwise nonvanishing; commons has convexity and
  vertical bounds, `completedLFunction_eq`, `rootNumber_*`).
* **§5** explicit formula; **§6–§7** positivity & extremal functions (with
  Brun–Titchmarsh); **§8–§10** Deuring–Heilbronn and the λ-bounds
  (`λ₂ ≥ 0.702`, `λ₃ ≥ 0.857`, `λ ≥ (12/11−ε) log(1/λ₁)`); **§11–§12** zero density;
  **§13** Lemmas 13.1–13.3; **§14–§15** Lemma 14.2 / 15.1 + the interval numerics ⇒
  `Σ ≫ L/φ(q)` ⇒ Theorem 6.

This file will grow helper lemmas as the layers are published into the commons.
The statement below is untouched and is the single deliverable.
-/

namespace Commons.NumberTheory.Linnik


/-! ### Helper lemmas toward the §13 (Heath-Brown Lemma 13.1) assembly -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Step-1a of the §13 assembly: the class-filtered von-Mangoldt sum splits by
primality into the prime part (which equals the prime sum, termwise via
`ArithmeticFunction.vonMangoldt_apply_prime`) plus the non-prime part. -/
theorem class_sum_split {q X a : ℕ} {L K : ℝ} :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => n ≡ a [MOD q]),
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
      = (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => n.Prime ∧ n ≡ a [MOD q]),
          ((Real.log (n : ℝ) / (n : ℝ) : ℝ) : ℂ) *
            ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
        + (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
            (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
              ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) := by
  classical
  set s : Finset ℕ := (Finset.Icc 1 X).filter (fun n : ℕ => n ≡ a [MOD q]) with hs
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s)
      (p := fun n : ℕ => n.Prime)
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
  rw [← hsplit, hs]
  congr 1
  · apply Finset.sum_congr ?_ ?_
    · ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn, hp⟩
        exact ⟨hn.1, hp, hn.2⟩
      · rintro ⟨hn, hp, hmod⟩
        exact ⟨⟨hn, hmod⟩, hp⟩
    · intro n hn
      have hp : n.Prime := (Finset.mem_filter.mp hn).2.1
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      push_cast
      ring
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hnp⟩
      exact ⟨hn.1, hnp, hn.2⟩
    · rintro ⟨hn, hnp, hmod⟩
      exact ⟨⟨hn, hmod⟩, hnp⟩


/-- Step-1b crux: below the threshold `q^(L-2K)` the tent weight vanishes, so those
terms drop out of the non-prime sum. -/
theorem tent_vanish_below {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L) {q n : ℕ}
    (hq : 2 ≤ q) (hn : 1 ≤ n) (hnq : (n : ℝ) ≤ (q : ℝ) ^ (L - 2 * K)) :
    tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlog_le : Real.log (n : ℝ) ≤ Real.log ((q : ℝ) ^ (L - 2 * K)) :=
    Real.log_le_log hnR hnq
  rw [Real.log_rpow hqR] at hlog_le
  have hdiv : Real.log (n : ℝ) / Real.log (q : ℝ) ≤ L - 2 * K := by
    rw [div_le_iff₀ hlogq]
    exact hlog_le
  exact (tentWeight_bounds hK h2K).2.2.1 _ hdiv


/-- Step-1b pointwise bound for the non-prime part of the §13 sum:
`‖Λ(n)/n · f(...)‖ ≤ K·Λ(n)/n`. -/
theorem nonprime_term_bound {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L) {q n : ℕ}
    (hn : 1 ≤ n) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
        ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖
      ≤ K * (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) := by
  have hbounds := tentWeight_bounds hK h2K
  have hfnn : 0 ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) := hbounds.1 _
  have hfle : tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) ≤ K := hbounds.2.1 _
  have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [norm_mul, Complex.norm_div]
  rw [show ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ = ArithmeticFunction.vonMangoldt n
        from by rw [Complex.norm_real]; exact Real.norm_of_nonneg hLam,
      show ‖(((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))) : ℝ) : ℂ)‖ =
          tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
        from by rw [Complex.norm_real]; exact Real.norm_of_nonneg hfnn,
      show ‖(n : ℂ)‖ = (n : ℝ) from Complex.norm_natCast n]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
  nlinarith [mul_le_mul_of_nonneg_left hfle hLam]


/-- Step-1b.2: terms below the tent threshold `T = q^(L-2K)` drop out of the
non-prime class sum (via `tent_vanish_below`). -/
theorem nonprime_sum_drop_below {q X a : ℕ} {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L)
    (hq : 2 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      = (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hT : (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)
  · simp [hT]
  · have hf0 : tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 := by
      refine tent_vanish_below hK h2K hq ?_ (le_of_lt (lt_of_not_ge hT))
      exact (Finset.mem_Icc.mp hn).1
    simp [hT, hf0]


/-- Step-1b.3 (WEAK, superseded by `nonprime_restricted_le'` below): termwise push —
the restricted non-prime sum is at most `K · Σ_{n ≤ X, T ≤ n} Λ(n)/n`. -/
theorem nonprime_restricted_le {q X a : ℕ} {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    (hq : 2 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      ≤ K * (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
            ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
  classical
  rw [Finset.mul_sum]
  have h1 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    have h1n : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    simpa [mul_div_assoc] using nonprime_term_bound (le_of_lt hK) (le_of_lt h2K) h1n
  have h2 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ)))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        (Finset.mem_filter.mp hn).2.2.2⟩
    · intro n hn _
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := div_nonneg hLam (le_of_lt hnR)
      have hK0 : 0 ≤ K := le_of_lt hK
      linarith [mul_nonneg hK0 this]
  exact le_trans h1 h2


/-- Step-1b.3 (REFINED): keeping the `¬prime` restriction on the right-hand side, so
the bound decays (the unrestricted sum would grow like `log (X/T)`). -/
theorem nonprime_restricted_le' {q X a : ℕ} {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L)
    (hq : 2 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      ≤ K * (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
  classical
  rw [Finset.mul_sum]
  have h1 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro n hn
    have h1n : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    simpa [mul_div_assoc] using nonprime_term_bound (le_of_lt hK) (le_of_lt h2K) h1n
  have h2 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ)))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          K * (ArithmeticFunction.vonMangoldt n / (n : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        ⟨(Finset.mem_filter.mp hn).2.1, (Finset.mem_filter.mp hn).2.2.2⟩⟩
    · intro n hn _
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := div_nonneg hLam (le_of_lt hnR)
      have hK0 : 0 ≤ K := le_of_lt hK
      linarith [mul_nonneg hK0 this]
  exact le_trans h1 h2


/-- An `IsPrimePow` natural is a prime power with exponent at least 1. -/
theorem isPrimePow_exists {n : ℕ} (hn : IsPrimePow n) :
    ∃ p e : ℕ, Nat.Prime p ∧ 1 ≤ e ∧ n = p ^ e := by
  rw [isPrimePow_def] at hn
  obtain ⟨p, k, hp, hk, hpk⟩ := hn
  exact ⟨p, k, Nat.prime_iff.mpr hp, hk, hpk.symm⟩

/-- If `n` is a non-prime prime power `p^e`, then `2 ≤ e`. -/
theorem exp_two_le_of_not_prime {n p e : ℕ} (hp : Nat.Prime p) (he : 1 ≤ e)
    (hnp : ¬ n.Prime) (h : n = p ^ e) : 2 ≤ e := by
  by_contra hlt
  push Not at hlt
  have he1 : e = 1 := by omega
  subst he1
  rw [h, pow_one] at hnp
  exact hnp hp

/-- `Λ n ≠ 0` and `n` not prime ⇒ `n` is `p^e` with `e ≥ 2` (move (4)'s micro-lemma). -/
theorem nonprime_isPrimePow_exp {n : ℕ}
    (hnΛ : ArithmeticFunction.vonMangoldt n ≠ 0) (hnp : ¬ n.Prime) :
    ∃ p e : ℕ, Nat.Prime p ∧ 2 ≤ e ∧ n = p ^ e := by
  have hIPP : IsPrimePow n := by
    by_contra h
    exact hnΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
  obtain ⟨p, e, hp, he, hne⟩ := isPrimePow_exists hIPP
  exact ⟨p, e, hp, exp_two_le_of_not_prime hp he hnp hne, hne⟩


/-- Move (4), step A: extending the threshold `T ≤ n` to `⌈T⌉ ≤ n` only increases the
sum (nonnegative summands). -/
theorem nonprime_tail_filter_mono {q X : ℕ} {L K : ℝ} (hq : 2 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
        ArithmeticFunction.vonMangoldt n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ Nat.ceil ((q : ℝ) ^ (L - 2 * K)) ≤ n),
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hmem := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1,
      Nat.ceil_le.mpr hmem.2.2⟩
  · intro n hn _
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    exact div_nonneg hLam (le_of_lt hnR)


/-- Move (4), step B: the `Λ = 0` terms off prime powers contribute nothing. -/
theorem nonprime_tail_eq_primePow {q X : ℕ} {L K : ℝ} (hq : 2 ≤ q) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
          ¬ n.Prime ∧ Nat.ceil ((q : ℝ) ^ (L - 2 * K)) ≤ n),
        ArithmeticFunction.vonMangoldt n / (n : ℝ))
      = (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ Nat.ceil ((q : ℝ) ^ (L - 2 * K)) ≤ n ∧ IsPrimePow n),
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hP : IsPrimePow n
  · simp [hP]
  · have h0 : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hP
    simp [hP, h0]


/-! ### Step-1b.4/5: the non-prime part is `O(q^{-(L-2K)/2})`.

The truncated von Mangoldt function supported on prime powers `p^e`, `e ≥ 2`. -/
noncomputable def ppLambda (n : ℕ) : ℝ :=
  if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e then ArithmeticFunction.vonMangoldt n else 0

theorem ppLambda_nonneg (n : ℕ) : 0 ≤ ppLambda n := by
  classical
  unfold ppLambda
  split
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_refl 0

theorem ppLambda_eq_zero_of_not (n : ℕ)
    (h : ¬ ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e) : ppLambda n = 0 := by
  classical
  unfold ppLambda
  rw [if_neg h]

/-- For a **non-prime** `n`, `ppLambda n ≥ Λ n`: off the exponent-`≥2` prime
powers `Λ` already vanishes. -/
theorem le_ppLambda {n : ℕ} (hn : ¬ n.Prime) :
    ArithmeticFunction.vonMangoldt n ≤ ppLambda n := by
  classical
  by_cases h : ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
  · unfold ppLambda; rw [if_pos h]
  · rw [ppLambda_eq_zero_of_not n h]
    have hIPP : ¬ IsPrimePow n := by
      intro hi
      obtain ⟨p, e, hp, he, hne⟩ := isPrimePow_exists hi
      by_cases he1 : e = 1
      · subst he1
        rw [pow_one] at hne
        exact hn (hne ▸ hp)
      · exact h ⟨p, e, hp, by omega, hne⟩
    exact le_of_eq (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hIPP)

/-- Cumulative bound for `ppLambda` from the Chebyshev prime-power estimate. -/
theorem ppLambda_cum_bound {B : ℝ}
    (hB : ∀ x : ℝ, 0 ≤ x →
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          (if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
            then ArithmeticFunction.vonMangoldt n else 0))
        ≤ B * Real.sqrt x) (m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m, ppLambda k) ≤ B * Real.sqrt (m : ℝ) := by
  classical
  have h := hB (m : ℝ) (by positivity)
  rw [Nat.floor_natCast] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro k _
  unfold ppLambda
  rfl

/-- **Step-1b.4/5.** The non-prime part of the class-filtered von-Mangoldt sum, with
the tent weight, is `O(q^{-(L-2K)/2})`: below `q^{L-2K}` the weight vanishes, the
remaining terms are dominated by `K·Λ(n)/n` on non-primes (i.e. exponent-`≥2`
prime powers), and those are `O(N^{-1/2})` by Abel summation. -/
theorem nonprime_tail_le {q : ℕ} {L K : ℝ} (hq : 2 ≤ q) (hLK : 2 ≤ L - 2 * K) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ C / Real.sqrt ((q : ℝ) ^ (L - 2 * K)) := by
  classical
  obtain ⟨B, hBpos, hBbd⟩ := Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
  refine ⟨3 * B, by positivity, fun X => ?_⟩
  set T : ℝ := (q : ℝ) ^ (L - 2 * K) with hT
  set N : ℕ := Nat.ceil T with hN
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT4 : (2 : ℝ) ≤ T := by
    have h1 : ((2 : ℝ) ^ (2 : ℝ)) ≤ T := by
      rw [hT]
      calc ((2 : ℝ) ^ (2 : ℝ)) ≤ (2 : ℝ) ^ (L - 2 * K) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hLK
        _ ≤ (q : ℝ) ^ (L - 2 * K) :=
            Real.rpow_le_rpow (by norm_num) hq2 (le_trans zero_le_two hLK)
    have h2 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by rw [Real.rpow_two]; norm_num
    rw [h2] at h1
    linarith
  have hN2 : 2 ≤ N := by
    have h := Nat.ceil_mono hT4
    rw [hN]
    have : Nat.ceil (2 : ℝ) = 2 := by simp
    omega
  have hcum : ∀ m : ℕ, (∑ k ∈ Finset.Icc 0 m, ppLambda k) ≤ B * Real.sqrt (m : ℝ) :=
    ppLambda_cum_bound (fun x hx => hBbd x hx)
  have hstep1a : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1.1
    exact div_le_div_of_nonneg_right (le_ppLambda hn.2.1) (by positivity)
  have hstep1b : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ T ≤ (n : ℝ)),
          ppLambda n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => N ≤ n), ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, Nat.ceil_le.mpr hn.2.2⟩
    · intro n hn _
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      exact div_nonneg (ppLambda_nonneg n) (by positivity)
  have hstep1 := le_trans hstep1a hstep1b
  have hstep2 : (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => N ≤ n), ppLambda n / (n : ℝ))
      ≤ (∑ n ∈ Finset.Icc N X, ppLambda n / (n : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.2, hn.1.2⟩
    · intro n hn _
      simp only [Finset.mem_Icc] at hn
      exact div_nonneg (ppLambda_nonneg n) (by positivity)
  have hstep3 : (∑ n ∈ Finset.Icc N X, ppLambda n / (n : ℝ)) ≤ 3 * B / Real.sqrt (N : ℝ) := by
    by_cases hNX : N ≤ X
    · exact Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt ppLambda_nonneg
        (le_of_lt hBpos) hcum hN2 hNX
    · rw [Finset.Icc_eq_empty hNX, Finset.sum_empty]
      positivity
  have hle : (N : ℝ) ≥ T := Nat.le_ceil T
  have hsqrt : Real.sqrt T ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hle
  have hTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hfinal : 3 * B / Real.sqrt (N : ℝ) ≤ 3 * B / Real.sqrt T :=
    div_le_div_of_nonneg_left (by positivity) hTpos hsqrt
  refine le_trans ?_ hfinal
  exact le_trans (le_trans hstep1 hstep2) hstep3

/-- **Step 1 complete.** The whole non-prime contribution to the class-filtered
tent-weighted von-Mangoldt sum is `O(q^{-(L-2K)/2})`. -/
theorem nonprime_class_bound {q a X : ℕ} {L K : ℝ} (hK : 0 < K) (hLK : 2 ≤ L - 2 * K)
    (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
        ≤ C / Real.sqrt ((q : ℝ) ^ (L - 2 * K)) := by
  classical
  have h2K : 2 * K < L := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := nonprime_tail_le (q := q) (L := L) (K := K) hq hLK
  have hdrop := nonprime_sum_drop_below (q := q) (X := X) (a := a)
    (le_of_lt hK) (le_of_lt h2K) hq
  have hres := nonprime_restricted_le' (q := q) (X := X) (a := a) hK h2K hq
  refine ⟨K * C₁, by positivity, ?_⟩
  calc (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖)
      = (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ n ≡ a [MOD q] ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖) := hdrop
    _ ≤ K * (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ =>
            ¬ n.Prime ∧ (q : ℝ) ^ (L - 2 * K) ≤ (n : ℝ)),
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) := hres
    _ ≤ K * (C₁ / Real.sqrt ((q : ℝ) ^ (L - 2 * K))) :=
        mul_le_mul_of_nonneg_left (hC₁ X) (le_of_lt hK)
    _ = K * C₁ / Real.sqrt ((q : ℝ) ^ (L - 2 * K)) := by rw [mul_div_assoc]

theorem leastPrimeBound :
    ∃ c : ℝ, ∀ ⦃a d : ℕ⦄, 0 < a → a < d → a.Coprime d →
      ∃ p : ℕ, a ≤ p ∧ p ≤ c * (d : ℝ) ^ (5.5 : ℝ) ∧ p.Prime ∧ p ≡ a [MOD d] := by
  sorry

end Commons.NumberTheory.Linnik
