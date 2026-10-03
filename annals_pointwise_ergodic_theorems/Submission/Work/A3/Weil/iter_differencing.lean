import Mathlib
import Submission.Work.A3.Weil.normSq_le_sum_corr
import Submission.Work.A3.Weil.sum_piFinset_snoc

/-!
# Iterated Weyl (van der Corput) differencing

We prove the `k`-fold van der Corput / Weyl differencing inequality: for every sequence
`u : ℤ → ℂ` vanishing off the window `wRange N = {0, …, N-1}`,

`‖∑_{n ∈ wRange N} u n‖ ^ (2 ^ k) ≤ c · N ^ (2 ^ k - 1 - k) ·
    ∑_{l ∈ (shiftIdx N)^k} ‖∑_{n ∈ wRange N} (Δ_{l_1} ⋯ Δ_{l_k} u)(n)‖`

with a constant `c = c k` depending only on `k`, where `iterCorr k l u` is the `k`-fold
autocorrelation of `u` along the shifts `l` and `shiftIdx N = {-(N-1), …, N-1}`.

The proof is the standard iteration of the elementary identity
`|∑_n v n|² = ∑_h ∑_n v (n+h) · conj (v n)` (`Work.A3.Weil.normSq_le_sum_corr`),
which for a sequence `v` supported in `wRange N` says

`‖∑_{n ∈ wRange N} v n‖² ≤ ∑_{h ∈ shiftIdx N} ‖∑_{n ∈ wRange N} v (n + h) * conj (v n)‖`,

and the definitional recursion `iterCorr (k+1) (Fin.snoc l h) u n =
iterCorr k l u (n + h) * conj (iterCorr k l u n)`.

Writing `M = #(shiftIdx N)` and
`B_k = ∑_{l ∈ (shiftIdx N)^k} ‖∑_{n ∈ wRange N} iterCorr k l u n‖`,
the induction step is

`‖S‖^{2^{k+1}} = (‖S‖^{2^k})² ≤ (M^{e_k} B_k)² ≤ M^{2 e_k} · M^k · ∑_l ‖C_k(l)‖²  ≤ M^{2 e_k + k} B_{k+1}`,

using Cauchy–Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`) for the middle step and the
single-step inequality for each `l` in the last one; the exponent satisfies
`e_{k+1} = 2 e_k + k`.  Finally `M ≤ 2N`, so `c = 2^{e_k}` works.
-/

set_option autoImplicit false

namespace Work.A3.Weil

open Finset
open scoped BigOperators

noncomputable section

/-- The exponent `e k = 2 ^ k - 1 - k` (nonnegative for every `k`, since `k + 1 ≤ 2 ^ k`). -/
def iexp (k : ℕ) : ℕ := 2 ^ k - 1 - k

lemma iexp_zero : iexp 0 = 0 := rfl

lemma iexp_one : iexp 1 = 0 := rfl

lemma iexp_succ (k : ℕ) : iexp (k+1) = 2 * iexp k + k := by
  have hk : k + 1 ≤ 2 ^ k := by have := Nat.lt_two_pow_self (n := k); omega
  unfold iexp
  rw [pow_succ]
  omega

/-- The `k`-fold correlation block sum `∑_{n ∈ wRange N} iterCorr k l v n`. -/
def cSum (N : ℕ) (k : ℕ) (l : Fin k → ℤ) (v : ℤ → ℂ) : ℂ :=
  ∑ n ∈ wRange N, iterCorr k l v n

/-- The `k`-th level quantum: the `ℓ¹`-sum of the correlation block sums over all `k`-tuples
of admissible shifts. -/
def lvl (N : ℕ) (k : ℕ) (v : ℤ → ℂ) : ℝ :=
  ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N), ‖cSum N k l v‖

lemma card_piFinset_const (k : ℕ) (s : Finset ℤ) :
    (Fintype.piFinset (fun _ : Fin k => s)).card = s.card ^ k := by
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, Fintype.card_fin]

/-- The definitional recursion for the iterated autocorrelation. -/
lemma iterCorr_succ_snoc (k : ℕ) (l : Fin k → ℤ) (h : ℤ) (v : ℤ → ℂ) (n : ℤ) :
    iterCorr (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v n
      = iterCorr k l v (n + h) * star (iterCorr k l v n) := by
  simp [iterCorr]

/-- The iterated autocorrelation of a sequence supported in `wRange N` is again supported
in `wRange N`. -/
lemma support_iterCorr {N : ℕ} {v : ℤ → ℂ} (hv : ∀ n, n ∉ wRange N → v n = 0) :
    ∀ (k : ℕ) (l : Fin k → ℤ) (n : ℤ), n ∉ wRange N → iterCorr k l v n = 0
  | 0, l, n, hn => hv n hn
  | k+1, l, n, hn => by
      have h : iterCorr k (fun i => l i.castSucc) v n = 0 :=
        support_iterCorr hv k (fun i => l i.castSucc) n hn
      show iterCorr k (fun i => l i.castSucc) v (n + l (Fin.last k)) *
          star (iterCorr k (fun i => l i.castSucc) v n) = 0
      rw [h, star_zero, mul_zero]

lemma lvl_zero (N : ℕ) (v : ℤ → ℂ) :
    lvl N 0 v = ‖∑ n ∈ wRange N, v n‖ := by
  rw [lvl, Fintype.piFinset_of_isEmpty]
  rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → ℤ)]
  · simp [cSum, iterCorr]
  · intro b _ hb
    exact absurd (Subsingleton.elim b (Fin.elim0 : Fin 0 → ℤ)) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The `k`-fold Weyl differencing estimate.**  For a sequence `v` supported in `wRange N`,

`‖∑_{n ∈ wRange N} v n‖ ^ (2 ^ k) ≤ #(shiftIdx N) ^ (2 ^ k - 1 - k) · B_k`. -/
theorem lvl_bound (N : ℕ) (v : ℤ → ℂ) (hv : ∀ n, n ∉ wRange N → v n = 0) (k : ℕ) :
    ‖∑ n ∈ wRange N, v n‖ ^ (2 ^ k) ≤ ((shiftIdx N).card : ℝ) ^ (iexp k) * lvl N k v := by
  induction k with
  | zero =>
      rw [iexp_zero, pow_zero, pow_zero, pow_one, one_mul]
      rw [lvl_zero N v]
  | succ k ih =>
      set V : ℂ := ∑ n ∈ wRange N, v n with hV
      set M : ℝ := ((shiftIdx N).card : ℝ) with hM
      set B : ℝ := lvl N k v with hB
      have hMnn : (0:ℝ) ≤ M := by rw [hM]; positivity
      have h1 : ‖V‖ ^ (2 ^ (k+1)) = (‖V‖ ^ (2^k))^2 := by
        rw [pow_succ (2:ℕ) k, pow_mul]
      have h2 : (‖V‖ ^ (2^k))^2 ≤ (M ^ iexp k * B)^2 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [hV, hM, hB]; exact ih
      have h3 : (M ^ iexp k * B)^2 = M ^ (2 * iexp k) * B^2 := by
        rw [mul_pow, ← pow_mul, mul_comm (iexp k) 2]
      have h4 : B^2 ≤ M ^ k * ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
            ‖cSum N k l v‖ ^ 2 := by
        have key := sq_sum_le_card_mul_sum_sq
          (s := Fintype.piFinset (fun _ : Fin k => shiftIdx N))
          (f := fun l => ‖cSum N k l v‖)
        rw [card_piFinset_const] at key
        simpa [hB, lvl, hM, Nat.cast_pow] using key
      have h5 : ∀ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
            ‖cSum N k l v‖ ^ 2 ≤
            ∑ h ∈ shiftIdx N, ‖cSum N (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v‖ := by
        intro l _
        have hsupp : ∀ n, n ∉ wRange N → iterCorr k l v n = 0 := support_iterCorr hv k l
        have hstep := normSq_le_sum_corr (N := N) (v := iterCorr k l v) hsupp
        have hcongr : ∀ h : ℤ, (∑ n ∈ wRange N,
              iterCorr k l v (n + h) * star (iterCorr k l v n))
            = ∑ n ∈ wRange N, iterCorr (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v n := by
          intro h
          exact Finset.sum_congr rfl (fun n _ => (iterCorr_succ_snoc k l h v n).symm)
        calc ‖cSum N k l v‖ ^ 2
            = ‖∑ n ∈ wRange N, iterCorr k l v n‖ ^ 2 := rfl
          _ ≤ ∑ h ∈ shiftIdx N, ‖∑ n ∈ wRange N,
                iterCorr k l v (n + h) * star (iterCorr k l v n)‖ := hstep
          _ = ∑ h ∈ shiftIdx N, ‖∑ n ∈ wRange N,
                iterCorr (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v n‖ := by
                refine Finset.sum_congr rfl (fun h _ => ?_)
                rw [hcongr h]
          _ = ∑ h ∈ shiftIdx N, ‖cSum N (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v‖ := rfl
      have h6 : ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
            ‖cSum N k l v‖ ^ 2 ≤ lvl N (k+1) v := by
        calc ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N), ‖cSum N k l v‖ ^ 2
            ≤ ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
                ∑ h ∈ shiftIdx N, ‖cSum N (k+1) (Fin.snoc (α := fun _ => ℤ) l h) v‖ :=
                Finset.sum_le_sum h5
          _ = ∑ l ∈ Fintype.piFinset (fun _ : Fin (k+1) => shiftIdx N), ‖cSum N (k+1) l v‖ :=
                sum_piFinset_snoc k (shiftIdx N) (fun l => ‖cSum N (k+1) l v‖)
          _ = lvl N (k+1) v := rfl
      calc ‖V‖ ^ (2 ^ (k+1))
          = (‖V‖ ^ (2^k))^2 := h1
        _ ≤ (M ^ iexp k * B)^2 := h2
        _ = M ^ (2 * iexp k) * B^2 := h3
        _ ≤ M ^ (2 * iexp k) * (M ^ k * ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
              ‖cSum N k l v‖ ^ 2) := by
              gcongr
        _ = M ^ (2 * iexp k) * M ^ k * (∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
              ‖cSum N k l v‖ ^ 2) := by ring
        _ = M ^ (2 * iexp k + k) * (∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
              ‖cSum N k l v‖ ^ 2) := by rw [← pow_add]
        _ ≤ M ^ (2 * iexp k + k) * lvl N (k+1) v := by
              gcongr
        _ = M ^ (iexp (k+1)) * lvl N (k+1) v := by rw [iexp_succ]

lemma shiftIdx_card_le (N : ℕ) : (shiftIdx N).card ≤ 2 * N := by
  have h1 : (shiftIdx N).card = ((N:ℤ) - 1 + 1 - (-((N:ℤ)-1))).toNat := by
    simp only [shiftIdx, Int.card_Icc]
  have h2 : ((N:ℤ) - 1 + 1 - (-((N:ℤ)-1))) = (2:ℤ) * N - 1 := by ring
  omega

/-- **Iterated Weyl differencing.**  For every `k` there is `c = c k > 0` such that for every
`N ≥ 1` and every sequence `u` supported in `wRange N = {0, …, N-1}`,

`‖∑_{n ∈ wRange N} u n‖ ^ (2 ^ k) ≤ c · N ^ (2 ^ k - 1 - k) ·
    ∑_{l ∈ (shiftIdx N)^k} ‖∑_{n ∈ wRange N} iterCorr k l u n‖`. -/
theorem iter_differencing (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (u : ℤ → ℂ),
      (∀ n : ℤ, n ∉ Work.A3.Weil.wRange N → u n = 0) →
      ‖∑ n ∈ Work.A3.Weil.wRange N, u n‖ ^ (2 ^ k) ≤
        c * (N : ℝ) ^ (2 ^ k - 1 - k) *
          ∑ l ∈ Fintype.piFinset (fun _ : Fin k => Work.A3.Weil.shiftIdx N),
            ‖∑ n ∈ Work.A3.Weil.wRange N, Work.A3.Weil.iterCorr k l u n‖ := by
  refine ⟨(2:ℝ) ^ (iexp k), by positivity, ?_⟩
  intro N hN u hu
  have hmain : ‖∑ n ∈ wRange N, u n‖ ^ (2^k) ≤
      ((shiftIdx N).card : ℝ) ^ (iexp k) * lvl N k u := lvl_bound N u hu k
  have hcard : ((shiftIdx N).card : ℝ) ≤ 2 * (N : ℝ) := by
    have h := shiftIdx_card_le N
    exact_mod_cast h
  have hpow : ((shiftIdx N).card : ℝ) ^ (iexp k) ≤
      (2:ℝ) ^ (iexp k) * (N:ℝ) ^ (iexp k) := by
    calc ((shiftIdx N).card : ℝ) ^ (iexp k)
        ≤ (2 * (N:ℝ)) ^ (iexp k) := pow_le_pow_left₀ (by positivity) hcard (iexp k)
      _ = (2:ℝ) ^ (iexp k) * (N:ℝ) ^ (iexp k) := by rw [mul_pow]
  have hlvl : 0 ≤ lvl N k u := by
    rw [lvl]; exact Finset.sum_nonneg (fun l _ => norm_nonneg _)
  calc ‖∑ n ∈ wRange N, u n‖ ^ (2^k)
      ≤ ((shiftIdx N).card : ℝ) ^ (iexp k) * lvl N k u := hmain
    _ ≤ ((2:ℝ) ^ (iexp k) * (N:ℝ) ^ (iexp k)) * lvl N k u := by gcongr
    _ = (2:ℝ) ^ (iexp k) * (N:ℝ) ^ (2 ^ k - 1 - k) *
          ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
            ‖∑ n ∈ wRange N, iterCorr k l u n‖ := by
        simp only [iexp, lvl, cSum]

end

end Work.A3.Weil
