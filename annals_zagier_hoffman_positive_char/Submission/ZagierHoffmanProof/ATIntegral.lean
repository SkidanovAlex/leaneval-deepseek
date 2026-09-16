import Submission.ZagierHoffmanProof.ATMain
import Submission.ZagierHoffmanProof.Carlitz
import Submission.Commons.Data.Nat.sum_digits_decomp
import Submission.Commons.Data.Nat.geom_pred_mul_sum
import Submission.Commons.Data.Nat.sum_mul_pow_le_compl_shift
import Submission.Commons.Algebra.BigOperators.prod_range_prod_range_pow
import Submission.Commons.Algebra.BigOperators.prod_range_prod_range_pow_strict

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# The Anderson–Thakur integrality at the special indices

Chen's theorem (`ATPeel.atCoeff_atIndex_eq_atForm`) computes the Anderson–Thakur
coefficients at the special indices `m - 1 = q^n - 1 - ∑_{i<n} N_i q^i`:
`atCoeff F (m-1) = ∏_{i<n-1} R_{n-1-i}^{N_i q^i}` with `R_k = P_k / L_k`.
The Anderson–Thakur integrality `α_m = Γ_m · atCoeff F (m-1) ∈ A[t]` is therefore the
divisibility `∏_{i<n-1} L_{n-1-i}^{N_i q^i} ∣ Γ_m` in `A = F[θ]`.

Writing `L_k = (-1)^k ∏_{s ≤ k} [s]`, `D_j = ∏_{s ≤ j} [s]^{q^{j-s}}` and using the base-`q`
digits of `m - 1 = ∑_{i<n}(q-1-N_i)q^i` (so `Γ_m = ∏_{i<n} D_i^{q-1-N_i}`), the divisibility
reduces to the exponent inequality

  `∑_{i ≤ n-1-s} N_i q^i ≤ ∑_{i = s}^{n-1} (q-1-N_i) q^{i-s}`   (`1 ≤ s ≤ n-1`),

which is `Commons.Data.Nat.sum_mul_pow_le_compl_shift` (private-field counterexamples exist
when `s = 0`), together with the two triangular resummations of the products
(`Commons.Algebra.BigOperators.prod_range_prod_range_pow` and `..pow_strict`).

The result is the integrality of `α_m` at *every* special index — the only range of the
Anderson–Thakur integrality for which the literature has a proof (Chen 2015).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `∑_{i<n}(q-1-N_i)q^i = q^n - 1 - ∑_{i<n}N_iq^i`, for digits `N_i ≤ q-1`. -/
lemma sum_compl_mul_pow (n : ℕ) (N : ℕ → ℕ) (hN : ∀ i < n, N i ≤ Nat.card F - 1) :
    (∑ i ∈ Finset.range n, (Nat.card F - 1 - N i) * Nat.card F ^ i)
      = Nat.card F ^ n - 1 - ∑ i ∈ Finset.range n, N i * Nat.card F ^ i := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have h1 : (∑ i ∈ Finset.range n, (Nat.card F - 1 - N i) * Nat.card F ^ i)
      + (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) = Nat.card F ^ n - 1 := by
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ i ∈ Finset.range n,
        (Nat.card F - 1 - N i) * Nat.card F ^ i + N i * Nat.card F ^ i
          = (Nat.card F - 1) * Nat.card F ^ i := by
      intro i hi
      rw [← add_mul, Nat.sub_add_cancel (hN i (Finset.mem_range.mp hi))]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    exact Commons.Data.Nat.geom_pred_mul_sum (Nat.card F) hq1 n
  exact Nat.eq_sub_of_add_eq h1

/-- The special index as a base-`q` digit sum. -/
lemma atIndex_eq_sum_compl (n : ℕ) (N : ℕ → ℕ) (hN : ∀ i < n, N i ≤ Nat.card F - 1) :
    atIndex F n N = ∑ i ∈ Finset.range n, (Nat.card F - 1 - N i) * Nat.card F ^ i := by
  rw [atIndex, sum_compl_mul_pow F n N hN]

/-- The base-`q` digits of the special index. -/
lemma atIndex_digit (n : ℕ) (N : ℕ → ℕ) (hN : ∀ i < n, N i ≤ Nat.card F - 1) (j : ℕ) :
    atIndex F n N / Nat.card F ^ j % Nat.card F
      = if j < n then Nat.card F - 1 - N j else 0 := by
  rw [atIndex_eq_sum_compl F n N hN]
  exact Commons.Data.Nat.sum_digits_decomp (fun i => Nat.card F - 1 - N i)
    (fun i hi => by
      have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
      have := hN i hi
      omega) j

/-- `n ≤ q^(n-1)` for `n ≥ 1` and `q ≥ 2`. -/
lemma self_le_card_pow_pred (n : ℕ) (hn : 1 ≤ n) : n ≤ Nat.card F ^ (n - 1) := by
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have h1 : n ≤ 2 ^ (n - 1) := by
    have h2 := Nat.lt_two_pow_self (n := n - 1)
    omega
  exact le_trans h1 (Nat.pow_le_pow_left hq _)

/-- `q^n - (q-1)·q^(n-1) = q^(n-1)`. -/
lemma card_pow_sub_pred_mul (n : ℕ) (hn : 1 ≤ n) :
    Nat.card F ^ n - (Nat.card F - 1) * Nat.card F ^ (n - 1) = Nat.card F ^ (n - 1) := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have h3 : Nat.card F ^ n = Nat.card F ^ (n - 1) * Nat.card F := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have h4 : (Nat.card F - 1) * Nat.card F ^ (n - 1)
      = Nat.card F ^ (n - 1) * Nat.card F - Nat.card F ^ (n - 1) := by
    rw [Nat.sub_mul, one_mul, Nat.mul_comm]
  rw [h3, h4, Nat.sub_sub_self]
  exact Nat.le_mul_of_pos_right _ (by omega : 0 < Nat.card F)

/-- `n ≤ atIndex F n N + 1` for a shape with `∑ N_i ≤ q-1`. -/
lemma le_atIndex_add_one_of_sum_le (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∀ i < n, N i ≤ Nat.card F - 1)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    n ≤ atIndex F n N + 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hS : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      ≤ (Nat.card F - 1) * Nat.card F ^ (n - 1) := by
    have hle : ∀ i ∈ Finset.range n, N i * Nat.card F ^ i
        ≤ N i * Nat.card F ^ (n - 1) := by
      intro i hi
      have hile : i ≤ n - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
      exact Nat.mul_le_mul_left _ (pow_le_pow_right₀ hq1 hile)
    calc (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
        ≤ ∑ i ∈ Finset.range n, N i * Nat.card F ^ (n - 1) := Finset.sum_le_sum hle
      _ = (∑ i ∈ Finset.range n, N i) * Nat.card F ^ (n - 1) := by rw [Finset.sum_mul]
      _ ≤ (Nat.card F - 1) * Nat.card F ^ (n - 1) := Nat.mul_le_mul_right _ hsum
  have h4 := card_pow_sub_pred_mul F n hn
  have hSle : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n - 1 := by
    refine le_trans hS ?_
    have h5 : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  have e1 : atIndex F n N + 1
      = Nat.card F ^ n - ∑ i ∈ Finset.range n, N i * Nat.card F ^ i := by
    have h1 : 1 ≤ Nat.card F ^ n := Nat.one_le_pow _ _ (by omega)
    rw [atIndex, ← Nat.sub_add_comm hSle, Nat.sub_add_cancel h1]
  rw [e1]
  calc n ≤ Nat.card F ^ (n - 1) := self_le_card_pow_pred F n hn
    _ = Nat.card F ^ n - (Nat.card F - 1) * Nat.card F ^ (n - 1) := h4.symm
    _ ≤ Nat.card F ^ n - ∑ i ∈ Finset.range n, N i * Nat.card F ^ i :=
        Nat.sub_le_sub_left hS _

/-- ★ `Γ` at a special index depends only on the shape: `Γ_{m} = ∏_{i<n}D_i^{q-1-N_i}` for
`m = atIndex F n N + 1`. -/
lemma carlitzGamma_atIndex (n : ℕ) (N : ℕ → ℕ) (hN : ∀ i < n, N i ≤ Nat.card F - 1)
    (hn : 1 ≤ n) (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    carlitzGamma F (atIndex F n N + 1)
      = ∏ i ∈ Finset.range n, (carlitzFact F i) ^ (Nat.card F - 1 - N i) := by
  have hle := le_atIndex_add_one_of_sum_le F n hn N hN hsum
  have hsub : Finset.range n ⊆ Finset.range (atIndex F n N + 1) := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hle)
  have hdig : ∀ j ∈ Finset.range (atIndex F n N + 1),
      (atIndex F n N + 1 - 1) / Nat.card F ^ j % Nat.card F
        = if j < n then Nat.card F - 1 - N j else 0 := by
    intro j _
    rw [Nat.add_sub_cancel]
    exact atIndex_digit F n N hN j
  rw [carlitzGamma]
  rw [← Finset.prod_subset hsub (fun x hx hxnot => ?_)]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hdig i (hsub hi), if_pos (Finset.mem_range.mp hi)]
  · rw [hdig x hx, if_neg (by simpa using hxnot)]
    exact pow_zero _

/-- `L_k = (-1)^k ∏_{s<k} [s+1]`. -/
lemma carlitzL_eq_neg_pow_mul_prod_bracket (k : ℕ) :
    carlitzL F k = (-1 : F[X]) ^ k * ∏ s ∈ Finset.range k, carlitzBracket F (s + 1) := by
  rw [carlitzL_eq_prod_neg, Finset.prod_neg, Finset.card_range]

/-- `D_j = ∏_{s<j} [s+1]^(q^(j-1-s))`. -/
lemma carlitzFact_eq_prod_range_bracket (j : ℕ) :
    carlitzFact F j
      = ∏ s ∈ Finset.range j, (carlitzBracket F (s + 1)) ^ (Nat.card F ^ (j - 1 - s)) := by
  rw [carlitzFact_eq_prod_bracket, prod_Icc_one_eq_prod_range]
  apply Finset.prod_congr rfl
  intro s hs
  rw [show j - (s + 1) = j - 1 - s by have := Finset.mem_range.mp hs; omega]

/-- The `L`-product of the divisibility, resummed over the brackets. -/
lemma prod_carlitzL_eq (n : ℕ) (N : ℕ → ℕ) :
    (∏ i ∈ Finset.range (n - 1), (carlitzL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      = (-1 : F[X]) ^ (∑ i ∈ Finset.range (n - 1), (n - 1 - i) * (N i * Nat.card F ^ i))
        * ∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
            (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i) := by
  have hstep : (∏ i ∈ Finset.range (n - 1), (carlitzL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      = (∏ i ∈ Finset.range (n - 1), ((-1 : F[X]) ^ (n - 1 - i)) ^ (N i * Nat.card F ^ i))
        * ∏ i ∈ Finset.range (n - 1),
            (∏ s ∈ Finset.range (n - 1 - i), carlitzBracket F (s + 1)) ^
              (N i * Nat.card F ^ i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [carlitzL_eq_neg_pow_mul_prod_bracket, mul_pow]
  rw [hstep, Commons.Algebra.BigOperators.prod_range_prod_range_pow]
  congr 1
  have hsign : (∏ i ∈ Finset.range (n - 1), ((-1 : F[X]) ^ (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      = ∏ i ∈ Finset.range (n - 1),
          (-1 : F[X]) ^ ((n - 1 - i) * (N i * Nat.card F ^ i)) :=
    Finset.prod_congr rfl (fun i _ => by rw [← pow_mul])
  rw [hsign, Finset.prod_pow_eq_pow_sum]

/-- The `D`-product of the divisibility, resummed over the brackets. -/
lemma prod_carlitzFact_eq (n : ℕ) (d : ℕ → ℕ) :
    (∏ j ∈ Finset.range n, (carlitzFact F j) ^ (d j))
      = ∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
          (∑ j ∈ Finset.Icc (s + 1) (n - 1), d j * Nat.card F ^ (j - 1 - s)) := by
  have hstep : (∏ j ∈ Finset.range n, (carlitzFact F j) ^ (d j))
      = ∏ j ∈ Finset.range n, ∏ s ∈ Finset.range j,
          (carlitzBracket F (s + 1)) ^ (d j * Nat.card F ^ (j - 1 - s)) := by
    apply Finset.prod_congr rfl
    intro j _
    rw [carlitzFact_eq_prod_range_bracket, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro s _
    rw [← pow_mul, mul_comm]
  rw [hstep, Commons.Algebra.BigOperators.prod_range_prod_range_pow_strict]

/-- The exponent inequality behind the divisibility, for every bracket `[s+1]`. -/
lemma prod_carlitzL_exponent_le (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∀ i < n, N i ≤ Nat.card F - 1)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) (s : ℕ) :
    (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i)
      ≤ ∑ j ∈ Finset.Icc (s + 1) (n - 1),
          (Nat.card F - 1 - N j) * Nat.card F ^ (j - 1 - s) := by
  have h := Commons.Data.Nat.sum_mul_pow_le_compl_shift (carlitz_card_ge_two F) (n := n)
    (s := s + 1) (by omega) N (fun i hi => hN i hi) hsum
  rw [show n - (s + 1) = n - 1 - s by omega] at h
  refine le_trans h (le_of_eq ?_)
  refine (Finset.sum_bij (fun j (_ : j ∈ Finset.Icc (s + 1) (n - 1)) => j - (s + 1))
    ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (by omega)
  · intro j1 hj1 j2 hj2 heq
    rw [Finset.mem_Icc] at hj1 hj2
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    exact ⟨i + (s + 1), by rw [Finset.mem_Icc]; omega, by omega⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [show j - (s + 1) + (s + 1) = j by omega, show j - (s + 1) = j - 1 - s by omega]

/-- ★ The `L`-product divides `Γ` at every special index. -/
lemma prod_carlitzL_dvd_carlitzGamma (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∀ i < n, N i ≤ Nat.card F - 1)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    (∏ i ∈ Finset.range (n - 1), (carlitzL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      ∣ carlitzGamma F (atIndex F n N + 1) := by
  set E := ∑ i ∈ Finset.range (n - 1), (n - 1 - i) * (N i * Nat.card F ^ i) with hE
  set AA : ℕ → ℕ := fun s => ∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i with hAA
  set BB : ℕ → ℕ := fun s => ∑ j ∈ Finset.Icc (s + 1) (n - 1),
      (Nat.card F - 1 - N j) * Nat.card F ^ (j - 1 - s) with hBB
  have hle : ∀ s, AA s ≤ BB s := fun s => prod_carlitzL_exponent_le F n hn N hN hsum s
  have hprod : (∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^ (AA s))
      * (∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^ (BB s - AA s))
      = ∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^ (BB s) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    rw [← pow_add, Nat.add_sub_cancel' (hle s)]
  have hu : (-1 : F[X]) ^ E * (-1 : F[X]) ^ E = 1 := by
    rw [← mul_pow, show (-1 : F[X]) * (-1) = 1 by ring, one_pow]
  refine ⟨(-1 : F[X]) ^ E * ∏ s ∈ Finset.range (n - 1),
      (carlitzBracket F (s + 1)) ^ (BB s - AA s), ?_⟩
  rw [carlitzGamma_atIndex F n N hN hn hsum, prod_carlitzL_eq F n N,
    prod_carlitzFact_eq F n (fun j => Nat.card F - 1 - N j), hAA, hBB, hE]
  calc (∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
        (∑ j ∈ Finset.Icc (s + 1) (n - 1), (Nat.card F - 1 - N j) * Nat.card F ^ (j - 1 - s)))
      = (∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
          (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i))
        * (∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
          ((∑ j ∈ Finset.Icc (s + 1) (n - 1), (Nat.card F - 1 - N j) * Nat.card F ^ (j - 1 - s))
            - (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i))) := by
        rw [← hprod]
    _ = ((-1 : F[X]) ^ (∑ i ∈ Finset.range (n - 1),
            (n - 1 - i) * (N i * Nat.card F ^ i))
          * ∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
            (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i))
        * ((-1 : F[X]) ^ (∑ i ∈ Finset.range (n - 1),
            (n - 1 - i) * (N i * Nat.card F ^ i))
          * ∏ s ∈ Finset.range (n - 1), (carlitzBracket F (s + 1)) ^
            ((∑ j ∈ Finset.Icc (s + 1) (n - 1), (Nat.card F - 1 - N j) * Nat.card F ^ (j - 1 - s))
              - (∑ i ∈ Finset.range (n - 1 - s), N i * Nat.card F ^ i))) := by
        rw [mul_mul_mul_comm, hu, one_mul]

/-- The polynomial model of `P_k` inside `A = F[θ][t]`. -/
noncomputable def atPkPoly (k : ℕ) : (F[X])[X] :=
  ∏ j ∈ Finset.Icc 1 k,
    (Polynomial.C (Polynomial.X : F[X]) - Polynomial.X ^ (Nat.card F ^ j))

lemma atPk_eq_algebraMap (k : ℕ) :
    atPk F k = algebraMap ((F[X])[X]) (atQ F) (atPkPoly F k) := by
  rw [atPk, atPkPoly, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_sub, map_pow, atTheta, atT]

lemma atL_ne_zero (k : ℕ) : atL F k ≠ 0 := by
  rw [atL]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ((F[X])[X]) (atQ F))).mpr
    (Polynomial.C_ne_zero.mpr (carlitzL_ne_zero F k))

/-- ★★ **The Anderson–Thakur integrality at the special indices**: for `1 ≤ n` and a shape
`N` with `∑_{i<n}N_i ≤ q-1`, the Anderson–Thakur polynomial `α_{m}` at
`m = atIndex F n N + 1 = q^n - ∑_{i<n}N_iq^i` is a polynomial in `θ` and `t`. -/
theorem atAlpha_atIndex_mem (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    ∃ P : (F[X])[X], atAlpha F (atIndex F n N + 1) = algebraMap ((F[X])[X]) (atQ F) P := by
  classical
  have hN : ∀ i < n, N i ≤ Nat.card F - 1 := fun i hi =>
    le_trans (Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr hi)) hsum
  obtain ⟨Q, hQ⟩ := prod_carlitzL_dvd_carlitzGamma F n hn N hN hsum
  have hΓ : (∏ i ∈ Finset.range (n - 1), (carlitzL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      * Q = carlitzGamma F (atIndex F n N + 1) := hQ.symm
  refine ⟨Polynomial.C Q * ∏ i ∈ Finset.range (n - 1),
      (atPkPoly F (n - 1 - i)) ^ (N i * Nat.card F ^ i), ?_⟩
  have hm : atIndex F n N + 1 - 1 = atIndex F n N := Nat.add_sub_cancel _ _
  -- the image of the witness
  have hmapQ : algebraMap ((F[X])[X]) (atQ F)
      (Polynomial.C Q * ∏ i ∈ Finset.range (n - 1),
        (atPkPoly F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      = algebraMap ((F[X])[X]) (atQ F) (Polynomial.C Q)
        * ∏ i ∈ Finset.range (n - 1), (atPk F (n - 1 - i)) ^ (N i * Nat.card F ^ i) := by
    simp only [map_mul, map_prod, map_pow, atPk_eq_algebraMap]
  -- `Γ` in terms of the `L`-product
  have hGamma : algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzGamma F (atIndex F n N + 1)))
      = (∏ i ∈ Finset.range (n - 1), (atL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
        * algebraMap ((F[X])[X]) (atQ F) (Polynomial.C Q) := by
    simp only [← hΓ, map_mul, map_prod, map_pow, atL]
  have hform : atForm F n N = ∏ i ∈ Finset.range (n - 1),
      (atPk F (n - 1 - i) * (atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i) := by
    rw [atForm]
    apply Finset.prod_congr rfl
    intro i _
    rw [atR]
  rw [atAlpha, hm, atCoeff_atIndex_eq_atForm F n hn N hsum, hform, hmapQ]
  -- the products
  have hprod : ∀ i ∈ Finset.range (n - 1),
      (atPk F (n - 1 - i) * (atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i)
        = (atPk F (n - 1 - i)) ^ (N i * Nat.card F ^ i)
          * ((atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i) := fun i _ => mul_pow _ _ _
  rw [Finset.prod_congr rfl hprod, Finset.prod_mul_distrib]
  have hAD : (∏ i ∈ Finset.range (n - 1), (atL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
      * (∏ i ∈ Finset.range (n - 1), ((atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (atL_ne_zero F (n - 1 - i)))]
  rw [hGamma]
  calc ((∏ i ∈ Finset.range (n - 1), (atL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
          * algebraMap ((F[X])[X]) (atQ F) (Polynomial.C Q))
        * ((∏ i ∈ Finset.range (n - 1), (atPk F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
          * ∏ i ∈ Finset.range (n - 1), ((atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i))
      = (algebraMap ((F[X])[X]) (atQ F) (Polynomial.C Q)
          * ∏ i ∈ Finset.range (n - 1), (atPk F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
        * ((∏ i ∈ Finset.range (n - 1), (atL F (n - 1 - i)) ^ (N i * Nat.card F ^ i))
          * ∏ i ∈ Finset.range (n - 1), ((atL F (n - 1 - i))⁻¹) ^ (N i * Nat.card F ^ i)) := by
        ring
    _ = algebraMap ((F[X])[X]) (atQ F) (Polynomial.C Q)
          * ∏ i ∈ Finset.range (n - 1), (atPk F (n - 1 - i)) ^ (N i * Nat.card F ^ i) := by
        rw [hAD, mul_one]

end ZagierHoffmanPositiveChar
