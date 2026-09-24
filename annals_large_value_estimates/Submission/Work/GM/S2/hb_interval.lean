import Mathlib
import Submission.Work.GM.S2.Defs

/-!
# `HBStatement` for a Dirichlet polynomial supported on `[1, M]`

Guth–Maynard §6 needs Heath-Brown's large-value bound
(`Submission.GM.HBStatement`), which is stated for the *dyadic* range `[N, 2N]`,
for a Dirichlet polynomial supported on an arbitrary initial interval `[1, M]`.

The reduction is the standard dyadic one.  Split `[1, M]` into the `≍ log M`
blocks `(⌊M/2^{k+1}⌋, ⌊M/2^k⌋]`, `k < K = Nat.clog 2 (M+1)`; the `k`-th block sits
inside the dyadic range `[N_k, 2 N_k]` with `N_k = ⌊M/2^{k+1}⌋ + 1`.  Apply
`HBStatement` block by block and Cauchy–Schwarz in the block index.  The `log M`
loss is absorbed by the arbitrary power `M^η`, `η > 0`, allowed by the statement.
-/

namespace Work.GM.S2

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## A `log M`-versus-`M^η` bound for `Nat.clog` -/

theorem dya_clog_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      ((Nat.clog 2 (M + 1) : ℝ)) ≤ C * (M : ℝ) ^ (η / 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hη2 : 0 < η / 2 := by linarith
  set c : ℝ := 2 ^ (η / 2) / ((η / 2) * Real.log 2) with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity)
  refine ⟨1 + c, by linarith, ?_⟩
  intro M hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hKge1 : 1 ≤ Nat.clog 2 (M + 1) := by
    have h := Nat.le_pow_clog (show 1 < 2 by norm_num) (M + 1)
    by_contra hlt
    have h0 : Nat.clog 2 (M + 1) = 0 := by omega
    rw [h0] at h
    simp at h
    omega
  have hpow : 2 ^ (Nat.clog 2 (M + 1) - 1) < M + 1 := by
    have hmin : ¬ (Nat.clog 2 (M + 1) ≤ Nat.clog 2 (M + 1) - 1) := by omega
    rw [Nat.clog_le_iff_le_pow (show 1 < 2 by norm_num)] at hmin
    omega
  have hloglt : (((Nat.clog 2 (M + 1) - 1 : ℕ)) : ℝ) * Real.log 2
      < Real.log ((M : ℝ) + 1) := by
    have h2 : (2 : ℝ) ^ (Nat.clog 2 (M + 1) - 1) < (M : ℝ) + 1 := by
      exact_mod_cast hpow
    have h := Real.log_lt_log
      (show (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 (M + 1) - 1) by positivity) h2
    rwa [Real.log_pow] at h
  have hcast : (((Nat.clog 2 (M + 1) - 1 : ℕ)) : ℝ)
      = ((Nat.clog 2 (M + 1) : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hKge1]
    norm_num
  have hKle : ((Nat.clog 2 (M + 1) : ℕ) : ℝ) ≤ 1 + Real.log ((M : ℝ) + 1) / Real.log 2 := by
    have h2 : ((Nat.clog 2 (M + 1) : ℕ) : ℝ) - 1 < Real.log ((M : ℝ) + 1) / Real.log 2 := by
      rw [lt_div_iff₀ hlog2]
      rw [hcast] at hloglt
      linarith [hloglt]
    linarith
  have hlogM : Real.log ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ (η / 2) / (η / 2) :=
    Real.log_le_rpow_div (by positivity) hη2
  have hcomp : ((M : ℝ) + 1) ^ (η / 2) ≤ 2 ^ (η / 2) * (M : ℝ) ^ (η / 2) := by
    rw [← Real.mul_rpow (by norm_num) hMpos.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hη2.le
  have hbound : Real.log ((M : ℝ) + 1) / Real.log 2 ≤ c * (M : ℝ) ^ (η / 2) := by
    calc Real.log ((M : ℝ) + 1) / Real.log 2
        ≤ (((M : ℝ) + 1) ^ (η / 2) / (η / 2)) / Real.log 2 :=
          div_le_div_of_nonneg_right hlogM hlog2.le
      _ ≤ ((2 ^ (η / 2) * (M : ℝ) ^ (η / 2)) / (η / 2)) / Real.log 2 :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hcomp hη2.le) hlog2.le
      _ = c * (M : ℝ) ^ (η / 2) := by
          rw [hc]
          field_simp
  calc ((Nat.clog 2 (M + 1) : ℕ) : ℝ) ≤ 1 + Real.log ((M : ℝ) + 1) / Real.log 2 := hKle
    _ ≤ 1 + c * (M : ℝ) ^ (η / 2) := by linarith [hbound]
    _ ≤ (1 + c) * (M : ℝ) ^ (η / 2) := by
        have h1 : (1 : ℝ) ≤ (M : ℝ) ^ (η / 2) := Real.one_le_rpow hM1 hη2.le
        nlinarith [h1, hcpos]

/-! ## Dyadic blocks of `[1, M]` -/

/-- `⌊M / 2^k⌋`. -/
def dyaA (M k : ℕ) : ℕ := M / 2 ^ k

/-- The `k`-th dyadic block `(⌊M/2^{k+1}⌋, ⌊M/2^k⌋]`. -/
def dyaBlk (M k : ℕ) : Finset ℕ := Finset.Ioc (dyaA M (k + 1)) (dyaA M k)

/-- `⌊M/2^{k+1}⌋ + 1`, the left end of `dyaBlk M k`; the block lies in
`[dyaN M k, 2 * dyaN M k]`. -/
def dyaN (M k : ℕ) : ℕ := dyaA M (k + 1) + 1

lemma dyaA_succ (M k : ℕ) : dyaA M (k + 1) = dyaA M k / 2 := by
  rw [dyaA, dyaA, Nat.div_div_eq_div_mul, pow_succ]

lemma dyaA_succ_le (M k : ℕ) : dyaA M (k + 1) ≤ dyaA M k := by
  rw [dyaA_succ]; exact Nat.div_le_self _ _

lemma dyaA_le (M k : ℕ) : dyaA M k ≤ M := Nat.div_le_self _ _

lemma dyaN_pos (M k : ℕ) : 1 ≤ dyaN M k := by rw [dyaN]; omega

lemma dyaN_le (M k : ℕ) : dyaN M k ≤ M + 1 := by
  rw [dyaN]; exact Nat.add_le_add_right (dyaA_le M (k + 1)) 1

lemma dyaBlk_subset (M k : ℕ) : dyaBlk M k ⊆ Finset.Icc (dyaN M k) (2 * dyaN M k) := by
  intro x hx
  rw [dyaBlk, Finset.mem_Ioc] at hx
  rw [Finset.mem_Icc]
  have hdiv : dyaA M k ≤ 2 * dyaA M (k + 1) + 1 := by
    have hdd := Nat.div_add_mod (dyaA M k) 2
    have hmod : dyaA M k % 2 ≤ 1 := by
      have := Nat.mod_lt (dyaA M k) (by norm_num : 0 < 2)
      omega
    rw [dyaA_succ]
    omega
  have hbig : dyaA M k ≤ 2 * dyaN M k := by rw [dyaN]; omega
  exact ⟨by rw [dyaN]; omega, hx.2.trans hbig⟩

/-- The blocks `dyaBlk M k`, `k < K`, tile `(⌊M/2^K⌋, M]`. -/
lemma sum_Ioc_dyaBlk (M K : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc (dyaA M K) M, f n = ∑ k ∈ Finset.range K, ∑ n ∈ dyaBlk M k, f n := by
  induction K with
  | zero => simp [dyaBlk, dyaA]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hu : Finset.Ioc (dyaA M (K + 1)) M = dyaBlk M K ∪ Finset.Ioc (dyaA M K) M := by
      rw [dyaBlk, Finset.Ioc_union_Ioc_eq_Ioc (dyaA_succ_le M K) (dyaA_le M K)]
    have hd : Disjoint (dyaBlk M K) (Finset.Ioc (dyaA M K) M) := by
      rw [dyaBlk, Finset.Ioc_disjoint_Ioc]
      rw [min_eq_left (dyaA_le M K), max_eq_right (dyaA_succ_le M K)]
    rw [hu, Finset.sum_union hd, add_comm]

/-- The blocks `dyaBlk M k`, `k < K`, tile `[1, M]` when `M < 2^K`. -/
lemma sum_Icc_dyaBlk (M K : ℕ) (hK : M < 2 ^ K) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 M, f n = ∑ k ∈ Finset.range K, ∑ n ∈ dyaBlk M k, f n := by
  rw [← sum_Ioc_dyaBlk M K f]
  have h0 : dyaA M K = 0 := by rw [dyaA, Nat.div_eq_of_lt hK]
  rw [h0]
  rw [show Finset.Ioc 0 M = Finset.Icc 1 M from by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega]

/-! ## The block polynomials -/

/-- The coefficients of the `k`-th block, extended by zero. -/
def dyaC (M : ℕ) (c : ℕ → ℂ) (k : ℕ) (n : ℕ) : ℂ := if n ∈ dyaBlk M k then c n else 0

/-- The `k`-th block polynomial `Σ_{N_k ≤ n ≤ 2 N_k} a_{k,n} n^{iτ}`, where `a_k`
is the restriction of `c` to the `k`-th block. -/
noncomputable def dyaPoly (M : ℕ) (c : ℕ → ℂ) (k : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (dyaN M k) (2 * dyaN M k),
    dyaC M c k n * (n : ℂ) ^ (Complex.I * (τ : ℂ))

lemma dyaC_norm_le (M : ℕ) (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k n : ℕ) :
    ‖dyaC M c k n‖ ≤ 1 := by
  rw [dyaC]
  split_ifs with h
  · exact hc n
  · simp

/-- The block polynomial is the sub-sum of the original polynomial over the block. -/
lemma dyaPoly_eq (M : ℕ) (c : ℕ → ℂ) (k : ℕ) (τ : ℝ) :
    dyaPoly M c k τ = ∑ n ∈ dyaBlk M k, c n * (n : ℂ) ^ (Complex.I * (τ : ℂ)) := by
  have h := Finset.sum_subset (dyaBlk_subset M k)
    (f := fun n => dyaC M c k n * (n : ℂ) ^ (Complex.I * (τ : ℂ)))
    (fun x _ hx => by rw [dyaC, if_neg hx, zero_mul])
  rw [dyaPoly, ← h]
  exact Finset.sum_congr rfl (fun x hx => by rw [dyaC, if_pos hx])

/-! ## The main reduction -/

theorem hb_interval (hHB : Submission.GM.HBStatement) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ 1) →
      (∀ n, n ∉ Finset.Icc 1 M → c n = 0) →
      ∀ (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ C * T ^ ε * (M : ℝ) ^ η *
            ((R : ℝ) ^ 2 * (M : ℝ) + (R : ℝ) * (M : ℝ) ^ 2
              + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
  intro ε hε η hη
  obtain ⟨CHB, hCHBpos, hHB'⟩ := hHB ε hε
  obtain ⟨C0, hC0pos, hC0⟩ := dya_clog_bound η hη
  refine ⟨CHB * (4 * C0 ^ 2), by positivity, ?_⟩
  intro M hM T hT c hc hcsupp R t ht hsep
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hTeps : (0 : ℝ) < T ^ ε := Real.rpow_pos_of_pos hTpos ε
  have hT12 : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := (Real.rpow_pos_of_pos hTpos _).le
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hR54 : (0 : ℝ) ≤ (R : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hRnn _
  have hMη : (0 : ℝ) < (M : ℝ) ^ η := Real.rpow_pos_of_pos hMpos η
  set K : ℕ := Nat.clog 2 (M + 1) with hKdef
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hKle : (K : ℝ) ≤ C0 * (M : ℝ) ^ (η / 2) := by
    rw [hKdef]; exact hC0 M hM
  have hKs : (K : ℝ) ^ 2 ≤ C0 ^ 2 * (M : ℝ) ^ η := by
    have h2 : ((M : ℝ) ^ (η / 2)) ^ 2 = (M : ℝ) ^ η := by
      rw [← Real.rpow_natCast ((M : ℝ) ^ (η / 2)) 2]
      rw [← Real.rpow_mul hMpos.le]
      congr 1
      ring
    calc (K : ℝ) ^ 2 ≤ (C0 * (M : ℝ) ^ (η / 2)) ^ 2 := pow_le_pow_left₀ hK0 hKle 2
      _ = C0 ^ 2 * (M : ℝ) ^ η := by rw [mul_pow, h2]
  have hMlt : M < 2 ^ K := by
    rw [hKdef]
    have h := Nat.le_pow_clog (show 1 < 2 by norm_num) (M + 1)
    omega
  have hK2a : (K : ℝ) ^ 2 * ((M : ℝ) + 1) ≤ (2 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ)) := by
    have h1 : ((M : ℝ) + 1) ≤ 2 * (M : ℝ) := by linarith
    calc (K : ℝ) ^ 2 * ((M : ℝ) + 1) ≤ (C0 ^ 2 * (M : ℝ) ^ η) * (2 * (M : ℝ)) :=
          mul_le_mul hKs h1 (by positivity) (by positivity)
      _ = (2 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ)) := by ring
  have hK2b : (K : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2 ≤ (4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) ^ 2) := by
    have h1 : ((M : ℝ) + 1) ^ 2 ≤ (2 * (M : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc (K : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2 ≤ (C0 ^ 2 * (M : ℝ) ^ η) * (2 * (M : ℝ)) ^ 2 :=
          mul_le_mul hKs h1 (by positivity) (by positivity)
      _ = (4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) ^ 2) := by ring
  -- decomposition of the polynomial into blocks
  have hP : ∀ τ : ℝ,
      (∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * (τ : ℂ)))
        = ∑ k ∈ Finset.range K, dyaPoly M c k τ := by
    intro τ
    rw [sum_Icc_dyaBlk M K hMlt]
    exact Finset.sum_congr rfl (fun k _ => (dyaPoly_eq M c k τ).symm)
  -- Cauchy–Schwarz in the block index, for a fixed pair of frequencies
  have hCS : ∀ i j : Fin R,
      ‖∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2
        ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ‖dyaPoly M c k (t i - t j)‖ ^ 2 := by
    intro i j
    rw [hP (t i - t j)]
    have h1 : ‖∑ k ∈ Finset.range K, dyaPoly M c k (t i - t j)‖
        ≤ ∑ k ∈ Finset.range K, ‖dyaPoly M c k (t i - t j)‖ := norm_sum_le _ _
    have h2 : (∑ k ∈ Finset.range K, ‖dyaPoly M c k (t i - t j)‖) ^ 2
        ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ‖dyaPoly M c k (t i - t j)‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K) (fun _ : ℕ => (1 : ℝ))
        (fun k => ‖dyaPoly M c k (t i - t j)‖)
      have h3 : (∑ k ∈ Finset.range K, (1 : ℝ) ^ 2) = (K : ℝ) := by simp
      rw [h3] at h
      simpa using h
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have heq1 : (∑ p : Fin R × Fin R, (K : ℝ)
        * ∑ k ∈ Finset.range K, ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2)
      = (K : ℝ) * ∑ p : Fin R × Fin R,
        ∑ k ∈ Finset.range K, ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2 := by
    rw [← Finset.mul_sum]
  have heq2 : (∑ p : Fin R × Fin R, ∑ k ∈ Finset.range K,
        ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2)
      = ∑ k ∈ Finset.range K, ∑ p : Fin R × Fin R,
        ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2 :=
    Finset.sum_comm
  have hBk : ∀ k ∈ Finset.range K,
      (∑ p : Fin R × Fin R, ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2)
        ≤ CHB * T ^ ε * ((R : ℝ) ^ 2 * (dyaN M k : ℝ) + (R : ℝ) * (dyaN M k : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ)) := by
    intro k _
    have hb := hHB' (dyaN M k) (dyaN_pos M k) T hT (dyaC M c k)
      (fun n => dyaC_norm_le M c hc k n) R t ht hsep
    rw [← Finset.sum_product', Finset.univ_product_univ] at hb
    simpa only [dyaPoly] using hb
  have hprod : (∑ p : Fin R × Fin R,
        ‖∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * ((t p.1 - t p.2 : ℝ) : ℂ))‖ ^ 2)
      ≤ (K : ℝ) * CHB * T ^ ε *
        (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ) + (R : ℝ) * (dyaN M k : ℝ) ^ 2
          + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ))) := by
    have hstep1 : (∑ p : Fin R × Fin R,
          ‖∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * ((t p.1 - t p.2 : ℝ) : ℂ))‖ ^ 2)
        ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ∑ p : Fin R × Fin R,
            ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2 := by
      refine (Finset.sum_le_sum (fun p _ => hCS p.1 p.2)).trans (le_of_eq ?_)
      rw [heq1, heq2]
    calc (∑ p : Fin R × Fin R,
          ‖∑ n ∈ Finset.Icc 1 M, c n * (n : ℂ) ^ (Complex.I * ((t p.1 - t p.2 : ℝ) : ℂ))‖ ^ 2)
        ≤ (K : ℝ) * ∑ k ∈ Finset.range K, ∑ p : Fin R × Fin R,
            ‖dyaPoly M c k (t p.1 - t p.2)‖ ^ 2 := hstep1
      _ ≤ (K : ℝ) * ∑ k ∈ Finset.range K, (CHB * T ^ ε *
            ((R : ℝ) ^ 2 * (dyaN M k : ℝ) + (R : ℝ) * (dyaN M k : ℝ) ^ 2
              + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact Finset.sum_le_sum (fun k hk => hBk k hk)
      _ = (K : ℝ) * CHB * T ^ ε *
            (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ) + (R : ℝ) * (dyaN M k : ℝ) ^ 2
              + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ))) := by
          rw [← Finset.mul_sum]
          ring
  -- bounds for the block lengths
  have hS1 : (∑ k ∈ Finset.range K, (dyaN M k : ℝ)) ≤ (K : ℝ) * ((M : ℝ) + 1) := by
    calc ∑ k ∈ Finset.range K, (dyaN M k : ℝ) ≤ ∑ k ∈ Finset.range K, ((M : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro k _
          exact_mod_cast dyaN_le M k
      _ = (K : ℝ) * ((M : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hS2 : (∑ k ∈ Finset.range K, (dyaN M k : ℝ) ^ 2) ≤ (K : ℝ) * ((M : ℝ) + 1) ^ 2 := by
    calc ∑ k ∈ Finset.range K, (dyaN M k : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.range K, ((M : ℝ) + 1) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          have h : (dyaN M k : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast dyaN_le M k
          exact pow_le_pow_left₀ (by positivity) h 2
      _ = (K : ℝ) * ((M : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hZ : (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ)
        + (R : ℝ) * (dyaN M k : ℝ) ^ 2
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ)))
      ≤ (R : ℝ) ^ 2 * ((K : ℝ) * ((M : ℝ) + 1)) + (R : ℝ) * ((K : ℝ) * ((M : ℝ) + 1) ^ 2)
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((K : ℝ) * ((M : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left hS1 (sq_nonneg (R : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hS2 hRnn
    have h3 := mul_le_mul_of_nonneg_left hS1 (mul_nonneg hR54 hT12)
    linarith
  -- the final arithmetic
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine hprod.trans ?_
  have hZ2 : (K : ℝ) * (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ)
        + (R : ℝ) * (dyaN M k : ℝ) ^ 2
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ)))
      ≤ (R : ℝ) ^ 2 * ((K : ℝ) ^ 2 * ((M : ℝ) + 1))
        + (R : ℝ) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hZ hK0
    nlinarith [h]
  have hW : (R : ℝ) ^ 2 * ((K : ℝ) ^ 2 * ((M : ℝ) + 1))
        + (R : ℝ) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1))
      ≤ (4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) * (R : ℝ) ^ 2
          + (M : ℝ) ^ η * (M : ℝ) ^ 2 * (R : ℝ)
          + (M : ℝ) ^ η * (M : ℝ) * ((R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2))) := by
    have h1 : (R : ℝ) ^ 2 * ((K : ℝ) ^ 2 * ((M : ℝ) + 1))
        ≤ (R : ℝ) ^ 2 * ((2 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hK2a (sq_nonneg (R : ℝ))
    have h2 : (R : ℝ) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)
        ≤ (R : ℝ) * ((4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hK2b hRnn
    have h3 : (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((K : ℝ) ^ 2 * ((M : ℝ) + 1))
        ≤ (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)
            * ((2 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hK2a (mul_nonneg hR54 hT12)
    have e1 : (0 : ℝ) ≤ C0 ^ 2 * (M : ℝ) ^ η * (M : ℝ) * (R : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C0) hMη.le) hMpos.le) (sq_nonneg (R : ℝ))
    have e2 : (0 : ℝ) ≤ C0 ^ 2 * (M : ℝ) ^ η * (M : ℝ) ^ 2 * (R : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C0) hMη.le) (pow_nonneg hMpos.le 2)) hRnn
    have e3 : (0 : ℝ) ≤ C0 ^ 2 * (M : ℝ) ^ η * (M : ℝ)
        * ((R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C0) hMη.le) hMpos.le) (mul_nonneg hR54 hT12)
    nlinarith [h1, h2, h3, e1, e2, e3]
  have hW2 : (4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) * (R : ℝ) ^ 2
          + (M : ℝ) ^ η * (M : ℝ) ^ 2 * (R : ℝ)
          + (M : ℝ) ^ η * (M : ℝ) * ((R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)))
      = (4 * C0 ^ 2) * (M : ℝ) ^ η * ((R : ℝ) ^ 2 * (M : ℝ) + (R : ℝ) * (M : ℝ) ^ 2
          + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
    ring
  calc (K : ℝ) * CHB * T ^ ε * (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ)
        + (R : ℝ) * (dyaN M k : ℝ) ^ 2
        + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ)))
      = CHB * T ^ ε * ((K : ℝ) * (∑ k ∈ Finset.range K, ((R : ℝ) ^ 2 * (dyaN M k : ℝ)
          + (R : ℝ) * (dyaN M k : ℝ) ^ 2
          + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (dyaN M k : ℝ)))) := by
        ring
    _ ≤ CHB * T ^ ε * ((4 * C0 ^ 2) * ((M : ℝ) ^ η * (M : ℝ) * (R : ℝ) ^ 2
          + (M : ℝ) ^ η * (M : ℝ) ^ 2 * (R : ℝ)
          + (M : ℝ) ^ η * (M : ℝ) * ((R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)))) :=
        mul_le_mul_of_nonneg_left (hZ2.trans hW)
          (mul_nonneg hCHBpos.le hTeps.le)
    _ = CHB * (4 * C0 ^ 2) * T ^ ε * (M : ℝ) ^ η *
          ((R : ℝ) ^ 2 * (M : ℝ) + (R : ℝ) * (M : ℝ) ^ 2
            + (R : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
        rw [hW2]
        ring

end Work.GM.S2
