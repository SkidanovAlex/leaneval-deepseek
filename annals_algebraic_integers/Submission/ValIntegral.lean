import Mathlib
import Submission.MonicDual
/-!
# Values `D(α_i)` of the dual polynomial are algebraic integers

For an integer polynomial `Q` of degree `n` with leading coefficient `c = Q.leadingCoeff`
(factorisation `Qc = C(c) · ∏_i (X − C(α_i))` over `ℂ`), and for
`D := Dpoly Q d = Σ_j C(d_j)·(rq Q j)` (the "divided-difference" combination), each value
`eval (α_i) (D.map φ)` is an algebraic integer over `ℤ`.

## Mathematical idea (no valuations / no DVR theory needed)

The crucial structural fact is that multiplication by `D` preserves the lattice
`Λ = ⟨1, X, …, X^(n−1)⟩_ℤ` inside `ℚ[X]/(Q)`.  Indeed `rq Q j` satisfies the
SYNTHETIC-DIVISION identity

    rq Q j · X^(j+1)  =  Q − (prefix Q j)          where  prefix Q j := Σ_{t ≤ j} q_t·X^t

so for each `k < n` one can reduce `D · X^k` modulo `Q` to a polynomial
`g_k ∈ ℤ[X]` of degree `< n` (reducing each term `rq Q j · X^k` for `j < k`
via the identity, and leaving the terms with `j ≥ k` untouched).  Concretely
`g_k := Σ_j d_j·(term_j)` where term_j = `rq Q j·X^k` if `j.val ≥ k` and
`term_j = −X^(k−j−1)·(prefix Q j.val)` if `j.val < k`; then
`D·X^k − g_k = Q·h_k` for `h_k := Σ_{j.val < k} d_j·X^(k−j.val−1)`.

Evaluating at the root `α := α i` (where `Q(α) = 0`) gives
`eval(α)(D)·α^k = eval(α)(g_k) ∈ Λ'` where `Λ' := span_ℤ {α^0,…,α^(n−1)} ⊂ ℂ`.
Hence multiplication by `x := eval(α)(D)` maps the finitely generated `ℤ`-submodule
`Λ'` of `ℂ` (viewed as a `ℂ`-module over itself) into itself.  Since `1 ∈ Λ'`,
the module criterion `isIntegral_of_smul_mem_submodule` yields `IsIntegral ℤ x`.

## What is provided
`Submission.MonicDual` supplies `qic`, `rq`, `Dpoly`, `Qc` and assorted lemmas
(`coeff_fintype_sum`, `rq_eval`, …).  The statement below is all that is needed.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.ValIntegral

open Submission.MonicDual

/-- `rq Q j · X^(j+1)` is the "high part" of `Q` (terms of degree `> j`); this is the
complement `Q − (rq Q j)·X^(j+1)`, of degree at most `j`. -/
noncomputable def restQ (Q : Polynomial ℤ) (j : ℕ) : Polynomial ℤ :=
  Q - (rq Q j) * Polynomial.X ^ (j + 1)

lemma rq_mul_Xpow_add_rest (Q : Polynomial ℤ) (j : ℕ) :
    (rq Q j) * Polynomial.X ^ (j + 1) + restQ Q j = Q := by
  rw [restQ]
  ring

lemma rq_mul_Xpow_eq_sub_rest (Q : Polynomial ℤ) (j : ℕ) :
    (rq Q j) * Polynomial.X ^ (j + 1) = Q - restQ Q j := by
  rw [restQ]
  ring

lemma rq_mul_Xpow_eq_sum (Q : Polynomial ℤ) (j : ℕ) :
    (rq Q j) * Polynomial.X ^ (j + 1) =
      ∑ t ∈ Finset.Icc (j + 1) Q.natDegree, Polynomial.C (Q.coeff t) * Polynomial.X ^ t := by
  rw [rq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have ht1 : j + 1 ≤ t := (Finset.mem_Icc.mp ht).1
  calc
    (Polynomial.C (Q.coeff t) * Polynomial.X ^ (t - (j + 1))) * Polynomial.X ^ (j + 1)
        = Polynomial.C (Q.coeff t) * (Polynomial.X ^ (t - (j + 1)) * Polynomial.X ^ (j + 1)) := by
            rw [mul_assoc]
    _ = Polynomial.C (Q.coeff t) * Polynomial.X ^ t := by
            rw [← pow_add]
            congr 1
            rw [Nat.sub_add_cancel ht1]

lemma coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] (s : Finset ℕ) (q : ℕ → R) (m : ℕ) :
    (∑ t ∈ s, Polynomial.C (q t) * Polynomial.X ^ t).coeff m =
      if m ∈ s then q m else 0 := by
  classical
  by_cases hms : m ∈ s
  · rw [if_pos hms]
    rw [coeff_finset_sum]
    calc
      (∑ t ∈ s, (Polynomial.C (q t) * Polynomial.X ^ t).coeff m)
          = (Polynomial.C (q m) * Polynomial.X ^ m).coeff m := by
            exact Finset.sum_eq_single (s := s)
              (f := fun t : ℕ => (Polynomial.C (q t) * Polynomial.X ^ t).coeff m) (a := m)
              (by
                intro b hb hbne
                have hmb : m ≠ b := Ne.symm hbne
                simp [Polynomial.coeff_X_pow, hmb])
              (fun hnot => (hnot hms).elim)
      _ = q m := by
            simp [Polynomial.coeff_X_pow]
  · rw [if_neg hms]
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro b hb
    have hmb : m ≠ b := by
      intro hmb
      exact hms (by simpa [hmb])
    simp [Polynomial.coeff_X_pow, hmb]

lemma coeff_rq_mul_Xpow (Q : Polynomial ℤ) (j m : ℕ) :
    ((rq Q j) * Polynomial.X ^ (j + 1)).coeff m =
      if j + 1 ≤ m ∧ m ≤ Q.natDegree then Q.coeff m else 0 := by
  rw [rq_mul_Xpow_eq_sum]
  rw [coeff_sum_C_mul_X_pow (s := Finset.Icc (j + 1) Q.natDegree) (q := Q.coeff) (m := m)]
  congr 1
  rw [Finset.mem_Icc]

lemma natDegree_restQ_le (Q : Polynomial ℤ) (j : ℕ) : (restQ Q j).natDegree ≤ j := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [restQ, Polynomial.coeff_sub, coeff_rq_mul_Xpow]
  by_cases hmb : m ≤ Q.natDegree
  · have hle : j + 1 ≤ m := by omega
    have h1 : (if j + 1 ≤ m ∧ m ≤ Q.natDegree then Q.coeff m else 0) = Q.coeff m := by
      rw [if_pos (by exact ⟨hle, hmb⟩)]
    rw [h1]
    ring
  · have hmq : Q.coeff m = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m)
    have h1 : (if j + 1 ≤ m ∧ m ≤ Q.natDegree then Q.coeff m else 0) = 0 := by
      rw [if_neg]
      intro h; exact hmb h.2
    rw [h1]
    rw [hmq]
    ring

/-- degree of `rq Q j` is at most `natDegree Q - 1 - j` -/
lemma natDegree_rq_le (Q : Polynomial ℤ) (j : ℕ) :
    (rq Q j).natDegree ≤ Q.natDegree - 1 - j := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  exact rq_coeff_eq_zero Q (j := j) (m := m) hm

lemma X_pow_eq_mul_X_pow {R : Type*} [Semiring R] (j kk : ℕ) (h : j < kk) :
    (Polynomial.X : Polynomial R) ^ kk
      = (Polynomial.X : Polynomial R) ^ (j + 1) * (Polynomial.X : Polynomial R) ^ (kk - j - 1) := by
  rw [← pow_add]
  congr 1
  omega

lemma rq_Xpow_eq_rest_mul (Q : Polynomial ℤ) {j kk : ℕ} (h : j < kk) :
    (rq Q j) * Polynomial.X ^ kk = (Q - restQ Q j) * Polynomial.X ^ (kk - j - 1) := by
  calc
    (rq Q j) * Polynomial.X ^ kk
        = (rq Q j) * (Polynomial.X ^ (j + 1) * Polynomial.X ^ (kk - j - 1)) := by
            rw [X_pow_eq_mul_X_pow j kk h]
    _ = ((rq Q j) * Polynomial.X ^ (j + 1)) * Polynomial.X ^ (kk - j - 1) := by
            rw [mul_assoc]
    _ = (Q - restQ Q j) * Polynomial.X ^ (kk - j - 1) := by
            rw [rq_mul_Xpow_eq_sub_rest]

lemma C_mul_rq_Xpow_eq (Q : Polynomial ℤ) (d : ℤ) {j kk : ℕ} (h : j < kk) :
    Polynomial.C d * (rq Q j) * Polynomial.X ^ kk
      = Polynomial.C d * Q * Polynomial.X ^ (kk - j - 1)
          - Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1) := by
  calc
    Polynomial.C d * (rq Q j) * Polynomial.X ^ kk
        = Polynomial.C d * ((rq Q j) * Polynomial.X ^ kk) := by rw [mul_assoc]
    _ = Polynomial.C d * ((Q - restQ Q j) * Polynomial.X ^ (kk - j - 1)) := by
            rw [rq_Xpow_eq_rest_mul Q h]
    _ = (Polynomial.C d * (Q - restQ Q j)) * Polynomial.X ^ (kk - j - 1) := by
            rw [mul_assoc]
    _ = Polynomial.C d * Q * Polynomial.X ^ (kk - j - 1)
          - Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1) := by
            ring

lemma X_pow_map_eval (α : ℂ) (kk : ℕ) :
    eval α ((Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) = α ^ kk := by
  rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X]

/-- evaluating `c·P·X^p` after mapping to `ℂ` -/
lemma eval_map_C_mul_X_pow (α : ℂ) (c : ℤ) (P : Polynomial ℤ) (p : ℕ) :
    eval α ((Polynomial.C c * P * Polynomial.X ^ p).map (algebraMap ℤ ℂ))
      = (c : ℂ) * eval α (P.map (algebraMap ℤ ℂ)) * (α ^ p) := by
  rw [Polynomial.map_mul, Polynomial.map_mul]
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.map_C, Polynomial.eval_C]
  rw [X_pow_map_eval α p]
  simp [mul_assoc]

/-- evaluating `c·X^p` after mapping to `ℂ` -/
lemma eval_map_C_mul_X_pow_one (α : ℂ) (c : ℤ) (p : ℕ) :
    eval α ((Polynomial.C c * Polynomial.X ^ p).map (algebraMap ℤ ℂ)) = (c : ℂ) * (α ^ p) := by
  simpa [mul_one] using (eval_map_C_mul_X_pow (α := α) (c := c) (P := 1) (p := p))

/-- evaluating the `Q`-term: vanishes at a root of `Q` -/
lemma eval_map_C_mul_Q_Xpow_zero (Q : Polynomial ℤ) (α : ℂ)
    (hroot : eval α (Q.map (algebraMap ℤ ℂ)) = 0) (c : ℤ) (p : ℕ) :
    eval α ((Polynomial.C c * Q * Polynomial.X ^ p).map (algebraMap ℤ ℂ)) = 0 := by
  rw [eval_map_C_mul_X_pow α c Q p]
  rw [hroot]
  ring

/-- case B value identity: at a root `α` of `Q`, `d·rq Q j·α^kk = eval` of the low part -/
lemma eval_C_rq_Xpow_eq_neg_rest (Q : Polynomial ℤ) (α : ℂ)
    (hroot : eval α (Q.map (algebraMap ℤ ℂ)) = 0) (d : ℤ) {j kk : ℕ} (h : j < kk) :
    eval α ((Polynomial.C d * (rq Q j) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))
      = eval α ((Polynomial.C (-d) * (restQ Q j)
            * Polynomial.X ^ (kk - j - 1)).map (algebraMap ℤ ℂ)) := by
  calc
    eval α ((Polynomial.C d * (rq Q j) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))
        = eval α (((Polynomial.C d * Q * Polynomial.X ^ (kk - j - 1))
              - (Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1))).map (algebraMap ℤ ℂ)) := by
            congr 1
            rw [C_mul_rq_Xpow_eq Q d h]
    _ = eval α ((Polynomial.C d * Q * Polynomial.X ^ (kk - j - 1)).map (algebraMap ℤ ℂ))
          - eval α ((Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1)).map (algebraMap ℤ ℂ)) := by
            rw [Polynomial.map_sub, Polynomial.eval_sub]
    _ = 0 - eval α ((Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1)).map (algebraMap ℤ ℂ)) := by
            rw [eval_map_C_mul_Q_Xpow_zero Q α hroot d (kk - j - 1)]
    _ = eval α ((Polynomial.C (-d) * (restQ Q j)
            * Polynomial.X ^ (kk - j - 1)).map (algebraMap ℤ ℂ)) := by
            rw [eval_map_C_mul_X_pow α d (restQ Q j) (kk - j - 1)]
            rw [eval_map_C_mul_X_pow α (-d) (restQ Q j) (kk - j - 1)]
            simp [mul_assoc, mul_comm, mul_left_comm]

/-- a polynomial of degree `< N` is its own truncation at `N` -/
lemma poly_eq_sum_range {R : Type*} [Semiring R] (p : R[X]) {N : ℕ} (hp : p.natDegree < N) :
    p = ∑ t ∈ Finset.range N, Polynomial.C (p.coeff t) * Polynomial.X ^ t := by
  classical
  ext m
  rw [coeff_sum_C_mul_X_pow (s := Finset.range N) (q := p.coeff) (m := m)]
  by_cases hm : m < N
  · rw [if_pos (Finset.mem_range.mpr hm)]
  · rw [if_neg (by exact fun hmm => hm (Finset.mem_range.mp hmm))]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m)

/-- membership of the evaluation of a degree `< n` integer polynomial in the span
of `1, α, …, α^(n-1)` -/
lemma eval_degree_lt_mem {n : ℕ} (hn : 1 ≤ n) (α : ℂ) (p : Polynomial ℤ)
    (hp : p.natDegree < n) :
    eval α (p.map (algebraMap ℤ ℂ)) ∈
      Submodule.span ℤ (Set.range (fun k : Fin n => α ^ k.val)) := by
  classical
  have hp_eq : p = ∑ t ∈ Finset.range n, Polynomial.C (p.coeff t) * Polynomial.X ^ t :=
    poly_eq_sum_range p hp
  rw [hp_eq]
  rw [polynomial_map_finset_sum (algebraMap ℤ ℂ) (s := Finset.range n)]
  rw [Polynomial.eval_finsetSum]
  apply Submodule.sum_mem
  intro t ht
  have ht' : t < n := Finset.mem_range.mp ht
  rw [eval_map_C_mul_X_pow_one α (p.coeff t) t]
  have hgen : α ^ t ∈ Submodule.span ℤ (Set.range (fun k : Fin n => α ^ k.val)) := by
    apply Submodule.subset_span
    exact ⟨⟨t, ht'⟩, rfl⟩
  have hsmul : (p.coeff t) • (α ^ t) ∈
      Submodule.span ℤ (Set.range (fun k : Fin n => α ^ k.val)) := by
    exact Submodule.smul_mem _ (p.coeff t) hgen
  simpa [Algebra.smul_def] using hsmul

/-- Case A degree bound: `d·rq Q j·X^kk` has degree `< n` when `kk ≤ j < n = natDegree Q` -/
lemma natDegree_C_mul_rq_mul_Xpow_lt {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (d : ℤ) {j kk : ℕ} (hj : j < n) (hkkj : kk ≤ j) :
    (Polynomial.C d * (rq Q j) * Polynomial.X ^ kk).natDegree < n := by
  have hn1 : 1 ≤ n := by omega
  have hC : (Polynomial.C d).natDegree = 0 := Polynomial.natDegree_C d
  have hrq : (rq Q j).natDegree ≤ n - 1 - j := by
    have h0 := natDegree_rq_le Q j
    rwa [hQn] at h0
  calc
    (Polynomial.C d * (rq Q j) * Polynomial.X ^ kk).natDegree
        ≤ (Polynomial.C d * (rq Q j)).natDegree + (Polynomial.X ^ kk).natDegree :=
            Polynomial.natDegree_mul_le
    _ ≤ (Polynomial.C d * (rq Q j)).natDegree + kk := by
          gcongr
          exact Polynomial.natDegree_X_pow_le kk
    _ ≤ ((Polynomial.C d).natDegree + (rq Q j).natDegree) + kk := by
          gcongr
          exact Polynomial.natDegree_mul_le
    _ = (rq Q j).natDegree + kk := by
          rw [hC]
          simp
    _ ≤ (n - 1 - j) + kk := by omega
    _ ≤ n - 1 := by omega
    _ < n := by omega

/-- Case B degree bound: `d·(restQ Q j)·X^(kk-j-1)` has degree `< n` when `j < kk < n` -/
lemma natDegree_C_mul_rest_mul_Xpow_lt {n : ℕ} (Q : Polynomial ℤ) (d : ℤ) {j kk : ℕ}
    (hjkk : j < kk) (hkk : kk < n) :
    (Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1)).natDegree < n := by
  have hn1 : 1 ≤ n := by omega
  have hC : (Polynomial.C d).natDegree = 0 := Polynomial.natDegree_C d
  have hr : (restQ Q j).natDegree ≤ j := natDegree_restQ_le Q j
  calc
    (Polynomial.C d * (restQ Q j) * Polynomial.X ^ (kk - j - 1)).natDegree
        ≤ (Polynomial.C d * (restQ Q j)).natDegree + (Polynomial.X ^ (kk - j - 1)).natDegree :=
            Polynomial.natDegree_mul_le
    _ ≤ (Polynomial.C d * (restQ Q j)).natDegree + (kk - j - 1) := by
          gcongr
          exact Polynomial.natDegree_X_pow_le (kk - j - 1)
    _ ≤ ((Polynomial.C d).natDegree + (restQ Q j).natDegree) + (kk - j - 1) := by
          gcongr
          exact Polynomial.natDegree_mul_le
    _ = (restQ Q j).natDegree + (kk - j - 1) := by
          rw [hC]
          simp
    _ ≤ j + (kk - j - 1) := by omega
    _ < n := by omega

/-- The value `D(α_i)` with `D = Dpoly Q d` is an algebraic integer, where `α` is
the list of the (distinct) complex roots from the factorisation of `Q`. -/
theorem val_integral {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) (hQn : Q.natDegree = n)
    (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    IsIntegral ℤ (eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ))) := by
  classical
  by_cases hn0 : n = 0
  · exfalso
    have hlt : i.val < n := i.isLt
    have hnz : n = 0 := hn0
    omega
  · have hn : 1 ≤ n := by omega
    let x : ℂ := eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ))
    let N : Submodule ℤ ℂ := Submodule.span ℤ (Set.range (fun k : Fin n => (α i) ^ k.val))
    have hroot : eval (α i) (Q.map (algebraMap ℤ ℂ)) = 0 := by
      rw [hfac]
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      have hprod : eval (α i) (∏ k : Fin n, (Polynomial.X - Polynomial.C (α k))) = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin n)))
          (f := fun k : Fin n => eval (α i) (Polynomial.X - Polynomial.C (α k)))
          (i := i) (by simp) (by simp)
      rw [hprod]
      simp
    have hN : N ≠ ⊥ := by
      intro hbot
      have h1 : (1 : ℂ) ∈ N := by
        dsimp [N]
        apply Submodule.subset_span
        refine ⟨⟨0, hn⟩, ?_⟩
        simp
      have hb : (1 : ℂ) ∈ (⊥ : Submodule ℤ ℂ) := by
        simpa [N, hbot] using h1
      have hone : (1 : ℂ) = 0 := by simpa using hb
      exact one_ne_zero (α := ℂ) hone
    have hNfg : N.FG := by
      rw [Submodule.fg_def]
      exact ⟨Set.range (fun k : Fin n => (α i) ^ k.val), Set.finite_range _, rfl⟩
    have hmem : ∀ {p : Polynomial ℤ}, p.natDegree < n → eval (α i) (p.map (algebraMap ℤ ℂ)) ∈ N := by
      intro p hp
      exact eval_degree_lt_mem hn (α i) p hp
    have hterm : ∀ (kk : ℕ), kk < n → ∀ j : Fin n,
        eval (α i) ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) ∈ N := by
      intro kk hkk j
      by_cases hcase : kk ≤ j.val
      · exact hmem (p := Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk)
          (natDegree_C_mul_rq_mul_Xpow_lt Q hQn (d j) (by simpa [hQn] using j.isLt) hcase)
      · have hjkk : j.val < kk := by omega
        have hval : eval (α i) ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))
            = eval (α i) ((Polynomial.C (-d j) * restQ Q (j.val)
                * Polynomial.X ^ (kk - j.val - 1)).map (algebraMap ℤ ℂ)) := by
              exact eval_C_rq_Xpow_eq_neg_rest Q (α i) hroot (d j) hjkk
        rw [hval]
        exact hmem (p := Polynomial.C (-d j) * restQ Q (j.val) * Polynomial.X ^ (kk - j.val - 1))
          (natDegree_C_mul_rest_mul_Xpow_lt Q (-d j) hjkk hkk)
    have hclose : ∀ k : Fin n, x • (α i) ^ k.val ∈ N := by
      intro k
      let kk := k.val
      have hkk : kk < n := k.isLt
      have hD : (Dpoly Q d) * Polynomial.X ^ kk
          = ∑ j : Fin n, Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk := by
            rw [Dpoly]
            rw [Finset.sum_mul]
      have hxval : x * (α i) ^ kk =
          ∑ j : Fin n, eval (α i)
              ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) := by
            dsimp [x]
            have h1 : eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)) * (α i) ^ kk
                = eval (α i) (((Dpoly Q d) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) := by
                  rw [Polynomial.map_mul, Polynomial.eval_mul, X_pow_map_eval (α i) kk]
            have h2 : eval (α i) (((Dpoly Q d) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))
                = eval (α i) ((∑ j : Fin n,
                      Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) := by
                  rw [hD]
            have h3 : eval (α i) ((∑ j : Fin n,
                      Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))
                = ∑ j : Fin n, eval (α i)
                    ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)) := by
                  rw [Polynomial.map_sum]
                  rw [Polynomial.eval_finsetSum]
            exact h1.trans (h2.trans h3)
      have hsum : (∑ j : Fin n,
            eval (α i) ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ))) ∈ N := by
            exact N.sum_mem (t := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n =>
                eval (α i) ((Polynomial.C (d j) * rq Q (j.val) * Polynomial.X ^ kk).map (algebraMap ℤ ℂ)))
              (by intro j hj; exact hterm kk hkk j)
      have hxsmul : x • (α i) ^ kk = x * (α i) ^ kk := by simp [smul_eq_mul]
      rw [hxsmul, hxval]
      exact hsum
    have hx : ∀ y ∈ N, x • y ∈ N := by
      intro y hy
      refine Submodule.span_induction (s := (Set.range (fun k : Fin n => (α i) ^ k.val)))
        (p := fun y _ => x • y ∈ N) ?mem ?zero ?add ?smul hy
      · intro y hyy
        rcases hyy with ⟨k, rfl⟩
        exact hclose k
      · simp [N]
      · intro a b _ _ hpa hpb
        rw [smul_add]
        exact N.add_mem hpa hpb
      · intro z a _ hpa
        have hz : (z : ℂ) • (x • a) ∈ N := by
          simpa [smul_eq_mul, mul_assoc, mul_comm] using (N.smul_mem z hpa)
        convert hz using 1
        simp only [smul_eq_mul]
        ring
    change IsIntegral ℤ x
    exact isIntegral_of_smul_mem_submodule (R := ℤ) (A := ℂ) (M := ℂ) N hN hNfg x hx

end Submission.ValIntegral
