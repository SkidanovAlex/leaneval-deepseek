import Submission.ZagierHoffmanProof.Rationality

/-!
# Dac's `lem: KuanLin` — the σ-linear equation `εδ = δ^{(1)}(t-θ)^m + F`

This is the algebraic heart of Dac §4.3 (`thm: trans ACMPL`): if `m ≥ 1`, `ε ∈ F_q^×` and

  `ε·δ^{(1)} = δ·(t - θ^q)^m + F`,   with `F ∈ F_q[θ][t]`,

then `δ ∈ F_q[θ][t]` — i.e. every `t`-coefficient of `δ` lies in the level-`0` Anderson ring
`ambA F 0 = F_q[θ]`.

The proof is the paper's coefficient recursion: writing `δ = ∑_k a_k t^k` and reading the
coefficient of `t^{k+m}` in the equation gives

  `a_k = ε·a_{k+m}^q - ∑_{i>k} a_i·[t^{k+m-i}](t-θ^q)^m - [t^{k+m}]F`,

which determines `a_k` from the coefficients of higher degree; descending induction on `k` gives
the claim (the hypothesis `m ≥ 1` is essential: for `m = 0` the equation only says
`ε a_k^q - a_k = F_k`, which need not be solvable in `F_q[θ]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Finset Matrix
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. Elementary memberships -/

lemma ambF_subset_ambA_zero {x : Ambient F} (hx : x ∈ ambF F) : x ∈ ambA F 0 := by
  obtain ⟨c, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hx
  exact (mem_ambA_iff F 0 _).mpr ⟨Polynomial.C c, by rw [Polynomial.eval₂_C]; rfl⟩

lemma ambTheta_mem_ambA_zero : ambTheta F ∈ ambA F 0 := by
  rw [← ambThetaNu_zero F]
  simpa using ambThetaNu_pow_mem F 0 1

lemma coeff_X_sub_C_pow_eq_zero {c : Ambient F} {i m : ℕ} (h : m < i) :
    ((Polynomial.X - Polynomial.C c) ^ m).coeff i = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  exact h

lemma coeff_X_sub_C_pow_self (c : Ambient F) (m : ℕ) :
    ((Polynomial.X - Polynomial.C c) ^ m).coeff m = 1 := by
  have hmon : ((Polynomial.X - Polynomial.C c) ^ m).Monic :=
    (Polynomial.monic_X_sub_C c).pow m
  rw [← hmon.coeff_natDegree]
  congr 1
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

lemma coeff_polyTwist_one (δ : Polynomial (Ambient F)) (j : ℕ) :
    (polyTwist (q := Nat.card F) 1 δ).coeff j = (δ.coeff j) ^ Nat.card F := by
  rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply, pow_one]

/-! ## §2. `lem: KuanLin` -/

/-- **Dac's `lem: KuanLin`** (in the form used in §4.3, with `m ≥ 1`). -/
theorem coeff_mem_ambA_zero_of_kuanLin {m : ℕ} (hm : 1 ≤ m) {ε : Ambient F}
    (hε : ε ∈ ambF F) {δ Fp : Polynomial (Ambient F)}
    (hFp : ∀ j, Fp.coeff j ∈ ambA F 0)
    (h : Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ
      = δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m + Fp) :
    ∀ k, δ.coeff k ∈ ambA F 0 := by
  classical
  have hεA : ε ∈ ambA F 0 := ambF_subset_ambA_zero hε
  have hcA : (ambTheta F) ^ Nat.card F ∈ ambA F 0 :=
    ambA_pow_mem F 0 ambTheta_mem_ambA_zero (Nat.card F)
  set Q : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)
    with hQ
  have hQmem : ∀ i, (Q ^ m).coeff i ∈ ambA F 0 := by
    intro i; rw [hQ]; exact coeff_X_sub_C_pow_mem hcA m i
  have hQzero : ∀ i, m < i → (Q ^ m).coeff i = 0 := by
    intro i hi; rw [hQ]; exact coeff_X_sub_C_pow_eq_zero hi
  have hQm : (Q ^ m).coeff m = 1 := by rw [hQ]; exact coeff_X_sub_C_pow_self _ m
  have hzero_pow : (0 : Ambient F) ^ Nat.card F = 0 :=
    zero_pow (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  -- the coefficient recursion
  have hrec : ∀ k, k ≤ δ.natDegree →
      (∀ i, k < i → i ≤ δ.natDegree → δ.coeff i ∈ ambA F 0) →
      δ.coeff k ∈ ambA F 0 := by
    intro k hk ih
    have hcoeff := congrArg (fun p : Polynomial (Ambient F) => p.coeff (k + m)) h
    rw [Polynomial.coeff_C_mul, coeff_polyTwist_one, Polynomial.coeff_add,
      Polynomial.coeff_mul] at hcoeff
    have hmem : (k, m) ∈ HasAntidiagonal.antidiagonal (k + m) := by
      rw [HasAntidiagonal.mem_antidiagonal]
    have hsum := Finset.sum_erase_add (HasAntidiagonal.antidiagonal (k + m))
      (fun x : ℕ × ℕ => δ.coeff x.1 * (Q ^ m).coeff x.2) hmem
    rw [hQm, mul_one] at hsum
    rw [← hsum] at hcoeff
    have hgoal : δ.coeff k = ε * (δ.coeff (k + m)) ^ Nat.card F
        - (∑ x ∈ (HasAntidiagonal.antidiagonal (k + m)).erase (k, m),
            δ.coeff x.1 * (Q ^ m).coeff x.2) - Fp.coeff (k + m) := by
      linear_combination -hcoeff
    rw [hgoal]
    refine ambA_sub_mem F (ambA_sub_mem F (ambA_mul_mem F hεA ?_) ?_) (hFp (k + m))
    · by_cases hj : k + m ≤ δ.natDegree
      · exact ambA_pow_card_mem F (ih (k + m) (by omega) hj)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : δ.natDegree < k + m),
          hzero_pow]
        exact (ambASub F 0).zero_mem
    · refine ambA_sum_mem F fun x hx => ?_
      have hxs : x.1 + x.2 = k + m :=
        HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase hx)
      have hxne : x ≠ (k, m) := Finset.ne_of_mem_erase hx
      by_cases hxm : x.2 ≤ m
      · have hxk : x.1 ≠ k := by
          rintro rfl
          exact hxne (Prod.ext rfl (by omega))
        have h1 : δ.coeff x.1 ∈ ambA F 0 := by
          by_cases hxi : x.1 ≤ δ.natDegree
          · exact ih x.1 (by omega) hxi
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : δ.natDegree < x.1)]
            exact (ambASub F 0).zero_mem
        exact ambA_mul_mem F h1 (hQmem x.2)
      · rw [hQzero x.2 (by omega), mul_zero]
        exact (ambASub F 0).zero_mem
  -- descending induction
  have hmain : (fun k => ∀ i, k ≤ i → i ≤ δ.natDegree → δ.coeff i ∈ ambA F 0) 0 :=
    Nat.decreasingInduction'
      (P := fun k => ∀ i, k ≤ i → i ≤ δ.natDegree → δ.coeff i ∈ ambA F 0)
      (m := 0) (n := δ.natDegree + 1)
      (fun k _ _ hP1 i hi hin => by
        rcases eq_or_lt_of_le hi with hik | hik
        · subst hik
          exact hrec k (by omega) (fun j hj hjn => hP1 j (by omega) hjn)
        · exact hP1 i (by omega) hin)
      (Nat.zero_le _) (fun i hi _ => absurd (by omega : False) not_false)
  intro k
  by_cases hk : k ≤ δ.natDegree
  · exact hmain k (Nat.zero_le _) hk
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact (ambASub F 0).zero_mem

end ZagierHoffmanPositiveChar
