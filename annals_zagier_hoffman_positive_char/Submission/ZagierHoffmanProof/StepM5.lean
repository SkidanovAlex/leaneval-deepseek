import Submission.ZagierHoffmanProof.StepM4
import Submission.ZagierHoffmanProof.ThakurDeg2
import Submission.ZagierHoffmanProof.PowerSum
import Submission.ZagierHoffmanProof.StepK6

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M5: the level recursion of the power sums (Thakur §3.2)

The depth-one power sums `S_d(k) = ∑_{a monic, deg a = d} a^{-k}` satisfy the level
recursion

  `S_{d+1}(k) = − ∑_{j ≥ 1, (q−1) ∣ j} C(−k, j) t^{−k−j} S_d(k+j)`

(Thakur, *Power sums with applications to multizeta values ...*, §3.2), obtained by
expanding `(tn+θ)^{-k} = (tn)^{-k}(1+θ/(tn))^{-k}` binomially and summing over `θ ∈ F`.

Here we only need the *truncated* form: the expansion cut at `N`, together with the
explicit bound on the remainder produced by the engine `trunc_expansion` of Step M2.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Coes

/-- The completion coercion is multiplicative on `RatFunc F`. -/
lemma coe_rat_mul (a b : RatFunc F) :
    ((a * b : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (a : RatFunc.CompletionAtInfty F) * (b : RatFunc.CompletionAtInfty F) := by
  rw [rat_cast_eq_algebraMap F (a * b), rat_cast_eq_algebraMap F a, rat_cast_eq_algebraMap F b,
    map_mul]

/-- The composite coercion `F[X] → K∞` is multiplicative. -/
lemma coe_poly_mul (p q : F[X]) :
    (((p * q : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (((p : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        (((q : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  rw [show (((p * q : F[X]) : RatFunc F)) =
      (((p : F[X]) : RatFunc F) * ((q : F[X]) : RatFunc F)) from by
    rw [poly_cast_eq_algebraMap F (p * q), poly_cast_eq_algebraMap F p,
      poly_cast_eq_algebraMap F q, map_mul]]
  exact coe_rat_mul F _ _

/-- The composite coercion `F[X] → K∞` commutes with powers. -/
lemma coe_poly_pow (p : F[X]) (n : ℕ) :
    (((p ^ n : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      ((((p : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rat_cast_eq_algebraMap F,
      poly_cast_eq_algebraMap F, map_one, map_one]
  | succ k ih => rw [pow_succ, pow_succ, coe_poly_mul F, ih]

end Coes

section Head

/-- `X · n` has degree `d + 1` for `n` monic of degree `d`. -/
lemma natDegree_X_mul_head (d : ℕ) (n : HeadD F d) :
    (Polynomial.X * n.1).natDegree = d + 1 := by
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero n.2.1.ne_zero, Polynomial.natDegree_X,
    n.2.2]
  omega

/-- `X · n + C c` is monic of degree `d + 1`. -/
lemma natDegree_X_mul_head_add_C (d : ℕ) (n : HeadD F d) (c : F) :
    (Polynomial.X * n.1 + Polynomial.C c).natDegree = d + 1 :=
  (X_mul_monic_deg F (d + 1) (by omega) n.1 n.2.1 (by rw [n.2.2]; omega) c).2

end Head

section Expansion

/-- **The truncated level recursion** (Thakur §3.2).  For `d, N : ℕ` and `k : ℕ+`,

  `P_{d+1}(k) = ∑_{j ≤ N} cst(binF k j · psumF j) · (X^{k+j})^{−1} · P_d(k+j) + E`

where the error term satisfies `v E ≤ exp (−((d+1)·(k+N+1)))`. -/
theorem P_succ_expansion (d N : ℕ) (k : ℕ+) :
    ∃ E : RatFunc.CompletionAtInfty F,
      P F (d + 1) k =
        (∑ j ∈ Finset.range (N + 1),
          cst F (binF F k j * psumF F j) *
          (((((Polynomial.X : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) ^
            ((k : ℕ) + j))⁻¹ *
          P F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩) + E ∧
      Valued.v E ≤ exp (-(((d : ℤ) + 1) * ((k : ℤ) + N + 1))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  -- Step 1: split `P_{d+1}(k)` into a sum of depth-one sums `zetaSum k (X·n)`.
  have hP : P F (d + 1) k = ∑ n : HeadD F d,
      zetaSum F k (((Polynomial.X * n.1 : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F) := by
    rw [P_eq_sum_prod F (d + 1) (by omega) k, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact sum_translate_eq_zetaSum F k n.1
  -- Step 2: the hypotheses of `trunc_expansion` at `z n = X·n`.
  have hzne : ∀ n : HeadD F d,
      (((Polynomial.X * n.1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ≠ 0 := by
    intro n h
    have hp : (Polynomial.X * n.1 : F[X]) ≠ 0 :=
      mul_ne_zero Polynomial.X_ne_zero n.2.1.ne_zero
    have h1 := inftyValued_v_polynomial F _ hp
    rw [h, map_zero] at h1
    exact (WithZero.exp_ne_zero) h1.symm
  have hzv : ∀ n : HeadD F d,
      Valued.v (((Polynomial.X * n.1 : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F) = exp ((d : ℤ) + 1) := by
    intro n
    have hp : (Polynomial.X * n.1 : F[X]) ≠ 0 :=
      mul_ne_zero Polynomial.X_ne_zero n.2.1.ne_zero
    rw [inftyValued_v_polynomial F _ hp, natDegree_X_mul_head F d n]
    push_cast
    ring
  have hzshift : ∀ n : HeadD F d, ∀ c : F,
      Valued.v ((((Polynomial.X * n.1 : F[X]) : RatFunc F)
        : RatFunc.CompletionAtInfty F) + cst F c) = exp ((d : ℤ) + 1) := by
    intro n c
    have hp : (Polynomial.X * n.1 + Polynomial.C c : F[X]) ≠ 0 :=
      (X_mul_monic_deg F (d + 1) (by omega) n.1 n.2.1 (by rw [n.2.2]; omega) c).1.ne_zero
    have h1 := inftyValued_v_polynomial F _ hp
    rw [coe_X_mul_add_C F n.1 c] at h1
    rw [h1, natDegree_X_mul_head_add_C F d n c]
    push_cast
    ring
  choose W hW using fun n : HeadD F d =>
    trunc_expansion F k N k.pos (((Polynomial.X * n.1 : F[X]) : RatFunc F)
      : RatFunc.CompletionAtInfty F) ((d : ℤ) + 1) (hzne n) (hzv n) (by omega)
      (fun c => by rw [hzshift n c, hzv n])
  -- Step 3: factor the truncated part.
  have hzpow : ∀ (n : HeadD F d) (j : ℕ),
      ((((Polynomial.X * n.1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^
          ((k : ℕ) + j))⁻¹ =
        (((((Polynomial.X : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) ^
            ((k : ℕ) + j))⁻¹ * ((((n.1 : F[X]) : RatFunc F)
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹ := by
    intro n j
    have h1 : (((Polynomial.X * n.1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
        ((((Polynomial.X : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) *
          (((n.1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) :=
      coe_poly_mul F Polynomial.X n.1
    rw [h1, mul_pow, mul_inv_rev, mul_comm]
  refine ⟨∑ n : HeadD F d, W n, ?_, ?_⟩
  · rw [hP]
    have hsum : (∑ n : HeadD F d, zetaSum F k (((Polynomial.X * n.1 : F[X]) : RatFunc F)
          : RatFunc.CompletionAtInfty F))
        = (∑ n : HeadD F d, trExp F k N (((Polynomial.X * n.1 : F[X]) : RatFunc F)
            : RatFunc.CompletionAtInfty F)) + ∑ n : HeadD F d, W n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => (hW n).1
    rw [hsum]
    congr 1
    simp only [trExp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hPj := P_eq_sum F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩
    calc ∑ n : HeadD F d, cst F (binF F k j * psumF F j) *
            (((((Polynomial.X * n.1 : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹
        = ∑ n : HeadD F d, (cst F (binF F k j * psumF F j) *
            (((((Polynomial.X : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹) *
            (((((n.1 : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hzpow n j]
          ring
      _ = cst F (binF F k j * psumF F j) *
            (((((Polynomial.X : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹ *
            ∑ n : HeadD F d, (((((n.1 : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹ := by
          rw [← Finset.mul_sum]
      _ = cst F (binF F k j * psumF F j) *
            (((((Polynomial.X : F[X]) : RatFunc F))
              : RatFunc.CompletionAtInfty F) ^ ((k : ℕ) + j))⁻¹ *
            P F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩ := by
          rw [hPj, PNat.mk_coe]
  · refine v_finset_sum_le F Finset.univ (fun n : HeadD F d => W n) ?_
    intro n _
    exact (hW n).2

end Expansion

end ZagierHoffmanPositiveChar
