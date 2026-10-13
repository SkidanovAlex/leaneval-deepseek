/-
  WilE5 — the a-priori *profile* sequences (Gabrielov–Vorobjov §3 `M_0, …, M_n` and the degree
  bounds `β_k`), as explicit polynomials in the initial degree `D = X.deg`.

  `Me` is `E3_identity`'s multiplicity polynomial (its order bound is
  `Me.eval (∑ atomDeg h + atomDeg f)`).

  For a state at level `k` (i.e. with `k` pivots) we track
  * `S k = (profS k).eval D`  — a bound on `∑ a, atomDeg (hFun σ.B a)`;
  * `d k = (profD k).eval D`  — a bound on the `atomDeg` of every function occurring in the state
    (`Φ`, `Ξ`, `ν`, and hence the pivots);
  * `M k = (profM k).eval D`  — the test-order bound used at level `k`
    (`Me.eval (S k + d k + 2p + 1)`).
  The recursion is the a-priori one: the new pivot of a child is an operator of order `≤ q * M k`
  applied to a source of degree `≤ d k`, whence its degree is `≤ d k + q * M k * (S k + 1)`.

  `(profN k).eval D` bounds the length of the flatness family `Φ` at level `k`, and
  `NPhi Me D p q = (profN (q+1)).eval D` is the global index bound `NΦ` of the test list.
-/
import Mathlib
import Submission.Work.WilE5.SysL

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5

/-! ## §1. Monotonicity of `Polynomial.eval` on `ℕ` -/

/-- `Polynomial.eval` at natural numbers is monotone when the coefficients are natural
numbers. -/
theorem eval_mono_nat {P : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-! ## §2. The polynomial sequences -/

/-- The pair `(d k, S k)` of a-priori bounds at level `k`, as polynomials in the initial degree
`D`. -/
def profPair (Me : Polynomial ℕ) (p q : ℕ) : ℕ → Polynomial ℕ × Polynomial ℕ
  | 0 => (Polynomial.X + Polynomial.C 3, Polynomial.C (2 * q))
  | (k + 1) =>
      let d := (profPair Me p q k).1
      let s := (profPair Me p q k).2
      let m := Me.comp (s + d + Polynomial.C (2 * p + 1))
      let d' := d + Polynomial.C q * m * (s + Polynomial.C 1)
      (d', s + d')

/-- The a-priori degree bound `d k` at level `k` (polynomial in `D`). -/
def profD (Me : Polynomial ℕ) (p q : ℕ) (k : ℕ) : Polynomial ℕ := (profPair Me p q k).1

/-- The a-priori pivot-degree-sum bound `S k` at level `k` (polynomial in `D`). -/
def profS (Me : Polynomial ℕ) (p q : ℕ) (k : ℕ) : Polynomial ℕ := (profPair Me p q k).2

/-- The a-priori test-order bound at level `k`. -/
def profM (Me : Polynomial ℕ) (p q : ℕ) (k : ℕ) : Polynomial ℕ :=
  Me.comp (profS Me p q k + profD Me p q k + Polynomial.C (2 * p + 1))

/-- The a-priori bound on the length of the flatness family at level `k`. -/
def profN (Me : Polynomial ℕ) (p q : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X + Polynomial.C 1
  | (k + 1) =>
      Polynomial.C 3 * profN Me p q k +
        Polynomial.C q * (profM Me p q k + Polynomial.C 1) ^ q * profN Me p q k +
        Polynomial.C 1

/-- The global index bound `NΦ` of the test list. -/
def NPhi (Me : Polynomial ℕ) (D p q : ℕ) : ℕ := (profN Me p q (2 * q + 1)).eval D

/-- The test-order profile of a `SemiPf` set of degree `≤ D`. -/
def MlOf (Me : Polynomial ℕ) (D p q : ℕ) : ℕ → ℕ := fun k => (profM Me p q k).eval D

/-! ## §3. Unfolding lemmas -/

theorem profD_zero (Me : Polynomial ℕ) (p q : ℕ) :
    profD Me p q 0 = Polynomial.X + Polynomial.C 3 := rfl

theorem profS_zero (Me : Polynomial ℕ) (p q : ℕ) :
    profS Me p q 0 = Polynomial.C (2 * q) := rfl

theorem profD_succ (Me : Polynomial ℕ) (p q k : ℕ) :
    profD Me p q (k + 1) =
      profD Me p q k + Polynomial.C q * profM Me p q k * (profS Me p q k + Polynomial.C 1) :=
  rfl

theorem profS_succ (Me : Polynomial ℕ) (p q k : ℕ) :
    profS Me p q (k + 1) = profS Me p q k + profD Me p q (k + 1) :=
  rfl

theorem profN_succ (Me : Polynomial ℕ) (p q k : ℕ) :
    profN Me p q (k + 1) =
      Polynomial.C 3 * profN Me p q k +
        Polynomial.C q * (profM Me p q k + Polynomial.C 1) ^ q * profN Me p q k +
        Polynomial.C 1 := rfl

/-! ## §4. Evaluated (numeric) forms -/

theorem profM_eval (Me : Polynomial ℕ) (p q k D : ℕ) :
    (profM Me p q k).eval D =
      Me.eval ((profS Me p q k).eval D + (profD Me p q k).eval D + (2 * p + 1)) := by
  simp [profM, Polynomial.eval_comp]

theorem profD_eval_succ (Me : Polynomial ℕ) (p q k D : ℕ) :
    (profD Me p q (k + 1)).eval D =
      (profD Me p q k).eval D +
        q * (profM Me p q k).eval D * ((profS Me p q k).eval D + 1) := by
  simp [profD_succ, profM_eval]

theorem profS_eval_succ (Me : Polynomial ℕ) (p q k D : ℕ) :
    (profS Me p q (k + 1)).eval D =
      (profS Me p q k).eval D + (profD Me p q (k + 1)).eval D := by
  simp [profS_succ]

theorem profS_eval_zero (Me : Polynomial ℕ) (p q D : ℕ) :
    (profS Me p q 0).eval D = 2 * q := by simp [profS_zero]

theorem profD_eval_zero (Me : Polynomial ℕ) (p q D : ℕ) :
    (profD Me p q 0).eval D = D + 3 := by simp [profD_zero]

/-! ## §5. Monotonicity in the level (of the evaluated bounds) -/

theorem profD_eval_mono (Me : Polynomial ℕ) (p q D : ℕ) :
    Monotone fun k => (profD Me p q k).eval D := by
  intro a b h
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    change (profD Me p q _).eval D ≤ (profD Me p q (_ + 1)).eval D
    refine le_trans ih ?_
    rw [profD_eval_succ]
    exact le_add_right le_rfl

theorem profS_eval_mono (Me : Polynomial ℕ) (p q D : ℕ) :
    Monotone fun k => (profS Me p q k).eval D := by
  intro a b h
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    change (profS Me p q _).eval D ≤ (profS Me p q (_ + 1)).eval D
    refine le_trans ih ?_
    rw [profS_eval_succ]
    exact le_add_right le_rfl

theorem profM_eval_mono (Me : Polynomial ℕ) (p q D : ℕ) :
    Monotone fun k => (profM Me p q k).eval D := by
  intro a b h
  change (profM Me p q a).eval D ≤ (profM Me p q b).eval D
  rw [profM_eval, profM_eval]
  refine eval_mono_nat ?_
  have h1 : (profS Me p q a).eval D ≤ (profS Me p q b).eval D := profS_eval_mono Me p q D h
  have h2 : (profD Me p q a).eval D ≤ (profD Me p q b).eval D := profD_eval_mono Me p q D h
  omega

theorem profN_eval_mono (Me : Polynomial ℕ) (p q D : ℕ) :
    Monotone fun k => (profN Me p q k).eval D := by
  intro a b h
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    change (profN Me p q _).eval D ≤ (profN Me p q (_ + 1)).eval D
    refine le_trans ih ?_
    rw [profN_succ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    calc (profN Me p q _).eval D
        ≤ 3 * (profN Me p q _).eval D := by omega
      _ ≤ 3 * (profN Me p q _).eval D +
            q * ((profM Me p q _).eval D + 1) ^ q * (profN Me p q _).eval D :=
          Nat.le_add_right _ _
      _ ≤ 3 * (profN Me p q _).eval D +
            q * ((profM Me p q _).eval D + 1) ^ q * (profN Me p q _).eval D + 1 :=
          Nat.le_succ _

/-- The test bound used at level `k` dominates `Me` evaluated at the state's data. -/
theorem profM_eval_ge (Me : Polynomial ℕ) (p q D k S d : ℕ)
    (hS : S ≤ (profS Me p q k).eval D) (hd : d ≤ (profD Me p q k).eval D) :
    Me.eval (S + 2 * p + d) ≤ (profM Me p q k).eval D := by
  rw [profM_eval]
  refine eval_mono_nat ?_
  omega

/-! ## §6. `eval` commutes with finite sums -/

theorem eval_finset_sum {α : Type*} (D : ℕ) (s : Finset α) (f : α → Polynomial ℕ) :
    (∑ i ∈ s, f i).eval D = ∑ i ∈ s, (f i).eval D := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.eval_add, ih]

/-! ## §7. The count and degree polynomials

`profCount k` bounds the number of states at level `k`; `profLeaf k` bounds the degree of a
stratum produced at level `k`. -/

/-- A bound on the number of states at level `k`: `|initStates| ≤ 3^q (D+1)` and each state has
at most `2 * |testL| ≤ 2 * NΦ * (M (2q+1) + 1)^q * q` children (a state at depth `k ≤ q` has at
most `2q` pivots, since its initial state already carries up to `q` face equations). -/
def profCount (Me : Polynomial ℕ) (p q : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.C (3 ^ q) * (Polynomial.X + Polynomial.C 1)
  | (k + 1) =>
      profCount Me p q k *
        (Polynomial.C 2 * profN Me p q (2 * q + 1) * (profM Me p q (2 * q + 1) + Polynomial.C 1) ^ q *
          Polynomial.C q)

/-- A bound on the degree of a stratum produced at any level `≤ q` (all indices `≤ 2q+1`). -/
def profLeaf (Me : Polynomial ℕ) (p q : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C 1) + profS Me p q (2 * q + 1) +
    (Polynomial.X + Polynomial.C 1) *
      (profS Me p q (2 * q + 1) +
        (profN Me p q (2 * q + 1) + Polynomial.X + Polynomial.C (2 * q + 1)) *
          profD Me p q (2 * q + 1) +
        profN Me p q (2 * q + 1) * (profM Me p q (2 * q + 1) + Polynomial.C 1) ^ q *
          Polynomial.C q * profD Me p q (2 * q + 1))

/-- The global bound on the number of strata of one `SemiPf` set (all levels `≤ q`). -/
def bCount (Me : Polynomial ℕ) (p q : ℕ) : Polynomial ℕ :=
  Polynomial.C (q + 1) * profCount Me p q q

/-- The global bound on the degree of one stratum. -/
def bDeg (Me : Polynomial ℕ) (p q : ℕ) : Polynomial ℕ := profLeaf Me p q

theorem bCount_eval (Me : Polynomial ℕ) (p q D : ℕ) :
    (bCount Me p q).eval D = (q + 1) * (profCount Me p q q).eval D := by
  simp [bCount]

theorem bDeg_eval (Me : Polynomial ℕ) (p q D : ℕ) :
    (bDeg Me p q).eval D = (profLeaf Me p q).eval D := rfl

end Work.WilE5
