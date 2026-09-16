import Submission.ZagierHoffmanProof.EndgameNum
import Submission.ZagierHoffmanProof.DegRow

/-!
# SESSION 360 — `deg_θ N ∈ {0, q}` for the inhomogeneity of the two-term datum

`PLAN.md` §«SESSION 360» §5.1.  The inhomogeneity of the *integral* recursion produced by
`EndgameNum.exists_integral_recursion` is

  `N := (X^q - X)·(A₁·ambH F w) - A₂·(X^q - C(θ^q))`,
  `A₁, A₂ ∈ F_q[X] ∖ {0}`,  `q < w`,  `w = k + (q-1)`.

Writing `H_w = P + C(w-q)·L^q` (`ambH_factor_of_lt`, valid since `q < w`) and
`L^q = X^q - C(θ^q)` (`X_sub_C_pow_card`),

  `N = A₁·P² + M·L^q`,   `M := A₁·P·C(w-q) - A₂ ∈ F_q[X]`.

`A₁·P²` is `θ`-free (`deg_θ = 0`) while `M·L^q` has `θ`-degree exactly `q` when `M ≠ 0`
(`deg_θ(M) = 0`, `deg_θ(L^q) = q`).  Hence **`deg_θ N = 0` if `M = 0` and `deg_θ N = q` otherwise** —
which is `PLAN.md`'s `n₂ ∈ {0, q}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. Closure of `ambF F` under products and powers -/

lemma coeff_mul_mem_ambF {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambF F) (hq : ∀ n, q.coeff n ∈ ambF F) (n : ℕ) :
    (p * q).coeff n ∈ ambF F := by
  rw [Polynomial.coeff_mul]
  exact Subfield.sum_mem _ (fun x _ => (ambF F).mul_mem (hp x.1) (hq x.2))

lemma coeff_pow_two_mem_ambF {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambF F) (n : ℕ) : (p ^ 2).coeff n ∈ ambF F := by
  rw [pow_two]
  exact coeff_mul_mem_ambF F hp hp n

lemma coeff_C_natCast_mem_ambF (m : ℕ) (n : ℕ) :
    (Polynomial.C ((m : ℕ) : Ambient F) : Polynomial (Ambient F)).coeff n ∈ ambF F := by
  rw [Polynomial.coeff_C]
  split_ifs with h
  · simpa [h] using natCast_mem_ambF F m
  · exact (ambF F).zero_mem

/-! ## §2. The degree of `N` -/

/-- ★★★ **`deg_θ N ∈ {0, q}`** for `N = (X^q - X)·(A₁·H_w) - A₂·(X^q - C(θ^q))` with `q < w` and
`A₁, A₂ ∈ F_q[X]`.  This is the `n₂ ∈ {0, q}` of Dac §6 / `PLAN.md` §«SESSION 360» §1.2. -/
theorem degPolyNu_N_eq_zero_or_card {A₁ A₂ : Polynomial (Ambient F)} {w : ℕ}
    (hwq : Nat.card F < w)
    (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (hA₂ : ∀ n, A₂.coeff n ∈ ambF F) :
    degPolyNu F 0 ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
        - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)))
      = 0
    ∨ degPolyNu F 0 ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
        - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)))
      = Nat.card F := by
  classical
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hPs
  set Lq : Polynomial (Ambient F) := (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F with hLs
  set c : Polynomial (Ambient F) := Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) with hcs
  set M : Polynomial (Ambient F) := A₁ * P * c - A₂ with hMs
  have hmemP : ∀ n, P.coeff n ∈ ambF F := by
    rw [hPs]; exact coeff_X_pow_sub_X_mem_ambF
  have hLmem : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F)).coeff n ∈ ambA F 0 :=
    fun n => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero n
  have hmemLq : ∀ n, Lq.coeff n ∈ ambA F 0 := fun n => by
    rw [hLs]
    exact coeff_pow_mem_ambA hLmem (Nat.card F) n
  have hmemA₁P2 : ∀ n, (A₁ * P ^ 2).coeff n ∈ ambF F := fun n =>
    coeff_mul_mem_ambF F hA₁ (coeff_pow_two_mem_ambF F hmemP) n
  have hmemM : ∀ n, M.coeff n ∈ ambF F := by
    rw [hMs]; intro n
    rw [Polynomial.coeff_sub]
    exact (ambF F).sub_mem
      (coeff_mul_mem_ambF F (coeff_mul_mem_ambF F hA₁ hmemP)
        (fun m => coeff_C_natCast_mem_ambF F _ m) n) (hA₂ n)
  have hH : ambH F w = P + c * Lq := by
    rw [ambH_factor_of_lt hwq, hPs, hLs, hcs]
  have hLqeq : (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)
      : Polynomial (Ambient F)) = Lq := by rw [hLs, X_sub_C_pow_card]
  have hN : (Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
      - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))
      = A₁ * P ^ 2 + M * Lq := by
    rw [hH, hLqeq, hMs, ← hPs]
    ring
  rw [hN]
  by_cases hM : M = 0
  · left
    rw [hM, zero_mul, add_zero]
    exact degPolyNu_eq_zero_of_coeff_mem_ambF hmemA₁P2
  · right
    have hdegA₁P2 : degPolyNu F 0 (A₁ * P ^ 2) = 0 :=
      degPolyNu_eq_zero_of_coeff_mem_ambF hmemA₁P2
    have hLq0 : Lq ≠ 0 := by
      rw [hLs]
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (ambTheta F))
    have hdegMLq : degPolyNu F 0 (M * Lq) = Nat.card F := by
      rw [degPolyNu_mul (fun n => ambF_subset_ambA_zero (F := F) (hmemM n)) hmemLq hM hLq0,
        degPolyNu_eq_zero_of_coeff_mem_ambF hmemM, zero_add]
      simpa using degPolyNu_X_sub_theta_pow_card (F := F) 0
    have hlt : degPolyNu F 0 (A₁ * P ^ 2) < degPolyNu F 0 (M * Lq) := by
      rw [hdegA₁P2, hdegMLq]
      have := two_le_ambCard F
      omega
    have hcomm : M * Lq + A₁ * P ^ 2 = A₁ * P ^ 2 + M * Lq := add_comm _ _
    rw [← hcomm,
      degPolyNu_add_of_lt (p := M * Lq) (q := A₁ * P ^ 2)
        (fun n => coeff_mul_mem_ambA (fun m => ambF_subset_ambA_zero (F := F) (hmemM m))
          hmemLq n)
        (fun n => ambF_subset_ambA_zero (F := F) (hmemA₁P2 n)) hlt,
      hdegMLq]

/-! ## §3. The `θ`-degree identity of the recursion, and the `max` case -/

/-- ★★★★ **The `θ`-degree of the integral recursion is an exact identity:**

  `q · deg_θ num = w·q + deg_θ(num + N·D)`,

from `σ num = W^w·(num + N·D)` (`EndgameNum.exists_integral_recursion`).  This is the `q·t = w·q + e`
of `PLAN.md` §«SESSION 360» §1.2, and the hypothesis of `EndgameA0.dvd_pred_of_theta_degree`. -/
theorem degPolyNu_recursion {num D N : Polynomial (Ambient F)} {w : ℕ}
    (hnum0 : num ≠ 0) (hD0 : D ≠ 0)
    (hnum : ∀ n, num.coeff n ∈ ambA F 0)
    (hD : ∀ n, D.coeff n ∈ ambA F 0)
    (hN : ∀ n, N.coeff n ∈ ambA F 0)
    (hrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D)) :
    Nat.card F * degPolyNu F 0 num
      = w * Nat.card F + degPolyNu F 0 (num + N * D) := by
  have hW0 : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hzerotw : polyTwist (q := Nat.card F) 1 (0 : Polynomial (Ambient F)) = 0 := by simp
  have hsum0 : num + N * D ≠ 0 := by
    intro h0
    refine hnum0 (polyTwist_one_injective F ?_)
    rw [hrec, h0, mul_zero, hzerotw]
  have hWmem : ∀ n, ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    coeff_X_sub_C_theta_pow_pow_mem_ambA 0 w
  have hWlin : ∀ n, (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    coeff_X_sub_C_theta_pow_mem_ambA 0
  have hsummem : ∀ n, (num + N * D).coeff n ∈ ambA F 0 := fun n =>
    coeff_add_mem_ambA hnum (fun m => coeff_mul_mem_ambA hN hD m) n
  have hdegW : degPolyNu F 0 ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
      : Polynomial (Ambient F)) = w * Nat.card F := by
    rw [degPolyNu_pow hWlin hW0 w]
    congr 1
    simpa using degPolyNu_X_sub_theta_pow (F := F) 0
  have h := congrArg (degPolyNu F 0) hrec
  rw [degPolyNu_polyTwist_one hnum, degPolyNu_mul hWmem hsummem (pow_ne_zero w hW0) hsum0,
    hdegW] at h
  exact h

/-- ★★★ **`e = max t n₂` when `t ≠ n₂`** (`PLAN.md` §5.3): for two `A_0[X]`-polynomials whose
`θ`-degrees differ, the degree of the sum is the larger of the two.  In the endgame
`p := num`, `q := N·D`, so `n₂ := deg_θ(N·D) = deg_θ N ∈ {0,q}` (`EndgameNdeg`'s main theorem). -/
theorem degPolyNu_add_eq_max {p q : Polynomial (Ambient F)} {t n₂ : ℕ}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0)
    (ht : degPolyNu F 0 p = t) (hn : degPolyNu F 0 q = n₂) (hne : t ≠ n₂) :
    degPolyNu F 0 (p + q) = max t n₂ := by
  rcases lt_or_ge n₂ t with hlt | hle
  · rw [max_eq_left (le_of_lt hlt),
      degPolyNu_add_of_lt (p := p) (q := q) hp hq (by rw [ht, hn]; exact hlt), ht]
  · have hlt : t < n₂ := lt_of_le_of_ne hle hne
    rw [max_eq_right (le_of_lt hlt), add_comm,
      degPolyNu_add_of_lt (p := q) (q := p) hq hp (by rw [ht, hn]; exact hlt), hn]

end ZagierHoffmanPositiveChar
