import Submission.ZagierHoffmanProof.EndgameNdeg
import Submission.ZagierHoffmanProof.Step7Endgame

/-!
# SESSION 360 — `TwRowFalse` at `(q-1) ∤ w`: the endgame closes

`PLAN.md` §«SESSION 360» §5.4–§5.5.  Assembling

* `EndgameNum.exists_integral_recursion` (`σ num = W^w·(num + N·D)`),
* `KuanLin.coeff_mem_ambA_zero_of_kuanLin` (`num ∈ ambA F 0[X]`),
* `EndgameNdeg.degPolyNu_recursion` (`q·deg_θ num = w·q + deg_θ(num + N·D)`),
* `EndgameNdeg.degPolyNu_N_eq_zero_or_card` (`deg_θ N ∈ {0,q}`),
* `EndgameNdeg.degPolyNu_add_eq_max` (`e = max t n₂` for `t ≠ n₂`),
* `EndgameA0.dvd_pred_of_theta_degree` (the arithmetic),

gives **`(q-1) ∣ w`** for every two-term datum of weight `w > q`.  Hence `TwRowFalse F w` holds
whenever `q < w` and `(q-1) ∤ w` — i.e. for every `q < w < 2q-2` — and the **only** surviving weight
of `TwRowFalse` is `w = 2q-2` (Dac §6's explicit computation).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open Polynomial
open scoped Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. `θ^q ≠ θ` -/

/-- `θ^q ≠ θ`: otherwise the non-constant `X^q - X ∈ F[X]` would vanish at the transcendental `θ`. -/
lemma ambTheta_pow_card_ne_self (hq : 3 ≤ Nat.card F) : (ambTheta F) ^ Nat.card F ≠ ambTheta F := by
  intro h
  have hzero : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial F).eval₂
      (algebraMap F (Ambient F)) (ambTheta F) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, h, sub_self]
  have h0 := ambTheta_transcendental F (Polynomial.X ^ Nat.card F - Polynomial.X) hzero
  have h1 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial F).coeff (Nat.card F) = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X, if_pos rfl,
      if_neg (by omega : ¬ (1 = Nat.card F)), sub_zero]
  rw [h0] at h1
  simpa using h1

/-! ## §2. `Z ≠ 0` (`PLAN.md` §5.4) -/

/-- The `evaluation of `X^q - X` at `θ` does not vanish. -/
lemma eval_X_pow_sub_X_theta_ne_zero (hq : 3 ≤ Nat.card F) :
    ((Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F))).eval (ambTheta F)
      ≠ 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_ne_zero]
  exact ambTheta_pow_card_ne_self F hq

/-- ★★★ **`Z ≠ 0`** for the two-term rows.  If `Z = 0` then `Y = -Q·A₁·H_w`, and the `(A)`-row
`Y·P = A₂·(C(θ^q) - X^q)·Q` becomes `A₁·H_w·P = A₂·(X - C θ)^q`; the prime `L = X - C θ` then divides
one of `A₁`, `H_w`, `P` — all three impossible (`A₁(θ) ≠ 0`, `H_w(θ) ≠ 0`, `P(θ) = θ^q - θ ≠ 0`). -/
theorem tw_Z_ne_zero {w : ℕ} (hq : 3 ≤ Nat.card F)
    {A₁ A₂ Q Z Y : Polynomial (Ambient F)}
    (hA₁m : ∀ n, A₁.coeff n ∈ ambF F) (hA₂m : ∀ n, A₂.coeff n ∈ ambF F)
    (hA₁ne : A₁ ≠ 0) (hA₂ne : A₂ ≠ 0) (hQ : Q ≠ 0)
    (hR : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Q * (A₁ * ambH F w) + Z + Y))
    (hA : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    Z ≠ 0 := by
  classical
  have hzerotw : polyTwist (q := Nat.card F) 1 (0 : Polynomial (Ambient F)) = 0 := by simp
  intro hZ0
  set W : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) with hWs
  set L : Polynomial (Ambient F) := Polynomial.X - Polynomial.C (ambTheta F) with hLs
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hPs
  have hLne : L ≠ 0 := by rw [hLs]; exact Polynomial.X_sub_C_ne_zero _
  have hWne : W ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hPeval : P.eval (ambTheta F) ≠ 0 := by
    rw [hPs]; exact eval_X_pow_sub_X_theta_ne_zero F hq
  have hσQ : polyTwist (q := Nat.card F) 1 Q ≠ 0 := fun h0 =>
    hQ (polyTwist_one_injective F (by rw [h0, hzerotw]))
  -- `Q·A₁·H_w + Y = 0`
  have hsum : Q * (A₁ * ambH F w) + Y = 0 := by
    have h := hR
    rw [hZ0, hzerotw, mul_zero] at h
    have h2 : polyTwist (q := Nat.card F) 1 Q * W ^ w * (Q * (A₁ * ambH F w) + 0 + Y) = 0 := h.symm
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hσQ
      · exact absurd h4 (pow_ne_zero w hWne)
    · simpa using h3
  have hY : Y = -(Q * (A₁ * ambH F w)) := by linear_combination hsum
  -- the `(A)`-row becomes `A₁·H_w·P = A₂·L^q`
  have hmain : A₁ * ambH F w * P = A₂ * L ^ Nat.card F := by
    have h := hA
    rw [hY, C_theta_pow_sub_X_pow_eq_neg, ← hLs] at h
    have h3 : Q * (A₁ * ambH F w * P) = A₂ * L ^ Nat.card F * Q := by
      linear_combination -h
    exact mul_left_cancel₀ hQ (by rw [h3]; ring)
  -- `L` divides one of the three factors
  have hdvdpow : L ^ Nat.card F ∣ A₁ * ambH F w * P := ⟨A₂, by rw [hmain]; ring⟩
  have hdvd : L ∣ A₁ * ambH F w * P :=
    dvd_trans (dvd_pow_self L (by omega : Nat.card F ≠ 0)) hdvdpow
  have hprime : Prime L := by rw [hLs]; exact Polynomial.prime_X_sub_C _
  have hnotA₁ : ¬ L ∣ A₁ := by
    rw [hLs]; exact not_dvd_X_sub_C_theta_of_coeff_mem_ambF F hA₁m hA₁ne
  have hnotH : ¬ L ∣ ambH F w := by
    rw [hLs, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact ambH_eval_theta_ne_zero (F := F) w
  have hnotP : ¬ L ∣ P := by
    rw [hLs, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact hPeval
  rcases hprime.dvd_or_dvd (by rwa [mul_assoc] at hdvd) with h | h
  · exact hnotA₁ h
  · rcases hprime.dvd_or_dvd h with h' | h'
    · exact hnotH h'
    · exact hnotP h'

/-! ## §3. `(q-1) ∣ w` from the two rows, and `TwRowFalse` at `(q-1) ∤ w` (`PLAN.md` §5.5) -/

/-- `N`-membership for the inhomogeneity `N` of the two-term datum. -/
theorem twN_coeff_mem {A₁ A₂ : Polynomial (Ambient F)} {w : ℕ}
    (hA₁m : ∀ n, A₁.coeff n ∈ ambF F) (hA₂m : ∀ n, A₂.coeff n ∈ ambF F) :
    ∀ n, ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
      - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) :
        Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  intro n
  rw [Polynomial.coeff_sub]
  refine (ambASub F 0).sub_mem ?_ ?_
  · exact coeff_mul_mem_ambA (fun m => ambF_subset_ambA_zero (F := F) (coeff_X_pow_sub_X_mem_ambF m))
      (fun m => coeff_mul_mem_ambA (fun k => ambF_subset_ambA_zero (F := F) (hA₁m k))
        (fun k => ambH_coeff_mem F w k) m) n
  · refine coeff_mul_mem_ambA (fun m => ambF_subset_ambA_zero (F := F) (hA₂m m))
      (fun m => ?_) n
    have hL0 : ∀ k, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff k
        ∈ ambA F 0 := fun k => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero k
    have h2 := coeff_pow_mem_ambA hL0 (Nat.card F) m
    rwa [X_sub_C_pow_card] at h2

/-- ★★★★★ **The `θ`-degree data forces `(q-1) ∣ w`.**  From the integral recursion
`σ num = W^w·(num + N·D)` (`W = X - C(θ^q)`), the `ambF F`-coefficients of `D`, the `ambA F 0`-membership
of `N` and `deg_θ N ∈ {0,q}`, the arithmetic of `EndgameA0.dvd_pred_of_theta_degree` gives `(q-1) ∣ w`.

This is the "cheap half" of `dvd_pred_of_rows`, with the heavy row hypotheses already consumed. -/
theorem dvd_pred_of_data {w : ℕ} (hq : 3 ≤ Nat.card F) (hqw : Nat.card F < w)
    {N num D : Polynomial (Ambient F)} (hD0 : D ≠ 0) (hnum0 : num ≠ 0)
    (hDambF : ∀ n, D.coeff n ∈ ambF F)
    (hNm : ∀ n, N.coeff n ∈ ambA F 0)
    (hnumrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D))
    (hNdeg : degPolyNu F 0 N = 0 ∨ degPolyNu F 0 N = Nat.card F) :
    (Nat.card F - 1) ∣ w := by
  have hWmem : ∀ n, ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := coeff_X_sub_C_theta_pow_pow_mem_ambA 0 w
  have hDmA0 : ∀ n, D.coeff n ∈ ambA F 0 := fun n => ambF_subset_ambA_zero (F := F) (hDambF n)
  have hnumA0 : ∀ n, num.coeff n ∈ ambA F 0 :=
    coeff_mem_ambA_zero_of_kuanLin (F := F) (m := w) (by omega) (ε := 1) (δ := num)
      (ambF F).one_mem
      (fun j => coeff_mul_mem_ambA (fun n => coeff_mul_mem_ambA hNm hDmA0 n) hWmem j)
      (by rw [hnumrec, Polynomial.C_1, one_mul]; ring)
  have hdeg := degPolyNu_recursion (F := F) (num := num) (D := D) (N := N)
    hnum0 hD0 hnumA0 hDmA0 hNm hnumrec
  have hND : degPolyNu F 0 (N * D) = 0 ∨ degPolyNu F 0 (N * D) = Nat.card F := by
    by_cases hN0 : N = 0
    · left; rw [hN0, zero_mul, degPolyNu_zero]
    · rw [degPolyNu_mul hNm hDmA0 hN0 hD0, degPolyNu_eq_zero_of_coeff_mem_ambF hDambF, add_zero]
      exact hNdeg
  exact dvd_pred_of_theta_degree (q := Nat.card F) (w := w)
    (t := degPolyNu F 0 num) (e := degPolyNu F 0 (num + N * D)) (n₂ := degPolyNu F 0 (N * D))
    (by omega) hND hdeg
    (fun hmax => degPolyNu_add_eq_max (F := F) (p := num) (q := N * D)
      hnumA0 (fun n => coeff_mul_mem_ambA hNm hDmA0 n) rfl rfl hmax)
    hqw

/-- ★★★★★ **The two rows force `(q-1) ∣ w`.**  The integral numerator of `Ξ = P·Z/Q`
(`EndgameNum.exists_integral_recursion`), its `θ`-integrality (Kuan–Lin), the exact `θ`-degree
identity of the recursion, `deg_θ N ∈ {0,q}` (`EndgameNdeg`) and the arithmetic of
`EndgameA0.dvd_pred_of_theta_degree` combine to give `(q-1) ∣ w`. -/
theorem dvd_pred_of_rows {w : ℕ} (hq : 3 ≤ Nat.card F) (hqw : Nat.card F < w)
    {A₁ A₂ Q Z Y : Polynomial (Ambient F)}
    (hA₁m : ∀ n, A₁.coeff n ∈ ambF F) (hA₂m : ∀ n, A₂.coeff n ∈ ambF F)
    (hA₁ne : A₁ ≠ 0) (hA₂ne : A₂ ≠ 0) (hQ : Q ≠ 0)
    (hR : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Q * (A₁ * ambH F w) + Z + Y))
    (hA : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    (Nat.card F - 1) ∣ w := by
  classical
  have hZ : Z ≠ 0 :=
    tw_Z_ne_zero (F := F) hq hA₁m hA₂m hA₁ne hA₂ne hQ hR hA
  have hP0 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) ≠ 0 := by
    intro h0
    have h1 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).eval
        (ambTheta F) = 0 := by rw [h0, Polynomial.eval_zero]
    exact eval_X_pow_sub_X_theta_ne_zero F hq h1
  have hPZ0 : (Polynomial.X ^ Nat.card F - Polynomial.X) * Z ≠ 0 := mul_ne_zero hP0 hZ
  have hrec := sigma_recursion_of_rows (F := F) (w := w) hR hA
  obtain ⟨num, D, hD0, hDambF, hnum0, hnumrec⟩ :=
    exists_integral_recursion (F := F) (P := Polynomial.X ^ Nat.card F - Polynomial.X)
      (Z := Z) (Q := Q) (N := (Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
        - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) hQ hPZ0 hrec
  exact dvd_pred_of_data (F := F) hq hqw hD0 hnum0 hDambF (twN_coeff_mem (F := F) hA₁m hA₂m) hnumrec
    (degPolyNu_N_eq_zero_or_card (F := F) (A₁ := A₁) (A₂ := A₂) (w := w) (by omega) hA₁m hA₂m)

/-! ## §4. The `w = 2q-2` case: `deg_θ num = 2q` (`PLAN.md` §1.3(B), first step) -/

/-- The arithmetic of the `k = q-1` weight: with `w = 2q-2`, `n₂ ∈ {0,q}` and `q·t = w·q + e` with
no cancellation at the top, one has `t = 2q`. -/
theorem theta_degree_eq_of_card {q w t e n₂ : ℕ} (hq : 3 ≤ q) (hw : w = 2 * q - 2)
    (hn₂ : n₂ = 0 ∨ n₂ = q) (he : q * t = w * q + e) (hmax : t ≠ n₂ → e = max t n₂) :
    t = 2 * q := by
  have hq1 : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos (by omega)).symm
  by_cases h : t = n₂
  · rcases hn₂ with h0 | hq'
    · rw [h0] at h
      have he0 : w * q = 0 := by rw [h, mul_zero] at he; omega
      have hw0 : w = 0 := (mul_eq_zero.mp he0).resolve_right (by omega)
      omega
    · rw [hq'] at h
      have h1 : w * q ≤ q * q := by rw [h] at he; omega
      have h2 : w ≤ q := Nat.le_of_mul_le_mul_right h1 (by omega)
      omega
  · rw [hmax h] at he
    rcases lt_or_ge t n₂ with hlt | hle
    · rw [max_eq_right (le_of_lt hlt)] at he
      rcases hn₂ with h0 | hq'
      · rw [h0, add_zero] at he
        rw [h0] at hlt
        have h1 : t = w := mul_left_cancel₀ (by omega : q ≠ 0)
          (by rw [mul_comm w q] at he; exact he)
        omega
      · rw [hq'] at he hlt
        have h1 : t = w + 1 := mul_left_cancel₀ (by omega : q ≠ 0)
          (by rw [mul_comm w q] at he; exact he)
        omega
    · rw [max_eq_left hle] at he
      have hA : (q - 1) * t = w * q := by
        have h4 : ((q - 1) + 1) * t = w * q + t := by rw [← hq1]; exact he
        rw [Nat.add_mul, one_mul] at h4
        omega
      have hB : w * q = (q - 1) * (2 * q) := by
        have hw2 : w = 2 * (q - 1) := by omega
        rw [hw2]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q - 1) (hA.trans hB)

/-- ★★★★ **At `w = 2q-2` the integral numerator has `θ`-degree exactly `2q`.**  This is the first
input of Dac's explicit computation (`PLAN.md` §1.3(B)): it makes `deg_θ u₂ = 2` for
`u₂ = Ξ/L^w`. -/
theorem degPolyNu_num_eq_two_card {w : ℕ} (hq : 3 ≤ Nat.card F) (hwk : w = 2 * Nat.card F - 2)
    {N num D : Polynomial (Ambient F)} (hD0 : D ≠ 0) (hnum0 : num ≠ 0)
    (hDambF : ∀ n, D.coeff n ∈ ambF F)
    (hNm : ∀ n, N.coeff n ∈ ambA F 0)
    (hnumrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D))
    (hNdeg : degPolyNu F 0 N = 0 ∨ degPolyNu F 0 N = Nat.card F) :
    degPolyNu F 0 num = 2 * Nat.card F := by
  have hWmem : ∀ n, ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := coeff_X_sub_C_theta_pow_pow_mem_ambA 0 w
  have hDmA0 : ∀ n, D.coeff n ∈ ambA F 0 := fun n => ambF_subset_ambA_zero (F := F) (hDambF n)
  have hnumA0 : ∀ n, num.coeff n ∈ ambA F 0 :=
    coeff_mem_ambA_zero_of_kuanLin (F := F) (m := w) (by omega) (ε := 1) (δ := num)
      (ambF F).one_mem
      (fun j => coeff_mul_mem_ambA (fun n => coeff_mul_mem_ambA hNm hDmA0 n) hWmem j)
      (by rw [hnumrec, Polynomial.C_1, one_mul]; ring)
  have hdeg := degPolyNu_recursion (F := F) (num := num) (D := D) (N := N)
    hnum0 hD0 hnumA0 hDmA0 hNm hnumrec
  have hND : degPolyNu F 0 (N * D) = 0 ∨ degPolyNu F 0 (N * D) = Nat.card F := by
    by_cases hN0 : N = 0
    · left; rw [hN0, zero_mul, degPolyNu_zero]
    · rw [degPolyNu_mul hNm hDmA0 hN0 hD0, degPolyNu_eq_zero_of_coeff_mem_ambF hDambF,
        add_zero]
      exact hNdeg
  exact theta_degree_eq_of_card (q := Nat.card F) (by omega) hwk hND hdeg
    (fun hmax => degPolyNu_add_eq_max (F := F) (p := num) (q := N * D)
      hnumA0 (fun n => coeff_mul_mem_ambA hNm hDmA0 n) rfl rfl hmax)

end ZagierHoffmanPositiveChar
