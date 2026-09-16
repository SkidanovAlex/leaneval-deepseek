import Submission.ZagierHoffmanProof.EndgameLast7

/-!
# SESSION 363 — the last case `w = 2q-2`: item (iii), the wiring

`PLAN.md` §«SESSION 362» §7.3.  `TwRowFalse F (2q-2)`: the same skeleton as
`EndgameTwRow.TwRowFalse_of_not_dvd` (rows via `tw_Y_mul_P_eq`, then `exists_integral_recursion`),
followed by the new endgame.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open Polynomial
open scoped Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem degPolyNu_add_eq_two_card {w : ℕ} (hq : 3 ≤ Nat.card F) (hwk : w = 2 * Nat.card F - 2)
    {N num D : Polynomial (Ambient F)} (hD0 : D ≠ 0) (hnum0 : num ≠ 0)
    (hDambF : ∀ n, D.coeff n ∈ ambF F) (hNm : ∀ n, N.coeff n ∈ ambA F 0)
    (hnumrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D))
    (hNdeg : degPolyNu F 0 N = 0 ∨ degPolyNu F 0 N = Nat.card F) :
    degPolyNu F 0 (num + N * D) = 2 * Nat.card F := by
  have hDmA0 : ∀ n, D.coeff n ∈ ambA F 0 := fun n => ambF_subset_ambA_zero (F := F) (hDambF n)
  have hnumA0 : ∀ n, num.coeff n ∈ ambA F 0 :=
    coeff_mem_ambA_zero_of_kuanLin (F := F) (m := w) (by omega) (ε := 1) (δ := num)
      (ambF F).one_mem
      (fun j => coeff_mul_mem_ambA (fun n => coeff_mul_mem_ambA hNm hDmA0 n)
        (coeff_X_sub_C_theta_pow_pow_mem_ambA 0 w) j)
      (by rw [hnumrec, Polynomial.C_1, one_mul]; ring)
  have hdeg := degPolyNu_recursion (F := F) (num := num) (D := D) (N := N)
    hnum0 hD0 hnumA0 hDmA0 hNm hnumrec
  have ht := degPolyNu_num_eq_two_card (F := F) hq hwk hD0 hnum0 hDambF hNm hnumrec hNdeg
  rw [ht, hwk] at hdeg
  rw [show (2 * Nat.card F - 2) * Nat.card F
      = 2 * Nat.card F * Nat.card F - 2 * Nat.card F from Nat.sub_mul _ _ _] at hdeg
  rw [show Nat.card F * (2 * Nat.card F) = 2 * Nat.card F * Nat.card F from by ring] at hdeg
  set A : ℕ := 2 * Nat.card F * Nat.card F with hA
  set B : ℕ := 2 * Nat.card F with hB
  have hAB : B ≤ A := by
    rw [hA, hB]
    nlinarith [two_le_ambCard F]
  have he : A = A - B + degPolyNu F 0 (num + N * D) := hdeg
  have hfin : degPolyNu F 0 (num + N * D) = B := by omega
  rw [hfin, hB]

/-!
## REMAINING WIRING (next session)

`TwRowFalse F (2q-2)` is assembled exactly as in `EndgameTwRow.TwRowFalse_of_not_dvd` (copy its
body verbatim: `tw_Y_mul_p_eq` → `Q`, `Y` → `Z ≠ 0` → `hrec` → `exists_integral_recursion` →
`num, D`), but in the form

```
theorem TwRowFalse_of_eq_two_card_aux {w : ℕ} (hq : 3 ≤ Nat.card F)
    (hw2 : w = 2 * Nat.card F - 2) : TwRowFalse F w := by
  have hqw : Nat.card F < w := by omega
  classical
  intro k hw hk hwk hkq A₁ A₂ hA₁inv hA₂inv hA₁ne hA₂ne hval
  <body of TwRowFalse_of_not_dvd verbatim up to `exists_integral_recursion`>
  ...
theorem TwRowFalse_of_eq_two_card (hq : 3 ≤ Nat.card F) :
    TwRowFalse F (2 * Nat.card F - 2) := TwRowFalse_of_eq_two_card_aux F hq rfl
```

so that `w` stays in scope, and with the following tail:

* `set Nm := (X^q - X) * (A₁ * ambH F w) - A₂ * (X^q - C(θ^q))` with `hNms`;
* `set P  := X^q - X`, `set Lam := X^q - C(θ^q)`, `set Mm := A₁ * P * C((w - q : ℕ) : Ambient F) - A₂`
  and `hNmdecomp : Nm = A₁*P^2 + Mm*Lam` (from `ambH_factor_of_lt` + `X_sub_C_pow_card` + `ring`);
* **`hNsupp : ∀ n j, ¬ q ∣ j → coeffNu F 0 j (Nm.coeff n) = 0`** — the one genuinely new sub-lemma:
  `rw [hNmdecomp, Polynomial.coeff_add, coeffNu_add F _ _]` and kill the two summands:
  `A₁*P^2` is `θ`-free (`coeff_mul_mem_ambF` + `coeffNu_eq_zero_of_mem_ambF`), and
  `Mm*Lam` has `θ`-support `⊆ {0, q}` because `(Lam).coeff b` is `0` except for `b = q` (value `1`)
  and `b = 0` (value `-θ^q`), so `coeffNu F 0 j (Lam.coeff b) = 0` whenever `j ≠ 0` and `j ≠ q`
  (`coefficientwise`: `coeff_C_mem_ambA`, `Polynomial.coeff_sub`, `coeffNu_*`);
* `V := qthRootPoly F (num + Nm*D) hmem`, `hV1`, `hVσ`, `hnumV` (`num_eq_L_pow_mul_qthRoot`),
  `hbound` (`qthRootPoly_degNu_one_le` + **`degPolyNu_add_eq_two_card`** above),
  `hV0`/`hVd2` (`V_support_and_deg`);
* `hnumq : ∀ j ∉ qℤ, tp F (L^w * V) j = 0` — `rw [← hnumV]` and `tp_num_eq_zero F hV0 hnumA0 hNm
  hVσ hNsupp hDambF`  (the `hnumA0` = `coeff_mem_ambA_zero_of_kuanLin` line, as in `dvd_pred_of_data`);
* the endgame: `D_one_eq`, `D_zero_eq`, `V_eq_D2_mul_sq` (with `cast_two_card_sub_two`,
  `cast_choose_two_two_card_sub_two`), `num_eq_D2_mul_theta`, `num = D₂·L^{2q}`, `ND_eq`,
  `contradiction_of_ND`.
-/

end ZagierHoffmanPositiveChar
