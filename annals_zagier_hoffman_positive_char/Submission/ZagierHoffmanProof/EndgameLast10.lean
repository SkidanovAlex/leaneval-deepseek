import Submission.ZagierHoffmanProof.EndgameLast9

/-!
# SESSION 364 — the last case `w = 2q-2`: the wiring (item iii)

`PLAN.md` §«SESSION 363» §3.  `TwRowFalse F (2q-2)`: the body of
`EndgameTwRow.TwRowFalse_of_not_dvd` (rows via `tw_Y_mul_P_eq`, then `exists_integral_recursion`)
followed by the new endgame: the `q`-th root `V` of `num + Nm·D`, the two reads, `V = D₂·L²`,
`num = D₂·Λ²`, `N·D = D₂·P·(P-2Λ)` and the final contradiction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open Polynomial
open scoped Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem TwRowFalse_of_eq_two_card_aux {w : ℕ} (hq : 3 ≤ Nat.card F)
    (hw2 : w = 2 * Nat.card F - 2) : TwRowFalse F w := by
  have hqw : Nat.card F < w := by omega
  classical
  intro k hw hk hwk hkq A₁ A₂ hA₁inv hA₂inv hA₁ne hA₂ne hval
  obtain ⟨P, Z, _hPmem, hP0, _hZeq, hArow, hRrow⟩ :=
    tw_Y_mul_P_eq (F := F) hq hw hk hwk hkq A₁ A₂ hA₁inv hA₂inv hval
  set Q : Polynomial (Ambient F) := P none with hQs
  set Y : Polynomial (Ambient F) := P (some (twK F w k hw hk hkq)) with hYs
  have hA₁m : ∀ n, A₁.coeff n ∈ ambF F := coeff_mem_ambF_of_twA₂ (F := F) hA₁inv
  have hA₂m : ∀ n, A₂.coeff n ∈ ambF F := coeff_mem_ambF_of_twA₂ (F := F) hA₂inv
  -- `Z ≠ 0` (inlined from `tw_Z_ne_zero`, to keep the elaborator cheap)
  have hZ : Z ≠ 0 := by
    intro hZ0
    have hzerotw : polyTwist (q := Nat.card F) 1 (0 : Polynomial (Ambient F)) = 0 := by simp
    set W : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) with hWs
    set L : Polynomial (Ambient F) := Polynomial.X - Polynomial.C (ambTheta F) with hLs
    set P' : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hPs
    have hWne : W ≠ 0 := Polynomial.X_sub_C_ne_zero _
    have hPeval : P'.eval (ambTheta F) ≠ 0 := by
      rw [hPs]; exact eval_X_pow_sub_X_theta_ne_zero F hq
    have hσQ : polyTwist (q := Nat.card F) 1 Q ≠ 0 := fun h0 =>
      hP0 (polyTwist_one_injective F (by rw [h0, hzerotw]))
    have hsum : Q * (A₁ * ambH F w) + Y = 0 := by
      have h := hRrow
      rw [hZ0, hzerotw, mul_zero] at h
      have h2 : polyTwist (q := Nat.card F) 1 Q * W ^ w * (Q * (A₁ * ambH F w) + 0 + Y) = 0 := by
        rw [show polyTwist (q := Nat.card F) 1 Q * W ^ w * (Q * (A₁ * ambH F w) + 0 + Y)
            = polyTwist (q := Nat.card F) 1 Q * (W ^ w * (Q * (A₁ * ambH F w) + 0 + Y))
            from by ring]
        exact h.symm
      rcases mul_eq_zero.mp h2 with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 hσQ
        · exact absurd h4 (pow_ne_zero w hWne)
      · simpa using h3
    have hY : Y = -(Q * (A₁ * ambH F w)) := by linear_combination hsum
    have hmain : A₁ * ambH F w * P' = A₂ * L ^ Nat.card F := by
      have h := hArow
      rw [hY, C_theta_pow_sub_X_pow_eq_neg, ← hLs] at h
      have h3 : Q * (A₁ * ambH F w * P') = A₂ * L ^ Nat.card F * Q := by
        linear_combination -h
      exact mul_left_cancel₀ hP0 (by rw [h3]; ring)
    have hdvdpow : L ^ Nat.card F ∣ A₁ * ambH F w * P' := ⟨A₂, by rw [hmain]; ring⟩
    have hdvd : L ∣ A₁ * ambH F w * P' :=
      dvd_trans (dvd_pow_self L (by omega : Nat.card F ≠ 0)) hdvdpow
    have hprime : Prime L := by rw [hLs]; exact Polynomial.prime_X_sub_C _
    have hnotA₁ : ¬ L ∣ A₁ := by
      rw [hLs]; exact not_dvd_X_sub_C_theta_of_coeff_mem_ambF F hA₁m hA₁ne
    have hnotH : ¬ L ∣ ambH F w := by
      rw [hLs, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      exact ambH_eval_theta_ne_zero (F := F) w
    have hnotP : ¬ L ∣ P' := by
      rw [hLs, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      exact hPeval
    rcases hprime.dvd_or_dvd (by rwa [mul_assoc] at hdvd) with h | h
    · exact hnotA₁ h
    · rcases hprime.dvd_or_dvd h with h' | h'
      · exact hnotH h'
      · exact hnotP h'
  have hP0' : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) ≠ 0 := by
    intro h0
    have h1 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).eval
        (ambTheta F) = 0 := by rw [h0, Polynomial.eval_zero]
    exact eval_X_pow_sub_X_theta_ne_zero F hq h1
  have hPZ0 : (Polynomial.X ^ Nat.card F - Polynomial.X) * Z ≠ 0 := mul_ne_zero hP0' hZ
  have hrec : Q * polyTwist (q := Nat.card F) 1 ((Polynomial.X ^ Nat.card F - Polynomial.X) * Z)
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * ((Polynomial.X ^ Nat.card F - Polynomial.X) * Z
           + ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
              - A₂ * (Polynomial.X ^ Nat.card F
                  - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q) := by
    rw [polyTwist_mul, polyTwist_one_X_pow_sub_X]
    have hstep : Q * ((Polynomial.X ^ Nat.card F - Polynomial.X)
        * polyTwist (q := Nat.card F) 1 Z)
        = (Polynomial.X ^ Nat.card F - Polynomial.X)
          * (Q * polyTwist (q := Nat.card F) 1 Z) := by ring
    rw [hstep, hRrow]
    have hPY : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
        = -(A₂ * (Polynomial.X ^ Nat.card F
            - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
      rw [hArow]; ring
    have hPY' : (Polynomial.X ^ Nat.card F - Polynomial.X) * Y
        = -(A₂ * (Polynomial.X ^ Nat.card F
            - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
      rw [mul_comm]; exact hPY
    have hinner : (Polynomial.X ^ Nat.card F - Polynomial.X) * (Q * (A₁ * ambH F w) + Z + Y)
        = (Polynomial.X ^ Nat.card F - Polynomial.X) * Z
          + ((Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
             - A₂ * (Polynomial.X ^ Nat.card F
                - Polynomial.C ((ambTheta F) ^ Nat.card F))) * Q := by
      rw [mul_add, mul_add, hPY']; ring
    rw [show (Polynomial.X ^ Nat.card F - Polynomial.X)
          * (polyTwist (q := Nat.card F) 1 Q
              * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
                * (Q * (A₁ * ambH F w) + Z + Y)))
        = polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
          * ((Polynomial.X ^ Nat.card F - Polynomial.X) * (Q * (A₁ * ambH F w) + Z + Y))
        from by ring, hinner]
  obtain ⟨num, D, hD0, hDambF, hnum0, hnumrec⟩ :=
    exists_integral_recursion (F := F) (P := Polynomial.X ^ Nat.card F - Polynomial.X)
      (Z := Z) (Q := Q)
      (N := (Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
        - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) hP0 hPZ0 hrec
  have hq0 : 0 < Nat.card F := by omega
  set Nm : Polynomial (Ambient F) := (Polynomial.X ^ Nat.card F - Polynomial.X) * (A₁ * ambH F w)
    - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) with hNms
  have hNm : ∀ n, Nm.coeff n ∈ ambA F 0 := by
    rw [hNms]; exact twN_coeff_mem (F := F) hA₁m hA₂m
  have hNdeg : degPolyNu F 0 Nm = 0 ∨ degPolyNu F 0 Nm = Nat.card F := by
    rw [hNms]
    exact degPolyNu_N_eq_zero_or_card (F := F) (A₁ := A₁) (A₂ := A₂) (w := w) (by omega) hA₁m hA₂m
  have hnumA0 : ∀ n, num.coeff n ∈ ambA F 0 :=
    coeff_mem_ambA_zero_of_kuanLin (F := F) (m := w) (by omega) (ε := 1) (δ := num)
      (ambF F).one_mem
      (fun j => coeff_mul_mem_ambA (fun n => coeff_mul_mem_ambA hNm
        (fun n => ambF_subset_ambA_zero (F := F) (hDambF n)) n)
        (coeff_X_sub_C_theta_pow_pow_mem_ambA 0 w) j)
      (by rw [hnumrec, Polynomial.C_1, one_mul]; ring)
  have hmem : ∀ n, (num + Nm * D).coeff n ∈ ambA F 0 := fun n =>
    coeff_add_mem_ambA hnumA0
      (fun m => coeff_mul_mem_ambA hNm (fun m => ambF_subset_ambA_zero (F := F) (hDambF m)) m) n
  set V : Polynomial (Ambient F) := qthRootPoly F (num + Nm * D) hmem with hVs
  have hV1 : ∀ n, V.coeff n ∈ ambA F 1 := fun n => qthRootPoly_coeff_mem F hmem n
  have hVσ : polyTwist (q := Nat.card F) 1 V = num + Nm * D := polyTwist_qthRootPoly F hmem
  have hnumV : num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V :=
    num_eq_L_pow_mul_qthRoot (F := F) (w := w) (by rw [hNms]; exact hnumrec) hmem
  have hbound : ∀ n, degNu F 1 (V.coeff n) ≤ 2 * Nat.card F := fun n =>
    (qthRootPoly_degNu_one_le F hmem n).trans
      (le_of_eq (degPolyNu_add_eq_two_card F hq hw2 (D := D) (N := Nm) (num := num)
        hD0 hnum0 hDambF hNm (by rw [hNms]; exact hnumrec) hNdeg))
  obtain ⟨hV0, hVd2⟩ := V_support_and_deg (F := F) hV1 hnumA0 hnumV hbound hq
  have hnumq : ∀ j, ¬ Nat.card F ∣ j →
      tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) j = 0 := by
    intro j hj
    rw [← hnumV]
    refine tp_num_eq_zero (F := F) (V := V) (num := num) (N := Nm) (D := D)
      hV0 hnumA0 hNm hVσ ?_ hDambF j hj
    intro n k hk
    rw [hNms]
    exact coeffNu_Nm_eq_zero F hq hqw hA₁m hA₂m hk
  have hread1 := D_one_eq (F := F) (w := w) (V := V) hV0 hVd2 hnumq hq hw2
  have hread0 := D_zero_eq (F := F) (w := w) (V := V) hV0 hVd2 hnumq hq hw2
  have hD2m : ∀ n, (tp F V 2).coeff n ∈ ambF F := fun n => tp_coeff_mem_ambF F hV0 2 n
  have hVsq : V = tp F V 2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ 2 :=
    V_eq_D2_mul_sq (F := F) (w := w) (V := V) (D0 := tp F V 0) (D1 := tp F V 1)
      (D2 := tp F V 2) (tp_decomp F hV0 hVd2) hread1 hread0 (by rw [hw2]; exact cast_two_card_sub_two F)
      (by rw [hw2]; exact cast_choose_two_two_card_sub_two F hq)
  have hnumD2 : num = tp F V 2 * (Polynomial.X ^ Nat.card F
      - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2 :=
    num_eq_D2_mul_theta (F := F) (w := w) (V := V) (D1 := tp F V 1) (D2 := tp F V 2)
      hnumV hVsq hw2
  have hnumL : num = tp F V 2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ (2 * Nat.card F) := by
    rw [hnumD2, show 2 * Nat.card F = Nat.card F * 2 from by ring, pow_mul,
      X_sub_C_pow_card F (ambTheta F)]
  have hND := ND_eq (F := F) (w := w) (num := num) (N := Nm) (D := D) (D2 := tp F V 2)
    hw2 (by rw [hNms]; exact hnumrec) (fun n => hD2m n) hnumL
  exact contradiction_of_ND (F := F) (w := w) (A₁ := A₁) (A₂ := A₂) (D := D) (D2 := tp F V 2)
    hq hqw hw2 hA₁m hA₂m hDambF hD2m hA₂ne hD0 hND

/-- ★★★★★ **`TwRowFalse` at the last weight `w = 2q-2`.** -/
theorem TwRowFalse_of_eq_two_card (hq : 3 ≤ Nat.card F) :
    TwRowFalse F (2 * Nat.card F - 2) :=
  TwRowFalse_of_eq_two_card_aux F hq rfl

end ZagierHoffmanPositiveChar
