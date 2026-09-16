import Submission.ZagierHoffmanProof.EndgameFinal

/-!
# SESSION 360 — `TwRowFalse` at `(q-1) ∤ w`

`PLAN.md` §«SESSION 360» §5.5.  The mathematical content is
`EndgameFinal.dvd_pred_of_data` (`(q-1) ∣ w` from the `θ`-degree data) and
`EndgameFinal.dvd_pred_of_rows` (the same from the two rows); this module only *wires* the `(LD)`
hypothesis of `TwRowFalse` to `tw_Y_mul_P_eq` + `dvd_pred_of_data`.  The wiring is done with the
hypotheses already abbreviated by `set` (the raw `P none` / `P (some (twK …))` terms make the
elaborator's `whnf` blow up).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open Polynomial
open scoped Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★★★ **`TwRowFalse` at `(q-1) ∤ w` and `q < w`** — i.e. for every `q < w < 2q-2`.  The only
weight at which `TwRowFalse` can still fail is `w = 2q-2` (Dac §6's explicit computation). -/
theorem TwRowFalse_of_not_dvd {w : ℕ} (hq : 3 ≤ Nat.card F) (hqw : Nat.card F < w)
    (hne : ¬ (Nat.card F - 1) ∣ w) : TwRowFalse F w := by
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
  exact False.elim (hne (dvd_pred_of_data (F := F) hq hqw hD0 hnum0 hDambF
    (twN_coeff_mem (F := F) hA₁m hA₂m) hnumrec
    (degPolyNu_N_eq_zero_or_card (F := F) (A₁ := A₁) (A₂ := A₂) (w := w) (by omega) hA₁m hA₂m)))

end ZagierHoffmanPositiveChar
