import Submission.ZagierHoffmanProof.EndgameDeg

/-!
# The two row identities of the two-term endgame (ND21 §6, IMKDP §3.3)

The two surviving rows of the two-term datum `{(w), (k, q-1)}` (`w = k + q - 1 = q + (k-1)`) are

* **(A)** `Q · σ(Y) = σ(Q) · (X - θ^q)^{q-1} · (Y + Q·A₂)`   (the `(k)`-column),
* **(R)** `Q · σ(Z) = σ(Q) · (X - θ^q)^w · (Z + Y + Q·A₁·H_w)`   (the empty column),

where `σ = polyTwist 1` (coefficientwise `q`-th power, `X` fixed) — see
`Submission/ZagierHoffmanProof/Endgame2.lean` (`tmB_nil_row`, `tmB_col_eq`) and
`PLAN.md` §«SESSION 352».

This module proves the FIRST of the two consequences, Dac's **(6.4) solved without any integrality
hypothesis**:

> **`Y · (X^q - X) = A₂ · (θ^q - X^q) · Q`   (★)**

The proof is the "Mahler degree trick": the polynomial
`G := Y·(X^q - X) - A₂·(θ^q - X^q)·Q` satisfies the *homogeneous* equation
`Q · σ(G) = σ(Q) · (X - θ^q)^{q-1} · G`, whose two sides have `X`-degrees differing by `q - 1 ≥ 1`.
Hence `G = 0`.

(★) is what makes the endgame's `θ`-degree bound accessible: it gives `(X - θ)^q ∣ Y` and
`P = X^q - X ∣ A₂·Q`, so that the empty row becomes a `σ`-equation in `u` with `Z = (X-θ)^w·u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. Preliminaries: injectivity of `σ`, and `X^q - X` is `σ`-fixed -/

/-- `X^q - X` has `F_q`-coefficients, hence is fixed by `σ`. -/
lemma polyTwist_X_pow_sub_X :
    polyTwist (K := Ambient F) (q := Nat.card F) 1
        (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F))
      = (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) := by
  refine (polyTwist_one_eq_self_iff F _).mpr fun n => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  by_cases h1 : n = Nat.card F
  · rw [if_pos h1]
    by_cases h2 : (1 : ℕ) = n
    · rw [if_pos h2, sub_self]; exact (ambF F).zero_mem
    · rw [if_neg h2, sub_zero]; exact (ambF F).one_mem
  · rw [if_neg h1]
    by_cases h2 : (1 : ℕ) = n
    · rw [if_pos h2, zero_sub]; exact (ambF F).neg_mem (ambF F).one_mem
    · rw [if_neg h2, sub_zero]; exact (ambF F).zero_mem

/-! ## §2. The `σ`-behaviour of `D := θ^q - X^q` and of `W := X - θ^q` -/

lemma polyTwist_theta_pow_sub_X_pow :
    polyTwist (q := Nat.card F) 1
        (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      = Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F))
        - Polynomial.X ^ Nat.card F := by
  have hexp : ((ambTheta F) ^ Nat.card F) ^ (Nat.card F ^ 1)
      = (ambTheta F) ^ (Nat.card F * Nat.card F) := by
    rw [pow_one, ← pow_mul]
  rw [polyTwist_sub, polyTwist_C, polyTwist_pow, polyTwist_X, hexp]

/-- The Frobenius identity `(X - θ^q)^q = X^q - θ^{q·q}`. -/
lemma X_sub_C_theta_pow_card :
    (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ Nat.card F
      = Polynomial.X ^ Nat.card F
        - Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F)) := by
  rw [X_sub_C_pow_card F ((ambTheta F) ^ Nat.card F), ← pow_mul]

/-- ★ **`σ(D) = (D + P)·W^{q-1}`** where `D = θ^q - X^q`, `P = X^q - X`, `W = X - θ^q`. -/
lemma polyTwist_theta_pow_sub_X_pow_eq :
    polyTwist (q := Nat.card F) 1
        (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      = ((Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
          + (Polynomial.X ^ Nat.card F - Polynomial.X))
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hpowS : ∀ R : Polynomial (Ambient F),
      R ^ Nat.card F = R * R ^ (Nat.card F - 1) := by
    intro R
    conv_lhs => rw [show Nat.card F = Nat.card F - 1 + 1 from by omega, pow_succ']
  have hDP : (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      + (Polynomial.X ^ Nat.card F - Polynomial.X)
      = -(Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by ring
  calc polyTwist (q := Nat.card F) 1
        (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      = Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F))
        - Polynomial.X ^ Nat.card F := polyTwist_theta_pow_sub_X_pow F
    _ = -((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ Nat.card F) := by
          rw [X_sub_C_theta_pow_card F]; ring
    _ = -((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)) := by
          rw [hpowS]
    _ = ((Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
          + (Polynomial.X ^ Nat.card F - Polynomial.X))
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1) := by
          rw [hDP]; ring

/-! ## §3. Dac's (6.4): the `(k)`-row forces `Y·(X^q - X) = A₂·(θ^q - X^q)·Q` -/

/-- ★ **The `(k)`-row of the two-term datum, solved without any integrality hypothesis.**
If `Q ≠ 0` and
`Q·σ(Y) = σ(Q)·(X - θ^q)^{q-1}·(Y + Q·A₂)`   with `A₂ ∈ F_q[X]`,
then the polynomial `G := Y·(X^q - X) - A₂·(θ^q - X^q)·Q` satisfies the homogeneous equation
`Q·σ(G) = σ(Q)·(X - θ^q)^{q-1}·G`, whose two sides have `X`-degrees differing by `q - 1 ≥ 1`;
hence `G = 0`, i.e. Dac's (6.4) in its explicit form. -/
theorem tw_k_row_factor {A₂ Q Y : Polynomial (Ambient F)}
    (hQ0 : Q ≠ 0) (hA₂ : ∀ n, A₂.coeff n ∈ ambF F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Y + Q * A₂)) :
    Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  set W : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)
    with hW
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hP
  set D : Polynomial (Ambient F) :=
    Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F with hD
  set G : Polynomial (Ambient F) := Y * P - A₂ * D * Q with hG
  have hrow' : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q * W ^ (Nat.card F - 1) * (Y + Q * A₂) := by
    rw [hW]; exact hrow
  have hA₂fix : polyTwist (q := Nat.card F) 1 A₂ = A₂ := polyTwist_one_fixed F A₂ hA₂
  have hPfix : polyTwist (q := Nat.card F) 1 P = P := by
    rw [hP]; exact polyTwist_X_pow_sub_X F
  have hDfix : polyTwist (q := Nat.card F) 1 D = (D + P) * W ^ (Nat.card F - 1) := by
    rw [hD, hP, hW]; exact polyTwist_theta_pow_sub_X_pow_eq F
  have hmain : Q * polyTwist (q := Nat.card F) 1 G
      = polyTwist (q := Nat.card F) 1 Q * W ^ (Nat.card F - 1) * G := by
    have hexp : polyTwist (q := Nat.card F) 1 G
        = polyTwist (q := Nat.card F) 1 Y * P
          - A₂ * ((D + P) * W ^ (Nat.card F - 1)) * polyTwist (q := Nat.card F) 1 Q := by
      simp only [hG, polyTwist_sub, polyTwist_mul, hPfix, hA₂fix, hDfix] <;> ring
    rw [hexp, mul_sub,
      show Q * (polyTwist (q := Nat.card F) 1 Y * P)
          = (Q * polyTwist (q := Nat.card F) 1 Y) * P from by ring,
      hrow', hG]
    ring
  have hGzero : G = 0 := by
    by_contra hG0
    have hGσ : polyTwist (q := Nat.card F) 1 G ≠ 0 := by
      intro h
      exact hG0 (polyTwist_one_injective F (by simpa using h))
    have hQσ : polyTwist (q := Nat.card F) 1 Q ≠ 0 := by
      intro h
      exact hQ0 (polyTwist_one_injective F (by simpa using h))
    have hW0 : W ≠ 0 := by rw [hW]; exact Polynomial.X_sub_C_ne_zero _
    have hWe : W ^ (Nat.card F - 1) ≠ 0 := pow_ne_zero _ hW0
    have hdeg : Q.natDegree + G.natDegree
        = Q.natDegree + (Nat.card F - 1) + G.natDegree := by
      calc Q.natDegree + G.natDegree
          = (Q * polyTwist (q := Nat.card F) 1 G).natDegree := by
              rw [Polynomial.natDegree_mul hQ0 hGσ, polyTwist_one_natDegree]
        _ = (polyTwist (q := Nat.card F) 1 Q * W ^ (Nat.card F - 1) * G).natDegree := by
              rw [hmain]
        _ = Q.natDegree + (Nat.card F - 1) + G.natDegree := by
              rw [Polynomial.natDegree_mul (mul_ne_zero hQσ hWe) hG0,
                Polynomial.natDegree_mul hQσ hWe, Polynomial.natDegree_pow,
                show W.natDegree = 1 from by rw [hW]; exact Polynomial.natDegree_X_sub_C _,
                polyTwist_one_natDegree]
              ring
    omega
  rw [hG] at hGzero
  exact sub_eq_zero.mp hGzero

end ZagierHoffmanPositiveChar
