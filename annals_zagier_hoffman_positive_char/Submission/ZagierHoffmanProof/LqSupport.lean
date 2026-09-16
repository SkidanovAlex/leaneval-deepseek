import Submission.ZagierHoffmanProof.EndgameRow

/-!
# The `θ`-support of `L^q = (X - C θ)^q`

The `d_0`/`d_1` bookkeeping of the `k = q-1` two-term endgame
(`Submission/PLAN.md` §«SESSION 354» §«continued 10»):

`δ₂ + A₁H_w = -A₂·L^q/P + A₁·P + A₁(w-q)·L^q`, and in characteristic `p`
**`L^q = (X - C θ)^q = X^q - C (θ^q)`**, so `L^q` has exactly two `θ`-coefficients, at `θ^0` and
`θ^q`.  Hence the `θ^0`- and `θ^q`-coefficients of `δ₂ + A₁H_w` are

  `d_0 = -A₂X^q/P + A₁P + A₁(w-q)X^q`,   `d_1 = A₂/P - A₁(w-q)`

(after clearing the denominator `P`), which is what `(E0)` and `(E1)` read off.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ `(X - C θ)^q = X^q - C (θ^q)` — Freshman's dream. -/
lemma Lq_eq :
    ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F : Polynomial (Ambient F))
      = Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :=
  X_sub_C_pow_card F (ambTheta F)

@[simp] lemma coeff_Lq_zero :
    ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff 0 = -((ambTheta F) ^ Nat.card F) := by
  rw [Lq_eq, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    if_neg (Ne.symm (FrobPow.ne_zero (Ambient F) (q := Nat.card F))), if_pos rfl]
  ring

@[simp] lemma coeff_Lq_card :
    ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff (Nat.card F) = 1 := by
  rw [Lq_eq, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    if_pos rfl, if_neg (FrobPow.ne_zero (Ambient F) (q := Nat.card F))]
  ring

/-- ★★ **The `θ`-support of `L^q` is `{0, q}`.** -/
lemma coeff_Lq_of_ne {m : ℕ} (h0 : m ≠ 0) (hm : m ≠ Nat.card F) :
    ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff m = 0 := by
  rw [Lq_eq, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    if_neg hm, if_neg h0]
  ring

/-! ## §2. The level-`0` data of the two-term endgame (naming step) -/

/-- The endgame's `w = 2q - 2`. -/
noncomputable def twW (F : Type*) [Field F] [Finite F] : ℕ := 2 * Nat.card F - 2

/-- The endgame's `L = X - C θ`. -/
noncomputable def twL (F : Type*) [Field F] [Finite F] : Polynomial (Ambient F) :=
  Polynomial.X - Polynomial.C (ambTheta F)

@[simp] lemma twL_apply :
    twL F = (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)) := rfl

@[simp] lemma twW_apply : twW F = 2 * Nat.card F - 2 := rfl

lemma twL_ne_zero : twL F ≠ 0 := by
  rw [twL_apply]; exact Polynomial.X_sub_C_ne_zero _

/-- `L^q = X^q - C(θ^q)` — the Freshman's dream, in the endgame's notation. -/
lemma twL_pow_card :
    (twL F) ^ Nat.card F
      = Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :=
  Lq_eq F

/-- `L` is monic of `X`-degree one: the `X`-coefficient of `L` is `1`. -/
@[simp] lemma twL_coeff_one : (twL F).coeff 1 = 1 := by
  rw [twL_apply, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
    if_pos rfl, if_neg (by norm_num : ¬ (1 : ℕ) = 0)]
  ring

end ZagierHoffmanPositiveChar
