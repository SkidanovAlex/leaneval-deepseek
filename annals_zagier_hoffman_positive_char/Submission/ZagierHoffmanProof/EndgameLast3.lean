import Submission.ZagierHoffmanProof.EndgameLast2

/-!
# SESSION 362 — the last case `w = 2q-2`: the two `θ`-reads of `num = L^w·V`

`PLAN.md` §«SESSION 362».  Reading `num = L^w·V` at `θ`-degrees `w+1 = 2q-1` and `w = 2q-2` (both
outside `qℤ`, where `num ∈ F_q[θ^q][X]` vanishes) gives the two relations

  **(R1)** `D_1 = w·X·D_2`,   **(R2)** `D_0 = w·X·D_1 - C(w,2)·X²·D_2`,

with `D_i = tp F V i`.  Together with `w ≡ -2 (mod p)` and `w² - C(w,2) ≡ 1 (mod p)` these give
`V = D_2·L²` — Dac §6's explicit computation at `k = q-1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma not_dvd_two_card_sub_two (hq : 3 ≤ Nat.card F) : ¬ Nat.card F ∣ 2 * Nat.card F - 2 := by
  rintro ⟨k, hk⟩
  have h3 : Nat.card F ∣ 2 * Nat.card F - Nat.card F * k :=
    Nat.dvd_sub (dvd_mul_left (Nat.card F) 2) (dvd_mul_right (Nat.card F) k)
  have h4 : 2 * Nat.card F - Nat.card F * k = 2 := by omega
  rw [h4] at h3
  have := Nat.le_of_dvd (by norm_num : 0 < 2) h3
  omega

lemma not_dvd_two_card_sub_one (hq : 3 ≤ Nat.card F) : ¬ Nat.card F ∣ 2 * Nat.card F - 1 := by
  rintro ⟨k, hk⟩
  have h3 : Nat.card F ∣ 2 * Nat.card F - Nat.card F * k :=
    Nat.dvd_sub (dvd_mul_left (Nat.card F) 2) (dvd_mul_right (Nat.card F) k)
  have h4 : 2 * Nat.card F - Nat.card F * k = 1 := by omega
  rw [h4] at h3
  have := Nat.le_of_dvd (by norm_num : 0 < 1) h3
  omega

/-! ## §6. The two `θ`-reads of `num = L^w·V` -/

/-- ★★★★★ **Read A** (`θ`-degree `w+1 = 2q-1`): `D_1 = w·X·D_2`. -/
theorem D_one_eq {w : ℕ} {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hd : ∀ n, degNu F 0 (V.coeff n) ≤ 2)
    (hnum : ∀ j, ¬ Nat.card F ∣ j →
      tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) j = 0)
    (hq : 3 ≤ Nat.card F) (hw : w = 2 * Nat.card F - 2) :
    tp F V 1 = Polynomial.C ((w : ℕ) : Ambient F) * (Polynomial.X * tp F V 2) := by
  have hwe : (-1 : F) ^ w = 1 := by
    rw [hw]; exact Even.neg_one_pow ⟨Nat.card F - 1, by omega⟩
  have hwo : (-1 : F) ^ (w - 1) = -1 := by
    rw [hw]; exact Odd.neg_one_pow ⟨Nat.card F - 2, by omega⟩
  have hw1 : w + 1 = 2 * Nat.card F - 1 := by rw [hw]; omega
  have h1 : tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) (w + 1) = 0 := by
    refine hnum (w + 1) ?_
    rw [hw1]
    exact not_dvd_two_card_sub_one F hq
  rw [tp_L_pow_mul_add_one F hV hd hwe hwo (by omega : 1 ≤ w)] at h1
  have h3 : tp F V 1
      = -(tp F V 2 * (Polynomial.C (ambCoeff F (-(((w : ℕ)) : F))) * Polynomial.X)) := by
    linear_combination h1
  rw [h3, show ambCoeff F (-(((w : ℕ)) : F)) = -(((w : ℕ)) : Ambient F) from by
    rw [map_neg, map_natCast], Polynomial.C_neg]
  ring

/-- ★★★★★ **Read B** (`θ`-degree `w = 2q-2`): `D_0 = w·X·D_1 - C(w,2)·X²·D_2`. -/
theorem D_zero_eq {w : ℕ} {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hd : ∀ n, degNu F 0 (V.coeff n) ≤ 2)
    (hnum : ∀ j, ¬ Nat.card F ∣ j →
      tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) j = 0)
    (hq : 3 ≤ Nat.card F) (hw : w = 2 * Nat.card F - 2) :
    tp F V 0 = Polynomial.C ((w : ℕ) : Ambient F) * (Polynomial.X * tp F V 1)
      - Polynomial.C (((w.choose 2 : ℕ) : Ambient F)) * (Polynomial.X ^ 2 * tp F V 2) := by
  have hwe : (-1 : F) ^ w = 1 := by
    rw [hw]; exact Even.neg_one_pow ⟨Nat.card F - 1, by omega⟩
  have hwo : (-1 : F) ^ (w - 1) = -1 := by
    rw [hw]; exact Odd.neg_one_pow ⟨Nat.card F - 2, by omega⟩
  have hw2' : (-1 : F) ^ (w - 2) = 1 := by
    rw [hw]; exact Even.neg_one_pow ⟨Nat.card F - 2, by omega⟩
  have h1 : tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) w = 0 := by
    refine hnum w ?_
    rw [hw]
    exact not_dvd_two_card_sub_two F hq
  rw [tp_L_pow_mul_self F hV hd hwe hwo (by omega : 2 ≤ w) hw2'] at h1
  have h3 : tp F V 0
      = -(tp F V 1 * (Polynomial.C (ambCoeff F (-(((w : ℕ)) : F))) * Polynomial.X)
        + tp F V 2 * (Polynomial.C (ambCoeff F (((w.choose 2 : ℕ) : F))) * Polynomial.X ^ 2)) := by
    linear_combination h1
  rw [h3, show ambCoeff F (-(((w : ℕ)) : F)) = -(((w : ℕ)) : Ambient F) from by
      rw [map_neg, map_natCast],
    show ambCoeff F (((w.choose 2 : ℕ) : F)) = (((w.choose 2 : ℕ)) : Ambient F) from by
      rw [map_natCast],
    Polynomial.C_neg]
  ring

end ZagierHoffmanPositiveChar
