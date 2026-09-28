import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.GM.exists_not_dvd_mul_of_dvd_gcdMinors2_veronese
import Submission.Work.HP.GM.dvd_gcdMinors2_veronese_of_dvd
import Submission.Work.HP.GM.nat_eq_of_forall_prime_pow_dvd_iff

/-!
# `gcdMinors2_veronese_natAbs`

`gcdMinors2 x y` is the gcd of the `2 × 2` minors `x_i y_j - x_j y_i` of the two columns `x, y`.
This file proves that, for `d ≥ 1` and *primitive* `x, y : ℤ^{n+1}`, the gcd of the `2 × 2` minors
of the pair of Veronese vectors `(ν_{d,n}(x), ν_{d,n}(y))` has the same absolute value as the gcd
of the `2 × 2` minors of `(x, y)` — the paper's "Lemma G" (Browning–Le Boudec–Sawin), in the
sign-free form needed downstream.

Equivalently (and this is how it is proved): for every prime `p` and every `e ≥ 0`,
`p^e ∣ gcdMinors2 (νx) (νy) ↔ p^e ∣ gcdMinors2 x y`.

* `p^e ∣ gcdMinors2 x y ⟹ p^e ∣ gcdMinors2 (νx) (νy)`
  (`dvd_gcdMinors2_veronese_of_dvd`): if `x` is primitive at `p` then `y ≡ c·x (mod p^e)` for some
  `c` (`exists_lam_gcdMinors2`), hence `νy ≡ c^d·νx (mod p^e)` and every Veronese minor vanishes
  mod `p^e`.
* `p^e ∣ gcdMinors2 (νx) (νy) ⟹ p^e ∣ gcdMinors2 x y`
  (`dvd_gcdMinors2_of_dvd_veronese` below): by
  `exists_not_dvd_mul_of_dvd_gcdMinors2_veronese` there is a coordinate `j` with
  `p ∤ x_j y_j`; the Veronese minor indexed by the monomials `X_j^{d-1}X_k`, `X_j^{d-1}X_ℓ` is
  `(x_j y_j)^{d-1} (x_k y_ℓ - x_ℓ y_k)`, and the factor `(x_j y_j)^{d-1}` is a unit mod `p^e`, so it
  can be cancelled.
* `nat_eq_of_forall_prime_pow_dvd_iff` converts the prime-power equivalence into equality of the
  natural absolute values.
-/

set_option linter.unusedVariables false

namespace Work.HP.GM

open Work.HP

/-- **The reverse direction.** If the gcd of the `2 × 2` minors of the pair `(ν_{d,n}(x), ν_{d,n}(y))`
is divisible by `p^e`, then so is the gcd of the `2 × 2` minors of `(x, y)`.

(The hypothesis `1 ≤ d` and the primitivity of `x` and `y` enter through
`exists_not_dvd_mul_of_dvd_gcdMinors2_veronese`.) -/
theorem dvd_gcdMinors2_of_dvd_veronese (d n p e : ℕ) (hd : 1 ≤ d) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (h : (p : ℤ) ^ e ∣ gcdMinors2 (veronese d n x) (veronese d n y)) :
    (p : ℤ) ^ e ∣ gcdMinors2 x y := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  -- `p ∣ p^e`, so `p` divides the gcd of the Veronese minors
  have hp_dvd : (p : ℤ) ∣ (p : ℤ) ^ e := by
    simpa using pow_dvd_pow (p : ℤ) he
  -- a coordinate `j` whose product `x j * y j` is a unit mod `p`
  obtain ⟨j, hj⟩ := exists_not_dvd_mul_of_dvd_gcdMinors2_veronese d n p hd hp x y hx hy
    (dvd_trans hp_dvd h)
  have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  refine (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) x y).mpr (fun k l => ?_)
  -- the Veronese minor indexed by `X_j^{d-1} X_k` and `X_j^{d-1} X_ℓ`
  have hA : (p : ℤ) ^ e ∣
      veronese d n x (Work.HP.NA.monDij d n hd j k) * veronese d n y (Work.HP.NA.monDij d n hd j l)
        - veronese d n x (Work.HP.NA.monDij d n hd j l)
            * veronese d n y (Work.HP.NA.monDij d n hd j k) :=
    ((Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) (veronese d n x) (veronese d n y)).mp h)
      (Work.HP.NA.monDij d n hd j k) (Work.HP.NA.monDij d n hd j l)
  rw [Work.HP.NA.veronese_monDij d n hd x j k, Work.HP.NA.veronese_monDij d n hd y j l,
      Work.HP.NA.veronese_monDij d n hd x j l, Work.HP.NA.veronese_monDij d n hd y j k] at hA
  have hid : x j ^ (d - 1) * x k * (y j ^ (d - 1) * y l)
      - x j ^ (d - 1) * x l * (y j ^ (d - 1) * y k)
      = (x j * y j) ^ (d - 1) * (x k * y l - x l * y k) := by
    rw [mul_pow]; ring
  rw [hid] at hA
  -- cancel the unit `(x j * y j)^(d-1)`
  refine Work.HP.NA.dvd_of_dvd_mul_of_not_dvd_pow hpz (fun hc => hj ?_) hA
  exact hpz.dvd_of_dvd_pow hc

/-- **Lemma G of Browning–Le Boudec–Sawin**, in the sign-free form used downstream: for `1 ≤ d`,
`1 ≤ n` and primitive integer vectors `x, y` the gcd of the `2 × 2` minors of the pair of Veronese
vectors `(ν_{d,n}(x), ν_{d,n}(y))` has the same natural absolute value as the gcd of the `2 × 2`
minors of `(x, y)`. -/
theorem gcdMinors2_veronese_natAbs (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y) :
    (Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y)).natAbs
      = (Work.HP.gcdMinors2 x y).natAbs := by
  refine nat_eq_of_forall_prime_pow_dvd_iff (fun p e hp => ?_)
  rw [← Int.ofNat_dvd_left (n := p ^ e)
        (z := Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y)),
      ← Int.ofNat_dvd_left (n := p ^ e) (z := Work.HP.gcdMinors2 x y)]
  exact ⟨fun h => dvd_gcdMinors2_of_dvd_veronese d n p e hd hp x y hx hy h,
    fun h => dvd_gcdMinors2_veronese_of_dvd d n p e hp x y
      (exists_not_dvd_of_isPrim x hx hp) h⟩

end Work.HP.GM
