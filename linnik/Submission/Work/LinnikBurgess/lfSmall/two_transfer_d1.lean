import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.defect1_mul_Uval
import Submission.Work.LinnikBurgess.val_dvd_iff_castHom_eq_zero

/-!
# The first defect transfer for `p = 2` (`two_transfer_d1`)

The identity `defect1_mul_Uval` reads, in `ZMod (2^e)`,

  `D₁(y) · U(y) = N(y)`   (`D₁ = defect1 2 e a b y`, `U = Uval y a b`, `N = critN a b`),

and at a unit point `y` (`UnitAt 2 y a b`) the factor `U(y) = (∏ (y+a_l))·(∏ (y+b_l))` is **odd**,
hence a unit of `ZMod (2^k)` for every `k`.  Reducing the identity modulo `2^k` (`k ≤ e`) and
cancelling this unit therefore gives

  `D₁(y) = 0` in `ZMod (2^k)`  ↔  `N(y) = 0` in `ZMod (2^k)`,

and since `2^k ∣ c.val ↔ c = 0` in `ZMod (2^k)` for `c : ZMod (2^e)` (`k ≤ e`), while
`(2^k : ℤ) ∣ z ↔ z = 0` in `ZMod (2^k)`, this is precisely the claimed transfer
`2^k ∣ (D₁(y)).val ↔ (2^k : ℤ) ∣ N(y)`.
-/

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess

/-- At a unit point the product `(y + a 0)(y + a 1)(y + a 2)` is odd. -/
private lemma not_two_dvd_sh3 {y : ℕ} {a : Fin 3 → ℕ} (h : ∀ l, ¬ 2 ∣ y + a l) :
    ¬ 2 ∣ sh3 y a := by
  intro hd
  rw [sh3] at hd
  rcases Nat.prime_two.dvd_mul.mp hd with h01 | h2
  · rcases Nat.prime_two.dvd_mul.mp h01 with h0 | h1
    · exact h 0 h0
    · exact h 1 h1
  · exact h 2 h2

/-- At a unit point `y` the product `U(y) = f_a(y) f_b(y)` is odd, hence invertible modulo `2^k`. -/
private lemma not_two_dvd_Uval {y : ℕ} {a b : Fin 3 → ℕ} (hy : UnitAt 2 y a b) :
    ¬ 2 ∣ Uval y a b := by
  intro hd
  rw [Uval] at hd
  rcases Nat.prime_two.dvd_mul.mp hd with h | h
  · exact not_two_dvd_sh3 (fun l => (hy l).1) h
  · exact not_two_dvd_sh3 (fun l => (hy l).2) h

theorem two_transfer_d1 {e k : ℕ} (he : 1 ≤ e) (hk : k ≤ e) (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt 2 y a b) :
    (2 ^ k ∣ (defect1 2 e a b y).val) ↔ ((2 ^ k : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
  have hdiv : 2 ^ k ∣ 2 ^ e := pow_dvd_pow 2 hk
  -- `U(y)` is odd, hence a unit modulo `2 ^ k`
  have hunitU : IsUnit (((Uval y a b : ℕ)) : ZMod (2 ^ k)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (((Nat.prime_two.coprime_iff_not_dvd).mpr (not_two_dvd_Uval hy)).pow_left k).symm
  -- the defect identity, reduced modulo `2 ^ k`
  have hEq : (ZMod.castHom hdiv (ZMod (2 ^ k)) (defect1 2 e a b y))
        * (((Uval y a b : ℕ)) : ZMod (2 ^ k))
      = (((critN a b).eval (y : ℤ) : ℤ) : ZMod (2 ^ k)) := by
    have h := defect1_mul_Uval (p := 2) (e := e) a b hy
    have h2 := congrArg (ZMod.castHom hdiv (ZMod (2 ^ k))) h
    simpa only [map_mul, map_natCast, map_intCast] using h2
  rw [Work.LinnikBurgess.val_dvd_iff_castHom_eq_zero hdiv (defect1 2 e a b y)]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← hEq]
  exact (IsUnit.mul_left_eq_zero hunitU).symm

end Work.LinnikBurgess.lfSmall
