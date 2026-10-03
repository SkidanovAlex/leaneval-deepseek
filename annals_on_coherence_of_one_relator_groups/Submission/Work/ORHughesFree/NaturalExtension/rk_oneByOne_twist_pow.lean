import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Mapping a function over a `1 × 1` matrix scales its unique entry. -/
private theorem oneByOne_map {R S : Type*} (f : R → S) (a : R) :
    (Work.ORHughesFree.oneByOne a).map f = Work.ORHughesFree.oneByOne (f a) := by
  ext i j
  simp [Work.ORHughesFree.oneByOne]

/-- In `Multiplicative ℤ`, the `c`-th power of `ofAdd 1` is `ofAdd (c : ℤ)`. -/
private theorem ofAdd_natCast_eq_pow (c : ℕ) :
    (Multiplicative.ofAdd ((c : ℕ) : ℤ) : Multiplicative ℤ)
      = Multiplicative.ofAdd (1 : ℤ) ^ c := by
  rw [← nsmul_one c]
  rfl

theorem rk_oneByOne_twist_pow {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : Work.ORHughesFree.SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (a : U) (c : ℕ) :
    rk.rk 1 1 (Work.ORHughesFree.oneByOne ((Multiplicative.ofAdd ((c : ℕ) : ℤ)) • a))
      = rk.rk 1 1 (Work.ORHughesFree.oneByOne a) := by
  have hmain : ∀ k : ℕ,
      rk.rk 1 1 (Work.ORHughesFree.oneByOne ((Multiplicative.ofAdd (1 : ℤ)) ^ k • a))
        = rk.rk 1 1 (Work.ORHughesFree.oneByOne a) := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ', mul_smul, ← oneByOne_map]
      rw [hτ 1 1 (Work.ORHughesFree.oneByOne ((Multiplicative.ofAdd (1 : ℤ)) ^ n • a)), ih]
  rw [ofAdd_natCast_eq_pow c]
  exact hmain c

end Work.ORHughesFree.NaturalExtension
