/-
The Hilbert symbol at a finite odd place of `ℚ` satisfies `(a, -a)_p = 1`: the quaternion
algebra `(a, -a)` splits, since `x² - a y² + a z²` has the nontrivial zero `(0, 1, 1)`.

This file verifies the identity directly from the explicit formula which *defines*
`hilbertSymbolOdd`.  Writing `v = v_p(a)`, `c = (p-1)/2`, `L = (u(a)/p)` and
`M = (-1/p) = (-1)^c` one has `L * L = 1` and

  `(a, -a)_p = (-1)^{v² c} · L^v · (M·L)^v = (-1)^{v² c} · M^v · (L·L)^v
             = (-1)^{v² c + c v} = (-1)^{c·v·(v+1)} = 1`,

because `v (v+1)` is even.  The only non-formulaic input is the supplementary law
`(-1/p) = (-1)^{(p-1)/2}`.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.legendreOf_intUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- Transporting the even/odd parity of `(-1)^n ∈ ℤ` to the group of units `ℤˣ`. -/
private theorem intUnitOf_neg_one_pow (n : ℕ) :
    intUnitOf ((-1 : ℤ) ^ n) = (-1 : ℤˣ) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, intUnitOf_one, h.neg_one_pow]
  · rw [h.neg_one_pow, intUnitOf_neg_one, h.neg_one_pow]

/-- The quartic character `χ₄` evaluated at an odd natural number. -/
private theorem chi4_nat_of_odd (p : ℕ) (hp : p % 2 = 1) :
    ZMod.χ₄ (p : ZMod 4) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four p, if_neg (by omega : ¬ p % 2 = 0)]
  by_cases h : p % 4 = 1
  · rw [if_pos h, eq_comm, neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)]
    exact Nat.even_iff.mpr (by omega)
  · rw [if_neg h, eq_comm, neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)]
    exact Nat.odd_iff.mpr (by omega)

/-- A prime `p` does not divide `-1`. -/
private theorem prime_not_dvd_neg_one (p : ℕ) [Fact p.Prime] : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
  intro hd
  have hd1 : (p : ℤ) ∣ (1 : ℤ) := dvd_neg.mp hd
  have hu : IsUnit (p : ℤ) := isUnit_of_dvd_one hd1
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · exact (Fact.out : p.Prime).ne_one (by exact_mod_cast h1)
  · have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
    omega

/-- `-1` as an element of `ℚˣ` is `intUnit (-1)`. -/
private theorem intUnit_neg_one : intUnit (-1) (by norm_num) = (-1 : ℚˣ) := by
  ext; simp [intUnit, ratUnit]

/-- The supplementary law `(-1/p) = (-1)^{(p-1)/2}` for the Legendre symbol of the unit part,
in the form used by the Hilbert symbol at the finite places. -/
private theorem legendreOf_neg_one (p : ℕ) [Fact p.Prime] :
    legendreOf p (-1) = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) := by
  have hbase : legendreOf p (-1) = intUnitOf (legendreSym p (-1)) := by
    rw [← legendreOf_intUnit (m := -1) (by norm_num) (prime_not_dvd_neg_one p), intUnit_neg_one]
  rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with hp | hp
  · subst hp
    rw [hbase]
    norm_num [legendreSym]
  · have hpne : p ≠ 2 := by rintro rfl; omega
    rw [hbase, legendreSym.at_neg_one hpne, chi4_nat_of_odd p hp, intUnitOf_neg_one_pow,
      zpow_natCast]

/-- Two copies of a unit of `ℤ` multiply to `1`. -/
private theorem intUnit_mul_self' (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

/-- Rearrangement of a product of four group elements in an abelian group. -/
private theorem mul_rearrange {G : Type*} [CommGroup G] (A L P : G) :
    A * L * (P * L) = A * P * (L * L) := by
  simp only [mul_left_comm, mul_comm]

/-- `(-1)^{v² c + c v} = 1`, because `v(v+1)` is even. -/
private theorem negOne_pow_vsq_add (v c : ℤ) : (-1 : ℤˣ) ^ (v * v * c + c * v) = 1 := by
  have he : Even (v * v * c + c * v) := by
    rw [show v * v * c + c * v = c * (v * (v + 1)) by ring]
    exact (Int.even_mul_succ_self v).mul_left c
  exact (Int.negOnePow_eq_one_iff _).mpr he

theorem hilbertSymbolOdd_neg_self (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    hilbertSymbolOdd p a (-a) = 1 := by
  have hM : legendreOf p (-1) = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) := legendreOf_neg_one p
  have hneg : padicVal p (-a) = padicVal p a := padicVal_neg p a
  have hleg : legendreOf p (-a) = legendreOf p (-1) * legendreOf p a := by
    rw [← neg_one_mul, legendreOf_mul]
  have hLL : legendreOf p a * legendreOf p a = 1 := intUnit_mul_self' _
  rw [hilbertSymbolOdd, hneg, hleg, hM, mul_zpow, ← zpow_mul, mul_rearrange,
      ← mul_zpow, hLL, one_zpow, mul_one, ← zpow_add]
  exact negOne_pow_vsq_add (padicVal p a) (((p - 1) / 2 : ℕ) : ℤ)

end Work.HilbertSymbol
