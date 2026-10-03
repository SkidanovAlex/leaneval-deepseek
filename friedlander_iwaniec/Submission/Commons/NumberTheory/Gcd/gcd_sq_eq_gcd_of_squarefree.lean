import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

namespace Commons.NumberTheory.Gcd

/-- For squarefree `m`, squaring the first argument of `gcd` changes nothing:
`gcd (c ^ 2) m = gcd c m`. -/
theorem gcd_sq_eq_gcd_of_squarefree {c m : ℕ} (hm : Squarefree m) :
    Nat.gcd (c ^ 2) m = Nat.gcd c m := by
  refine Nat.dvd_antisymm ?_ ?_
  · -- `gcd (c^2) m` divides `m`, hence is squarefree, so it divides `c` since it divides `c^2`
    have hgm : Nat.gcd (c ^ 2) m ∣ m := Nat.gcd_dvd_right _ _
    have hgc2 : Nat.gcd (c ^ 2) m ∣ c ^ 2 := Nat.gcd_dvd_left _ _
    have hgsq : Squarefree (Nat.gcd (c ^ 2) m) := hm.squarefree_of_dvd hgm
    have hgc : Nat.gcd (c ^ 2) m ∣ c :=
      (Squarefree.dvd_pow_iff_dvd hgsq (by norm_num)).mp hgc2
    exact Nat.dvd_gcd hgc hgm
  · -- `gcd c m` divides `c` hence `c^2`, and divides `m`
    exact Nat.dvd_gcd
      (by rw [pow_two]; exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left c m) c)
      (Nat.gcd_dvd_right c m)

end Commons.NumberTheory.Gcd