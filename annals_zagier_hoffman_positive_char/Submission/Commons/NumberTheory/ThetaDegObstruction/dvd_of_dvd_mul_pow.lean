import Mathlib.Data.Nat.GCD.Basic

namespace Commons.NumberTheory.ThetaDegObstruction

/-- If `q ≥ 2` and `q - 1` divides `w * q ^ ν`, then `q - 1` divides `w`:
coupling `q - 1` to `w` requires nothing of `q`, since `q` is coprime to `q - 1`. -/
theorem dvd_of_dvd_mul_pow {q w ν : ℕ} (hq : 2 ≤ q) (h : (q - 1) ∣ w * q ^ ν) : (q - 1) ∣ w := by
  have hcop : Nat.Coprime (q - 1) q := by
    have h1 : Nat.Coprime q 1 := Nat.coprime_one_right q
    exact ((Nat.coprime_self_sub_right (m := 1) (n := q) (by omega)).mpr h1).symm
  exact (hcop.pow_right ν).dvd_of_dvd_mul_right h

end Commons.NumberTheory.ThetaDegObstruction