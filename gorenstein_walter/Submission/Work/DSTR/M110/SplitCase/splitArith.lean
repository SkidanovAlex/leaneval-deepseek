import Mathlib
import Submission.Work.DSTR.M110.arithOrbitSubOne

namespace Work.DSTR.M110.SplitCase

/-- Arithmetic core of the split case: writing `N = p ^ (r * g) - 1 = ((p ^ g) ^ r - 1)`,
the `r`-power part of `N` (with `r` an odd prime) is strictly smaller than the cofactor
`N / (p ^ g - 1)`.

This is `Work.DSTR.M110.factorizationPowMulLt` with `q := r` and `x := p ^ g`, transported
across the identity `(p ^ g) ^ r = p ^ (r * g)` and divided by the positive number `p ^ g - 1`,
which divides `p ^ (r * g) - 1` since `g ∣ r * g`. -/
theorem splitArith (p r g : ℕ) (hp : p.Prime) (hodd : Odd p) (hr : r.Prime) (hro : Odd r)
    (hg : 1 ≤ g) :
    r ^ ((p ^ (r * g) - 1).factorization r) < (p ^ (r * g) - 1) / (p ^ g - 1) := by
  -- `(p ^ g) ^ r = p ^ (r * g)`
  have hpoweq : (p ^ g) ^ r = p ^ (r * g) := by
    rw [(pow_mul p g r).symm, Nat.mul_comm g r]
  -- `p ^ g ≥ 2`
  have hx2 : 2 ≤ p ^ g := by
    calc 2 ≤ p ^ 1 := by simpa using hp.two_le
      _ ≤ p ^ g := Nat.pow_le_pow_right hp.pos hg
  have hApos : 0 < p ^ g - 1 := by omega
  -- the arithmetic core, at `q = r`, `x = p ^ g`
  have hkey := Work.DSTR.M110.factorizationPowMulLt (q := r) (x := p ^ g) hr hro hx2
  rw [hpoweq] at hkey
  -- `hkey : r ^ ((p ^ (r * g) - 1).factorization r) * (p ^ g - 1) < p ^ (r * g) - 1`
  have hdiv : (p ^ g - 1) ∣ p ^ (r * g) - 1 := by
    rw [← hpoweq]
    exact Nat.sub_one_dvd_pow_sub_one (p ^ g) r
  have hlt : r ^ ((p ^ (r * g) - 1).factorization r) * (p ^ g - 1)
      < (p ^ (r * g) - 1) / (p ^ g - 1) * (p ^ g - 1) := by
    rw [Nat.div_mul_cancel hdiv]
    exact hkey
  exact (Nat.mul_lt_mul_right hApos).mp hlt

end Work.DSTR.M110.SplitCase
