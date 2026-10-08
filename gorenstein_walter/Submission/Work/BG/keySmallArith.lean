import Mathlib

namespace Work.BG

/-- **Key small arithmetic step.**

If `N · (1 + 1/a + 1/b + 1/c) = 2k²` holds in `ℂ` (with `a, b, c` non-zero integers), then
clearing denominators gives the identity `N · (abc + bc + ac + ab) = 2k² · abc` in `ℤ`.

The proof multiplies the complex identity by `abc`, simplifies the left-hand side with
`field_simp`/`ring` to the cast of the integer expression, and then descends to `ℤ` using
injectivity of `ℤ → ℂ`. -/
theorem keySmallArith (N k : ℕ) (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (N : ℂ) * (1 + 1 / (a : ℂ) + 1 / (b : ℂ) + 1 / (c : ℂ)) = 2 * ((k : ℂ)) ^ 2) :
    (N : ℤ) * (a * b * c + b * c + a * c + a * b) = 2 * (k : ℤ) ^ 2 * (a * b * c) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcast : ((N : ℤ) * (a * b * c + b * c + a * c + a * b) : ℂ)
      = (2 * (k : ℤ) ^ 2 * (a * b * c) : ℂ) := by
    push_cast
    have h' := congrArg (fun x : ℂ => x * ((a : ℂ) * b * c)) h
    have expand : (1 + 1 / (a : ℂ) + 1 / (b : ℂ) + 1 / (c : ℂ)) * ((a : ℂ) * b * c)
        = (a : ℂ) * b * c + b * c + a * c + a * b := by
      field_simp
    rw [mul_assoc] at h'
    rw [expand] at h'
    simpa using h'
  exact_mod_cast hcast

end Work.BG
