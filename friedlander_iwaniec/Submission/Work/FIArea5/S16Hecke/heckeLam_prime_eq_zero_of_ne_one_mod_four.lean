import Mathlib
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

noncomputable section

/-- **Vanishing of the Hecke eigenvalue at a non-split prime.**  For a rational prime `p` with
`p % 4 ≠ 1` the eigenvalue `λ(p)` vanishes: `p = 2` is even (so no primary Gaussian integer has
norm `p`, primary elements having odd norm), and `p ≡ 3 (mod 4)` is inert in `ℤ[i]` (so there is no
primary element of norm `p` at all, `λ(p^ν)` being supported on even `ν`).

This is the local factor at `p ≡ 3 (4)` in the Euler product (16.17): `1 - λ(p)T + cT² = 1`. -/
theorem heckeLam_prime_eq_zero_of_ne_one_mod_four {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ}
    (hp : p.Prime) (h4 : p % 4 ≠ 1) : heckeLam chi k p = 0 := by
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · subst hp2
    exact heckeLam_even chi k (by norm_num)
  · obtain ⟨m, hm⟩ := hpodd
    have h3 : p % 4 = 3 := by omega
    obtain ⟨-, -, -, hclass⟩ := inertPrimaryClass p hp h3
    have h := heckeLam_inertSumOdd chi k p (-(p : GaussianInt)) hclass 1 (by decide)
    simpa using h

end

end Work.FIArea5.S16Hecke
