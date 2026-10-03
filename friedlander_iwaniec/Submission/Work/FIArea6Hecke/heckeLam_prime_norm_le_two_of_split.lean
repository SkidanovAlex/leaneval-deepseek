import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.Defs

namespace Work.FIArea6Hecke

open Work.FIArea5.S16Hecke

/-- At a rational prime `p ≡ 1 (mod 4)` the Hecke eigenvalue `λ(p)` is the sum
`ψ(π) + ψ(π̄)` of the Größencharacter values at the two primary primes of norm `p`,
so its modulus is at most `2` since `‖ψ‖ ≤ 1`. -/
theorem heckeLam_prime_norm_le_two_of_split (chi : GaussianInt → ℂ) (k : ℤ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (h1 : chi 1 = 1)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi k p‖ ≤ 2 := by
  obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp hp4
  have hA : heckeLam chi k p = geo (psi chi k π) (psi chi k π') 1 := by
    have h := heckeLam_splitSum chi k p hp.pos hmul h1 π π' hπ hπ' hgπ hgπ' hclass 1
    simpa only [pow_one] using h
  rw [hA, geo_one]
  calc ‖psi chi k π + psi chi k π'‖
      ≤ ‖psi chi k π‖ + ‖psi chi k π'‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_psi_le_one chi k hb π) (norm_psi_le_one chi k hb π')
    _ = 2 := by norm_num

end Work.FIArea6Hecke
