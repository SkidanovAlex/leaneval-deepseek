/-
# `Work.FIArea6Hecke.heckeLam_prime_divergence`

*FI* §16: at a prime `p ≡ 1 (4)` the two primary Gaussian integers of norm `p` are `π` and
`conj π` (`splitPrimaryClass`), so the Hecke eigenvalue is a sum of two unit-modulus values
`λ(p) = ψ(π) + ψ(conj π)`; in particular `‖λ(p)‖ ≤ 2` and the "degree-`1`" divergence

  `Σ_{p ≡ 1(4)} ‖λ(p)‖/p = ∞`

is equivalent to the "degree-`2`" divergence `Σ_{p ≡ 1(4)} ‖λ(p)‖²/p = ∞` (as `‖λ(p)‖² ≤ 2‖λ(p)‖`).

The squared divergence is the content of the delegated lemma
`Work.FIArea6Hecke.heckeLam_sq_prime_recip_divergence` (the Hecke `L`-function chapter: the
Rankin–Selberg *2nd moment* along the split primes), and the present file is the elementary
reduction of the requested degree-`1` statement to it.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea6Hecke.chiTildeDefs
import Submission.Work.FIArea6Hecke.R.chiTrivLocalPrime

namespace Work.FIArea6Hecke

open Finset
open scoped BigOperators
open Work.FIPlan
open Work.FIArea5.S16Hecke

noncomputable section

/-- At a prime `p ≡ 1 (4)` the Hecke eigenvalue is a sum of two unit-modulus terms, hence bounded
by `2`. -/
lemma heckeLam_prime_norm_le_two {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ)
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ‖heckeLam chi m p‖ ≤ 2 := by
  obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp hp4
  have hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have h1 : chi 1 = 1 := hchi.1.1
  have hbnd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hsum := heckeLam_splitSum chi m p hp.pos hmul h1 π π' hπ hπ' hgπ hgπ' hclass 1
  rw [pow_one] at hsum
  rw [hsum, geo_one]
  calc ‖psi chi m π + psi chi m π'‖
      ≤ ‖psi chi m π‖ + ‖psi chi m π'‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_psi_le_one chi m hbnd π) (norm_psi_le_one chi m hbnd π')
    _ = 2 := by norm_num

end

end Work.FIArea6Hecke
