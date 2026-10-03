/-
# `Submission.Work.FIArea6Road.QfacRatioDefs`

Vocabulary for the bound `Work.FIArea6Road.QfacBoundRatioGeOne` of the §16 truncation sum
`Q(s) = Σ_{c ≤ C, (c,Π)=1} λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}` (*FI* (16.34)) in the region
`1 ≤ re s ≤ 2`.

The three objects isolated here are

* `QfacS Pa` — the index set `{c ≤ C : c squarefree, (c, Π) = 1}` of (16.34), `Π = ∏_{p ≤ Pz} p`;
* `QfacTerm Pa χ m s c` — the summand `λ(c)c^{-s}∏_{p|c}(1-λ(p)p^{-s})^{-1}`;
* `QfacW Pa p` — the per-prime weight `2(1+4p^{-3/4})/p` of the local majorant, set to `0` at the
  primes `p ≤ Pz` (which never divide an index `c ∈ QfacS Pa`).

The point of the isolation is that a bound on `Q(s)` decomposes into

  `‖Qfac Pa χ m s‖ ≤ Σ_{c ∈ QfacS Pa} ‖QfacTerm Pa χ m s c‖`
      `≤ Σ_{c ∈ QfacS Pa} ∏_{p | c} QfacW Pa p ≤ K·(1 + log C/log Pz)²`,

the last step being the (already available) Euler-product/Mertens estimate
`Work.FIArea6Road.zcub_Qfac_prod_le` together with the product expansion
`Work.FIArea6Road.QfacProdExpand`.

Useful already-proved inputs for the *middle* (per-summand) step:
`Work.FIArea6Road.zcub_heckeLam_prod_primeFactors` (multiplicativity of `λ` over the prime factors
of a squarefree integer), `Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two` (or the packaged
`Work.FIArea6Road.heckeLam_prime_norm_le_two'`, `‖λ(p)‖ ≤ 2`),
`Work.FIArea6Road.locF_inv_bound` (`‖(1-λ(p)p^{-s})^{-1}‖ ≤ locBnd p` for `re s ≥ 3/4`),
`Work.FIArea6Road.zcub_locBnd_le` (`locBnd p ≤ 1 + 4p^{-3/4}` for `p ≥ 7`) and
`Nat.prod_primeFactors_of_squarefree` (`c = ∏_{p|c} p`).
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.Basic

set_option autoImplicit false

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

noncomputable section

/-- The index set `{c ≤ ⌊C⌋ : c` squarefree, `(c, Π) = 1}` of the truncation sum (16.34), with
`Π = ∏_{p ≤ Pz} p`. -/
def QfacS (Pa : Work.FITop.Params) : Finset ℕ :=
  (Finset.Icc 1 ⌊Pa.C⌋₊).filter
    (fun c => Squarefree c ∧ Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p))

/-- The summand `λ(c)c^{-s}∏_{p ∣ c}(1-λ(p)p^{-s})^{-1}` of the truncation sum (16.34). -/
def QfacTerm (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (c : ℕ) : ℂ :=
  Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
    * ∏ p ∈ c.primeFactors, (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹

/-- The per-prime weight of the local majorant used on `re s ≥ 1`:
`QfacW Pa p = 2(1+4p^{-3/4})/p` for `p > Pz`, and `0` for `p ≤ Pz`. -/
def QfacW (Pa : Work.FITop.Params) (p : ℕ) : ℝ :=
  if Pa.Pz < p then 2 * (1 + 4 * (p : ℝ) ^ (-(3 / 4 : ℝ))) / (p : ℝ) else 0

/-- `Qfac` is the sum of `QfacTerm` over the index set `QfacS`. -/
lemma Qfac_eq_sum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea6.TauPieces.Qfac Pa chi m s = ∑ c ∈ QfacS Pa, QfacTerm chi m s c := by
  simp only [Work.FIArea6.TauPieces.Qfac, QfacS, QfacTerm]

/-- The weights `QfacW Pa p` are nonnegative. -/
lemma QfacW_nonneg (Pa : Work.FITop.Params) (p : ℕ) : 0 ≤ QfacW Pa p := by
  simp only [QfacW]
  by_cases h : Pa.Pz < p
  · rw [if_pos h]
    have hp : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (le_of_lt hp) _
    positivity
  · rw [if_neg h]

end

end Work.FIArea6Road
