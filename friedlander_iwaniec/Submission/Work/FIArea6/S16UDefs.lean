/-
# `Submission.Work.FIArea6.S16UDefs` — the vocabulary of the §16 chain for `Ucut`

*FI* §16 estimates `U(β) = 2Σ_{d≤X}(φ(d)/d)U_d(β)` by expanding each `U_d` into Hecke character
sums `S_χ^k(β)` (16.11)–(16.15) and then summing Lemma 16.2 (`Work.FITop4.Area5_6`) over the
characters, the moduli `d ≤ X` and the frequencies `|k| ≤ K = X³`.

This file fixes the objects that chain manipulates (nothing here is a theorem to be proved):

* `psiK k z = (z/|z|)^k` — the Grossencharacter factor of (16.14) (`k ∈ ℤ`);
* `omegaDet` — the `ω`-detection of (16.3)/(16.4), i.e. `Work.FIArea7.omegaDetect (4d) d`, the sum
  over the rational classes `ω (mod 4d)` of the weight `(ω|d)` on the (unique) class with
  `z₁ ≡ ω z₂ (mod 4d)`;
* `Vd Pa d β` — the *per-modulus* piece `U_d(β)` of (16.1)/(16.2), at the round-6 objects
  (`ratioSym` for the symbol, `logFac6` for the logarithm, the coprimality condition of (16.2));
* `DetSum Pa d k β` — the pair sum that the character expansion turns into `J(χ)|S_χ^k(β)|²`
  (the left-hand side of (16.11) with the Grossencharacter factor inserted);
* `fcoeff k` — the Fourier coefficients of the classical expansion
  `log(8/|sin α|) = log 16 + Σ_{k even, k≠0} e^{ikα}/|k|` of (16.7)/(16.8) at the *unmollified*
  weights (the `1/|k|` that (16.8) replaces by the exponentially decaying `û(k)` of the mollifier;
  both are usable for an upper bound, the classical one with an explicit remainder `4/(K|sin α|)`).

The constants: `K = X³` is the frequency cutoff of (16.9), and with `H = X` the truncation error
`K^{-1}H²log H = X^{-1}log X` of (16.9) is what (16.15) balances against the `H X⁴` of Lemma 16.2.
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea7.WBOmega
import Submission.Work.FIArea7.Section16Expansion

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Grossencharacter factor `(z/|z|)^k` of (16.14), `k ∈ ℤ`. -/
def psiK (k : ℤ) (z : GaussianInt) : ℂ :=
  (z.toComplex / (Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) : ℂ)) ^ k

/-- The `ω`-detection sum of (16.3)/(16.4) at the modulus `4d`: the sum over the rational classes
`ω (mod 4d)` of the weight `(ω|d)` on the (unique) class with `z₁ ≡ ω z₂ (mod 4d)`. -/
def omegaDet (d : ℕ) (z1 z2 : GaussianInt) : ℂ := Work.FIArea7.omegaDetect (4 * d) d z1 z2

/-- **(16.1)/(16.2) per modulus**: the piece `U_d(β)` of the `U`-cut, at the round-6 objects. -/
def Vd (Pa : Work.FITop.Params) (d : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
      β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ)
        * (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)

/-- The pair sum whose character expansion is (16.11): the `ω`-detected sum with the
Grossencharacter factor `(z₁z̄₂/|z₁z₂|)^k` inserted. -/
def DetSum (Pa : Work.FITop.Params) (d : ℕ) (k : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2
      * ((β z1 * psiK k z1) * star (β z2 * psiK k z2)) * omegaDet d z1 z2

/-- The Fourier coefficient `c_k` of the classical expansion of `log(8/|sin α|)`:
`c_0 = log 16` and `c_k = 1/|k|` for even `k ≠ 0`, `c_k = 0` for odd `k`. -/
def fcoeff (k : ℤ) : ℝ :=
  if k = 0 then Real.log 16 else if (2 : ℤ) ∣ k then 1 / |(k : ℝ)| else 0

/-- The frequency cutoff of (16.9): `K = X³`. -/
def Kcut (X : ℕ) : ℕ := X ^ 3

/-- The truncated Fourier sum of (16.9) as a complex number. -/
def ftrunc (X : ℕ) (α : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(Kcut X : ℤ)) (Kcut X : ℤ),
    (fcoeff k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (α : ℂ))

/-- **The truncated main sum of (16.15) at the modulus `d`**: the `DetSum` pieces weighed by the
Fourier coefficients `c_k` of the classical log-sine expansion, over the frequencies
`|k| ≤ 2X³` produced by `gtrunc` (the terms `n ≤ Kcut X = X³` of the cosine series). -/
def MainSum (Pa : Work.FITop.Params) (X : ℕ) (d : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(2 * (Kcut X) : ℤ)) (2 * (Kcut X) : ℤ),
    (fcoeff k : ℂ) * DetSum Pa d k β

/-- **(16.15) truncated**: the main term of §16, `2Σ_{d ≤ X}(φ(d)/d)·MainSum d`. -/
def Umain (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ d ∈ Finset.Icc 1 X,
        ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * MainSum Pa X d β


/-- The truncated classical Fourier series of the log-sine: `log 16 + Σ_{n ≤ K} cos(2nα)/n`
(compared with the mollified `(16.8)`, this is the *unmollified* expansion of (16.7), whose
tail is `O(1/(K|sin α|))` — enough for the purpose here because the constant `C` is free). -/
def gtrunc (X : ℕ) (α : ℝ) : ℝ :=
  Real.log 16 + ∑ n ∈ Finset.Icc 1 (Kcut X), Real.cos (2 * (n : ℝ) * α) / (n : ℝ)


/-! ## 2. The lattice counts of the §16 error terms

The three counts below are the only arithmetic/geometric inputs of the §16 error analysis
(compare `Work.FIArea6.card_dvd_delta_fiber_le` / `..._near_le` and
`Work.FIArea6.noncoprime_mass_le`):

* `fibCountDvd` — for `z₁` a unit mod `4d`, the number of `z₂` in the polar box, coprime to `4d`,
  with `4d ∣ |Δ(z₁,z₂)|`.  Since (for `z₂` a unit) `4d ∣ Δ(z₁,z₂) ⟺ z₂ ≡ ρ z₁ (mod 4d)` for one
  of the (at most `4d`) rational classes `ρ`, the coset count `card_fiber_mod_le` in the disc of
  radius `5θ√N` containing the polar box bounds it by `4d·(10θ√N/(4d)+1)²`.
* `fibCountDvdNear` — the same with the extra condition `|Δ(z₁,z₂)| ≤ M`; the strip `|Im(z̄₁k)| ≤
  M/(4d)` through the disc of radius `5θ√N/(4d)` contains `≪ (θ√N/d)(M/(d√N))` lattice points, which
  is what turns the truncation error `4/(K|sin α|)` into the required `X⁻¹` (`M = 2N/X`, `K = X³`).
* `ncPairCount` — the number of pairs with `4d ∣ |Δ(z₁,z₂)|` that are *not* coprime, each carrying a
  common divisor of norm `> Pz` by (5.8); that gives the `Pz⁻¹` saving of the coprimality removal.
-/

/-- The number of `z₂` in the polar box, coprime to `4d`, with `4d ∣ |Δ(z₁,z₂)|`. -/
def fibCountDvd (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (z1 : GaussianInt) : ℕ :=
  ((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z
    ∧ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)
    ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z)).card

/-- The same count with the near-diagonal restriction `|Δ(z₁,z₂)| ≤ M`. -/
def fibCountDvdNear (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (M : ℝ)
    (z1 : GaussianInt) : ℕ :=
  ((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z
    ∧ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)
    ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z
    ∧ (Work.FIPlan.Delta z1 z).natAbs ≤ M)).card

/-- The number of pairs `(z₁,z₂)` of the polar box, free of small primes, that are not coprime
and satisfy `4d ∣ |Δ(z₁,z₂)|`. -/
def ncPairCount (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) : ℕ :=
  ∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z
      ∧ Work.FITop3.NoSmallPrimes Pa z),
    ((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z
      ∧ Work.FITop3.NoSmallPrimes Pa z
      ∧ ¬ Work.FIPlan.GaussCoprime z1 z
      ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z)).card

end

end Work.FIArea6
