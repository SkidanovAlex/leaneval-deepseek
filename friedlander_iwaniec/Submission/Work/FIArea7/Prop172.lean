/-
# `Submission.Work.FIArea7.Prop172` — the vocabulary of *FI* (17.10)–(17.15) and §23

This file names the objects that Proposition 17.2 and the final counting (17.13) are stated with:

* the Grossencharacter (17.17) `ψ(z) = χ(z)(z/|z|)^k`;
* the character sum (17.12)/(17.14) `S^k_χ(β') = Σ_z β'_z ψ(z)`, with `β' = [z]β` of (17.8)/(17.16)
  (`Work.FIArea7.betaPrime`, `Work.FIArea7.JKSym`);
* the incomplete character sum (16.13)/(17.11) `J(χ) = Σ_{ω (mod 4d)} χ(ω)(ω|d)` (the sum over
  *rational* classes `ω` of `ℤ[i]/4d`);
* the quadratic eigenvalue (23.1) `λ(n) = Σ∧_{z z̄ = n} ψ(z)[z]`.

Only the vocabulary and the elementary size bound are recorded here; `Φ(d)` of (16.12) (the order
of `(ℤ[i]/4d)^*`) needs the group structure of `ℤ[i]/4d` and is left to the `ℤ[i]`-character
chapter (see `NOTES.md` §10, §14).
-/
import Mathlib
import Submission.Work.FIArea7.WBOmega
import Submission.Work.FIArea7.FIsymbols

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

open Classical

/-- **(17.17)**: the Grossencharacter `ψ(z) = χ(z)·(z/|z|)^k` attached to a multiplicative
character `χ` on `ℤ[i]` (a character of `(ℤ[i]/4d)^*` extended by `0`) and an integer `k`.
For `z = 0` the factor is `0/0 = 0`, so `ψ(0) = 0`. -/
def grossenChar (chi : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) : ℂ :=
  chi z * (z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)) ^ k

/-- **(17.12)/(17.14)**: `S^k_χ(β') = Σ_z β'_z χ(z)(z/|z|)^k`, with the twisted coefficients
`β'_z = [z]β_z` of (17.8)/(17.16). -/
def SChiK (Rz : ℤ) (β : GaussianInt → ℂ) (chi : GaussianInt → ℂ) (k : ℤ) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox Rz, betaPrime β z * grossenChar chi k z

/-- **(16.13)/(17.11)**: `J(χ) = Σ_{ω (mod 4d)} χ(ω)(ω|d)`, the sum running over the *rational*
classes `ω` modulo `4d` (encoded by the representatives `0, …, 4d-1`). -/
def JChar (d : ℕ) (chi : GaussianInt → ℂ) : ℂ :=
  ∑ ω ∈ Finset.range (4 * d), chi (ω : GaussianInt) * (jacobiSym (ω : ℤ) d : ℂ)

/-- **(23.1)**: the quadratic eigenvalue `λ(n) = Σ∧_{z z̄ = n} ψ(z)[z]`, where `∧` restricts the
sum to primary `z` (the box makes the sum finite). -/
def lambdaEig (Rz : ℤ) (psi : GaussianInt → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z then psi z * JKSym z else 0)

end

end Work.FIArea7
