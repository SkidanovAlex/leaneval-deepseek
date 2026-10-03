/-
# `Submission.Work.FIArea5.S16Hecke.ThetaDefs`

The objects of the **theta transformation** of the Grössencharacter theta series of `ℚ(i)`
(*FI* §16, the analytic engine behind Lemma 16.2).

* `isOddG z` — `z` is *odd*: not divisible by `1+i`.  The Grössencharacter `ψ(z) = χ(z)(z/|z|)^m`
  is defined on odd `z` and the primary elements are exactly the odd `z` up to a unit multiple.
* `chiOdd chi` — the periodic weight `χ` extended by `0` off the odd elements.  Summing over *all*
  odd `z` (rather than over the primary coset `1 + (1+i)³ℤ[i]`) is what makes the Gaussian factor
  `e^{-πu|z|²}` *centred at the origin*, so that twisted Poisson summation gives the clean duality
  between `χ` and `χ̄` (see `gaussSum` below).
* `gaussSum d chi ξ` — the finite Fourier transform ("Gauss sum")
  `Σ_{α odd mod 4d} χ(α)·e^{2πi Re(α·ξ̄)/(4d)}`.  This is precisely the weight produced by
  `Work.FIArea5.S16.poisson_periodic_2d` applied to the periodic weight `chiOdd chi`.
* `thetaOdd chi m u` — the holomorphic theta series `Σ_{z odd} χ(z) z^m e^{-πu|z|²}`.
* `IsPrimitive4d d chi` / `IsImprimitive4d d chi` — the *conductor* condition: `χ` (a character on
  `ℤ[i]/4d`) is imprimitive if it is trivial on a congruence subgroup `1 + mℤ[i]` of the unit group
  with `m | 4d` a proper divisor, i.e. if it is induced from a smaller modulus.  The Gauss sum
  identity `gaussSum d chi ξ = G(χ)·χ̄(ξ̄)` (and the vanishing of `gaussSum` on non-units) is the
  classical statement that holds for primitive `χ`.

The main chain proved downstream is: twisted Poisson summation over `ℤ²` at level `4d`
(`Work.FIArea5.S16.poisson_periodic_2d`), the two-dimensional Fourier transform of the holomorphic
Gaussian, the Gauss sum identity, giving the theta transformation

  `thetaOdd chi m u = (4d)^{-(m+2)}(-i)^m u^{-(m+1)}·G(χ)·conj (thetaOdd chi m (1/(16d²u)))`,

from which (via the Mellin transform `∫_0^∞ thetaOdd chi m u·u^{s-1} du = Γ(s)π^{-s}L(s+m/2,ψ)`)
comes Hecke's functional equation.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- `1+i` as a Gaussian integer. -/
def oneAddI : GaussianInt := 1 + (⟨0,1⟩ : GaussianInt)

/-- **Oddness** in `ℤ[i]`: `z` is odd when it is not divisible by `1+i`; these are exactly the
elements which are units modulo any power of `1+i`, i.e. the elements on which a character of
`ℤ[i]/4dℤ[i]` is allowed to be non-zero. -/
def isOddG (z : GaussianInt) : Prop := ¬ (oneAddI ∣ z)

/-- The periodic weight `χ` extended by `0` off the odd elements; this is the `g` of twisted
Poisson summation (`Work.FIArea5.S16.poisson_periodic_2d`). -/
def chiOdd (chi : GaussianInt → ℂ) (z : GaussianInt) : ℂ := by
  classical
  exact if isOddG z then chi z else 0

/-- **The Gauss sum** of `χ` at `ξ`: the finite Fourier transform of the periodic weight
`chiOdd chi` over `(ℤ[i]/4dℤ[i]) ≅ (ℤ/4d)²`,

  `gaussSum d chi ξ = Σ_{α odd mod 4d} χ(α)·e^{2πi(α₁ξ.re + α₂ξ.im)/(4d)} = Σ_{α odd} χ(α)e^{2πiRe(αξ̄)/(4d)}`.

This is the weight produced by Poisson summation, and for primitive `χ` it equals
`G(χ)·χ̄(ξ̄)` (with `G(χ) = gaussSum d chi 1`), which is what turns the dual sum into the conjugate
theta series. -/
def gaussSum (d : ℕ) (chi : GaussianInt → ℂ) (ξ : GaussianInt) : ℂ := by
  classical
  exact ∑ α ∈ (Finset.range (4 * d)).product (Finset.range (4 * d)),
    (if isOddG (⟨α.1, α.2⟩ : GaussianInt) then
      chi (⟨α.1, α.2⟩ : GaussianInt) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((((α.1 * ξ.re + α.2 * ξ.im : ℤ)) : ℂ) / ((4 * d : ℕ) : ℂ)))
     else 0)

/-- **The holomorphic theta series, summed over the odd elements**:
`thetaOdd chi m u = Σ_{z odd} χ(z)·z^m·e^{-πu|z|²}`.  This differs from
`Work.FIArea5.S16Hecke.thetaHol` only by the finite constant `Σ_{u ∈ μ₄}χ(u)u^m` (since every odd
`z` is `u·z'` with `u` a unit and `z'` primary), but its Gaussian factor is centred at the origin,
so that Poisson summation produces the duality `χ ↦ χ̄` directly. -/
def thetaOdd (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) : ℂ := by
  classical
  exact ∑' z : GaussianInt,
    (if isOddG z then chi z * (z.toComplex) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))
     else 0)

/-- **The four units** of `ℤ[i]`, as a `Finset`.  Every odd Gaussian integer is `u·z'` with a
unique unit `u` and a unique *primary* `z'` (`Work.FIPlan.IsPrimary`). -/
def units4 : Finset GaussianInt := {(1 : GaussianInt), -1, ⟨0,1⟩, ⟨0,-1⟩}

/-- The finite sum `Σ_{u ∈ μ₄} χ(u)·u^m` measuring the discrepancy between the theta series
summed over the odd elements and summed over the primary coset (`thetaOdd` vs `thetaHol`). -/
def unitSum (chi : GaussianInt → ℂ) (m : ℕ) : ℂ :=
  ∑ u ∈ units4, chi u * (u.toComplex) ^ m

/-- **Units modulo `4d`**: `z` is invertible modulo `4d` when there is `w` with `z·w ≡ 1`.  The
Grössencharacter `χ` of (16.16) is a character of the group `(ℤ[i]/4dℤ[i])^*` of such classes,
extended by zero off them. -/
def IsUnitMod4d (d : ℕ) (z : GaussianInt) : Prop :=
  ∃ w : GaussianInt, (((((4 * d : ℕ)) : ℤ)) : GaussianInt) ∣ (z * w - 1)

/-- `χ` is a **character modulo `4d` of the unit group, extended by zero**: the round-4 predicate
`Work.FITop3.IsCharMod4d` together with the vanishing of `χ` off the units.  (The vanishing off
non-units is not implied by `IsCharMod4d` alone; it is the extra clause which makes `χ` a genuine
multiplicative character of `(ℤ[i]/4dℤ[i])^*`.) -/
def IsCharMod4dStrict (d : ℕ) (chi : GaussianInt → ℂ) : Prop :=
  Work.FITop3.IsCharMod4d d chi ∧ ∀ z : GaussianInt, ¬ IsUnitMod4d d z → chi z = 0

/-- **Primitivity** of `χ` modulo `4d`, in the classical *Gauss sum* form: `χ` is primitive when
its Gauss sum has the maximal possible size `|G(χ)|² = #(ℤ[i]/4dℤ[i]) = 16d²`.  This is the
standard criterion "`|G(χ)|²` equals the conductor" (for the trivial character, for instance,
`G(χ) = Σ_{α ∈ (ℤ[i]/4d)^*} e^{2πiRe(α)/(4d)} = 0` whenever `d ≥ 1`).

The criterion is what makes the *duality* `gaussSum d chi ξ = G(χ)·χ̄(ξ̄)` provable: for units `ξ`
it is the elementary substitution `α ↦ α·ξ̄⁻¹`, and for non-units it follows from Parseval applied
to the finite Fourier transform (see the delegated lemma `gaussSum_eq`). -/
def IsPrimitive4d (d : ℕ) (chi : GaussianInt → ℂ) : Prop :=
  IsCharMod4dStrict d chi ∧ ‖gaussSum d chi 1‖ ^ 2 = ((16 * d ^ 2 : ℕ) : ℝ)


/-- **The completed Hecke `L`-function.**  With `X = 4d/π = √(4·(4d)²)/(2π)` (the standard Hecke
normalisation `√(|d_K|·N𝔣)/(2π)` for `K = ℚ(i)`, `|d_K| = 4`, `N𝔣 = 16d²`)

  `LambdaHecke d chi m s = X^s·Γ(s + m/2)·L(s, ψ)`,   `ψ(z) = χ(z)(z/|z|)^m`,

where `L(s,ψ) = heckeLSeries chi m s`.  Its functional equation is Hecke's
`LambdaHecke d chi m s = W·conj (LambdaHecke d chi m (conj (1-s)))` (see `NOTES_theta.md`); the
Gamma shift `s + m/2` is the one of the weight-`(m+1)` theta series, as in *FI* (16.17). -/
def LambdaHecke (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  ((((4 * (d : ℝ)) / Real.pi) : ℂ) ^ s) * Complex.Gamma (s + (m : ℂ) / 2) *
    heckeLSeries chi (m : ℤ) s

end

end Work.FIArea5.S16Hecke
