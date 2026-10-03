/-
# `Submission.Work.FIArea7.KStarDefs` — vocabulary for *FI* (22.4), the bound for `K*`

*FI* §22 proves, besides (22.3) for `K(N) = Σ∧_{z ∈ B} ψ(z)[wz]` (＝
`Work.FIArea7.KSum_bound`), the companion bound (22.4) for the co-primality restricted form

  `K*(N) = Σ∧_{z ∈ B, (z,w)=1} ψ(z)[wz]`

by Möbius inversion over the *Gaussian* divisors `e | w`:

  `K*(N) = Σ_{e | w} μ(e) ψ(e) Σ∧_{z ∈ B/e} ψ(z)[ewz]`.

This file collects the vocabulary of that reduction:

* `KInnerStar` — the fibre `z.re = r` of `K*`;
* `gaussPrimDivs w` — the (finite) set of *primary* Gaussian divisors of `w`, one representative of
  each associate class of divisors (so that summing over it is Möbius summation over the divisors
  of `w`, cf. `Work.FIArea7.KStarDefs`' companion lemmas).

The theorems *about* these objects (`gauss_divs_moebius`, `sum_inv_sqrt_gaussPrimDivs_le`,
`ap_char_sum_bound`, …) live in modules that import this one.
-/
import Mathlib
import Submission.Work.FIArea7.Prop172

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(22.2)**, fibre by fibre: the fibre `z.re = r` of `K∗(N)`,
`Σ_s 𝟙∧[(r+is, w) = 1] ψ(r+is)[w(r+is)]`. -/
def KInnerStar (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r : ℤ) : ℂ :=
  ∑ s ∈ Finset.Icc (-Rz) Rz,
    (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
        Work.FIPlan.GaussCoprime (⟨r, s⟩ : GaussianInt) w then
      grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)

/-- The **primary Gaussian divisors of `w`**: the finite set of `e` with `e | w` and `e` primary.
Since a primary element has odd real part, primary divisors are pairwise non-associate, so this is a
set of representatives of the divisor classes — the index set of the Gaussian Möbius sum. -/
def gaussPrimDivs (w : GaussianInt) : Finset GaussianInt :=
  (((Finset.Icc (-(((Work.FIPlan.gnorm w : ℕ) : ℤ))) (((Work.FIPlan.gnorm w : ℕ) : ℤ))).product
      (Finset.Icc (-(((Work.FIPlan.gnorm w : ℕ) : ℤ)))
        (((Work.FIPlan.gnorm w : ℕ) : ℤ)))).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))).filter
      (fun e => e ∣ w ∧ Work.FIPlan.IsPrimary e)

end

end Work.FIArea7
