/-
# `Submission.Work.FIArea7.omega_rep` — the `ω`-representation of the Dirichlet symbol

*FI* §19 represents the Dirichlet symbol of a primary primitive `w` by a rational residue,
`ξ_w(z) = ((r + ωs)/q)` with `q = |w|²`, `ω² + 1 ≡ 0 (mod q)`, `ω ≡ −v·u⁻¹` for `w = u + iv`
(19.2), (19.7).  This is the form in which the symbol is *evaluated* in §22 (proof of
Prop. 22.1), where the point is that for fixed `r` the summand becomes a Jacobi character in `s`:

  `(r + ωs | q) = (ω|q)·((s − ωr) | q)`,     because `r + ωs ≡ ω(s − ωr)`.

Here we prove the two identities, for the definition
`Work.FIArea7.DirichletSym w z = (Re(wz) | |w|²)` of (19.10):

* `dirichletSym_eq_jacobiSym_omega`: if `ω·u ≡ −v (mod |w|²)` then `ξ_w(z) = (r + ωs | |w|²)`;
* `jacobiSym_omega_shift`: `(r + ωs | q) = (ω|q)((s − ωr) | q)` whenever `ω² + 1 ≡ 0 (mod q)`.

Both use only `jacobiSym.mul_left`, `jacobiSym.mod_left` and the normalisation (19.8)
(`Work.FIArea7.jacobiSym_sq_add_sq`).
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.jacobiSym_sq_add_sq
import Submission.Work.FIArea7.dirichletSym_mul

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(19.2)/(19.7)**: a conjugate `ω` of `−v·u⁻¹` modulo `|w|²` evaluates the Dirichlet symbol:
`ξ_w(z) = (Re(w z) | |w|²) = (r + ωs | |w|²)`.  (The hypothesis is all that is used; `ω² ≡ −1` is
not needed here.) -/
theorem dirichletSym_eq_jacobiSym_omega {w z : GaussianInt} (hprim : Work.FIPlan.IsPrimary w)
    (hcop : IsCoprime w.re w.im) {ω : ℤ}
    (hω : ω * w.re ≡ -w.im [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)]) :
    jacobiSym (z.re + ω * z.im) (Work.FIPlan.gnorm w) = DirichletSym w z := by
  obtain ⟨hro, hie, _⟩ := hprim
  set q : ℕ := Work.FIPlan.gnorm w with hq
  -- `(r + ωs)·u ≡ Re(w z) (mod q)`
  have hmod : (z.re + ω * z.im) * w.re ≡ (w * z).re [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hω ⊢
    obtain ⟨c, hc⟩ := hω
    have hc' : w.im + ω * w.re = -((q : ℤ) * c) := by linarith [hc]
    refine ⟨z.im * c, ?_⟩
    rw [re_mul]
    linear_combination (-z.im) * hc'
  -- the normalisation (19.8)
  have h1 : jacobiSym w.re q = 1 := by
    have h := jacobiSym_sq_add_sq hro hie hcop
    rwa [← gnorm_eq_natAbs, ← hq] at h
  rw [DirichletSym]
  have h2 : jacobiSym ((z.re + ω * z.im) * w.re) q = jacobiSym (w * z).re q := by
    rw [jacobiSym.mod_left ((z.re + ω * z.im) * w.re) q, hmod,
      ← jacobiSym.mod_left (w * z).re q]
  rw [jacobiSym.mul_left, h1, mul_one] at h2
  rw [← hq]
  exact h2

/-- **The `ω`-shift of §22** (proof of Prop. 22.1): for `ω² + 1 ≡ 0 (mod q)` one has
`r + ωs ≡ ω(s − ωr) (mod q)`, hence `(r + ωs | q) = (ω|q)·((s − ωr) | q)`.  This turns the
`z`-sum in Prop. 22.1 into a sum over a *segment in s* of the two Jacobi characters
`(s − ωr | q)` and `(s | |r|)`. -/
theorem jacobiSym_omega_shift {q : ℕ} {ω : ℤ}
    (hω2 : (ω ^ 2 + 1) ≡ 0 [ZMOD (q : ℤ)]) (r s : ℤ) :
    jacobiSym (r + ω * s) q = jacobiSym ω q * jacobiSym (s - ω * r) q := by
  have hmod : r + ω * s ≡ ω * (s - ω * r) [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hω2 ⊢
    obtain ⟨c, hc⟩ := hω2
    refine ⟨r * c, ?_⟩
    linear_combination r * hc
  rw [jacobiSym.mod_left (r + ω * s) q, hmod,
    ← jacobiSym.mod_left (ω * (s - ω * r)) q, jacobiSym.mul_left]

end

end Work.FIArea7
