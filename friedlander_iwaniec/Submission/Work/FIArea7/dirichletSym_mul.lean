/-
# `Submission.Work.FIArea7.dirichletSym_mul` — *FI* (19.2)

The Dirichlet symbol `ξ_w(z) = (Re(wz) | |w|²)` of §19 is multiplicative in its argument:
for `w` primary primitive and all `z₁ z₂ ∈ ℤ[i]`,

  `ξ_w(z₁z₂) = ξ_w(z₁)·ξ_w(z₂)`.

This is the multiplicativity of the character of `ℤ[i]/|w|²ℤ[i]` given by `r + is ↦ r + ωs`
with `ω² ≡ −1 (mod |w|²)`, transported to the Jacobi symbol by (19.8)
(`Work.FIArea7.jacobiSym_sq_add_sq`).  The key algebraic identity is

  `Re(w z₁)·Re(w z₂) = |w|²·(Im z₁)(Im z₂) + (Re w)·Re(w (z₁z₂))`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.jacobiSym_sq_add_sq

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `|z|² = (r² + s²).natAbs`. -/
lemma gnorm_eq_natAbs (z : GaussianInt) :
    Work.FIPlan.gnorm z = (z.re ^ 2 + z.im ^ 2).natAbs := by
  have h1 : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have h2 : z.re ^ 2 + z.im ^ 2 = (((z.re ^ 2 + z.im ^ 2).natAbs : ℕ) : ℤ) :=
    (Int.natAbs_of_nonneg (by positivity)).symm
  exact Nat.cast_injective (h1.trans h2)

/-- The multiplicative identity behind (19.2):
`Re(w z₁)·Re(w z₂) = |w|²·(Im z₁)(Im z₂) + (Re w)·Re(w z₁z₂)`. -/
lemma re_mul_re_mul (w z1 z2 : GaussianInt) :
    (w * z1).re * (w * z2).re
      = (w * (z1 * z2)).re * w.re + (z1.im * z2.im) * (w.re ^ 2 + w.im ^ 2) := by
  simp only [re_mul, im_mul]
  ring

/-- *FI* (19.2): the Dirichlet symbol `ξ_w` is multiplicative in its argument. -/
theorem dirichletSym_mul {w : GaussianInt} (hprim : Work.FIPlan.IsPrimary w)
    (hcop : IsCoprime w.re w.im) (z1 z2 : GaussianInt) :
    Work.FIArea7.DirichletSym w (z1 * z2)
      = Work.FIArea7.DirichletSym w z1 * Work.FIArea7.DirichletSym w z2 := by
  obtain ⟨hro, hie, _⟩ := hprim
  set q : ℕ := Work.FIPlan.gnorm w with hq
  have hqZ : (q : ℤ) = w.re ^ 2 + w.im ^ 2 := by
    rw [hq, gnorm_eq_natAbs]
    exact Int.natAbs_of_nonneg (by positivity)
  -- the congruence `Re(w z₁)Re(w z₂) ≡ Re w · Re(w z₁z₂) (mod |w|²)`
  have hmod : (w * z1).re * (w * z2).re
      ≡ w.re * (w * (z1 * z2)).re [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(z1.im * z2.im), ?_⟩
    have h := re_mul_re_mul w z1 z2
    rw [hqZ, h]
    ring
  -- the normalisation (19.8)
  have h1 : jacobiSym w.re (q : ℕ) = 1 := by
    have h := jacobiSym_sq_add_sq hro hie hcop
    rwa [← gnorm_eq_natAbs, ← hq] at h
  rw [DirichletSym, DirichletSym, DirichletSym, ← jacobiSym.mul_left]
  have step : jacobiSym ((w * z1).re * (w * z2).re) q
      = jacobiSym (w * (z1 * z2)).re q := by
    rw [jacobiSym.mod_left ((w * z1).re * (w * z2).re) q, hmod,
      ← jacobiSym.mod_left (w.re * (w * (z1 * z2)).re) q, jacobiSym.mul_left, h1, one_mul]
  exact step.symm

end

end Work.FIArea7
