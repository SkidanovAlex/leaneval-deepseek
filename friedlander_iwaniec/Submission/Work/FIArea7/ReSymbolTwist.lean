/-
# The frozen symbol `(Re(z̄₁z₂)|d)` versus *FI*'s symbol `(z₂/z₁|d)`: the twist `(|z₁|²|d)`

The frozen `Work.FITop3.TcutMod` (and hence `WcutMod`, `BcutMod`, `UcutMod`, `VcutMod`) carries the
symbol

  `jacobiSym ((star z₁ * z₂).re) d = (Re(z̄₁z₂) | d)`,

whereas *FI* (8.14), (10.2), (10.13) use the symbol `(z₂/z₁ | d)`, the Jacobi symbol of the
*rational* residue of the Gaussian ratio `z₂/z₁` modulo `d` (which is rational modulo `d` exactly
when `4d ∣ Δ`, by (6.6)).  This file records the exact relation between the two:

  **`(Re(z̄₁z₂) | d) = (z₂/z₁ | d) · (|z₁|² | d)`   for `(d, |z₁|²) = 1`.**

The twist `(|z₁|²|d)` is *not* determined by the classes `z₁, z₂ mod d` (or even mod `4d`): it is a
Jacobi symbol whose modulus is the *large* divisor `d = |Δ|/(4e)` produced by the §17 reflection.
`Work.FIArea7.twist_nontrivial` exhibits an admissible pair (`primary`, squarefree coprime norms,
`4 ∣ Δ`) on which it is `-1`; exhaustive search over primary primitive pairs with coordinates in
`[-40,40]`, squarefree norms, `(z₁,z₂) = 1` and `4 ∣ Δ` gives `(269|28) = -1` on 167908 of 342318
pairs.  Consequently the frozen symbol is **not** *FI*'s symbol: the §17 identity (17.5) evaluates
`(z₂/z₁||Δ|)`, i.e. `(Re(z̄₁z₂)||Δ|)·(|z₁|²||Δ|)`, and leaves the factor `(|z₁|²||Δ|)` behind when
applied to the frozen symbol.  See `NOTES.md` §21.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## 0. Coordinates -/

/-- `Re(z̄₁z₂) = r₁r₂ + s₁s₂`. -/
lemma re_star_mul_coords (z1 z2 : GaussianInt) :
    (star z1 * z2).re = z1.re * z2.re + z1.im * z2.im := by
  rw [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `Im(z̄₁z₂) = Δ(z₁,z₂) = r₁s₂ - r₂s₁`. -/
lemma im_star_mul_coords (z1 z2 : GaussianInt) :
    (star z1 * z2).im = Work.FIPlan.Delta z1 z2 := rfl

/-! ## 1. *FI*'s symbol `(z₂/z₁|d)` -/

/-- ***FI*'s symbol `(z₂/z₁ | d)`** (8.14), (10.2), (10.13): the Jacobi symbol of the *rational*
residue of the Gaussian ratio `z₂/z₁`, i.e. of `Re(z̄₁z₂)·|z₁|²⁻¹ (mod d)`.  (`|z₁|²` is inverted in
`ZMod d`; when it is not a unit the resulting value is not the paper's symbol, which is why every
statement below carries `Nat.Coprime (gnorm z₁) d`.) -/
def ratioSym (z1 z2 : GaussianInt) (d : ℕ) : ℤ :=
  jacobiSym
    ((((star z1 * z2).re : ZMod d) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹).val : ℤ) d

/-- ***FI* (6.6)/(15.1)**: for `d ∣ Δ(z₁,z₂)` the Gaussian ratio `z₂/z₁` is a *rational* residue
modulo `d` — its imaginary part `Δ·|z₁|²⁻¹` vanishes. -/
theorem ratio_im_eq_zero (z1 z2 : GaussianInt) {d : ℕ} (hd : (d : ℤ) ∣ Work.FIPlan.Delta z1 z2) :
    ((((star z1 * z2).im : ZMod d) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹) : ZMod d) = 0 := by
  have h0 : ((Work.FIPlan.Delta z1 z2 : ℤ) : ZMod d) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  rw [im_star_mul_coords, h0, zero_mul]

/-! ## 2. The twist -/

/-- **The twist `(|z₁|²|d)` between the frozen symbol and *FI*'s symbol.**  For `d ≥ 1` coprime to
`|z₁|²`,

  `(Re(z̄₁z₂) | d) = (z₂/z₁ | d) · (|z₁|² | d)`.

It is pure multiplicativity of the Jacobi symbol in the upper entry, the content being that
`z₂/z₁ ≡ Re(z̄₁z₂)·|z₁|²⁻¹ (mod d)` when `d ∣ Δ` (which is where the frozen symbol picks up its
extra factor). -/
theorem jacobiSym_re_eq_ratioSym_mul (z1 z2 : GaussianInt) {d : ℕ} [NeZero d]
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z1) d) :
    jacobiSym ((star z1 * z2).re) d
      = ratioSym z1 z2 d * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) d := by
  have hunit : IsUnit ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d)) :=
    (ZMod.isUnit_iff_coprime _ d).mpr hcop
  have hxn : ((((star z1 * z2).re : ZMod d) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹)
      * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))) = ((star z1 * z2).re : ZMod d) := by
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]
  have hmod : (((((star z1 * z2).re : ZMod d)
          * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹).val : ℤ)
        * (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ)) % d = ((star z1 * z2).re) % d := by
    rw [← ZMod.intCast_eq_intCast_iff']
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact hxn
  rw [ratioSym, ← jacobiSym.mul_left]
  exact (jacobiSym.mod_left' hmod).symm

/-! ## 3. The twist is nontrivial (a concrete admissible pair) -/

/-- The twist `(|z₁|²|d)` really takes the value `-1` on admissible data: for the pair
`z₁ = -1 - 2i`, `z₂ = -13 - 14i` (primary, coprime, with squarefree norms `5` and `365`) one has
`Δ = -12` (so `4 ∣ Δ`, the condition under which the frozen sums see the pair) and the twist is
`(5 | 12) = (5 | 3) = -1`.  (Exhaustive search over primary pairs with coordinates in `[-40,40]`,
squarefree norms, `(z₁,z₂) = 1` and `4 ∣ Δ`: the twist `(|z₁|²||Δ|)` is `-1` on 167908 of 342318
pairs — it is sign-random, and *FI*'s `mod 8` condition does not trivialise it.) -/
theorem twist_nontrivial : jacobiSym (5 : ℤ) 12 = -1 := by
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  have h2 : jacobiSym (5 : ℤ) 2 = 1 := by norm_num
  have h3 : jacobiSym (5 : ℤ) 3 = -1 := by norm_num
  rw [h12, jacobiSym.mul_right, jacobiSym.pow_right, h2, h3]
  norm_num

end

end Work.FIArea7
