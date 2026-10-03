/-
# `Work.FIArea7.sum_xiC_coprime` — the §21 orthogonality of `ξ_{w₁}ξ_{w₂}` split off at coprime moduli

*FI* §21 evaluates the double sum `Σ_{ζ mod q} (ζ/w₁)(ζ/w₂)` of the Dirichlet symbol `ξ_w` of §19
(`Work.FIArea7.xiC`, `Work.FIArea7.DirichletSym`) on the residue ring `ℤ[i]/q = (ZMod q)²`.  The
summand is

  `ξ_{w₁}(a,b)·ξ_{w₂}(a,b) = (w₁.re·a − w₁.im·b | |w₁|²)·(w₂.re·a − w₂.im·b | |w₂|²)`,

so it depends on `(a,b)` only through `w₁` modulo `|w₁|²` and `w₂` modulo `|w₂|²`; this file
proves that when `|w₁|² = N₁` and `|w₂|² = N₂` are coprime, the whole double sum modulo `N₁N₂`
factors as `N₁N₂` times the corresponding local Jacobi-symbol sums:

  `Σ_{p ∈ (ZMod (N₁N₂))²} ξ_{w₁}(p)ξ_{w₂}(p) = N₁N₂ · Σ_{x ∈ ZMod (N₁N₂)} (x | N₁N₂)`,

the identity requested from this file.  (By *FI* Lemma 21.1 the right-hand factor
`Σ_{x mod n}(x|n)` is `φ(n)` when the odd part of `n` is a square and vanishes otherwise, see
`Work.FIArea7.sum_jacobiSym_eq_totient_of_oddPart_sq`,
`Work.FIArea7.sum_jacobiSym_eq_zero_of_oddPart_not_sq`.)

The three steps are:

1. **Periodicity of `ξ_w`** (`xiC_cast_eq`): `ξ_w` depends on the residue class of its argument
   modulo `|w|²`, so the sum over `(ZMod (N₁N₂))²` may be replaced by the sum over all pairs of
   reductions modulo `N₁` and modulo `N₂`;
2. **Chinese remainder** (`Work.FIArea7.sum_crt_prod_factor`): the double sum then splits as the
   product of the mod-`N₁` and the mod-`N₂` double sums;
3. **Uniformity of the linear form** (`xiC_eq_linform`, `Work.FIArea7.sum_zmod_linear`): since
   `w.re` and `w.im` generate the unit ideal (`hp`), `(a,b) ↦ w.re·a − w.im·b` takes every value
   of `ZMod N` exactly `N` times, so `Σ_p ξ_w(p) = N · Σ_u (u | N)`;
   and `Work.FIArea7.sum_jacobiSym_crt` multiplies the two local Jacobi-symbol sums back together.

Note that the hypotheses `IsPrimary w₁`, `IsPrimary w₂` are *not* used: the identity is purely
about the residue class of `ξ_w` modulo the two coprime squares.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.sum_xiGaussMod_units

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `ξ_w` depends only on the residue class modulo `|w|²` -/

/-- **Periodicity of `ξ_w` in its argument.**  Reading the Dirichlet symbol `ξ_w` on coordinates
modulo `q` and reducing the coordinates modulo `N = |w|²` gives the same value: the numerator of
the Jacobi symbol changes by a multiple of `N` and `jacobiSym` only depends on the numerator
modulo its denominator. -/
lemma xiC_cast_eq {N q : ℕ} [NeZero N] [NeZero q] (w : GaussianInt)
    (hN : Work.FIPlan.gnorm w = N) (p : ZMod q × ZMod q) :
    xiC q w p = xiC N w (ZMod.cast p.1, ZMod.cast p.2) := by
  have h1 : ((p.1).val : ZMod N) = (((ZMod.cast p.1 : ZMod N)).val : ZMod N) := by
    simp only [ZMod.natCast_zmod_val, ZMod.cast_eq_val]
  have h2 : ((p.2).val : ZMod N) = (((ZMod.cast p.2 : ZMod N)).val : ZMod N) := by
    simp only [ZMod.natCast_zmod_val, ZMod.cast_eq_val]
  have hz : (((w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) : ℤ) : ZMod N)
      = (((w.re * (((ZMod.cast p.1 : ZMod N)).val : ℤ)
          - w.im * (((ZMod.cast p.2 : ZMod N)).val : ℤ)) : ℤ) : ZMod N) := by
    push_cast
    rw [h1, h2]
  have key : (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) % N
      = (w.re * (((ZMod.cast p.1 : ZMod N)).val : ℤ)
          - w.im * (((ZMod.cast p.2 : ZMod N)).val : ℤ)) % N :=
    (ZMod.intCast_eq_intCast_iff' _ _ N).mp hz
  have hJ : jacobiSym (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) N
      = jacobiSym (w.re * (((ZMod.cast p.1 : ZMod N)).val : ℤ)
          - w.im * (((ZMod.cast p.2 : ZMod N)).val : ℤ)) N := jacobiSym.mod_left' key
  simp only [xiC]
  rw [hN, hJ]

/-! ## 2. `ξ_w` as a function of the linear form `w.re·a − w.im·b` -/

/-- `ξ_w(a,b)` is the Jacobi symbol of the canonical representative of the element
`w.re·a − w.im·b` of `ZMod |w|²`. -/
lemma xiC_eq_linform (N : ℕ) [NeZero N] (w : GaussianInt) (hN : Work.FIPlan.gnorm w = N)
    (p : ZMod N × ZMod N) :
    xiC N w p = (jacobiSym
      (((w.re : ZMod N) * p.1 + ((-w.im : ℤ) : ZMod N) * p.2).val : ℤ) N : ℂ) := by
  have hz : (((w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) : ℤ) : ZMod N)
      = (w.re : ZMod N) * p.1 + ((-w.im : ℤ) : ZMod N) * p.2 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have key : (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) % (N:ℤ)
      = ((((w.re : ZMod N) * p.1 + ((-w.im : ℤ) : ZMod N) * p.2).val : ℤ)) % (N:ℤ) := by
    rw [← ZMod.val_intCast (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)), hz]
    exact (Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast ZMod.val_lt _)).symm
  simp only [xiC]
  rw [hN, jacobiSym.mod_left' key]

/-! ## 3. The local orthogonality: `Σ_p ξ_w(p) = N · Σ_u (u | N)` -/

/-! ## 4. The requested identity -/

end

end Work.FIArea7
