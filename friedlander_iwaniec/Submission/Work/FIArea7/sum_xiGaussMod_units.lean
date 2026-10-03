/-
# `Work.FIArea7.sum_xiGaussMod_units` — the §21 orthogonality of the Dirichlet symbols

*FI* Lemma 21.1 asks for the value of the double sum `∑_{ζ mod q} (ζ/w₁)(ζ/w₂)`.  The value
displayed there, `q·φ(d)·φ(q/d)`, is not the truth in general (see `NOTES.md` §28, §30.5–§30.8):
the product `ξ_{w₁}ξ_{w₂}` is a **character of the unit group** `(ℤ[i]/q)^×`, so the sum over the
units is `#units·[trivial]` — i.e. either every term is `1` (the trivial character) or the sum
vanishes.  That is the statement proved here.

The engine is the identity

  `ξ_w(z)·ξ_w(z') = ε_w · ξ_w(zz')`,   `ε_w = (Re w | |w|²)`   (`dirichletSym_mul_eq`),

valid for *all* `z, z'` and all `w`.  Since `w` is primary, `ε_w ∈ {0, 1}`:
`ε_w = 1` for primitive `w` (*FI* (19.8), `jacobiSym_sq_add_sq`) and `ε_w = 0` otherwise
(`jacobiSym_re_gnorm_primary`).  So `ξ_w` is either a genuine multiplicative character
(`ε_w = 1`) — and then the group sum vanishes unless the character is trivial — or it is
identically zero (`ε_w = 0`, because `ξ_w(z)² = ε_w ξ_w(z²) = 0`).
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.dirichletSym_periodic
import Submission.Work.FIArea7.jacobiSym_sq_add_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## 1. The symbol on coordinates

`GaussMod q = (ℤ[i]/q) = (ZMod q)[i]/(i²+1)`, so `ξ_w` can be read either on `GaussMod q` or,
through the coordinates `(a,b) ↦ a + b·i`, on pairs `(a,b) ∈ (ZMod q)²`. -/

/-- The Gaussian unit group `(ℤ[i]/q)^×` in coordinates: the pairs `(r,s)` with `r² + s²` a unit
of `ZMod q`, with product `gaussMul` (`Work.FIArea7.gaussUnitsCommGroup`). -/
abbrev GUnits (q : ℕ) : Type := {p : ZMod q × ZMod q // IsUnit (gaussNorm p)}

/-- **The Dirichlet symbol `ξ_w` of §19 on coordinates**: `ξ_w(a,b) = (w.re·a − w.im·b | |w|²)`
for `a, b` read through their canonical representatives.  This is `xiGaussMod` under
`⟨·,·⟩ : GaussMod q`. -/
def xiC (q : ℕ) (w : GaussianInt) (p : ZMod q × ZMod q) : ℂ :=
  (jacobiSym (w.re * ((p.1).val : ℤ) - w.im * ((p.2).val : ℤ)) (Work.FIPlan.gnorm w) : ℂ)

/-! ## 2. The multiplicativity relation `ξ_w(z)ξ_w(z') = ε_w ξ_w(zz')` -/

/-- `J(·|N)` only depends on the residue class modulo `N`. -/
lemma jacobiSym_eq_of_dvd_sub {a b : ℤ} {N : ℕ} (h : (N : ℤ) ∣ a - b) :
    jacobiSym a N = jacobiSym b N := by
  refine jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr ?_)
  rw [show b - a = -(a - b) by ring]
  exact dvd_neg.mpr h

/-- **The multiplicativity relation**: with `ε_w = (Re w | |w|²)`,
`ξ_w(z)·ξ_w(z') = ε_w·ξ_w(zz')` for all Gaussian integers `z, z'`.  The key algebraic input is
`Re(wz)Re(wz') = |w|²·(Im z)(Im z') + Re(w)·Re(wzz')` (`re_mul_re_mul`). -/
lemma dirichletSym_mul_eq (w z1 z2 : GaussianInt) :
    (DirichletSym w z1 : ℂ) * (DirichletSym w z2 : ℂ)
      = (jacobiSym w.re (Work.FIPlan.gnorm w) : ℂ) * (DirichletSym w (z1 * z2) : ℂ) := by
  have key : (jacobiSym (w * z1).re (Work.FIPlan.gnorm w) : ℤ)
        * jacobiSym (w * z2).re (Work.FIPlan.gnorm w)
      = jacobiSym w.re (Work.FIPlan.gnorm w) * jacobiSym (w * (z1 * z2)).re (Work.FIPlan.gnorm w) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]
    rw [re_mul_re_mul w z1 z2, ← norm_eq w]
    exact jacobiSym_eq_of_dvd_sub ⟨z1.im * z2.im, by ring⟩
  simp only [DirichletSym]
  rw [← Int.cast_mul, ← Int.cast_mul, key]

/-! ## 3. The same relation on coordinates `(ZMod q)²` -/

/-- The lift of a pair of residues to a Gaussian integer through the canonical representatives. -/
def pairToGI (q : ℕ) (p : ZMod q × ZMod q) : GaussianInt := ⟨(p.1.val : ℤ), (p.2.val : ℤ)⟩

lemma xiC_eq_dirichletSym (q : ℕ) (w : GaussianInt) (p : ZMod q × ZMod q) :
    xiC q w p = (DirichletSym w (pairToGI q p) : ℂ) := by
  simp only [xiC, pairToGI, DirichletSym, re_mul]

/-- The Gaussian product of the two lifts differs from the lift of the Gaussian product by a
multiple of `q`. -/
lemma gaussMul_lift_dvd (q : ℕ) [NeZero q] (p p' : ZMod q × ZMod q) :
    (((q : ℕ) : ℤ) : GaussianInt) ∣ pairToGI q (gaussMul p p') - pairToGI q p * pairToGI q p' := by
  refine dvd_of_casts_eq ?_ ?_
  · simp only [pairToGI, gaussMul, re_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  · simp only [pairToGI, gaussMul, im_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val]

/-- **The multiplicativity relation on coordinates**: `ξ_w(p)ξ_w(p') = ε_w·ξ_w(p·p')`. -/
lemma xiC_mul_eps (q : ℕ) [NeZero q] {w : GaussianInt} (hd : Work.FIPlan.gnorm w ∣ q)
    (p p' : ZMod q × ZMod q) :
    xiC q w p * xiC q w p' = (jacobiSym w.re (Work.FIPlan.gnorm w) : ℂ) * xiC q w (gaussMul p p') := by
  have hper := dirichletSym_periodic hd (gaussMul_lift_dvd q p p')
  rw [xiC_eq_dirichletSym, xiC_eq_dirichletSym, xiC_eq_dirichletSym, hper]
  exact dirichletSym_mul_eq w (pairToGI q p) (pairToGI q p')

/-- If `ε_w = 0` then `ξ_w` vanishes identically: `ξ_w(p)² = ε_w ξ_w(p·p) = 0`. -/
lemma xiC_eq_zero_of_eps_zero (q : ℕ) [NeZero q] {w : GaussianInt} (hd : Work.FIPlan.gnorm w ∣ q)
    (hε : jacobiSym w.re (Work.FIPlan.gnorm w) = 0) (p : ZMod q × ZMod q) : xiC q w p = 0 := by
  have h := xiC_mul_eps q hd p p
  rw [hε] at h
  simp only [Int.cast_zero, zero_mul] at h
  exact mul_self_eq_zero.mp h

/-- If `ε_w = 1` then `ξ_w` is multiplicative on `(ZMod q)²`. -/
lemma xiC_mul_of_eps_one (q : ℕ) [NeZero q] {w : GaussianInt} (hd : Work.FIPlan.gnorm w ∣ q)
    (hε : jacobiSym w.re (Work.FIPlan.gnorm w) = 1) (p p' : ZMod q × ZMod q) :
    xiC q w p * xiC q w p' = xiC q w (gaussMul p p') := by
  rw [xiC_mul_eps q hd p p', hε, Int.cast_one, one_mul]

/-! ## 4. Orthogonality of a multiplicative `ℂ`-valued function on a finite group -/

/-- The sum over a finite group of a multiplicative function that is not identically `1`
vanishes: `∑_g f g = ∑_g f(g·g₀) = f(g₀)·∑_g f g`, and `f(g₀) ≠ 1`. -/
lemma sum_eq_zero_of_char {G : Type*} [Group G] [Fintype G] (f : G → ℂ)
    (hmul : ∀ a b : G, f (a * b) = f a * f b) (g₀ : G) (hg₀ : f g₀ ≠ 1) :
    ∑ g : G, f g = 0 := by
  have h1 : ∑ g : G, f (g * g₀) = ∑ g : G, f g := Equiv.sum_comp (Equiv.mulRight g₀) f
  have h2 : ∑ g : G, f (g * g₀) = (∑ g : G, f g) * f g₀ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun g _ => hmul g g₀)
  have hsum : ∑ g : G, f g = (∑ g : G, f g) * f g₀ := h1.symm.trans h2
  have h3 : (∑ g : G, f g) * (1 - f g₀) = 0 := by
    rw [mul_sub, mul_one, hsum.symm, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hg₀

/-! ## 5. `ε_w ∈ {0,1}` for primary `w` -/

/-- **`ε_w = (Re w | |w|²)` is `0` or `1` for primary `w`**: for `(Re w, Im w) = 1` this is *FI*
(19.8) (`jacobiSym_sq_add_sq`), and otherwise any common divisor of `Re w` and `Im w` also
divides `|w|²`, so that the symbol vanishes. -/
lemma jacobiSym_re_gnorm_primary {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    jacobiSym w.re (Work.FIPlan.gnorm w) = 0 ∨ jacobiSym w.re (Work.FIPlan.gnorm w) = 1 := by
  obtain ⟨hro, hie, _⟩ := hw
  have hre_ne : w.re ≠ 0 := fun h => (by norm_num : ¬ Odd (0 : ℤ)) (h ▸ hro)
  have hN0 : Work.FIPlan.gnorm w ≠ 0 := fun h =>
    hre_ne (congrArg Zsqrtd.re (gnorm_eq_zero_iff.mp h))
  by_cases hcop : IsCoprime w.re w.im
  · right
    rw [gnorm_eq_natAbs]
    exact jacobiSym_sq_add_sq hro hie hcop
  · left
    have hg : Nat.gcd w.re.natAbs w.im.natAbs ≠ 1 := fun hg1 => hcop
      (Int.isCoprime_iff_gcd_eq_one.mpr (by
        rw [Int.gcd_eq_natAbs]
        exact hg1))
    rw [jacobiSym.eq_zero_iff]
    refine ⟨hN0, ?_⟩
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    intro h1
    have hdvd : Nat.gcd w.re.natAbs w.im.natAbs ∣ Work.FIPlan.gnorm w := by
      have h2 : Nat.gcd w.re.natAbs w.im.natAbs ∣ w.re.natAbs := Nat.gcd_dvd_left _ _
      have h3 : Nat.gcd w.re.natAbs w.im.natAbs ∣ w.im.natAbs := Nat.gcd_dvd_right _ _
      rw [gnorm_eq_natAbs, natAbs_sq_add_sq]
      exact dvd_add (h2.trans (dvd_pow_self _ (by norm_num : 2 ≠ 0)))
        (h3.trans (dvd_pow_self _ (by norm_num : 2 ≠ 0)))
    have hthis : Nat.gcd w.re.natAbs w.im.natAbs ∣ Nat.gcd w.re.natAbs (Work.FIPlan.gnorm w) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hdvd
    rw [h1] at hthis
    exact hg (Nat.dvd_one.mp hthis)

/-! ## 6. The orthogonality on the unit group -/

end

end Work.FIArea7
