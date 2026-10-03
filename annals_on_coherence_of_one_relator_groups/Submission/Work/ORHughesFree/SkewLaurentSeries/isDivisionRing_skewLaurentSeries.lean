/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `A((t;τ))` is a division ring when `A` is

Let `A` be a division ring and let the group `Multiplicative ℤ` act on `A` by ring automorphisms
(so that `τ = ofAdd 1` generates the twisting).  Then the skew Laurent series ring
`SkewLaurentSeries A = A((t;τ))` of [JZLA20, §3.1] is a division ring.

The argument is the classical one, in two steps.

* **Vanishing filtration.** `VanishesBelow f N` (in `SkewLaurentSeries.VanishesBelow`) says that
  all coefficients of `f` below the index `N` vanish.  It is a ring filtration: if `f` vanishes
  below `M` and `g` below `N`, then `f * g` vanishes below `M + N`, hence `u ^ i` vanishes below
  `i`.  Consequently the geometric series `∑_{i ≥ 0} (-u)^i` is a series (finitely many terms
  contribute to each coefficient) and inverts `1 + u` whenever `u` vanishes below `1`; this is
  `isUnit_one_add_of_vanishesBelow_one`.

* **Leading term.**  A series `f` vanishing below `m` is `tᵐ · shift m f`, where `shift m f` has
  constant coefficient `(-m) • f_m` and vanishes below `0` (`mono_mul_shift`,
  `VanishesBelow.shift`).  Units of `A((t;τ))` are closed under multiplication by the monomials
  `a·tᵐ` with `a` a unit (`isUnit_mono_of_isUnit`), so it suffices to invert series whose constant
  coefficient is a unit; writing such an `f` as `c·(1 + w)` with `w` vanishing below `1` reduces
  this to the geometric series.  Since every nonzero series has a least nonzero coefficient
  (`exists_least_nonzero_coeff`), whose value is nonzero and hence a unit in the division ring `A`,
  every nonzero element of `A((t;τ))` is a unit.
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_one_add_of_vanishesBelow_one
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_mono_of_isUnit
import Submission.Work.ORHughesFree.DivisionClosure

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Work.ORHughesFree
namespace SkewLaurentSeries

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- **Units with invertible constant term.**  If `f` vanishes below `0` and its constant
coefficient `c = f₀` is a unit of `A`, then `f` is a unit of `A((t;τ))`.

Write `f = c·(1 + w)` with `w = c⁻¹·(f - c)`: the correction series `f - c` vanishes below `0` and
has zero constant coefficient, hence vanishes below `1`, and multiplying by the monomial `c⁻¹`
keeps it below `1`.  So `1 + w` is a unit by the geometric series lemma, and `c` is a unit. -/
theorem isUnit_of_isUnit_coeff_zero {f : SkewLaurentSeries A} (hf : VanishesBelow f 0)
    (h0 : IsUnit (f.1 0)) : IsUnit f := by
  obtain ⟨u, hu⟩ := h0
  have hsub0 : VanishesBelow (f - mono 0 (u : A)) 0 :=
    hf.sub (mono_vanishesBelow 0 (u : A) le_rfl)
  have hsub1 : VanishesBelow (f - mono 0 (u : A)) 1 := by
    refine hsub0.succ ?_
    rw [sub_apply, mono_apply, if_pos rfl, ← hu, sub_self]
  have hw : VanishesBelow (mono 0 (↑u⁻¹ : A) * (f - mono 0 (u : A))) 1 := by
    have h := (mono_vanishesBelow 0 (↑u⁻¹ : A) (N := 0) le_rfl).mul hsub1
    simpa using h
  have hmm : mono (0 : ℤ) (u : A) * mono (0 : ℤ) (↑u⁻¹ : A) = 1 := by
    rw [mono_mul, show (0 : ℤ) + 0 = 0 by ring]
    rw [show (u : A) * (Multiplicative.ofAdd (0 : ℤ) • (↑u⁻¹ : A)) = 1 by
      rw [ofAdd_zero, one_smul]
      exact Units.mul_inv u]
    exact mono_zero_one
  have hfac : mono (0 : ℤ) (u : A) * (1 + mono 0 (↑u⁻¹ : A) * (f - mono 0 (u : A))) = f := by
    rw [mul_add, mul_one, ← mul_assoc, hmm, one_mul]
    abel
  have hunit : IsUnit (mono 0 (u : A) * (1 + mono 0 (↑u⁻¹ : A) * (f - mono 0 (u : A)))) :=
    (isUnit_mono_of_isUnit 0 (show IsUnit (u : A) from ⟨u, rfl⟩)).mul
      (isUnit_one_add_of_vanishesBelow_one hw)
  rw [hfac] at hunit
  exact hunit

/-- **Units with invertible leading coefficient.**  If `f` vanishes below `m` and its `m`-th
coefficient is a unit of `A`, then `f` is a unit of `A((t;τ))`.

Indeed `f = tᵐ · shift m f` (`mono_mul_shift`), the shift vanishes below `0`
(`VanishesBelow.shift`) and its constant coefficient is `(-m) • f_m`, a unit because the action of
`Multiplicative ℤ` is by ring automorphisms.  So the shift is a unit with invertible constant term,
and `tᵐ` is a unit. -/
theorem isUnit_of_isUnit_coeff {f : SkewLaurentSeries A} {m : ℤ} (hm : VanishesBelow f m)
    (h : IsUnit (f.1 m)) : IsUnit f := by
  have hg : VanishesBelow (shift m f) 0 := hm.shift
  have hg0 : IsUnit ((shift m f).1 0) := by
    rw [shift_apply, show m + 0 = m by ring]
    have h' := h.map (MulSemiringAction.toRingHom (Multiplicative ℤ) A (Multiplicative.ofAdd (-m)))
    simpa only [MulSemiringAction.toRingHom_apply] using h'
  have hunit : IsUnit (mono m (1 : A) * shift m f) :=
    (isUnit_mono_of_isUnit m isUnit_one).mul (isUnit_of_isUnit_coeff_zero hg hg0)
  rwa [mono_mul_shift] at hunit

/-- **[JZLA20, §3.1]**: the skew Laurent series ring `A((t;τ))` over a division ring `A` is a
division ring.

It is nontrivial because `x ↦ x·t⁰` is injective, and every nonzero series `f` has a least nonzero
coefficient `f_m` (`exists_least_nonzero_coeff`), which is a nonzero element of the division ring
`A`, hence a unit; by the leading-term criterion `f` is then a unit. -/
theorem isDivisionRing_skewLaurentSeries {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] (hA : IsDivisionRing A) : IsDivisionRing (SkewLaurentSeries A) := by
  obtain ⟨hnt, hunits⟩ := hA
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hnt
    exact ⟨mono 0 x, mono 0 y, fun h => hxy (by
      have h' := congrArg (fun f : SkewLaurentSeries A => f.1 0) h
      simpa using h')⟩
  · intro f hf
    obtain ⟨m, hmne, hm⟩ := exists_least_nonzero_coeff f hf
    exact isUnit_of_isUnit_coeff hm (hunits (f.1 m) hmne)

end SkewLaurentSeries
end Work.ORHughesFree
