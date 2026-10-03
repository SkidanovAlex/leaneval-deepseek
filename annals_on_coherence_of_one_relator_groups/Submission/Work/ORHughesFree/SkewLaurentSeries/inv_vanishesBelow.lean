/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inverse of a series of order `m` vanishes below `t^(-m)`

Let `A` be a division ring and let `Multiplicative ℤ` act on `A` by ring automorphisms, so that
`SkewLaurentSeries A = A((t;τ))` is the skew Laurent series ring of [JZLA20, §3.1].  For a
nonzero series `f` the *order* of `f` is the least index `m` at which `f` has a nonzero
coefficient; `VanishesBelow f m` together with `f.1 m ≠ 0` says precisely that `m` is the order
of `f`.

The skew Laurent series ring over a division ring is itself a division ring
(`isDivisionRing_skewLaurentSeries`), so `f` has a two-sided inverse; the content of this file is
the *filtration* statement that this inverse has order exactly `-m`, i.e. that it vanishes below
`-m`.  This is the algebraic shadow of the formal identity
`(∑ₖ fₖ tᵏ)⁻¹ = f_m⁻¹ t^(-m) (1 + …)`.

The proof does not construct the inverse; it only reads off its order.  Let `g` be a two-sided
inverse of `f` and let `k₀` be the order of `g` (`exists_least_nonzero_coeff`).  Since `g`
vanishes below `k₀` and `f` vanishes below `m`, the coefficient of `g * f` in degree `k₀ + m` is,
by the leading-term computation `mul_apply_leading` below, the single term
`g.1 k₀ * (k₀ • f.1 m)`.  But `g * f = 1`, so that coefficient is `1` if `k₀ + m = 0` and `0`
otherwise.  Both factors `g.1 k₀` and `k₀ • f.1 m` are nonzero — the first by choice of `k₀`, the
second because `f.1 m ≠ 0` and the action is by ring automorphisms, so it is `IsUnit` and hence
nonzero — and `A` is a division ring, hence has no zero divisors.  So the product is nonzero, which
forces `k₀ + m = 0`, i.e. `k₀ = -m`.  Since `g` vanishes below its order `k₀`, it vanishes below
`-m`.
-/
import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_one_add_of_vanishesBelow_one
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_mono_of_isUnit
import Submission.Work.ORHughesFree.SkewLaurentSeries.isDivisionRing_skewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff

set_option autoImplicit false

namespace Work.ORHughesFree.SkewLaurentSeries

/-- **The leading term of a product.**  If `g` vanishes below `k₀` and `f` vanishes below `m`, then
the coefficient of `g * f` in degree `k₀ + m` receives the single contribution
`g.1 k₀ * (k₀ • f.1 m)`.

Indeed, by the truncated convolution formula `mul_apply_of_bounds` the relevant sum runs over
`Finset.Icc k₀ (k₀ + m - m) = {k₀}`. -/
theorem mul_apply_leading {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {g f : SkewLaurentSeries A} {k₀ m : ℤ}
    (hg : VanishesBelow g k₀) (hf : VanishesBelow f m) :
    (g * f).1 (k₀ + m) = g.1 k₀ * ((Multiplicative.ofAdd k₀) • f.1 m) := by
  rw [mul_apply_of_bounds g f k₀ m hg hf (k₀ + m),
    show k₀ + m - m = k₀ by ring, Finset.Icc_self, Finset.sum_singleton,
    show k₀ + m - k₀ = m by ring]

/-- **The inverse of a series of order `m` vanishes below `t^(-m)`.**  If `A` is a division ring, if
`f` vanishes below `m` and its `m`-th coefficient is nonzero — so that `m` is the least index at
which `f` has a nonzero coefficient — then `f` is a unit of `A((t;τ))` and the chosen two-sided
inverse `g` vanishes below `-m`. -/
theorem inv_vanishesBelow {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (hA : Work.ORHughesFree.IsDivisionRing A) {f : Work.ORHughesFree.SkewLaurentSeries A} {m : ℤ}
    (hm : Work.ORHughesFree.SkewLaurentSeries.VanishesBelow f m) (hm' : f.1 m ≠ 0) :
    ∃ g : Work.ORHughesFree.SkewLaurentSeries A, f * g = 1 ∧ g * f = 1 ∧
      Work.ORHughesFree.SkewLaurentSeries.VanishesBelow g (-m) := by
  classical
  -- `A((t;τ))` is a division ring, so `f ≠ 0` has a two-sided inverse `↑u⁻¹`.
  have hS : IsDivisionRing (SkewLaurentSeries A) := isDivisionRing_skewLaurentSeries hA
  have hntA : Nontrivial A := hA.1
  have hntS : Nontrivial (SkewLaurentSeries A) := hS.1
  have hf_ne : f ≠ 0 := fun h => hm' (by rw [h]; rfl)
  obtain ⟨u, hu⟩ := hS.2 f hf_ne
  have hfg : f * (↑(u⁻¹) : SkewLaurentSeries A) = 1 := by rw [← hu, Units.mul_inv]
  have hgf : (↑(u⁻¹) : SkewLaurentSeries A) * f = 1 := by rw [← hu, Units.inv_mul]
  have hg_ne : (↑(u⁻¹) : SkewLaurentSeries A) ≠ 0 := by
    intro h
    have h1 : (1 : SkewLaurentSeries A) = 0 := by rw [← hgf, h, zero_mul]
    exact one_ne_zero h1
  -- `k₀` is the order of the inverse, i.e. its least nonzero coefficient.
  obtain ⟨k₀, hk₀, hk₀v⟩ := exists_least_nonzero_coeff (↑(u⁻¹) : SkewLaurentSeries A) hg_ne
  -- the degree `k₀ + m` coefficient of `g * f` is the single term `g.1 k₀ * (k₀ • f.1 m)`
  have hsum := mul_apply_leading (g := (↑(u⁻¹) : SkewLaurentSeries A)) (f := f) hk₀v hm
  have hprod_eq : (↑(u⁻¹) : SkewLaurentSeries A).1 k₀ * ((Multiplicative.ofAdd k₀) • f.1 m)
      = (if k₀ + m = 0 then (1 : A) else 0) := by
    rw [← hsum, hgf, one_apply]
  -- both factors are nonzero: `f.1 m` is a unit of the division ring `A`, and the action is by
  -- ring automorphisms
  have hsmul : (Multiplicative.ofAdd k₀) • f.1 m ≠ 0 := by
    have h := (hA.2 (f.1 m) hm').map
      (MulSemiringAction.toRingHom (Multiplicative ℤ) A (Multiplicative.ofAdd k₀))
    simpa using h.ne_zero
  -- hence `k₀ + m = 0`: `A` has no zero divisors
  have hk0 : k₀ = -m := by
    by_contra hne
    have hzero : (if k₀ + m = 0 then (1 : A) else 0) = 0 := if_neg (by omega)
    rw [hzero] at hprod_eq
    have hz : (Multiplicative.ofAdd k₀) • f.1 m = 0 :=
      (IsUnit.mul_right_eq_zero (a := (↑(u⁻¹) : SkewLaurentSeries A).1 k₀)
        (hA.2 _ hk₀)).mp hprod_eq
    exact hsmul hz
  refine ⟨↑(u⁻¹), hfg, hgf, ?_⟩
  rw [← hk0]
  exact hk₀v

end Work.ORHughesFree.SkewLaurentSeries
