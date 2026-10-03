/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `1 + u` is a unit whenever `u` vanishes below `t¹`

The ring `A((t;τ)) = SkewLaurentSeries A` carries the `t`-adic filtration `VanishesBelow`
(see `Submission/Work/ORHughesFree/SkewLaurentSeries/VanishesBelow.lean`), and it is
*separated*: a series all of whose coefficients vanish is `0`.  Since the filtration is
multiplicative — `VanishesBelow u 1` gives `VanishesBelow (u^N) N` — the element `1 + u` is
invertible, with inverse the geometric series `∑_{i≥0} (-u)^i`.  The series is a well defined
element of `A((t;τ))` because its `n`-th coefficient is the *finite* sum `∑_{i≤n} (-u)^i`
(only the terms with `i ≤ n` can contribute to degree `n`, as `(-u)^i` vanishes below `i`).

The formal argument, which is the one used below, avoids any topological discussion.  Write
`x = -u`, so that `1 + u = 1 - x`, and let `v = ∑_{i≥0} x^i` and `p_N = ∑_{i<N} x^i`.  Then

* `(1 - x) * p_N = 1 - x^N` (the telescoping identity `mul_neg_geom_sum`), and
* `v - p_N` vanishes below `N` (the two series agree in all degrees `< N`),

so
`(1 - x) * v - 1 = (1 - x) * (v - p_N) - x^N` vanishes below `0 + N = N`.  As `N` is
arbitrary and the filtration is separated, `(1 - x) * v = 1`.  The same computation with the
factors interchanged gives `v * (1 - x) = 1`, hence `1 + u = 1 - x` is a unit.
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.SkewLaurentSeries

section

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- The geometric series `∑_{i≥0} x^i`, regarded as an element of the skew Laurent series ring.
It is well defined whenever `x` vanishes below `1`, but the definition only needs the weaker
fact that `x ^ i` vanishes below `i`, which is what makes the `n`-th coefficient the finite sum
over `i ≤ n`.  We index that sum by `range ((n+1).toNat)`, so that it is empty for `n < 0`. -/
noncomputable def geomSeries (x : SkewLaurentSeries A) : SkewLaurentSeries A :=
  ⟨fun n => ∑ i ∈ Finset.range ((n+1).toNat), (x ^ i).1 n,
    ⟨0, fun n hn => by
      have : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      simp [this]⟩⟩

@[simp] theorem geomSeries_apply (x : SkewLaurentSeries A) (n : ℤ) :
    (geomSeries x).1 n = ∑ i ∈ Finset.range ((n+1).toNat), (x ^ i).1 n := rfl

/-- The geometric series vanishes below `0`. -/
theorem geomSeries_vanishesBelow (x : SkewLaurentSeries A) : VanishesBelow (geomSeries x) 0 := by
  intro n hn
  have : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  simp [this]

/-- **The truncation lemma.**  The geometric series of `x` agrees with its partial sum
`∑_{i<N} x^i` in all degrees `< N`, i.e. their difference vanishes below `N`.  This is where the
hypothesis `VanishesBelow x 1` is used: the terms of the full series that are absent from the
partial sum are the `x^i` with `i ≥ N > n`, and `x^i` vanishes below `i`. -/
theorem geomSeries_sub_partialSum_vanishesBelow {x : SkewLaurentSeries A}
    (hx : VanishesBelow x 1) (N : ℕ) :
    VanishesBelow (geomSeries x - ∑ i ∈ Finset.range N, x ^ i) (N : ℤ) := by
  intro n hn
  rw [SkewLaurentSeries.sub_apply, SkewLaurentSeries.sum_apply, geomSeries_apply]
  rcases lt_or_ge n 0 with hn0 | hn0
  · -- `n < 0`: both sides vanish, the geometric series because the interval `[0, n]` is empty,
    -- the partial sum because every `x ^ i` vanishes below `i ≥ 0 > n`.
    have h1 : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have hL : ∑ i ∈ Finset.range ((n+1).toNat), (x ^ i).1 n = 0 := by simp [h1]
    have hR : ∑ i ∈ Finset.range N, (x ^ i).1 n = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact VanishesBelow.pow hx i n (by omega)
    rw [hL, hR, sub_zero]
  · -- `0 ≤ n < N`: the partial sum `∑_{i < n+1} x^i` is a sub-sum of `∑_{i < N} x^i`, and the
    -- extra terms `i ≥ n + 1` vanish in degree `n`.
    have h1 : (n + 1).toNat = n.toNat + 1 := by omega
    have hsub : Finset.range (n.toNat + 1) ⊆ Finset.range N := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      have : (i : ℤ) ≤ n := by
        have h2 : (i : ℤ) < (n.toNat : ℤ) + 1 := by exact_mod_cast hi
        rw [Int.toNat_of_nonneg hn0] at h2
        omega
      omega
    have hsum : ∑ i ∈ Finset.range (n.toNat + 1), (x ^ i).1 n
        = ∑ i ∈ Finset.range N, (x ^ i).1 n := by
      apply Finset.sum_subset hsub
      intro i _ hi'
      simp only [Finset.mem_range] at hi'
      have hi2 : n.toNat + 1 ≤ i := by omega
      apply VanishesBelow.pow hx i n
      have : (n.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hi2
      rw [Int.toNat_of_nonneg hn0] at this
      omega
    rw [h1, hsum]
    exact sub_self _

/-- The `t`-adic filtration is separated: a series vanishing below every natural bound is `0`. -/
theorem eq_zero_of_vanishesBelow_all {f : SkewLaurentSeries A}
    (h : ∀ N : ℕ, VanishesBelow f (N : ℤ)) : f = 0 := by
  apply Subtype.ext
  funext n
  exact h ((n + 1).toNat) n (by omega)

/-- If `x` vanishes below `1` then `(1 - x) * geomSeries x = 1`. -/
theorem one_sub_mul_geomSeries {x : SkewLaurentSeries A} (hx : VanishesBelow x 1) :
    (1 - x) * geomSeries x = 1 := by
  have hz : (1 - x) * geomSeries x - 1 = 0 := by
    apply eq_zero_of_vanishesBelow_all
    intro N
    have h1x : VanishesBelow (1 - x) 0 := by
      rw [sub_eq_add_neg]
      exact VanishesBelow.add (VanishesBelow.one 0 le_rfl)
        ((VanishesBelow.neg hx).mono (by norm_num))
    have htrunc := geomSeries_sub_partialSum_vanishesBelow hx N
    have hgeom : (1 - x) * (∑ i ∈ Finset.range N, x ^ i) = 1 - x ^ N :=
      mul_neg_geom_sum x N
    have hprod : VanishesBelow
        ((1 - x) * (geomSeries x - ∑ i ∈ Finset.range N, x ^ i)) (N : ℤ) := by
      have := VanishesBelow.mul h1x htrunc
      simpa using this
    have hpow : VanishesBelow (-(x ^ N)) (N : ℤ) := (VanishesBelow.pow hx N).neg
    have hdecomp : (1 - x) * geomSeries x - 1
        = (1 - x) * (geomSeries x - ∑ i ∈ Finset.range N, x ^ i)
          + ((1 - x) * (∑ i ∈ Finset.range N, x ^ i) - 1) := by
      noncomm_ring
    have h2 : (1 - x) * (∑ i ∈ Finset.range N, x ^ i) - 1 = -(x ^ N) := by
      rw [hgeom]; noncomm_ring
    rw [hdecomp, h2]
    exact hprod.add hpow
  rw [sub_eq_zero] at hz
  exact hz

/-- If `x` vanishes below `1` then `geomSeries x * (1 - x) = 1`. -/
theorem geomSeries_mul_one_sub {x : SkewLaurentSeries A} (hx : VanishesBelow x 1) :
    geomSeries x * (1 - x) = 1 := by
  have hz : geomSeries x * (1 - x) - 1 = 0 := by
    apply eq_zero_of_vanishesBelow_all
    intro N
    have h1x : VanishesBelow (1 - x) 0 := by
      rw [sub_eq_add_neg]
      exact VanishesBelow.add (VanishesBelow.one 0 le_rfl)
        ((VanishesBelow.neg hx).mono (by norm_num))
    have htrunc := geomSeries_sub_partialSum_vanishesBelow hx N
    have hgeom : (∑ i ∈ Finset.range N, x ^ i) * (1 - x) = 1 - x ^ N :=
      geom_sum_mul_neg x N
    have hprod : VanishesBelow
        ((geomSeries x - ∑ i ∈ Finset.range N, x ^ i) * (1 - x)) (N : ℤ) := by
      have := VanishesBelow.mul htrunc h1x
      simpa using this
    have hpow : VanishesBelow (-(x ^ N)) (N : ℤ) := (VanishesBelow.pow hx N).neg
    have hdecomp : geomSeries x * (1 - x) - 1
        = (geomSeries x - ∑ i ∈ Finset.range N, x ^ i) * (1 - x)
          + ((∑ i ∈ Finset.range N, x ^ i) * (1 - x) - 1) := by
      noncomm_ring
    have h2 : (∑ i ∈ Finset.range N, x ^ i) * (1 - x) - 1 = -(x ^ N) := by
      rw [hgeom]; noncomm_ring
    rw [hdecomp, h2]
    exact hprod.add hpow
  rw [sub_eq_zero] at hz
  exact hz

/-- If `x` vanishes below `1` then `1 - x` is a unit, with inverse the geometric series
`∑_{i≥0} x^i`. -/
theorem isUnit_one_sub_of_vanishesBelow_one {x : SkewLaurentSeries A} (hx : VanishesBelow x 1) :
    IsUnit (1 - x) :=
  ⟨⟨1 - x, geomSeries x, one_sub_mul_geomSeries hx, geomSeries_mul_one_sub hx⟩, rfl⟩

end

/-- If `u` vanishes below `t¹` then `1 + u` is a unit of `A((t;τ))`: apply the geometric series
construction to `x = -u`, for which `1 - x = 1 + u`. -/
theorem isUnit_one_add_of_vanishesBelow_one {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] {u : SkewLaurentSeries A} (hu : VanishesBelow u 1) : IsUnit (1 + u) := by
  have h := isUnit_one_sub_of_vanishesBelow_one (A := A) hu.neg
  simpa [sub_neg_eq_add] using h

end Work.ORHughesFree.SkewLaurentSeries
