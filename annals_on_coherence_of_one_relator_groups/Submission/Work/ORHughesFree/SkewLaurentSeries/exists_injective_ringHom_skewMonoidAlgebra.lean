/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The skew monoid algebra `A[t;τ]` sits inside the skew Laurent series ring `A((t;τ))`

The skew monoid algebra `SkewMonoidAlgebra A (Multiplicative ℤ)` is the ring of *finitely*
supported functions `Multiplicative ℤ → A`, while `SkewLaurentSeries A` is the ring of functions
`ℤ → A` vanishing below some bound.  Mapping a finitely supported function to the corresponding
eventually-vanishing function is a ring homomorphism, and it is injective because it is the
identity on coefficient functions (a finitely supported function is a fortiori eventually zero).

The main work is multiplicativity.  On `SkewMonoidAlgebra A (Multiplicative ℤ)` Mathlib's
`SkewMonoidAlgebra.coeff_mul_left` expresses the coefficient of a product as a single Finsupp sum
`∑ a ∈ support x, x_a * (a • y_{a⁻¹ x})`.  The product on `SkewLaurentSeries A` is instead a sum
over the integer interval `Icc (lo x) (n - lo y)`; using `mul_apply_of_bounds` we may replace the
opaque bound `lo` by any valid lower bound, and then `coeff_mul_eq_sum_Icc` identifies the two
sums: the finitely supported sum over `x.support` and the interval sum agree because every term
outside the interval vanishes (either `x` vanishes below `Nx`, or `y` vanishes below `Ny`).
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.SkewLaurentSeries

section

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- The group inverse in `Multiplicative ℤ` corresponds to subtraction of the exponents. -/
theorem ofAdd_inv_mul (k n : ℤ) :
    (Multiplicative.ofAdd k : Multiplicative ℤ)⁻¹ * Multiplicative.ofAdd n
      = Multiplicative.ofAdd (n - k) := by
  rw [← ofAdd_neg, ← ofAdd_add]
  congr 1
  ring

/-- Every element of `SkewMonoidAlgebra A (Multiplicative ℤ)` has a lower bound below which all
its `Multiplicative.ofAdd`-coefficients vanish.  This is the "eventually zero" property that lets
us regard it as an element of the skew Laurent series ring. -/
theorem exists_lower_bound (x : SkewMonoidAlgebra A (Multiplicative ℤ)) :
    ∃ N : ℤ, ∀ n : ℤ, n < N → x.coeff (Multiplicative.ofAdd n) = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      (x.coeff.support.image (fun g : Multiplicative ℤ => g.toAdd)) with hempty | hne
  · refine ⟨0, fun n _ => ?_⟩
    have hsupp : x.coeff.support = ∅ := Finset.image_eq_empty.mp hempty
    have hz : x.coeff = 0 := Finsupp.support_eq_empty.mp hsupp
    simp [hz]
  · obtain ⟨m, _, hmin⟩ := Finset.exists_min_image _ id hne
    refine ⟨m - 1, fun n hn => ?_⟩
    by_contra hc
    have hmem : n ∈ x.coeff.support.image (fun g : Multiplicative ℤ => g.toAdd) :=
      Finset.mem_image.mpr ⟨Multiplicative.ofAdd n, Finsupp.mem_support_iff.mpr hc, rfl⟩
    have hle : m ≤ n := hmin n hmem
    omega

/-- The function underlying the embedding `SkewMonoidAlgebra A (Multiplicative ℤ) → A((t;τ))`:
the coefficient at `n : ℤ` is the `Multiplicative.ofAdd n`-coefficient of `x`. -/
noncomputable def toSeries (x : SkewMonoidAlgebra A (Multiplicative ℤ)) : SkewLaurentSeries A :=
  ⟨fun n => x.coeff (Multiplicative.ofAdd n), exists_lower_bound x⟩

@[simp] theorem toSeries_apply (x : SkewMonoidAlgebra A (Multiplicative ℤ)) (n : ℤ) :
    (toSeries x).1 n = x.coeff (Multiplicative.ofAdd n) := rfl

/-- The `n`-th coefficient of a product in `SkewMonoidAlgebra A (Multiplicative ℤ)` computed as a
sum over the integer interval `Icc Nx (n - Ny)`, where `Nx` (resp. `Ny`) is any lower bound below
which the `ofAdd`-coefficients of `x` (resp. `y`) vanish.  This matches the product formula on
`SkewLaurentSeries A`. -/
theorem coeff_mul_eq_sum_Icc (x y : SkewMonoidAlgebra A (Multiplicative ℤ)) (Nx Ny n : ℤ)
    (hx : ∀ k : ℤ, k < Nx → x.coeff (Multiplicative.ofAdd k) = 0)
    (hy : ∀ m : ℤ, m < Ny → y.coeff (Multiplicative.ofAdd m) = 0) :
    (x * y).coeff (Multiplicative.ofAdd n)
      = ∑ k ∈ Finset.Icc Nx (n - Ny),
          x.coeff (Multiplicative.ofAdd k) *
            (Multiplicative.ofAdd k • y.coeff (Multiplicative.ofAdd (n - k))) := by
  classical
  set I : Finset (Multiplicative ℤ) := (Finset.Icc Nx (n - Ny)).image Multiplicative.ofAdd with hI
  have hL : (x * y).coeff (Multiplicative.ofAdd n)
      = ∑ a ∈ x.coeff.support, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)) := by
    rw [SkewMonoidAlgebra.coeff_mul_left]
    rfl
  have hIcc : (∑ k ∈ Finset.Icc Nx (n - Ny),
          x.coeff (Multiplicative.ofAdd k) *
            (Multiplicative.ofAdd k • y.coeff (Multiplicative.ofAdd (n - k))))
      = ∑ a ∈ I, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)) := by
    rw [hI, Finset.sum_image (s := Finset.Icc Nx (n - Ny)) (g := Multiplicative.ofAdd)
      (f := fun a => x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)))
      (fun a _ b _ hab => Multiplicative.ofAdd.injective hab)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ofAdd_inv_mul]
  have hA : (∑ a ∈ I, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)))
      = ∑ a ∈ x.coeff.support ∪ I, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)) := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro a _ ha
    obtain ⟨k, rfl⟩ := Multiplicative.ofAdd.surjective a
    have hkI : k ∉ Finset.Icc Nx (n - Ny) := by
      intro hk
      exact ha (by rw [hI]; exact Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hkI
    rcases hkI with hk | hk
    · rw [ofAdd_inv_mul, hx k hk, MulZeroClass.zero_mul]
    · rw [ofAdd_inv_mul, hy (n - k) (by omega), smul_zero, MulZeroClass.mul_zero]
  have hB : (∑ a ∈ x.coeff.support, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)))
      = ∑ a ∈ x.coeff.support ∪ I, x.coeff a * (a • y.coeff (a⁻¹ * Multiplicative.ofAdd n)) := by
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro a _ ha
    have : x.coeff a = 0 := by
      by_contra hc
      exact ha (Finsupp.mem_support_iff.mpr hc)
    rw [this, MulZeroClass.zero_mul]
  rw [hL, hIcc, hA, hB]

theorem toSeries_zero : toSeries (0 : SkewMonoidAlgebra A (Multiplicative ℤ)) = 0 := by
  apply Subtype.ext
  funext n
  simp [toSeries_apply]

theorem toSeries_add (x y : SkewMonoidAlgebra A (Multiplicative ℤ)) :
    toSeries (x + y) = toSeries x + toSeries y := by
  apply Subtype.ext
  funext n
  simp [toSeries_apply, SkewMonoidAlgebra.coeff_add]

theorem toSeries_one : toSeries (1 : SkewMonoidAlgebra A (Multiplicative ℤ)) = 1 := by
  apply Subtype.ext
  funext n
  rw [toSeries_apply, one_apply, SkewMonoidAlgebra.one_def, SkewMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases h : n = 0
  · subst h
    simp
  · have h1 : ¬ ((1 : Multiplicative ℤ) = Multiplicative.ofAdd n) := by
      rw [eq_comm, ofAdd_eq_one]; exact h
    simp [h1, h]

theorem toSeries_mul (x y : SkewMonoidAlgebra A (Multiplicative ℤ)) :
    toSeries (x * y) = toSeries x * toSeries y := by
  apply Subtype.ext
  funext n
  rw [toSeries_apply,
    mul_apply_of_bounds (toSeries x) (toSeries y) (lo (toSeries x)) (lo (toSeries y))
      (fun m hm => lt_lo hm) (fun m hm => lt_lo hm) n]
  rw [show (∑ k ∈ Finset.Icc (lo (toSeries x)) (n - lo (toSeries y)),
        (toSeries x).1 k * (Multiplicative.ofAdd k • (toSeries y).1 (n - k)))
      = ∑ k ∈ Finset.Icc (lo (toSeries x)) (n - lo (toSeries y)),
          x.coeff (Multiplicative.ofAdd k) *
            (Multiplicative.ofAdd k • y.coeff (Multiplicative.ofAdd (n - k))) from
    Finset.sum_congr rfl fun k _ => by rw [toSeries_apply, toSeries_apply]]
  exact coeff_mul_eq_sum_Icc x y (lo (toSeries x)) (lo (toSeries y)) n
    (fun k hk => lt_lo hk) (fun m hm => lt_lo hm)

/-- The natural embedding of the skew monoid algebra `A[t;τ]` in the skew Laurent series ring
`A((t;τ))`. -/
noncomputable def toRingHom :
    SkewMonoidAlgebra A (Multiplicative ℤ) →+* SkewLaurentSeries A where
  toFun := toSeries
  map_one' := toSeries_one
  map_mul' := toSeries_mul
  map_zero' := toSeries_zero
  map_add' := toSeries_add

theorem toRingHom_injective : Function.Injective (toRingHom (A := A)) := by
  intro x y hxy
  apply SkewMonoidAlgebra.coeff_injective
  ext g
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective g
  have h := congrArg (fun s : SkewLaurentSeries A => s.1 n) hxy
  simpa [toRingHom, toSeries_apply] using h

end

theorem exists_injective_ringHom_skewMonoidAlgebra {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] : ∃ f : SkewMonoidAlgebra A (Multiplicative ℤ) →+* SkewLaurentSeries A, Function.Injective f :=
  ⟨toRingHom, toRingHom_injective⟩

end Work.ORHughesFree.SkewLaurentSeries
