import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.FieldTheory.Galois

/-- An irreducible polynomial over a field in which `2 ≠ 0`, of degree at most `2`, is separable.
Indeed its derivative has the form `(deg f) * (leading coeff) * X ^ (deg f - 1) ≠ 0`. -/
theorem separable_of_irreducible_natDegree_le_two {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {f : F[X]} (hirr : Irreducible f) (hdeg : f.natDegree ≤ 2) : f.Separable := by
  rw [separable_iff_derivative_ne_zero hirr]
  intro hderiv
  have hpos : 0 < f.natDegree := hirr.natDegree_pos
  have h1le : 1 ≤ f.natDegree := hpos
  have hlc : leadingCoeff f ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hcoeff : coeff (derivative f) (f.natDegree - 1) = leadingCoeff f * (f.natDegree : F) := by
    rw [coeff_derivative, Nat.sub_add_cancel h1le, Nat.cast_sub h1le, Nat.cast_one,
      sub_add_cancel, leadingCoeff]
  rw [hderiv, coeff_zero] at hcoeff
  have hcast : (f.natDegree : F) ≠ 0 := by
    rcases (show f.natDegree = 1 ∨ f.natDegree = 2 by omega) with h | h
    · rw [h]; push_cast; exact one_ne_zero
    · rw [h]; push_cast; exact h2
  exact mul_ne_zero hlc hcast hcoeff.symm

/-- A polynomial over a field which has a root and whose degree is at most `2` splits. -/
theorem splits_of_natDegree_le_two_of_isRoot {F : Type*} [Field F] {f : F[X]}
    (hdeg : f.natDegree ≤ 2) {x : F} (hx : f.IsRoot x) : f.Splits := by
  rcases eq_or_ne f 0 with h0 | hf0
  · rw [h0]; exact Splits.zero
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hx
  have hXx : (X - C x : F[X]) ≠ 0 := (monic_X_sub_C x).ne_zero
  have hg0 : g ≠ 0 := by
    intro hgg
    rw [hgg, mul_zero] at hg
    exact hf0 hg
  have hgnat : g.natDegree = f.natDegree - 1 := by
    have hh := natDegree_mul hXx hg0
    rw [← hg, natDegree_X_sub_C] at hh
    omega
  have hgle : g.natDegree ≤ 1 := by omega
  obtain ⟨a, b, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one hgle
  rw [hg, hab]
  refine (Splits.X_sub_C x).mul ?_
  rcases eq_or_ne a 0 with ha | ha
  · rw [ha]; simp
  · rw [show (C a * X + C b : F[X]) = C a * (X + C (a⁻¹ * b)) by
      rw [mul_add, ← C_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]]
    exact (Splits.C a).mul (Splits.X_add_C _)

/-- A finite-dimensional field extension of degree `2` in characteristic `≠ 2` is Galois: it is
separable (degree `2` and `2 ≠ 0`), and normal (the minimal polynomial of any element outside the
base field has degree `2`, and its second root `trace x - x` already lies in the extension). -/
theorem isGalois_of_finrank_eq_two {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) : IsGalois F E := by
  rw [isGalois_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    exact separable_of_irreducible_natDegree_le_two h2 (minpoly.irreducible (IsIntegral.of_finite F x))
      (by have := minpoly.natDegree_le (A := F) x; omega)
  · rw [normal_iff]
    intro x
    refine ⟨IsIntegral.of_finite F x, ?_⟩
    have hdeg : ((minpoly F x).map (algebraMap F E)).natDegree ≤ 2 := by
      have h1 := natDegree_map_le (f := algebraMap F E) (p := minpoly F x)
      have h2' := minpoly.natDegree_le (A := F) x
      omega
    refine splits_of_natDegree_le_two_of_isRoot (x := x) hdeg ?_
    rw [IsRoot.def, ← eval₂_eq_eval_map, ← aeval_def]
    exact minpoly.aeval F x

end Commons.FieldTheory.Galois