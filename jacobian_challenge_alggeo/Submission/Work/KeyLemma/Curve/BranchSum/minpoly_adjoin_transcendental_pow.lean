import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.KeyLemma.Curve.BranchSum

open Polynomial

/-- Auxiliary: `X ^ n - C X` is irreducible over the rational function field `k(X)`.
This is the function-field incarnation of the irreducibility of `T ^ n - y` over `k(y)`
for `y` transcendental: `swap` turns the linear-in-one-variable identity
`T ^ n - X` into a degree-one polynomial, and Gauss's lemma descends from `k[X]` to `k(X)`. -/
theorem irreducible_X_pow_sub_C_ratFunc (k : Type u) [Field k] {n : ℕ} (hn : 0 < n) :
    Irreducible ((Polynomial.X : Polynomial (RatFunc k)) ^ n - Polynomial.C RatFunc.X) := by
  open scoped Polynomial.Bivariate in
  have h1 : Irreducible (Polynomial.C (-1) * Polynomial.X +
      Polynomial.C ((Polynomial.X : Polynomial k) ^ n) : Polynomial (Polynomial k)) := by
    apply irreducible_C_mul_X_add_C
    · simp
    · exact isUnit_neg_one.isRelPrime_left
  have h2 : Irreducible ((Polynomial.X : Polynomial (Polynomial k)) ^ n -
      Polynomial.C (Polynomial.X : Polynomial k)) := by
    have hh := (MulEquiv.irreducible_iff (Polynomial.Bivariate.swap (R := k))).mpr h1
    convert hh using 1
    simp [Polynomial.Bivariate.swap_apply]
    ring
  have hmonic : Monic ((Polynomial.X : Polynomial (Polynomial k)) ^ n -
      Polynomial.C (Polynomial.X : Polynomial k)) :=
    monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn)
  have h3 : Irreducible (((Polynomial.X : Polynomial (Polynomial k)) ^ n -
      Polynomial.C (Polynomial.X : Polynomial k)).map (algebraMap (Polynomial k) (RatFunc k))) :=
    (IsPrimitive.irreducible_iff_irreducible_map_fraction_map hmonic.isPrimitive).mp h2
  simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    RatFunc.algebraMap_X] using h3

theorem minpoly_adjoin_transcendental_pow {k : Type u} [Field k] {N : Type u} [Field N]
    [Algebra k N] (y : N) (hy : Transcendental k y) {n : ℕ} (hn : 0 < n) (r : N)
    (hr : r ^ n = y) :
    minpoly ↥(IntermediateField.adjoin k {y}) r =
      Polynomial.X ^ n - Polynomial.C (⟨y, IntermediateField.mem_adjoin_simple_self k y⟩ :
        ↥(IntermediateField.adjoin k {y})) := by
  have hIrr_rat := irreducible_X_pow_sub_C_ratFunc k hn
  have hmap : Polynomial.mapEquiv (RatFunc.algEquivOfTranscendental (K := k) y hy).toRingEquiv
      ((Polynomial.X : Polynomial (RatFunc k)) ^ n - Polynomial.C RatFunc.X)
      = (Polynomial.X ^ n -
          Polynomial.C (⟨y, IntermediateField.mem_adjoin_simple_self k y⟩ :
            ↥(IntermediateField.adjoin k {y})) : (↥(IntermediateField.adjoin k {y}))[X]) := by
    rw [Polynomial.mapEquiv_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    congr 1
    congr 1
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X y hy
  have hIrr : Irreducible (Polynomial.X ^ n -
      Polynomial.C (⟨y, IntermediateField.mem_adjoin_simple_self k y⟩ :
        ↥(IntermediateField.adjoin k {y})) : (↥(IntermediateField.adjoin k {y}))[X]) := by
    rw [← hmap]
    exact hIrr_rat.map _
  refine (minpoly.eq_of_irreducible_of_monic hIrr ?_ ?_).symm
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [IntermediateField.algebraMap_apply, hr]
    simp
  · exact monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn)

end Work.KeyLemma.Curve.BranchSum
