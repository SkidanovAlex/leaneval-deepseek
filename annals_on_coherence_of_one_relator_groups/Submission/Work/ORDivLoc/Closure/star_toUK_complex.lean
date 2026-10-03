/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `toUK E (RingHom.id ℂ) H` is a `∗`-homomorphism

For the complex envelope `U(G)` and a subgroup `H ≤ G`, the structure map
`toUK E (RingHom.id ℂ) H : ℂ[H] →+* U(G)` commutes with the involutions:

`star (toUK x) = toUK (star x)`,

where the involution of `ℂ[↥H]` is the group-algebra involution
`Work.ORVonNeumann.GroupAlgebraStar.starF` (`∑ c_h · h ↦ ∑ conj (c_h) · h⁻¹`) and the
involution of `U(G)` is that of the envelope `E`.

This is the "`hstar`" hypothesis of `Work.ORDivLoc.Closure.isEpic_starClosureCod_of_star_mem`: as
`toUK (star x) ∈ Set.range (toUK E (RingHom.id ℂ) H)` it exhibits `star (toUK x)` as a ring
expression in the image of `toUK`, i.e. the image of `ℂ[H]` is a `∗`-subring of `U(G)`.

The whole content lies in the two defining axioms of the envelope: `ι_star` (the structure map
`ℂ[G] → U(G)` is a `∗`-homomorphism) and `ι_algebraMap` (it is `ℂ`-linear); group elements are
inverted by the involution (`star (genU g) = genU g⁻¹`) and the scalars are conjugated
(`star (algebraMap ℂ U c) = algebraMap ℂ U (star c)`).

## Main results

* `Work.ORDivLoc.Closure.star_algebraMap_envelope`, `...star_smul_envelope` — the involution of
  `U(G)` conjugates the complex scalars, hence is conjugate-`ℂ`-linear;
* `Work.ORDivLoc.Closure.star_genU`, `...star_of_monoidAlgebra` — the involution inverts the
  group basis of `ℂ[↥H]`;
* `Work.ORDivLoc.Closure.star_toUK_complex`.
-/
import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary

namespace Work.ORDivLoc.Closure

open Work.ORVonNeumann Work.ORBridgeLinnell

/-- **The involution of `U(G)` conjugates the complex scalars**: `star (algebraMap ℂ U c)` is
`algebraMap ℂ U (star c)`.

`ι_algebraMap` rewrites both scalars as images under the structure map `ι : ℂ[G] → U(G)`, and
`ι_star` together with `MonoidAlgebra.star_single` (`star (single 1 c) = single 1 (star c)`)
computes the involution of the corresponding scalar of `ℂ[G]`. -/
theorem star_algebraMap_envelope {G : Type} [Group G] (E : StarRegularEnvelope G) (c : ℂ) :
    star (algebraMap ℂ E.U c) = algebraMap ℂ E.U (star c) := by
  rw [← E.ι_algebraMap c, ← E.ι_algebraMap (star c), ← E.ι_star]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    Work.ORVonNeumann.MonoidAlgebra.star_smul, star_one]

/-- **The involution of `U(G)` is conjugate-`ℂ`-linear**: `star (c • y) = star c • star y`.

Since `c • y = algebraMap ℂ U c * y` and `star` reverses products (in a `StarRing`), this is
`star_algebraMap_envelope` together with the centrality of the scalars (`Algebra.commutes`). -/
theorem star_smul_envelope {G : Type} [Group G] (E : StarRegularEnvelope G) (c : ℂ) (y : E.U) :
    star (c • y) = star c • star y := by
  rw [Algebra.smul_def, star_mul, star_algebraMap_envelope E c, Algebra.smul_def]
  exact (Algebra.commutes (star c) (star y)).symm

/-- **The involution of `U(G)` inverts the group basis**: `star (genU g) = genU g⁻¹`.

This is `ι_star` applied to `MonoidAlgebra.star_single`. -/
theorem star_genU {G : Type} [Group G] (E : StarRegularEnvelope G) (g : G) :
    star (genU E g) = genU E g⁻¹ := by
  rw [genU_apply, genU_apply, ← E.ι_star, Work.ORVonNeumann.MonoidAlgebra.star_single, star_one]

/-- **The involution of the group algebra inverts the basis**: `star (of m) = of m⁻¹`. -/
theorem star_of_monoidAlgebra {G : Type} [Group G] (m : G) :
    star (MonoidAlgebra.of ℂ G m) = MonoidAlgebra.of ℂ G m⁻¹ := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
    Work.ORVonNeumann.MonoidAlgebra.star_single, star_one]

/-- **The structure map `ℂ[H] → U(G)` is a `∗`-homomorphism** for the complex coefficients:
`star (toUK x) = toUK (star x)`.

`toUK E (RingHom.id ℂ) H` is the `ℂ`-algebra lift of `h ↦ genU (h : G)`, so it suffices (by
`MonoidAlgebra.induction_on`) to check the `ℂ`-linear span of the group basis: on `of h` both
sides are `genU h⁻¹` (`star_genU`), on sums the two maps are additive (`star_add`, `map_add`), and
on scalars `r • x` the conjugate-linearity of both involutions
(`star_smul_envelope`, `MonoidAlgebra.star_smul`) reduces the claim to the induction hypothesis. -/
theorem star_toUK_complex {G : Type} [Group G] (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (H : Subgroup G) (x : MonoidAlgebra ℂ ↥H) :
    star (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H x) =
      Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H (star x) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    rw [toUK_of, star_of_monoidAlgebra, toUK_of, star_genU]
    rfl
  | add a b ha hb =>
    rw [map_add, star_add, star_add, map_add, ha, hb]
  | smul r a ha =>
    rw [map_smul, star_smul_envelope, Work.ORVonNeumann.MonoidAlgebra.star_smul, map_smul,
      ← ha]

end Work.ORDivLoc.Closure
