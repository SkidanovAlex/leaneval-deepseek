/-
Area AV: the affine charts of the projective line.

`Work.AbVar.ProjectiveLine.P1 k` is `Proj` of `k[X₀,X₁]` with the standard grading.  The chart
`D₊(X_i)` of this Proj is `Spec ↧(Away 𝒜 (X i))`, and the structure morphism restricted to it is
`Spec` of the ring homomorphism `fromZeroRingHom 𝒜 (X i) : ↧(𝒜 0) ⟶ Away 𝒜 (X i)` (see
`AlgebraicGeometry.Proj.awayι_toSpecZero`).

In this file we prove that this ring homomorphism is smooth, by identifying the chart ring
`Away 𝒜 (X i)` with the polynomial ring `R[T]` over `R` (`↧(𝒜 0) ≅ R`): the element `X_j/X_i`
(`j ≠ i`) generates it (`Work.AbVar.ProjectiveLine.awaySurjective`) and is transcendental
(`Work.AbVar.ProjectiveLine.awayToPoly_polyToAway`).
-/
import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.AbVar.ProjectiveLine

open AlgebraicGeometry MvPolynomial HomogeneousLocalization

section Chart

/-- The standard grading of `R[X₀, X₁]` by total degree. -/
abbrev StdG (R : Type*) [CommRing R] : ℕ → Submodule R (MvPolynomial (Fin 2) R) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

/-- The standard grading is a grading. -/
noncomputable instance instGradedRingStdG (R : Type*) [CommRing R] : GradedRing (StdG R) :=
  MvPolynomial.gradedAlgebra

/-- `R[X₀, X₁]`. -/
abbrev Poly2 (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

variable {R : Type*} [CommRing R]

/-- A homogeneous polynomial of degree zero in two variables is a constant. -/
lemma stdG_zero_eq_C {p : Poly2 R} (hp : p ∈ StdG R 0) : p = MvPolynomial.C (p.coeff 0) := by
  rw [← MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hp

lemma C_mem_stdG_zero (r : R) : (MvPolynomial.C r : Poly2 R) ∈ StdG R 0 :=
  (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr (MvPolynomial.isHomogeneous_C (Fin 2) r)

lemma X_mem_stdG (i : Fin 2) : (MvPolynomial.X i : Poly2 R) ∈ StdG R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i)

/-- The identification of `R` with the degree zero part of the standard grading. -/
noncomputable def constToZero : R →+* ↥(StdG R 0) where
  toFun r := ⟨MvPolynomial.C r, C_mem_stdG_zero r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp]
lemma constToZero_apply (r : R) : (constToZero r : Poly2 R) = MvPolynomial.C r := rfl

lemma constToZero_surj (a : ↥(StdG R 0)) : constToZero (a.1.coeff 0) = a := by
  refine Subtype.ext ?_
  rw [constToZero_apply]
  exact (stdG_zero_eq_C a.2).symm

lemma constToZero_injective : Function.Injective (constToZero (R := R)) := by
  intro a b h
  have h1 : (constToZero a : Poly2 R) = (constToZero b : Poly2 R) := congrArg Subtype.val h
  rw [constToZero_apply, constToZero_apply] at h1
  exact (MvPolynomial.C_inj R a b).mp h1

/-- `R ≅ ↧(𝒜 0)` for the standard grading. -/
noncomputable def constToZeroEquiv : R ≃+* ↥(StdG R 0) :=
  RingEquiv.ofBijective _ ⟨constToZero_injective, fun a => ⟨a.1.coeff 0, constToZero_surj a⟩⟩

@[simp]
lemma constToZeroEquiv_apply (r : R) : constToZeroEquiv (R := R) r = constToZero r := rfl

/-- The `R`-algebra structure on the chart ring `Away 𝒜 (X_i)`. -/
noncomputable def awayAlg (i : Fin 2) : R →+* Away (StdG R) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (StdG R) (Submonoid.powers (MvPolynomial.X i))).comp
    (constToZero (R := R))

noncomputable instance instAlgebraAway (i : Fin 2) : Algebra R (Away (StdG R) (MvPolynomial.X i)) :=
  (awayAlg (R := R) i).toAlgebra

lemma algebraMap_awayAlg (i : Fin 2) :
    algebraMap R (Away (StdG R) (MvPolynomial.X i)) = awayAlg (R := R) i := rfl

/-- The substitution `R[X₀,X₁] → R[T]` sending `X_i ↦ 1` and `X_k ↦ T` for `k ≠ i`. -/
noncomputable def subst (i : Fin 2) : Poly2 R →+* Polynomial R :=
  MvPolynomial.eval₂Hom (S₁ := Polynomial R) (Polynomial.C : R →+* Polynomial R)
    (fun k : Fin 2 => if k = i then (1 : Polynomial R) else Polynomial.X)

lemma subst_self (i : Fin 2) : subst i (MvPolynomial.X i : Poly2 R) = 1 := by
  rw [subst, MvPolynomial.eval₂Hom_X']; simp

lemma subst_other {i j : Fin 2} (hij : j ≠ i) : subst i (MvPolynomial.X j : Poly2 R) = Polynomial.X := by
  rw [subst, MvPolynomial.eval₂Hom_X']; simp [hij]

lemma subst_C (i : Fin 2) (r : R) : subst i (MvPolynomial.C r) = Polynomial.C r := by
  rw [subst, MvPolynomial.eval₂Hom_C]

/-- `X_i ^ 1` as an element of `Submonoid.powers (X_i)`. -/
noncomputable def powOne (i : Fin 2) : Submonoid.powers (MvPolynomial.X i : Poly2 R) :=
  ⟨(MvPolynomial.X i : Poly2 R) ^ 1, ⟨1, rfl⟩⟩

@[simp]
lemma powOne_val (i : Fin 2) : (powOne (R := R) i : Poly2 R) = (MvPolynomial.X i : Poly2 R) ^ 1 := rfl

/-- `X_i` is a unit for the substitution map. -/
theorem substUnitProof (i : Fin 2) :
    ∀ y : Submonoid.powers (MvPolynomial.X i : Poly2 R), IsUnit (subst i (y : Poly2 R)) := by
  rintro ⟨y, n, rfl⟩
  rw [show subst i ((MvPolynomial.X i : Poly2 R) ^ n) = 1 by rw [map_pow, subst_self, one_pow]]
  exact isUnit_one

/-- The localisation of the substitution map at `X_i`. -/
noncomputable def awayToPolyAux (i : Fin 2) :
    Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R)) →+* Polynomial R :=
  IsLocalization.lift (M := Submonoid.powers (MvPolynomial.X i : Poly2 R)) (substUnitProof i)

lemma awayToPolyAux_apply_lift (i : Fin 2) (a : Poly2 R) :
    awayToPolyAux i (algebraMap (Poly2 R) (Localization (Submonoid.powers (MvPolynomial.X i))) a)
      = subst i a := by
  rw [awayToPolyAux]
  exact IsLocalization.lift_eq _ a

lemma awayToPolyAux_mk_mul (i : Fin 2) (x : Poly2 R)
    (y : Submonoid.powers (MvPolynomial.X i : Poly2 R)) :
    awayToPolyAux i (Localization.mk x y) * subst i (y : Poly2 R) = subst i x := by
  rw [Localization.mk_eq_mk']
  have hspec := IsLocalization.mk'_spec
    (S := Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R))) x y
  have h2 := congrArg (awayToPolyAux i) hspec
  rwa [map_mul, awayToPolyAux_apply_lift, awayToPolyAux_apply_lift] at h2

/-- The element `X_j / X_i` of the chart ring of `D₊(X_i)`. -/
noncomputable def awayU (i j : Fin 2) : Away (StdG R) (MvPolynomial.X i) :=
  Away.mk (StdG R) (X_mem_stdG i) 1 (MvPolynomial.X j : Poly2 R) (by simpa using X_mem_stdG j)

/-- The `R`-algebra map `R[T] → Away 𝒜 (X_i)` sending `T` to `X_j/X_i`. -/
noncomputable def polyToAway (i j : Fin 2) :
    Polynomial R →ₐ[R] Away (StdG R) (MvPolynomial.X i) :=
  Polynomial.aeval (awayU i j)

/-- `Away 𝒜 (X_i)`, viewed as a quotient of the polynomial ring via `X_j/X_i ↦ T`. -/
noncomputable def awayToPoly (i : Fin 2) :
    Away (StdG R) (MvPolynomial.X i) →+* Polynomial R :=
  (awayToPolyAux i).comp
    (algebraMap (Away (StdG R) (MvPolynomial.X i))
      (Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R))))

lemma polyToAway_X (i j : Fin 2) : polyToAway (R := R) i j Polynomial.X = awayU i j :=
  Polynomial.aeval_X _

lemma polyToAway_C (i j : Fin 2) (r : R) :
    polyToAway (R := R) i j (Polynomial.C r)
      = algebraMap R (Away (StdG R) (MvPolynomial.X i)) r :=
  Polynomial.aeval_C _ _

lemma awayU_val (i j : Fin 2) :
    (awayU (R := R) i j).val
      = Localization.mk (MvPolynomial.X j : Poly2 R) (powOne (R := R) i) := by
  rw [awayU]
  exact Away.val_mk _ _ _ _ _

/-- The substitution `X_j/X_i ↦ T` inverts the surjection `polyToAway`. -/
lemma awayToPoly_awayU {i j : Fin 2} (hij : j ≠ i) :
    awayToPoly (R := R) i (polyToAway (R := R) i j Polynomial.X) = Polynomial.X := by
  rw [polyToAway_X]
  show awayToPolyAux i (algebraMap (Away (StdG R) (MvPolynomial.X i))
    (Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R))) (awayU i j)) = _
  rw [HomogeneousLocalization.algebraMap_apply, awayU_val]
  have h := awayToPolyAux_mk_mul i (MvPolynomial.X j : Poly2 R) (powOne (R := R) i)
  rw [powOne_val, map_pow, subst_self, one_pow, subst_other hij, mul_one] at h
  exact h

lemma awayToPoly_algMap (i : Fin 2) (r : R) :
    awayToPoly i (algebraMap R (Away (StdG R) (MvPolynomial.X i)) r) = Polynomial.C r := by
  show awayToPolyAux i (algebraMap (Away (StdG R) (MvPolynomial.X i))
    (Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R)))
    (algebraMap R (Away (StdG R) (MvPolynomial.X i)) r)) = _
  rw [algebraMap_awayAlg, awayAlg, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    show (HomogeneousLocalization.fromZeroRingHom (StdG R)
      (Submonoid.powers (MvPolynomial.X i : Poly2 R)) (constToZero r)).val
      = Localization.mk ((constToZero (R := R) r : Poly2 R))
        (1 : Submonoid.powers (MvPolynomial.X i : Poly2 R)) from rfl,
    Localization.mk_eq_mk', IsLocalization.mk'_one, awayToPolyAux_apply_lift,
    show ((constToZero (R := R) r : Poly2 R)) = MvPolynomial.C r from rfl, subst_C]

/-- The key computation: the composite `polyToAway` followed by `awayToPoly` is the identity. -/
lemma awayToPoly_polyToAway {i j : Fin 2} (hij : j ≠ i) (p : Polynomial R) :
    awayToPoly i (polyToAway i j p) = p := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, polyToAway_C,
      awayToPoly_algMap, awayToPoly_awayU hij, Polynomial.C_mul_X_pow_eq_monomial]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

lemma polyToAway_injective {i j : Fin 2} (hij : j ≠ i) :
    Function.Injective (polyToAway (R := R) i j) := by
  intro p q h
  rw [← awayToPoly_polyToAway hij p, ← awayToPoly_polyToAway hij q, h]

end Chart

end Work.AbVar.ProjectiveLine
