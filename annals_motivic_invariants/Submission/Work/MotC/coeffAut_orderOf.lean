import Mathlib
import Submission.Work.MotC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order of the coefficient (Galois) automorphism of `L(E)`

This file proves that the coefficient action `coeffAut D` of the generator `σ` of the cyclic
quintic extension on the function field `L(E) = κ(C)` has order `5`.

The main mathematical content is that `g ↦ coeffAutOf D g` is a *monoid homomorphism* from the
Galois group `Gal(L/𝕜)` to the group of `𝕜`-algebra automorphisms of the function field, obtained
as the composite of the coefficient action on the coordinate ring `L[E]` (`coeffCoordEquivOf`,
functorial in `g`) with the induced action on the fraction field
(`IsFractionRing.ringEquivOfRingEquivHom`).  It is injective (it acts on the constants `L` by `g`),
so `orderOf (coeffAut D) = orderOf σ = 5`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Polynomial.Bivariate

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The Weierstrass polynomial of the base-changed curve `E_L`. -/
noncomputable abbrev cpoly (D : Work.TorsorExistence.QuinticTwist 𝕜) : D.ext.L[X][Y] :=
  WeierstrassCurve.Affine.polynomial (Work.MotC.baseCurve D)

/-- The affine coordinate ring `L[E]` of the base-changed curve. -/
noncomputable abbrev cRing (D : Work.TorsorExistence.QuinticTwist 𝕜) : Type :=
  WeierstrassCurve.Affine.CoordinateRing (Work.MotC.baseCurve D)

/-- The function field `L(E)` of the base-changed curve. -/
noncomputable abbrev fField (D : Work.TorsorExistence.QuinticTwist 𝕜) : Type :=
  WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)

/-- The Weierstrass polynomial of `E_L` is fixed by the coefficient action of any
`𝕜`-automorphism `g` of `L`: the curve is defined over `𝕜`. -/
theorem map_polynomial_of (D : Work.TorsorExistence.QuinticTwist 𝕜) (g : D.ext.L ≃ₐ[𝕜] D.ext.L) :
    (cpoly D).map (↑(Polynomial.mapAlgEquiv g) : D.ext.L[X] →+* D.ext.L[X]) = cpoly D := by
  simp only [cpoly, WeierstrassCurve.Affine.polynomial, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  simp

/-- **The coefficient action on the coordinate ring**, for an arbitrary `𝕜`-automorphism `g` of
`L`: apply `g` to the `L`-coefficients of `L[E]` and fix the classes of `X` and `Y`. -/
noncomputable def coeffCoordEquivOf (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) : cRing D ≃ₐ[𝕜] cRing D :=
  AdjoinRoot.mapAlgEquiv (Polynomial.mapAlgEquiv g) (cpoly D) (cpoly D)
    (by rw [map_polynomial_of D g])

/-- The coefficient action sends `p ∈ L[X] ⊂ L[E]` to `p.map g`. -/
theorem coeffCoordEquivOf_of (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) (r : D.ext.L[X]) :
    coeffCoordEquivOf D g (AdjoinRoot.of (cpoly D) r) =
      AdjoinRoot.of (cpoly D) (r.map (g : D.ext.L →+* D.ext.L)) := by
  simp [coeffCoordEquivOf]

/-- The coefficient action fixes the class of `Y`. -/
theorem coeffCoordEquivOf_root (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) :
    coeffCoordEquivOf D g (AdjoinRoot.root (cpoly D)) = AdjoinRoot.root (cpoly D) := by
  simp [coeffCoordEquivOf]

/-- The coefficient action of the identity is the identity. -/
theorem coeffCoordEquivOf_one (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    coeffCoordEquivOf D 1 = 1 := by
  have h : (coeffCoordEquivOf D 1 : cRing D →+* cRing D) = ↑(1 : cRing D ≃ₐ[𝕜] cRing D) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply]
      change coeffCoordEquivOf D 1 (AdjoinRoot.of (cpoly D) r) =
        (1 : cRing D ≃ₐ[𝕜] cRing D) (AdjoinRoot.of (cpoly D) r)
      rw [coeffCoordEquivOf_of, AlgEquiv.one_apply]
      congr 1
      rw [show (↑(1 : D.ext.L ≃ₐ[𝕜] D.ext.L) : D.ext.L →+* D.ext.L) = RingHom.id _ from rfl,
        Polynomial.map_id]
    · change coeffCoordEquivOf D 1 (AdjoinRoot.root (cpoly D)) =
        (1 : cRing D ≃ₐ[𝕜] cRing D) (AdjoinRoot.root (cpoly D))
      rw [coeffCoordEquivOf_root, AlgEquiv.one_apply]
  apply AlgEquiv.ext
  intro x
  exact RingHom.congr_fun h x

/-- **Functoriality of the coefficient action on the coordinate ring.** -/
theorem coeffCoordEquivOf_mul (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g h : D.ext.L ≃ₐ[𝕜] D.ext.L) :
    coeffCoordEquivOf D g * coeffCoordEquivOf D h = coeffCoordEquivOf D (g * h) := by
  have hh : (↑(coeffCoordEquivOf D g * coeffCoordEquivOf D h) : cRing D →+* cRing D)
      = ↑(coeffCoordEquivOf D (g * h) : cRing D ≃ₐ[𝕜] cRing D) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply]
      change (coeffCoordEquivOf D g * coeffCoordEquivOf D h) (AdjoinRoot.of (cpoly D) r)
        = coeffCoordEquivOf D (g * h) (AdjoinRoot.of (cpoly D) r)
      rw [AlgEquiv.mul_apply, coeffCoordEquivOf_of, coeffCoordEquivOf_of, coeffCoordEquivOf_of]
      congr 1
      rw [Polynomial.map_map]
      congr 1
    · change (coeffCoordEquivOf D g * coeffCoordEquivOf D h) (AdjoinRoot.root (cpoly D))
        = coeffCoordEquivOf D (g * h) (AdjoinRoot.root (cpoly D))
      rw [AlgEquiv.mul_apply, coeffCoordEquivOf_root, coeffCoordEquivOf_root,
        coeffCoordEquivOf_root]
  apply AlgEquiv.ext
  intro x
  exact RingHom.congr_fun hh x

/-- The constants of `L` sit in `L[E]` through `l ↦ C l`. -/
theorem algebraMap_eq_of_C (D : Work.TorsorExistence.QuinticTwist 𝕜) (l : D.ext.L) :
    algebraMap D.ext.L (cRing D) l = AdjoinRoot.of (cpoly D) (Polynomial.C l) := by
  rw [IsScalarTower.algebraMap_apply D.ext.L D.ext.L[X] (cRing D) l]
  rfl

/-- The coefficient action of `g` on the constants of `L[E]` is `g`. -/
theorem coeffCoordEquivOf_algebraMap (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) (l : D.ext.L) :
    (coeffCoordEquivOf D g).toRingEquiv (algebraMap D.ext.L (cRing D) l)
      = algebraMap D.ext.L (cRing D) (g l) := by
  change coeffCoordEquivOf D g (algebraMap D.ext.L (cRing D) l) =
    algebraMap D.ext.L (cRing D) (g l)
  rw [algebraMap_eq_of_C, coeffCoordEquivOf_of, Polynomial.map_C, algebraMap_eq_of_C]
  rfl

/-- The coefficient action fixes the base field `𝕜`. -/
theorem coeffCoordEquivOf_algebraMap_base (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) (c : 𝕜) :
    (coeffCoordEquivOf D g).toRingEquiv (algebraMap 𝕜 (cRing D) c) = algebraMap 𝕜 (cRing D) c := by
  change coeffCoordEquivOf D g (algebraMap 𝕜 (cRing D) c) = algebraMap 𝕜 (cRing D) c
  have h1 : algebraMap 𝕜 (cRing D) c =
      AdjoinRoot.of (cpoly D) (Polynomial.C (algebraMap 𝕜 D.ext.L c)) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 D.ext.L (cRing D) c]
    rfl
  rw [h1, coeffCoordEquivOf_of, Polynomial.map_C]
  congr 1
  exact congrArg Polynomial.C (g.commutes c)

/-- The coefficient action on the coordinate ring, as a monoid homomorphism out of
`Gal(L/𝕜)`. -/
noncomputable def coeffCoordHom (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    (D.ext.L ≃ₐ[𝕜] D.ext.L) →* (cRing D ≃+* cRing D) where
  toFun g := (coeffCoordEquivOf D g).toRingEquiv
  map_one' := by rw [coeffCoordEquivOf_one]; rfl
  map_mul' g h := by rw [← coeffCoordEquivOf_mul]; rfl

/-- The induced action on the function field `L(E)`, as a monoid homomorphism out of
`Gal(L/𝕜)`: coefficient action on `L[E]`, then functoriality of the fraction field. -/
noncomputable def ffHom (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    (D.ext.L ≃ₐ[𝕜] D.ext.L) →* (fField D ≃+* fField D) :=
  (IsFractionRing.ringEquivOfRingEquivHom (cRing D) (fField D)).comp (coeffCoordHom D)

/-- **The coefficient action on the function field `L(E)`** for an arbitrary `𝕜`-automorphism
`g` of `L`.  For `g = σ` this is `coeffAut D`. -/
noncomputable def coeffAutOf (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) : fField D ≃ₐ[𝕜] fField D :=
  AlgEquiv.ofRingEquiv (f := ffHom D g) (by
    intro c
    rw [show algebraMap 𝕜 (fField D) c = algebraMap (cRing D) (fField D)
        (algebraMap 𝕜 (cRing D) c) from
      (IsScalarTower.algebraMap_apply 𝕜 (cRing D) (fField D) c).symm]
    rw [show ffHom D g = IsFractionRing.ringEquivOfRingEquiv (coeffCoordEquivOf D g).toRingEquiv
      from rfl]
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquivOf_algebraMap_base])

/-- The underlying function of `coeffAutOf D g` is `ffHom D g`. -/
theorem coeffAutOf_apply (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) (x : fField D) :
    coeffAutOf D g x = ffHom D g x := AlgEquiv.ofRingEquiv_apply _ _

/-- `coeffAutOf` of the identity is the identity. -/
theorem coeffAutOf_one (D : Work.TorsorExistence.QuinticTwist 𝕜) : coeffAutOf D 1 = 1 := by
  apply AlgEquiv.ext
  intro x
  rw [AlgEquiv.one_apply, coeffAutOf_apply, map_one]
  rfl

/-- **Functoriality of the coefficient action on the function field.** -/
theorem coeffAutOf_mul (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g h : D.ext.L ≃ₐ[𝕜] D.ext.L) :
    coeffAutOf D g * coeffAutOf D h = coeffAutOf D (g * h) := by
  apply AlgEquiv.ext
  intro x
  rw [AlgEquiv.mul_apply, coeffAutOf_apply, coeffAutOf_apply, coeffAutOf_apply]
  change ((ffHom D g) * (ffHom D h)) x = (ffHom D (g * h)) x
  rw [← map_mul]

/-- The coefficient action of `g` on the constants `L ⊆ L(E)` is `g`. -/
theorem coeffAutOf_algebraMap (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (g : D.ext.L ≃ₐ[𝕜] D.ext.L) (l : D.ext.L) :
    coeffAutOf D g (algebraMap D.ext.L (fField D) l) = algebraMap D.ext.L (fField D) (g l) := by
  rw [coeffAutOf_apply]
  change (IsFractionRing.ringEquivOfRingEquiv (coeffCoordEquivOf D g).toRingEquiv)
      (algebraMap D.ext.L (fField D) l) = algebraMap D.ext.L (fField D) (g l)
  rw [show algebraMap D.ext.L (fField D) l = algebraMap (cRing D) (fField D)
      (algebraMap D.ext.L (cRing D) l) from
    (IsScalarTower.algebraMap_apply D.ext.L (cRing D) (fField D) l).symm]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquivOf_algebraMap]
  rw [IsScalarTower.algebraMap_apply D.ext.L (cRing D) (fField D) (g l)]

/-- `coeffAut D` is `coeffAutOf D σ`. -/
theorem coeffAut_eq (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    Work.MotC.coeffAut D = coeffAutOf D D.sigma := rfl

/-- The coefficient action on `L(E)`, bundled as a monoid homomorphism `Gal(L/𝕜) →* Aut(L(E))`. -/
noncomputable def coeffAutHom (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    (D.ext.L ≃ₐ[𝕜] D.ext.L) →* (fField D ≃ₐ[𝕜] fField D) where
  toFun g := coeffAutOf D g
  map_one' := coeffAutOf_one D
  map_mul' := fun g h => (coeffAutOf_mul D g h).symm

end

theorem coeffAut_orderOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) : orderOf (Work.MotC.coeffAut D) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have hσ5 : D.sigma ^ 5 = 1 := by
      have h := pow_orderOf_eq_one D.sigma
      rwa [D.sigma_orderOf] at h
    have h5 : (coeffAutHom D) (D.sigma ^ 5) = ((coeffAutHom D) D.sigma) ^ 5 := map_pow _ _ _
    rw [hσ5, map_one] at h5
    rw [show (coeffAutHom D) D.sigma = Work.MotC.coeffAut D from (coeffAut_eq D).symm] at h5
    exact h5.symm
  · intro h
    rw [coeffAut_eq] at h
    have hσ : D.sigma ≠ 1 := by
      intro hh
      have h1 : orderOf D.sigma = 1 := by rw [hh]; exact orderOf_one
      rw [D.sigma_orderOf] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨l, hl⟩ : ∃ l, D.sigma l ≠ l := by
      by_contra hc
      push Not at hc
      exact hσ (AlgEquiv.ext hc)
    have h1 := coeffAutOf_algebraMap D D.sigma l
    rw [h, AlgEquiv.one_apply] at h1
    exact hl ((RingHom.injective (algebraMap D.ext.L (fField D))) h1).symm

end Work.MotC
