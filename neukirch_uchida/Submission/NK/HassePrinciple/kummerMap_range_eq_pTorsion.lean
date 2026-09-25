import Mathlib
import Submission.NK.HassePrinciple.Mu
import Submission.NK.HassePrinciple.kummerMap_injective_of_pdivisible

/-!
# The range of the level-wise Kummer map is the `p`-torsion

Let `L/K` be a field extension, `G = Gal(L/K)`, `p : ℕ`, and suppose that the `p`-th power map on
the units `Lˣ` is surjective (hypothesis `hdiv`: every unit of `L` is a `p`-th power).  Then the
Kummer map

  `kummerMap p K L : H²(G, μ_p(L)) ⟶ H²(G, Lˣ)`

(`NK.HassePrinciple.Mu`) has image exactly the `p`-torsion subgroup of the relative Brauer group
`H²(G, Lˣ)`.

This is the exactness statement at the middle term of the long exact cohomology sequence of

  `0 ⟶ μ_p(L) ⟶ Lˣ --(·)^p--> Lˣ ⟶ 0`,

which is short exact precisely because every unit is a `p`-th power.  The long exact sequence gives
that the image of `kummerMap` is the kernel of the map on `H²` induced by the `p`-th power
endomorphism of the units, and that induced map is multiplication by `p`.
-/

open CategoryTheory Representation

universe u

namespace NK.HassePrinciple

section Aux

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **The `p`-th power endomorphism of the units is multiplication by `p`** in the category of
`CoeffInt`-linear representations of `Gal(L/K)`. -/
lemma unitsPow_eq_nsmul_one (p : ℕ) :
    unitsPow (K := K) (L := L) p = p • 𝟙 (unitsRep K L) := by
  apply Rep.hom_injective
  apply Representation.IntertwiningMap.ext
  rw [Rep.nsmul_hom]
  rfl

/-- `Hⁿ(G, ·)` is additive in the coefficient morphism. -/
lemma map_id_add {A B : Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L)} (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) φ n
        + groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) ψ n := by
  show HomologicalComplex.homologyMap
    (groupCohomology.cochainsMap (MonoidHom.id (L ≃ₐ[K] L)) (φ + ψ)) n = _
  rw [show groupCohomology.cochainsMap (MonoidHom.id (L ≃ₐ[K] L)) (φ + ψ)
        = groupCohomology.cochainsMap (MonoidHom.id (L ≃ₐ[K] L)) φ
          + groupCohomology.cochainsMap (MonoidHom.id (L ≃ₐ[K] L)) ψ from
      CategoryTheory.Functor.map_add
        (F := groupCohomology.cochainsFunctor CoeffInt (L ≃ₐ[K] L)) (f := φ) (g := ψ),
    HomologicalComplex.homologyMap_add]
  rfl

/-- `Hⁿ` sends the zero endomorphism to zero. -/
lemma map_id_zero {A : Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L)} (n : ℕ) :
    groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (0 : A ⟶ A) n = 0 := by
  show HomologicalComplex.homologyMap
    (groupCohomology.cochainsMap (MonoidHom.id (L ≃ₐ[K] L)) (0 : A ⟶ A)) n = 0
  rw [groupCohomology.cochainsMap_zero]
  simp

/-- `Hⁿ` is `ℕ`-linear in the coefficient morphism. -/
lemma map_id_nsmul {A : Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L)} (φ : A ⟶ A) (m n : ℕ) :
    groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (m • φ) n
      = m • groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) φ n := by
  induction m with
  | zero => rw [zero_nsmul, map_id_zero, zero_nsmul]
  | succ k ih => rw [succ_nsmul, map_id_add, ih, succ_nsmul]

/-- **The map on `H²` induced by the `p`-th power endomorphism of the units is multiplication
by `p`.** -/
lemma map_unitsPow_apply (p : ℕ) (x : groupCohomology (unitsRep K L) 2) :
    ((groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (unitsPow (K := K) (L := L) p) 2).hom) x
      = p • x := by
  rw [unitsPow_eq_nsmul_one (K := K) (L := L) p, map_id_nsmul, groupCohomology.map_id]
  simp

end Aux

section Main

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

set_option backward.isDefEq.respectTransparency false in
/-- The long exact cohomology sequence of the Kummer sequence, at the middle term `H²(G, Lˣ)`:
the range of the Kummer map is the kernel of the map induced by the `p`-th power endomorphism. -/
lemma range_kummerMap_eq_ker_unitsPow (p : ℕ)
    (hdiv : ∀ x : Lˣ, ∃ y : Lˣ, y ^ p = x) :
    LinearMap.range (kummerMap p K L).hom
      = LinearMap.ker (groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L))
          (unitsPow (K := K) (L := L) p) 2).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₂_exact
      (kummerShortComplex_shortExact (K := K) (L := L) p hdiv) 2)

set_option backward.isDefEq.respectTransparency false in
theorem kummerMap_range_eq_pTorsion {K L : Type u} [Field K] [Field L] [Algebra K L] (p : ℕ)
    (hdiv : ∀ x : Lˣ, ∃ y : Lˣ, y ^ p = x) :
    ∀ x : groupCohomology (NK.HassePrinciple.unitsRep K L) 2,
      x ∈ (NK.HassePrinciple.kummerMap p K L).hom.range ↔ p • x = 0 := by
  intro x
  rw [range_kummerMap_eq_ker_unitsPow p hdiv, LinearMap.mem_ker, map_unitsPow_apply]

end Main

end NK.HassePrinciple
