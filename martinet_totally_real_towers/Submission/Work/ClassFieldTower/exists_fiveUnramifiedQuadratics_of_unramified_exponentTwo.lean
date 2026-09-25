import Mathlib
import Submission.Work.ClassFieldTower.Main
import
  Submission.Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card

/-!
# Five independent unramified quadratics from an unramified exponent-`2` extension

`Work.ClassFieldTower.HasFiveIndependentUnramifiedQuadratics M` is the class-field-theory-free
form of the numerical certificate `rank₂ Cl(F) ≥ 5` for the maximal unramified pro-`2` extension
`M = F_∅` of a number field `F`: it asks for a surjection `G_∅ ↠ (𝔽₂)^5`, i.e. for five
independent unramified quadratic extensions of `F`.

It is supplied here from a *single* finite unramified Galois extension `L/F` whose Galois group
has exponent `2` and order `2 ^ 5`:

* `L/F` is unramified and pro-`2`, so it embeds into `F_∅` by the universal property of the
  maximal unramified pro-`2` extension; transporting the algebra structure along this embedding,
  the restriction map `AlgEquiv.restrictNormalHom` exhibits `Gal(L/F)` as a quotient of
  `G_∅ = Gal(F_∅/F)`;
* a finite group of exponent `2` and order `2 ^ 5` is `(𝔽₂)^5` -- it is commutative and
  `𝔽₂`-vector space of dimension `5`, which is the commons lemma
  `exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card`.

Composing the two gives the required surjection `G_∅ ↠ (𝔽₂)^5`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **A group all of whose elements are involutions is commutative.**

`(xy)(xy) = 1` exhibits `xy` as its own inverse, and `(xy)⁻¹ = y⁻¹x⁻¹ = yx` because `x` and `y`
are their own inverses. -/
theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) :
    ∀ x y : G, x * y = y * x := by
  have hinv : ∀ z : G, z⁻¹ = z := fun z =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact h z)
  intro x y
  have hxy : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact h (x * y))
  have h2 : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hinv x, hinv y]
  rw [← hxy, h2]

/-- **`Gal(L/F) ≃* (𝔽₂)^5` for a finite exponent-`2` Galois group of order `2 ^ 5`.**

A finite group of exponent dividing `2` is commutative (`mul_comm_of_sq_eq_one`), hence a vector
space over `𝔽₂`; with `2 ^ 5` elements its dimension is `5`, so it is `(𝔽₂)^5`
(`exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card`). -/
theorem nonempty_mulEquiv_galoisGroup_five {F : Type} [Field F] (L : Type) [Field L]
    [Algebra F L] [FiniteDimensional F L] (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) :
    Nonempty ((L ≃ₐ[F] L) ≃* Multiplicative (Fin 5 → ZMod 2)) := by
  classical
  letI : IsMulCommutative (L ≃ₐ[F] L) :=
    ⟨Std.Commutative.mk (mul_comm_of_sq_eq_one hexp)⟩
  exact
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      hexp hcard

/-- **Five independent unramified quadratics from one unramified exponent-`2` extension of
degree `2 ^ 5`.**

`L/F` is a finite unramified Galois extension with `Gal(L/F)` of exponent `2` and order `2 ^ 5`.
The universal property of `F_∅` embeds `L` into `F_∅`; the resulting restriction
`G_∅ →* Gal(L/F)` is surjective, and `Gal(L/F) ≃* (𝔽₂)^5`, so `G_∅` maps onto `(𝔽₂)^5`. -/
theorem exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo {F : Type} [Field F]
    [NumberField F] (M : MaximalUnramifiedProP.{0} F 2) (L : Type) [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤)
    (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) :
    HasFiveIndependentUnramifiedQuadratics M := by
  classical
  -- `L/F` is pro-`2`, so by the universal property of `F_∅` it embeds in `F_∅`.
  have hpro : IsPGroup 2 (L ≃ₐ[F] L) := fun σ => ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨φ, -⟩ := M.universal L hpro hunr
  -- Transport the `F`-algebra structure of `F_∅` along this embedding: `F ≤ L ≤ F_∅`.
  letI : Algebra L M.K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F L M.K := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  -- Restriction of automorphisms of `F_∅` to the normal subfield `L` is surjective, and
  -- `Gal(L/F) ≃* (𝔽₂)^5`.
  obtain ⟨e⟩ := nonempty_mulEquiv_galoisGroup_five L hexp hcard
  exact ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) L),
    e.surjective.comp (AlgEquiv.restrictNormalHom_surjective M.K)⟩

end Work.ClassFieldTower
