import Mathlib.NumberTheory.NumberField.Basic

namespace Commons.NumberTheory.RamificationInertia

open NumberField

/-- For `L → M` a map of fields, the structure map `𝓞 L →+* 𝓞 M` of rings of integers is
compatible with the structure maps `𝓞 L →+* L` and `L →+* M`: both composites send `y` to
`algebraMap L M (y : L)`. -/
lemma coe_algebraMap_ringOfIntegers {L M : Type*} [Field L] [Field M] [Algebra L M]
    (y : 𝓞 L) :
    algebraMap (𝓞 M) M (algebraMap (𝓞 L) (𝓞 M) y) = algebraMap L M (algebraMap (𝓞 L) L y) :=
  rfl

/-- The action of `Gal(K/F)` on the ring of integers `𝓞 K` is compatible with the action on `K`. -/
lemma coe_smul_ringOfIntegers {F K : Type*} [Field F] [Field K] [Algebra F K]
    (σ : K ≃ₐ[F] K) (y : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • y) = σ • algebraMap (𝓞 K) K y :=
  rfl

/-- The canonical map `𝓞 L → 𝓞 M` of rings of integers is equivariant for the restriction
`Gal(M/F) →* Gal(L/F)`. -/
lemma algebraMap_smul_restrictNormalHom {F L M : Type*} [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [NumberField F] [NumberField L] [NumberField M]
    [Normal F L] [Normal F M] [FiniteDimensional F M]
    (σ : M ≃ₐ[F] M) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 M) ((AlgEquiv.restrictNormalHom (F := F) (K₁ := M) (E := L) σ) • x)
      = σ • (algebraMap (𝓞 L) (𝓞 M) x) := by
  apply RingOfIntegers.coe_injective (K := M)
  rw [coe_algebraMap_ringOfIntegers, coe_smul_ringOfIntegers, AlgEquiv.smul_def,
    coe_smul_ringOfIntegers, coe_algebraMap_ringOfIntegers, AlgEquiv.smul_def]
  change algebraMap L M ((σ.restrictNormal L) (algebraMap (𝓞 L) L x)) =
    σ (algebraMap L M (algebraMap (𝓞 L) L x))
  rw [AlgEquiv.restrictNormal_commutes]

open NumberField in
/-- **The inertia group of a subextension.**  If `L ⊆ M` is a tower of Galois extensions of a
number field `F`, and `Q` is a prime of `𝓞 L` lying over `p` of `𝓞 F` with `P` a prime of `𝓞 M`
lying over `Q`, then restricting the inertia group of `P` (in `Gal(M/F)`) to `L` lands in the
inertia group of `Q` (in `Gal(L/F)`).

Proof: `Ideal.inertia` is the kernel of the action on the residue field.  If `σ` acts trivially on
`𝓞 M ⧸ P`, then for `x : 𝓞 L` the element `σ x - x` maps into `P` under the ring map
`𝓞 L → 𝓞 M`; but `AlgEquiv.restrictNormalHom_apply` gives
`AlgEquiv.restrictNormalHom (K₁ := M) (E := L) σ x = σ x`, so `σ|_L` acts trivially on
`𝓞 L ⧸ Q`. -/
theorem inertia_map_restrictNormalHom_le {F L M : Type*} [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [NumberField F] [NumberField L] [NumberField M]
    [Normal F L] [Normal F M] [FiniteDimensional F M]
    (p : Ideal (RingOfIntegers F)) (Q : Ideal (RingOfIntegers L)) (P : Ideal (RingOfIntegers M))
    [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p] [Q.IsPrime] [P.IsPrime] :
    (Ideal.inertia (M ≃ₐ[F] M) P).map
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) (E := L)) ≤
      Ideal.inertia (L ≃ₐ[F] L) Q := by
  rintro τ ⟨σ, hσ, rfl⟩
  simp only [Ideal.inertia, SetLike.mem_coe, AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  have hQ : Q = P.under (𝓞 L) := (Ideal.liesOver_iff P Q).mp inferInstance
  rw [hQ]
  change algebraMap (𝓞 L) (𝓞 M)
      ((AlgEquiv.restrictNormalHom (F := F) (K₁ := M) (E := L) σ) • x - x) ∈ P
  rw [map_sub, algebraMap_smul_restrictNormalHom]
  exact hσ (algebraMap (𝓞 L) (𝓞 M) x)

end Commons.NumberTheory.RamificationInertia