import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.finite_lcCocycleImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of `localDataSpace K T ⧸ localVanish K T`

The quotient of the level-`K` local-data space at a finite set `T` of finite places by the submodule
of tuples vanishing on the local groups `H_A = decomp k A ⊓ G_K` is the product over `A ∈ T` of the
locally constant `1`-cocycles on `H_A` (functions on `H_A`).  Since `H_A ≤ G_K = ker (res k K)`, a
cocycle on `H_A` is an additive homomorphism `H_A → ZMod p`, and `IsLocConstOn` says that its kernel
is open; hence the cocycle space injects into the finite set
`{χ : ↥H_A →* Multiplicative (ZMod p) // IsOpen χ.ker}` of
`Work.SSGRoute.finite_openKernel_homs_decomp_kernel` (`ZDataMup/finite_lcCocycleImage`).  The
quotient is therefore a subspace of a finite product of finite sets, hence finite-dimensional.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- The level-`K` local-data space is the product over `A ∈ T` of the local cocycle spaces on the
level-`K` local groups `decomp k A ⊓ G_K`. -/
theorem localDataSpace_eq_pi (T : Finset (ValuationSubring Ω)) :
    localDataSpace (p := p) K T =
      Submodule.pi Set.univ (fun A : {A : ValuationSubring Ω // A ∈ T} =>
        localCocycle (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) := by
  ext a
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_implies]
  exact Iff.rfl

/-- The vanishing submodule is the product over `A ∈ T` of the functions vanishing on `H_A`. -/
theorem productVanish_eq_pi (T : Finset (ValuationSubring Ω)) :
    productVanish (p := p) K T =
      Submodule.pi Set.univ (fun A : {A : ValuationSubring Ω // A ∈ T} =>
        vanishOn (p := p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) := by
  ext a
  rw [Submodule.mem_pi]
  simp only [Set.mem_univ, true_implies]
  exact Iff.rfl

/-- Membership in the local-data space, componentwise. -/
theorem mem_localCocycle_of_mem_localDataSpace (T : Finset (ValuationSubring Ω))
    (a : ↥(localDataSpace (p := p) K T)) (A : {A : ValuationSubring Ω // A ∈ T}) :
    a.1 A ∈ localCocycle (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) := by
  have hpi : a.1 ∈ Submodule.pi Set.univ (fun A : {A : ValuationSubring Ω // A ∈ T} =>
      localCocycle (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) := by
    rw [← localDataSpace_eq_pi]; exact a.2
  exact (Submodule.mem_pi.mp hpi) A (Set.mem_univ A)

/-- Membership in the vanishing submodule, spelled out. -/
theorem mem_productVanish_iff (T : Finset (ValuationSubring Ω))
    (a : {A : ValuationSubring Ω // A ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p) :
    a ∈ productVanish (p := p) K T ↔
      ∀ (A : {A : ValuationSubring Ω // A ∈ T}) (g : Ω ≃ₐ[k] Ω),
        g ∈ SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup → a A g = 0 := by
  rw [productVanish_eq_pi, Submodule.mem_pi]
  constructor
  · intro h A g hg
    exact h A (Set.mem_univ A) g hg
  · intro h A _ g hg
    exact h A g hg

/-- Restriction of the local data at `T` to the level-`K` local groups, as a `ZMod p`-linear map
into the product of the spaces of locally constant cocycles on the local groups. -/
noncomputable def phi (T : Finset (ValuationSubring Ω)) :
    ↥(localDataSpace (p := p) K T) →ₗ[ZMod p]
      (∀ A : {A : ValuationSubring Ω // A ∈ T},
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) where
  toFun a := fun A =>
    ⟨restrictToSub (p := p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A),
      Submodule.mem_map.mpr ⟨a.1 A, mem_localCocycle_of_mem_localDataSpace (p := p) T a A, rfl⟩⟩
  map_add' a b := by
    funext A
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, restrictToSub_apply]
  map_smul' c a := by
    funext A
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, restrictToSub_apply, RingHom.id_apply]

/-- The kernel of `phi` is exactly the submodule of local data vanishing on the local groups. -/
theorem ker_phi (T : Finset (ValuationSubring Ω)) :
    (phi (p := p) T).ker = localVanish (p := p) K T := by
  ext a
  rw [LinearMap.mem_ker, localVanish, Submodule.mem_comap, mem_productVanish_iff]
  constructor
  · intro ha A g hg
    have h1 : phi (p := p) T a A = 0 := congrFun ha A
    have h2 := congrArg (fun x : ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) =>
        (x : ↥(SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) → ZMod p)) h1
    have h3 : restrictToSub (p := p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) = 0 :=
      h2
    have h4 := congrFun h3 (⟨g, hg⟩ : ↥(SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))
    show (a.1 A) g = 0
    simpa only [restrictToSub_apply, Pi.zero_apply] using h4
  · intro ha
    funext A
    apply Subtype.ext
    funext x
    simp only [restrictToSub_apply, Submodule.coe_zero, Pi.zero_apply]
    exact ha A x.1 x.2

theorem finite_localDataSpace_quotient {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    Module.Finite (ZMod p) (↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T) ⧸
      Work.SSGRoute.ZDataMup.localVanish (p := p) K T) := by
  haveI hfin : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Finite ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) :=
    fun A => finite_lcCocycleImage (p := p) (K := K) (hA := hTfin A.1 A.2)
  haveI hmodfin : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Module.Finite (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) :=
    fun A => Module.Finite.of_finite
  haveI hpi : Module.Finite (ZMod p)
      (∀ A : {A : ValuationSubring Ω // A ∈ T},
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) :=
    Module.Finite.pi
  haveI hcod : Finite (∀ A : {A : ValuationSubring Ω // A ∈ T},
      ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) := Pi.finite
  haveI hrangeFin : Finite ↥((phi (p := p) (K := K) T).range) :=
    Finite.of_injective
      (Subtype.val : ↥((phi (p := p) (K := K) T).range) →
        (∀ A : {A : ValuationSubring Ω // A ∈ T},
          ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))))
      Subtype.val_injective
  haveI hrange : Module.Finite (ZMod p) ↥((phi (p := p) (K := K) T).range) :=
    Module.Finite.of_finite
  have e : (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) ≃ₗ[ZMod p]
      ↥((phi (p := p) (K := K) T).range) :=
    (Submodule.quotEquivOfEq (localVanish (p := p) K T) ((phi (p := p) (K := K) T).ker)
      (ker_phi (p := p) (K := K) T).symm).trans
        (LinearMap.quotKerEquivRange (phi (p := p) (K := K) T))
  exact Module.Finite.equiv e.symm

end Work.SSGRoute.ZDataMup
