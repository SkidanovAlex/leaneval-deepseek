/-
# The cokernel obstruction class of the local data

Steps 1–2 of the assembly of `Work.SSGRoute.coker_obstruction`:

* the form `Φ = ω_N` on the `1`-cocycles `Gal(N/k) → E^∨(1)` given by the sum of the local pairings
  of the data `(α, β)` (`Work.SSGRoute.H1Pair.omega_functional_contra`);
* the class `X ∈ H₁(Gal(N/k), E ⊗ T)` which represents `Φ` under the canonical Tate pairing
  (`Work.SSGRoute.H1Pair.exists_x_of_Phi`).

The pairings enter only through the *local* clauses (additivity on locally constant cocycles,
vanishing on coboundaries) at the module `E`; no arithmetic input is needed here.  The class `X` is
the "cokernel obstruction" of the level-`N` data: the vanishing of its image at a level `N₂ ≤ N` is
what forces the pushed data to glue (the remaining steps, which do use Poitou–Tate).
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.H1Pair.Pairing
import Submission.Work.SSGRoute.H1Pair.Stage
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.H1Pair.omega_contra
import Submission.Work.SSGRoute.H1Pair.exists_x
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct
open CategoryTheory

namespace Work.SSGRoute.H1Pair

/-- **The transpose of a morphism of representations**: `ψ ↦ ψ ∘ F`.  Its underlying linear map is
`F.hom.dualMap`, and it satisfies the defining property `F'.hom ψ v = ψ (F.hom v)` (`rfl`), which is
what the naturality of the Tate pairing (`H1Pair.tatePairLin_natural`) consumes. -/
noncomputable def repTranspose {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂]
    {φ : G₁ →* G₂} {M₁ : Rep k G₁} {M₂ : Rep k G₂} (F : M₁ ⟶ Rep.res φ M₂) :
    Rep.res φ (contra M₂) ⟶ contra M₁ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (Rep.res φ (contra M₂)).ρ (contra M₁).ρ (LinearMap.dualMap F.hom.toLinearMap)
    (fun g ψ => by
      ext v
      simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, Representation.dual_apply,
        Module.Dual.transpose_apply, Rep.res_obj_ρ, MonoidHom.comp_apply]
      have h := Rep.hom_comm_apply F (g⁻¹) v
      have h2 : ((Rep.res φ M₂).ρ (g⁻¹)) = M₂.ρ (φ g)⁻¹ := by
        rw [DFunLike.congr_fun (Rep.res_obj_ρ φ M₂) (g⁻¹), MonoidHom.comp_apply, map_inv]
      rw [h2] at h
      exact congrArg ψ h.symm))

/-- The defining property of `repTranspose`: it is the transpose of `F`. -/
theorem repTranspose_hom_apply {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂]
    {φ : G₁ →* G₂} {M₁ : Rep k G₁} {M₂ : Rep k G₂} (F : M₁ ⟶ Rep.res φ M₂)
    (ψ : (contra M₂).V) (v : M₁.V) : (repTranspose F).hom ψ v = ψ (F.hom v) := rfl

/-- **Step 1–2 of the assembly**: from the local data `(α, β)` and a family of local pairings
satisfying the local clauses at the module `E`, build the form `ω` on the `1`-cocycles of the
contragredient Tate twist and a class `X ∈ H₁(Gal(N/k), E ⊗ T)` whose pairing with every cocycle is
`ω`.  Everything here is formal: the local clauses at `E`, plus finite-group Tate duality. -/
theorem exists_obstruction_class
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hloc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (H : Subgroup (Ω ≃ₐ[k] Ω)),
        IsLocalGroup k Ω H → PairClauses p K T M (fun a b => pair M H a b) H)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) :
    ∃ (X : groupHomology.H1 (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p)
            (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))))
      (Φ : ↥(groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
            (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
              (TensorProduct (ZMod p) E T)))))) →ₗ[ZMod p] ZMod p),
      (∀ (b₀ : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
        (hb : b₀ ∈ groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
          (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T)))))),
        Φ ⟨b₀, hb⟩ =
          S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
            (fun σ => b₀ (SSGRoute.res k N σ))) +
          C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
            (fun σ => b₀ (SSGRoute.res k N σ)))) ∧
      (∀ (b₀ : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
        (hb : b₀ ∈ groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
          (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T)))))),
        tatePairLin (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p)
            (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))) X
          ((groupCohomology.H1π (contra (Rep.res πN (Rep.of
            (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
              (TensorProduct (ZMod p) E T)))))).hom ⟨b₀, hb⟩) = Φ ⟨b₀, hb⟩) := by
  classical
  haveI : Fintype (N ≃ₐ[k] N) := AlgEquiv.fintype k N
  haveI hEt : Finite (TensorProduct (ZMod p) E T) :=
    finite_tensor_of_isCyclotomicDual p k Ω K ζ T hT E
  obtain ⟨Φ, hΦkill, hΦform⟩ := omega_functional_contra p k Ω K N hKN ζ hζ hζK E T
    hT πN hπN (pair E) (fun H hH => hloc E H hH) S hSfin C hCinv α hα β hβ
  obtain ⟨X, hX⟩ := exists_x_of_Phi p (Rep.res πN (Rep.of
    (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))) Φ hΦkill
  exact ⟨X, Φ, hΦform, fun b₀ hb => hX ⟨b₀, hb⟩⟩

end Work.SSGRoute.H1Pair
