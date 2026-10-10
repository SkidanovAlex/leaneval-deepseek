import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PT.exists_place_under_isFinPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

-- The prime `p` of the coefficient ring `ZMod p` (an implicit parameter of
-- `factorised_isCrossedHom`, as in the requester's file `PT/g1plus_finHalf.lean`).
variable (p : ℕ)

theorem factorised_isCrossedHom (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] [FiniteDimensional k L] [IsGalois k L] [NumberField L] (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hAw : ∀ y : NumberField.RingOfIntegers L, y ∈ w.asIdeal ↔ A.valuation (((y : L) : Ω)) < 1)
    (hglue : (SSGRoute.decomp k A).map (SSGRoute.res k L) =
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
    (M' : Type) [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']
    (b : (Ω ≃ₐ[k] Ω) → M')
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → M')
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ ((g * h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) :
          ↥L ≃ₐ[k] ↥L)
        = b₀ (g : ↥L ≃ₐ[k] ↥L) + (SSGRoute.PTExt.galRes k (↥K) (↥L)
            (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L) := by
  intro g h
  -- Both `g` and `h` lie in the image of `decomp k A` under `res k L`, by the glue `hglue`.
  have hg : (g : ↥L ≃ₐ[k] ↥L) ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L) := by
    rw [hglue]; exact g.2
  obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hg
  have hh : (h : ↥L ≃ₐ[k] ↥L) ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L) := by
    rw [hglue]; exact h.2
  obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.mp hh
  have hmem : σ * τ ∈ SSGRoute.decomp k A := mul_mem hσ hτ
  -- The action of `σ` on `M'` through `res k K` is the action of `g` through `galRes`.
  have hcomp : SSGRoute.res k K σ = SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L) := by
    rw [← hσeq]
    exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥K) (↥L) σ
  -- The image of `g * h` is the product of the images.
  have hcoe : (((g * h) : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) :
        ↥L ≃ₐ[k] ↥L) = SSGRoute.res k L (σ * τ) := by
    rw [Subgroup.coe_mul, ← hσeq, ← hτeq, map_mul]
  have key1 : b₀ (((g * h) :
        ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) :
          ↥L ≃ₐ[k] ↥L) = b (σ * τ) := by
    rw [hcoe, ← hb₀ (σ * τ) hmem]
  -- Now apply the cocycle identity for `b` on `decomp k A` and rewrite through `hb₀`.
  rw [key1, hb σ hσ τ hτ, hb₀ σ hσ, hb₀ τ hτ, hσeq, hτeq, hcomp]

end Work.SSGRoute.PT
