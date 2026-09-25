import Mathlib
import Submission.Work.CFTLib.InvCharCrux
import Submission.Work.CFTLib.InvCharCrux.restrictKerHom

namespace Work.CFTLib.PGroupConjTrivial

/-- Let `K'/F` and `K/F` be finite Galois extensions of number fields with `K ⊆ K'` (scalar
tower), and let `M ⊆ K'` be a finite Galois extension of `K` of degree `p` (a prime).  With

`N = ker (AlgEquiv.restrictNormalHom K : Gal(K'/F) →* Gal(K/F)) = Gal(K'/K)`

and `H = (IntermediateField.restrictScalars F M).fixingSubgroup = Gal(K'/M) ≤ Gal(K'/F)`, the
quotient `N / (H ∩ N)` has `p` elements.

Indeed `restriction to M` gives a surjection `N ↠ Gal(M/K)` whose kernel is `H ∩ N`
(`Work.CFTLib.InvCharCrux.restrictKerHom`), and `Nat.card Gal(M/K) = [M : K] = p`
(`IsGalois.card_aut_eq_finrank`). -/
theorem card_quotient_fixingSubgroup {F K K' : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (p : ℕ) [Fact p.Prime] (M : IntermediateField K K')
    [FiniteDimensional K ↥M] [IsGalois K ↥M] (hfin : Module.finrank K ↥M = p) :
    Nat.card ((AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker ⧸
      (IntermediateField.restrictScalars F M).fixingSubgroup.subgroupOf
        (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) = p := by
  classical
  -- `K'/K` is Galois (so `K` is normal in `K'`), and `M/K` is Galois (so normal in `K'`).
  haveI hIsGalKK' : IsGalois K K' := IsGalois.tower_top_of_isGalois F K K'
  haveI hNormKK' : Normal K K' := IsGalois.to_normal
  haveI hNormKM : Normal K ↥M := IsGalois.to_normal
  -- Restriction to `M` gives a surjection `N ↠ Gal(M/K)` with kernel `Gal(K'/M)`.
  obtain ⟨ρ, hsurj, hker⟩ :=
    Work.CFTLib.InvCharCrux.restrictKerHom (F := F) (K := K) (K' := K') M
  -- Its kernel, written as a subgroup of `N = Gal(K'/K)`, is `H ∩ N`.
  have hker_eq : ρ.ker = (IntermediateField.restrictScalars F M).fixingSubgroup.subgroupOf
      (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker := by
    ext n
    rw [MonoidHom.mem_ker, hker n, Subgroup.mem_subgroupOf,
      IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  -- `H ∩ N` is normal in `N` because it is (via the above) the kernel of `ρ`.
  haveI hK0 : ((IntermediateField.restrictScalars F M).fixingSubgroup.subgroupOf
      (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker).Normal :=
    hker_eq ▸ (inferInstance : ρ.ker.Normal)
  calc Nat.card ((AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker ⧸
        (IntermediateField.restrictScalars F M).fixingSubgroup.subgroupOf
          (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker)
      = Nat.card ((AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker ⧸ ρ.ker) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).toEquiv
    _ = Nat.card (↥M ≃ₐ[K] ↥M) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv
    _ = p := by rw [IsGalois.card_aut_eq_finrank K ↥M, hfin]

end Work.CFTLib.PGroupConjTrivial
