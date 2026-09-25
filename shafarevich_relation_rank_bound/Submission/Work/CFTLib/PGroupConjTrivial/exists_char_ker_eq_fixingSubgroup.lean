import Mathlib
import Submission.Work.CFTLib.InvCharCrux
import Submission.Work.CFTLib.InvCharCrux.restrictKerHom

namespace Work.CFTLib.PGroupConjTrivial

/-- Let `K'/F`, `K/F` be finite Galois extensions of number fields with `K ⊆ K'` (scalar tower),
and `M ⊆ K'` a finite Galois extension of `K` of degree `p` (a prime).  Write
`N = ker (AlgEquiv.restrictNormalHom K : Gal(K'/F) →* Gal(K/F)) = Gal(K'/K)` and
`H = (IntermediateField.restrictScalars F M).fixingSubgroup = Gal(K'/M) ≤ Gal(K'/F)`.

Then there is a surjective group homomorphism `φ : N →* Multiplicative (ZMod p)` whose kernel is
exactly `H ∩ N = H.subgroupOf N`.

Indeed `N/(H∩N) ≅ Gal(M/K)` (restriction to `M`), which is a group of order `p`, hence cyclic of
order `p` and isomorphic to `Multiplicative (ZMod p)` (`zmodCyclicMulEquiv`); composing the
quotient map `N ↠ N/(H∩N)` with this isomorphism gives `φ`. -/
theorem exists_char_ker_eq_fixingSubgroup {F K K' : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (p : ℕ) [Fact p.Prime] (M : IntermediateField K K')
    [FiniteDimensional K ↥M] [IsGalois K ↥M] (hfin : Module.finrank K ↥M = p) :
    ∃ φ : (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker →*
        Multiplicative (ZMod p),
      φ.ker = (IntermediateField.restrictScalars F M).fixingSubgroup.subgroupOf
        (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker ∧
      Function.Surjective φ := by
  classical
  -- `K'/K` is Galois and `M/K` is Galois.
  haveI hIsGalKK' : IsGalois K K' := IsGalois.tower_top_of_isGalois F K K'
  haveI hNormKK' : Normal K K' := IsGalois.to_normal
  haveI hNormKM : Normal K ↥M := IsGalois.to_normal
  -- Restriction to `M` gives a surjection `N ↠ Gal(M/K)` with kernel `H ∩ N`.
  obtain ⟨ρ, hsurj, hker⟩ :=
    Work.CFTLib.InvCharCrux.restrictKerHom (F := F) (K := K) (K' := K') M
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
  -- `Gal(M/K)` is a group of prime order `p`, hence isomorphic to `Multiplicative (ZMod p)`.
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hcardM : Nat.card (↥M ≃ₐ[K] ↥M) = p := by
    rw [IsGalois.card_aut_eq_finrank K ↥M, hfin]
  let iso : (↥M ≃ₐ[K] ↥M) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcardM hcardZ
  refine ⟨iso.toMonoidHom.comp ρ, ?_, ?_⟩
  · -- kernel of the composite is the kernel of `ρ`, i.e. `H ∩ N`
    ext n
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    rw [← hker_eq]
    constructor
    · intro h
      rw [MulEquiv.coe_toMonoidHom] at h
      rw [MonoidHom.mem_ker]
      exact iso.injective (by rw [h, map_one])
    · intro h
      rw [MonoidHom.mem_ker] at h
      rw [h, map_one]
  · exact iso.surjective.comp hsurj

end Work.CFTLib.PGroupConjTrivial
