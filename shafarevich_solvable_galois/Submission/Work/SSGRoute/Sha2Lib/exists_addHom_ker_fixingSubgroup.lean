import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- A finite Galois extension, whose base field is a number field and whose Galois group is
isomorphic to `ZMod p`, admits a nonzero additive character on its Galois group.

Concretely: if `L/k` is finite Galois and `F` is an intermediate field with `F/k` Galois of
prime degree `p`, then the restriction map `Gal(L/k) →* Gal(F/k)` is surjective with kernel the
fixing subgroup `F.fixingSubgroup`, and `Gal(F/k)` is cyclic of order `p`, hence isomorphic to
`Multiplicative (ZMod p)`. Composing these gives a monoid homomorphism `Gal(L/k) →* ZMod p`
(additively) with the required kernel. -/
theorem exists_addHom_ker_fixingSubgroup (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    (F : IntermediateField k L) [FiniteDimensional k F] [IsGalois k F] [NumberField F]
    (hF : Module.finrank k F = p) :
    ∃ g : Additive (L ≃ₐ[k] L) →+ ZMod p,
      g ≠ 0 ∧ ∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup := by
  -- `Gal(F/k)` is cyclic of order `p`
  have hcard : Nat.card (F ≃ₐ[k] F) = p := by
    rw [IsGalois.card_aut_eq_finrank (k) (F), hF]
  have hcyc : IsCyclic (F ≃ₐ[k] F) := isCyclic_of_prime_card hcard
  -- an isomorphism of `Gal(F/k)` with the additive group `ZMod p`
  let e : (F ≃ₐ[k] F) ≃* Multiplicative (ZMod p) := hcard ▸ (zmodCyclicMulEquiv hcyc).symm
  -- restriction of `Gal(L/k)` to `Gal(F/k)`
  let φ : (L ≃ₐ[k] L) →* (F ≃ₐ[k] F) := AlgEquiv.restrictNormalHom ↥F
  let f : (L ≃ₐ[k] L) →* Multiplicative (ZMod p) := e.toMonoidHom.comp φ
  -- the kernel of `f` is exactly the fixing subgroup of `F`
  have hkerf : f.ker = F.fixingSubgroup := by
    have h1 : f = e.toMonoidHom.comp φ := rfl
    rw [h1, MonoidHom.ker_comp_of_injective φ e.toMonoidHom e.injective,
      IntermediateField.restrictNormalHom_ker F]
  -- `f` is onto, since `e` is an isomorphism and `φ` is onto
  have hsurj : Function.Surjective f := e.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥F) L)
  have hker : ∀ σ : L ≃ₐ[k] L, f.toAdditive (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup := by
    intro σ
    rw [← hkerf, MonoidHom.mem_ker]
    exact Iff.rfl
  refine ⟨f.toAdditive, ?_, hker⟩
  -- `f.toAdditive` is nonzero because `f` is onto onto a nontrivial group
  intro hg
  obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod p))
  have h0 : f.toAdditive (Additive.ofMul σ) = 0 := by rw [hg]; rfl
  have hmem := (hker σ).mp h0
  rw [← hkerf, MonoidHom.mem_ker, hσ] at hmem
  exact one_ne_zero (Multiplicative.ofAdd.injective hmem)

end Work.SSGRoute.Sha2Lib
