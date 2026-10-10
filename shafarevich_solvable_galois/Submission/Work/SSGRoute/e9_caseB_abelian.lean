import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The fixed field of the kernel of a nontrivial homomorphism into a commutative group is a
nontrivial abelian Galois extension.**  Let `L/K` be a finite Galois extension of fields and let
`φ : Gal(L/K) →* Multiplicative M` be a homomorphism into the multiplicative group of an additive
commutative group `M` (so the target is commutative).  If `φ ≠ 1`, then for
`E := fixedField φ.ker` the extension `E/K` has commutative Galois group and `[E : K] ≠ 1`.

Route: `IsGalois.normalAutEquivQuotient φ.ker` identifies `Gal(E/K)` with `Gal(L/K) ⧸ φ.ker`, which
is isomorphic to `φ.range`, a subgroup of the commutative group `Multiplicative M`; hence
`Gal(E/K)` is commutative.  If moreover `[E : K] = 1` then `E = ⊥ = K`, so `φ.ker = ⊤` and `φ = 1`
(using `IntermediateField.fixedField_top` and `IntermediateField.fixingSubgroup_fixedField`),
contradicting the hypothesis; use `IsGalois.card_aut_eq_finrank` to move between `[E : K]` and
`Nat.card (↥E ≃ₐ[K] ↥E)`. -/
theorem e9_caseB_abelian
    {K L M : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup M] (φ : (L ≃ₐ[K] L) →* Multiplicative M)
    (hφ : ∃ σ : L ≃ₐ[K] L, φ σ ≠ 1) :
    IsMulCommutative
        (↥(IntermediateField.fixedField φ.ker) ≃ₐ[K] ↥(IntermediateField.fixedField φ.ker)) ∧
      Module.finrank K ↥(IntermediateField.fixedField φ.ker) ≠ 1 := by
  have hnormal : φ.ker.Normal := MonoidHom.normal_ker φ
  refine ⟨?_, ?_⟩
  · -- `Gal(E/K)` is a quotient of `Gal(L/K)` modulo `φ.ker`, hence is isomorphic to the
    -- subgroup `φ.range` of the commutative group `Multiplicative M`.
    let e : ↥φ.range ≃* (↥(IntermediateField.fixedField φ.ker) ≃ₐ[K]
        ↥(IntermediateField.fixedField φ.ker)) :=
      (QuotientGroup.quotientKerEquivRange φ).symm.trans (IsGalois.normalAutEquivQuotient φ.ker)
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    have hcomm : a' * b' = b' * a' :=
      Subtype.ext (mul_comm (a' : Multiplicative M) (b' : Multiplicative M))
    rw [← map_mul, ← map_mul, hcomm]
  · -- If `[E : K] = 1` then `E = ⊥`, so `φ.ker = fixingSubgroup ⊥ = ⊤` and `φ = 1`.
    intro h1
    have hE : IntermediateField.fixedField φ.ker = ⊥ := by
      refine (IntermediateField.eq_of_le_of_finrank_eq
        (F := (⊥ : IntermediateField K L)) (E := IntermediateField.fixedField φ.ker)
        bot_le ?_).symm
      rw [IntermediateField.finrank_bot, h1]
    have hker : φ.ker = ⊤ := by
      rw [← IntermediateField.fixingSubgroup_fixedField φ.ker, hE,
        IntermediateField.fixingSubgroup_bot]
    obtain ⟨σ, hσ⟩ := hφ
    exact hσ (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top σ))

end Work.SSGRoute
