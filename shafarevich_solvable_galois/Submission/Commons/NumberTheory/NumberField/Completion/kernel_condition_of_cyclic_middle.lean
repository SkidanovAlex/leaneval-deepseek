import Mathlib
import Submission.Commons.FieldTheory.Galois.ker_le_range_of_natCard_quotient_units_range_norm_eq_mul
import Submission.Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

/-- **The kernel condition for a tower with cyclic middle extension.**

Let `B ⊆ B₁ ⊆ E` be a tower of finite Galois extensions of a local field
`Q.adicCompletion K`, with `E / B` abelian (so in particular every intermediate extension is
abelian).  If `B₁ / B` is cyclic, then the group of norm-one units of `B₁ / B` is contained in the
group of norms from `E / B₁`.

The proof is the multiplicativity of the norm index along the tower: the abelian local norm index
theorem (`abelian_local_norm_index_at_base`, local class field theory) computes
`|Bˣ ⧸ N_{E/B}(Eˣ)| = #Gal(E/B)`, `|Bˣ ⧸ N_{B₁/B}(B₁ˣ)| = #Gal(B₁/B)` and
`|B₁ˣ ⧸ N_{E/B₁}(Eˣ)| = #Gal(E/B₁)`, and the three degrees multiply; then
`ker_le_range_of_natCard_quotient_units_range_norm_eq_mul` converts this tower multiplicativity
into the stated containment. -/

theorem kernel_condition_of_cyclic_middle
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra (Q.adicCompletion K) B₁]
    [Algebra (Q.adicCompletion K) E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E]
    [IsScalarTower (Q.adicCompletion K) B B₁] [IsScalarTower (Q.adicCompletion K) B E]
    [IsScalarTower B B₁ E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional (Q.adicCompletion K) B₁]
    [FiniteDimensional B B₁] [FiniteDimensional B E] [FiniteDimensional B₁ E]
    [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois B B₁] [IsGalois B₁ E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    (hcyc : IsCyclic (B₁ ≃ₐ[B] B₁)) :
    MonoidHom.ker (Units.map (Algebra.norm B : B₁ →* B)) ≤
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) := by
  have hST : IsScalarTower (Q.adicCompletion K) B₁ E := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    symm
    rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B B₁ x,
        ← IsScalarTower.algebraMap_apply B B₁ E ((algebraMap (Q.adicCompletion K) B) x),
        ← IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E x]
  have hcommB₁ : ∀ a b : B₁ ≃ₐ[B] B₁, a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := AlgEquiv.restrictNormalHom_surjective (F := B) (K₁ := B₁) (E := E) a
    obtain ⟨b', hb'⟩ := AlgEquiv.restrictNormalHom_surjective (F := B) (K₁ := B₁) (E := E) b
    rw [← ha', ← hb', ← map_mul, hcomm a' b', map_mul, ha', hb']
  have hcommE : ∀ a b : E ≃ₐ[B₁] E, a * b = b * a := by
    intro a b
    have h := hcomm (a.restrictScalars B) (b.restrictScalars B)
    apply AlgEquiv.ext; intro x
    have hx := congr_fun (congrArg (fun g : E ≃ₐ[B] E => (g : E → E)) h) x
    simpa [AlgEquiv.mul_apply] using hx
  have h1 := abelian_local_norm_index_at_base (K := K) Q (B := B) (E := E) hcomm
  have h2 := abelian_local_norm_index_at_base (K := K) Q (B := B) (E := B₁) hcommB₁
  have h3 := abelian_local_norm_index_at_base (K := K) Q (B := B₁) (E := E) hcommE
  have hdeg : Nat.card (E ≃ₐ[B] E) =
      Nat.card (B₁ ≃ₐ[B] B₁) * Nat.card (E ≃ₐ[B₁] E) := by
    rw [IsGalois.card_aut_eq_finrank B E, IsGalois.card_aut_eq_finrank B B₁,
      IsGalois.card_aut_eq_finrank B₁ E, Module.finrank_mul_finrank]
  have hE : Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (B₁ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁))) *
        Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))) := by
    rw [h1, h3, h2, mul_comm, hdeg]
  have hpos1 : 0 < Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) := by
    rw [h1]; exact Nat.card_pos
  have hpos2 : 0 < Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))) := by
    rw [h2]; exact Nat.card_pos
  have hfin1 : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_eq_card]; exact hpos1.ne'
  have hfin2 : (MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_eq_card]; exact hpos2.ne'
  exact Commons.FieldTheory.Galois.ker_le_range_of_natCard_quotient_units_range_norm_eq_mul
    (F := B) (M := B₁) (E := E) hfin1 hfin2 hE

end Commons.NumberTheory.NumberField.Completion
