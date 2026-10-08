import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_twoPointStabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.map_conj_stabilizer_inf_of_twoTransitive
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.SL2

set_option linter.style.haveILetI false

open scoped LinearAlgebra.Projectivization

/-- In characteristic two, a finite field `K` has even cardinality. -/
theorem even_natCard_of_charP_two {K : Type*} [Field K] [Fintype K] (hchar : CharP K 2) :
    Even (Nat.card K) := by
  haveI : CharP K 2 := hchar
  obtain ⟨n, _hpr, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact Nat.even_pow.mpr ⟨even_two, (PNat.pos n).ne'⟩

theorem stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup {K : Type*} [Field K] [Fintype K]
    (hchar : CharP K 2) (hcard : 2 ≤ Nat.card K) (a : Projectivization K (Fin 2 → K)) :
    (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a ≠ ⊤) ∧
      Even (Nat.card (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a)) ∧
      ∀ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K,
        g ∉ MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a →
        Odd (Nat.card ((MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a ⊓
          (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a).map
            (MulAut.conj g).toMonoidHom :
              Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))) := by
  classical
  haveI : CharP K 2 := hchar
  haveI : MulAction.IsMultiplyPretransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K)) 2 :=
    isMultiplyPretransitive_projectiveSpecialLinearGroup_two
  haveI : MulAction.IsPretransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hcardPSL := card_stabilizer_projectiveSpecialLinearGroup (K := K) hchar hcard a
  have hKeven : Even (Nat.card K) := even_natCard_of_charP_two hchar
  refine ⟨?_, ?_, ?_⟩
  · -- the stabilizer is not the whole group
    haveI : Fintype (Projectivization K (Fin 2 → K)) := Fintype.ofFinite _
    have hlt : 1 < Fintype.card (Projectivization K (Fin 2 → K)) := by
      rw [← Nat.card_eq_fintype_card, natCard_projectivization_fin_two]
      omega
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hlt a
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
      (M := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a b
    intro htop
    have hgmem : g ∈ MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a := by
      rw [htop]; exact Subgroup.mem_top g
    rw [MulAction.mem_stabilizer_iff] at hgmem
    exact hb (hg ▸ hgmem)
  · -- the stabilizer has even cardinality
    rw [hcardPSL]
    exact hKeven.mul_right (Nat.card K - 1)
  · -- the intersection of two distinct point stabilizers has odd cardinality
    intro g hg
    have hga : g • a ≠ a := by
      intro h
      exact hg (by rw [MulAction.mem_stabilizer_iff]; exact h)
    have hmap : (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a).map
        (MulAut.conj g).toMonoidHom =
        MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (g • a) :=
      (MulAction.stabilizer_smul_eq_stabilizer_map_conj g a).symm
    rw [hmap]
    rw [card_twoPointStabilizer_projectiveSpecialLinearGroup (K := K) hchar hcard a (g • a)
      (Ne.symm hga)]
    exact Nat.Even.sub_odd (by omega) hKeven odd_one

end Commons.GroupTheory.SL2
