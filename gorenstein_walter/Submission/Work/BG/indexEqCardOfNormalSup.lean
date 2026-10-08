import Mathlib

open scoped Pointwise

namespace Work.BG

/-- If a normal subgroup `K` of a finite group `X` satisfies `B ⊔ K = ⊤` and `B ⊓ K = ⊥`, then the index of `B` in `X` equals `|K|`. -/
theorem indexEqCardOfNormalSup {X : Type*} [Group X] [Finite X]
    (B K : Subgroup X) (hK : K.Normal) (hsup : B ⊔ K = ⊤) (hinf : B ⊓ K = ⊥) :
    B.index = Nat.card K := by
  -- `B` and `K` are lattice complements, hence `X → B × K`, `x ↦ (b, k)`, is a bijection.
  have hdisj : Disjoint B K := disjoint_iff.mpr hinf
  -- Since `K` is normal, the set-theoretic product `B * K` is the carrier of `B ⊔ K = ⊤`.
  have hmul : (B : Set X) * (K : Set X) = Set.univ := by
    rw [← Subgroup.mul_normal B K (hN := hK), hsup]
    rfl
  have hcomp : B.IsComplement' K := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  -- `B.index = Nat.card K` is `IsComplement'.index_eq_card` applied to the symmetric complement.
  exact hcomp.symm.index_eq_card

end Work.BG
