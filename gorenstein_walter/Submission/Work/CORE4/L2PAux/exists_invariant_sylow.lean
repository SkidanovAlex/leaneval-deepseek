import Mathlib
import Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

namespace Work.CORE4.L2PAux

set_option linter.style.haveILetI false

open Subgroup
open OddOrder.Isaacs.Ch03

/-- Given a finite group `L`, a subgroup `Q`, and a `p`-subgroup `T ≤ N_L(Q)` with
`p` coprime to `|Q|`, there is a `T`-invariant Sylow `ℓ`-subgroup `R` of `Q`.

This is Isaacs, *Finite Group Theory*, Theorem 3.23(a) applied to the conjugation action of
`T` on `Q` (a coprime action: `(|T|, |Q|) = 1` because `T` is a `p`-group and `p ∤ |Q|`), with
the trivial subgroup as the invariant subgroup to be extended to an invariant Sylow. -/
theorem exists_invariant_sylow {L : Type} [Group L] [Finite L] {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (Q T : Subgroup L) (hTN : T ≤ Subgroup.normalizer (Q : Set L)) (hT : IsPGroup p T)
    (hcop : Nat.Coprime p (Nat.card Q)) :
    ∃ R : Subgroup L, R ≤ Q ∧ IsPGroup ℓ R ∧ Nat.card R = ℓ ^ (Nat.card Q).factorization ℓ ∧
      T ≤ Subgroup.normalizer (R : Set L) := by
  classical
  -- The conjugation action of `T` on `Q`, well defined because `T ≤ N_L(Q)`.
  letI act : MulDistribMulAction ↥T ↥Q :=
    MulDistribMulAction.compHom ↥Q (Subgroup.inclusion hTN)
  let φ : ↥T →* MulAut ↥Q := MulDistribMulAction.toMulAut ↥T ↥Q
  -- The action is conjugation in `L`.
  have hφ_coe : ∀ (a : ↥T) (k : ↥Q),
      (((φ a) k : ↥Q) : L) = (a : L) * (k : L) * (a : L)⁻¹ := by
    intro a k
    have h1 : (φ a) k = a • k := by
      rw [MulDistribMulAction.toMulAut_apply]
      rfl
    rw [h1]
    rfl
  -- `(|T|, |Q|) = 1`.
  have hcop' : Nat.Coprime (Nat.card ↥T) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    rw [hn]
    exact hcop.pow_left n
  -- `T` is solvable (it is a `p`-group, hence nilpotent).
  have hsolv : Group.IsSolvable ↥T ∨ Group.IsSolvable ↥Q := by
    haveI : Group.IsNilpotent ↥T := hT.isNilpotent
    exact Or.inl inferInstance
  -- Isaacs 3.23/3.25: an invariant Sylow `ℓ`-subgroup of `Q` containing `⊥`.
  obtain ⟨S, hS_inv, -⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow (G := ↥Q) (A := ↥T)
      (φ := φ) hcop' hsolv (p := ℓ) (P := ⊥) IsPGroup.of_bot (IsAInvariant.bot φ)
  refine ⟨(S : Subgroup ↥Q).map Q.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact (S.isPGroup').map Q.subtype
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  · intro t ht
    exact IsAInvariant.mem_normalizer_map_subtype_of_smul_val (G := L) (W := Q) (A := ↥T)
      (φ := φ) (L := (S : Subgroup ↥Q)) hS_inv (a := ⟨t, ht⟩) (g := t) (hφ_coe ⟨t, ht⟩)

end Work.CORE4.L2PAux
