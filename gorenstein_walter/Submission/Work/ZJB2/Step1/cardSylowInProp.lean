import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

open Work.ZJB

open scoped Classical

/-- A maximal `p`-subgroup `T` of a subgroup `M` (in the sense of `IsSylowIn`) has order
equal to `p ^ ν_p(|M|)`.  This is the statement that a Sylow `p`-subgroup of the group `M`
has order the full `p`-part of `|M|`, transported to subgroups of a finite ambient group
via the isomorphism `M ≃* ↥M`.

The proof builds the Sylow `p`-subgroup `T' = T.subgroupOf M` of `↥M` and compares it with
a Sylow `p`-subgroup `P` of `↥M` provided by `IsPGroup.exists_le_sylow`. -/
theorem cardSylowInProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.CardSylowInProp p G := by
  intro T M hTM
  obtain ⟨hle, hpT, hmax⟩ := hTM
  -- `T'` is `T` regarded as a subgroup of `↥M`.
  let T' : Subgroup ↥M := T.subgroupOf M
  have hT'_p : IsPGroup p ↥T' := by
    have h : T' = T.comap M.subtype := rfl
    rw [h]
    exact hpT.comap_of_injective M.subtype (Subgroup.subtype_injective M)
  -- A Sylow `p`-subgroup of `↥M` containing `T'`.
  obtain ⟨P, hT'P⟩ := hT'_p.exists_le_sylow
  -- `P`, pushed back into `G`, is a `p`-subgroup of `M` containing `T`.
  have hmap : Subgroup.map M.subtype (P : Subgroup ↥M) = T :=
    hmax _ (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hle]
      exact Subgroup.map_mono hT'P)
      (Subgroup.map_subtype_le _)
      (P.isPGroup'.map M.subtype)
  -- Hence `P = T'`.
  have hPT : (P : Subgroup ↥M) = T' := by
    have h := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)
      (P : Subgroup ↥M)
    rw [hmap] at h
    show (P : Subgroup ↥M) = T.subgroupOf M
    rw [← Subgroup.comap_subtype T M, ← h]
  calc Nat.card T = Nat.card T' :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    _ = Nat.card (P : Subgroup ↥M) := by rw [hPT]
    _ = p ^ (Nat.card ↥M).factorization p := Sylow.card_eq_multiplicity P
    _ = p ^ nuP p M := rfl

end Work.ZJB2.Step1
