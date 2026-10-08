import Mathlib

namespace Work.CORE3.A7V18

theorem QuotientCenterIso {Y : Type} [Group Y] [Group.IsPerfect Y]
    (M : Subgroup Y) [M.Normal] (hM : M ≤ Subgroup.center Y) (hne : M ≠ ⊤)
    (hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y)) :
    Nonempty (((Y ⧸ M) ⧸ Subgroup.center (Y ⧸ M)) ≃* (Y ⧸ Subgroup.center Y)) ∧
    IsSimpleGroup ((Y ⧸ M) ⧸ Subgroup.center (Y ⧸ M)) := by
  -- The centre of `(Y ⧸ M) ⧸ (Z Y / M)` is trivial: this quotient is `Y / Z Y` by the third
  -- isomorphism theorem, and `Y / Z Y` has trivial centre because `Y` is perfect (Grün's lemma).
  have hbot : Subgroup.center ((Y ⧸ M) ⧸ (Subgroup.center Y).map (QuotientGroup.mk' M)) = ⊥ := by
    rw [← Subgroup.map_center_eq (QuotientGroup.quotientQuotientEquivQuotient M (Subgroup.center Y) hM).symm,
      Group.IsPerfect.center_quotient_center_eq_bot Y]
    exact Subgroup.map_bot _
  -- Consequently the centre of `Y ⧸ M` is exactly the image of the centre of `Y`.
  have hcenter : Subgroup.center (Y ⧸ M) = (Subgroup.center Y).map (QuotientGroup.mk' M) := by
    apply le_antisymm
    · have h1 : Subgroup.map (QuotientGroup.mk' ((Subgroup.center Y).map (QuotientGroup.mk' M)))
          (Subgroup.center (Y ⧸ M)) ≤
          Subgroup.center ((Y ⧸ M) ⧸ (Subgroup.center Y).map (QuotientGroup.mk' M)) :=
        Subgroup.map_center_le_center (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      rw [hbot] at h1
      have h2 : Subgroup.map (QuotientGroup.mk' ((Subgroup.center Y).map (QuotientGroup.mk' M)))
          (Subgroup.center (Y ⧸ M)) = ⊥ := le_bot_iff.mp h1
      have h3 : Subgroup.center (Y ⧸ M) ≤
          (QuotientGroup.mk' ((Subgroup.center Y).map (QuotientGroup.mk' M))).ker :=
        (Subgroup.map_eq_bot_iff _).mp h2
      rwa [QuotientGroup.ker_mk'] at h3
    · exact Subgroup.map_center_le_center (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have e1 : ((Y ⧸ M) ⧸ Subgroup.center (Y ⧸ M)) ≃*
      ((Y ⧸ M) ⧸ (Subgroup.center Y).map (QuotientGroup.mk' M)) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  have e2 : ((Y ⧸ M) ⧸ (Subgroup.center Y).map (QuotientGroup.mk' M)) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.quotientQuotientEquivQuotient M (Subgroup.center Y) hM
  exact ⟨⟨e1.trans e2⟩, (e1.trans e2).isSimpleGroup_congr.mpr hsimple⟩

end Work.CORE3.A7V18
