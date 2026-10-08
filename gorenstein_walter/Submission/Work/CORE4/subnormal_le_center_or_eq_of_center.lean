import Mathlib

namespace Work.CORE4

/-- **The dichotomy for a group with simple central quotient** (the elementary part of Bender's
components theory): in a group `S` that is perfect and has `S / Z(S)` simple, every subnormal
subgroup is either contained in the centre or is the whole group.

Route: the image of `D` in the simple group `S / Z(S)` is subnormal
(`Subgroup.IsSubnormal.quotient`), hence trivial or everything.  Trivial gives `D ≤ Z(S)`;
everything gives `D ⊔ Z(S) = ⊤` (via `QuotientGroup.comap_map_mk'`), whence `D ◁ S` with
`S / D ≅ Z(S) / (D ⊓ Z(S))` commutative, so `commutator S ≤ D`
(`Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top`), and perfectness gives
`D = ⊤`. -/
theorem subnormal_le_center_or_eq_of_center {S : Type*} [Group S] (D : Subgroup S)
    (hD : D.IsSubnormal) (hperf : commutator S = ⊤)
    (hsimp : IsSimpleGroup (S ⧸ Subgroup.center S)) :
    D ≤ Subgroup.center S ∨ D = ⊤ := by
  -- The image of `D` in the simple group `S ⧸ Z(S)` is subnormal.
  have hDq : (D.map (QuotientGroup.mk' (Subgroup.center S))).IsSubnormal := hD.quotient
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hDq with hbot | htop
  · -- Trivial image: `D` lies in the kernel of `S → S ⧸ Z(S)`, i.e. in `Z(S)`.
    left
    rw [Subgroup.map_eq_bot_iff] at hbot
    rwa [QuotientGroup.ker_mk'] at hbot
  · -- Full image: `D ⊔ Z(S) = ⊤`, so `D` is normal and `S / D` is commutative.
    right
    have hsup : D ⊔ Subgroup.center S = ⊤ := by
      have h := QuotientGroup.comap_map_mk' (Subgroup.center S) D
      rw [htop, Subgroup.comap_top] at h
      simpa [sup_comm] using h.symm
    have hDnorm : D.Normal := by
      -- `D` and the central `Z(S)` both normalise `D`, hence `S = D ⊔ Z(S) ≤ N(D)`.
      have hle : D ⊔ Subgroup.center S ≤ Subgroup.normalizer (D : Set S) :=
        sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer (D : Set S))
      rw [hsup] at hle
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    -- `Z(S)` is commutative and `D ⊔ Z(S) = ⊤`, so `S' ≤ D`.
    have hcomm : commutator S ≤ D :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup (inferInstance)
    rw [hperf] at hcomm
    exact top_le_iff.mp hcomm

end Work.CORE4
