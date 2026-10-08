import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

/-- **Cardinality bound for `R/Z(R)` inside `Q/Z(Q)`.**

For a subgroup `R ≤ Q` the natural composite `↥R → Q → Q/Z(Q)` has kernel `R ∩ Z(Q)`,
which lies in `Z(R)`; hence `R/Z(R)` is a quotient of the image of `R` in `Q/Z(Q)`,
and the cardinality can only drop.  This is the elementary counting step behind the
`|R/Z(R)| ≥ 60` bound used in `QOddCent`. -/
theorem QOddCentCard {Q : Type*} [Group Q] [Finite Q] (R : Subgroup Q) :
    Nat.card (↥R ⧸ Subgroup.center ↥R) ≤
      Nat.card (R.map (QuotientGroup.mk' (Subgroup.center Q))) := by
  -- The composite `↥R → Q → Q/Z(Q)`.
  let f : ↥R →* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp R.subtype
  -- Its kernel is `R ∩ Z(Q) ⊆ Z(R)`.
  have hker_le : f.ker ≤ Subgroup.center ↥R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hmem : ((x : ↥R) : Q) ∈ Subgroup.center Q := by
      have h := (MonoidHom.mem_ker).1 hx
      simp only [f, MonoidHom.comp_apply] at h
      have h2 : ((x : ↥R) : Q) ∈ (QuotientGroup.mk' (Subgroup.center Q)).ker :=
        (MonoidHom.mem_ker).2 h
      rwa [QuotientGroup.ker_mk' (Subgroup.center Q)] at h2
    exact (Subgroup.mem_center_iff).1 hmem (y : Q)
  -- The range of the composite is the image of `R` in `Q/Z(Q)`.
  have hrange : f.range = R.map (QuotientGroup.mk' (Subgroup.center Q)) := by
    rw [show f = (QuotientGroup.mk' (Subgroup.center Q)).comp R.subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  calc Nat.card (↥R ⧸ Subgroup.center ↥R)
      = (Subgroup.center ↥R).index := (Subgroup.index_eq_card _).symm
    _ ≤ f.ker.index := by
        -- `Z(R)/ker` is a quotient of `R/ker`, so the index divides and drops.
        apply Nat.le_of_dvd _ (Subgroup.index_dvd_of_le hker_le)
        rw [Subgroup.index_ker]
        exact Nat.card_pos
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (R.map (QuotientGroup.mk' (Subgroup.center Q))) := by rw [hrange]

end Work.CORE4
