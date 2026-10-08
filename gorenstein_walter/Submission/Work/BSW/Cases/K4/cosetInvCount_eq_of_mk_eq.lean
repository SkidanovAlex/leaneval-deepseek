import Mathlib
import Submission.Work.BSW.Defs

/-!
# `cosetInvCount` is a function of the left coset

`Work.GW2.cosetInvCount H g` counts the involutions `x` of `G` with `g⁻¹ * x ∈ H`, i.e. the
involutions lying in the left coset `g H` (`x ∈ g H ↔ g⁻¹ * x ∈ H`).  Consequently it only
depends on the left coset of `g`, and in particular two elements with the same image in
`G ⧸ H` give the same count.  This is the lemma needed by the `K4` case analysis.
-/

namespace Work.BSW.Cases.K4

/-- Two elements in the same left coset of `H` give the same `cosetInvCount`; stated directly
through the quotient map `G → G ⧸ H`. -/
theorem cosetInvCount_eq_of_mk_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) {g g' : G}
    (h : (g : G ⧸ H) = (g' : G ⧸ H)) :
    Work.GW2.cosetInvCount H g = Work.GW2.cosetInvCount H g' := by
  -- The hypothesis says `g⁻¹ * g' ∈ H`.
  have hmem : g⁻¹ * g' ∈ H := QuotientGroup.eq.mp h
  unfold Work.GW2.cosetInvCount
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro ⟨hx, hgx⟩
    refine ⟨hx, ?_⟩
    have : g'⁻¹ * x = (g⁻¹ * g')⁻¹ * (g⁻¹ * x) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hmem) hgx
  · intro ⟨hx, hgx⟩
    refine ⟨hx, ?_⟩
    have : g⁻¹ * x = (g⁻¹ * g') * (g'⁻¹ * x) := by group
    rw [this]
    exact H.mul_mem hmem hgx

end Work.BSW.Cases.K4
