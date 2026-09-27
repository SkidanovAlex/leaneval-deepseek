import Mathlib

open Set

namespace Work.EQ

/-- **Second-countable form.**  In a second-countable space, the set of points of `A` that are
*not* condensation points of `A` is countable: it is covered by the (countably many) basis
elements `b` for which `A ∩ b` is countable.  Hence an uncountable `A` has a condensation point
outside any countable set `D`. -/
theorem exists_condensationPt_of_secondCountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {A D : Set X} (hD : D.Countable) (hA : ¬ A.Countable) :
    ∃ x : X, x ∉ D ∧ ∀ U : Set X, IsOpen U → x ∈ U → ¬ (A ∩ U).Countable := by
  classical
  obtain ⟨B, hBct, -, hBbasis⟩ := TopologicalSpace.exists_countable_basis X
  -- the (countable) family of basis elements on which `A` is countable
  let G : Set (Set X) := {b ∈ B | (A ∩ b).Countable}
  have hGct : G.Countable := hBct.mono (fun b hb => hb.1)
  -- the set of points of `A` that are *not* condensation points of `A`
  let Bad : Set X := {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (A ∩ U).Countable}
  -- `A ∩ Bad` sits inside a countable union of countable sets
  have hBad_sub : A ∩ Bad ⊆ ⋃ b ∈ G, (A ∩ b) := by
    rintro x ⟨hxA, U, hUo, hxU, hUct⟩
    obtain ⟨b, hbB, hxb, hbU⟩ := hBbasis.exists_subset_of_mem_open hxU hUo
    exact mem_biUnion ⟨hbB, hUct.mono (inter_subset_inter_right A hbU)⟩ ⟨hxA, hxb⟩
  have hBadct : (A ∩ Bad).Countable :=
    (hGct.biUnion (fun b hb => hb.2)).mono hBad_sub
  -- hence the condensation points of `A` inside `A` are uncountable
  have hgood : ¬ (A \ Bad).Countable := by
    intro h
    apply hA
    have heq : A = (A ∩ Bad) ∪ (A \ Bad) := by
      rw [Set.sdiff_eq, Set.inter_union_compl]
    rw [heq]
    exact hBadct.union h
  -- removing the countable set `D` keeps it nonempty
  have hne : ((A \ Bad) \ D).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hgood (Countable.of_sdiff (by rw [h]; exact countable_empty) hD)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hx.2, ?_⟩
  have hxBad : x ∉ Bad := hx.1.2
  intro U hUo hxU hUct
  exact hxBad ⟨U, hUo, hxU, hUct⟩

/-- **A countable exceptional set is invisible to condensation points.**  If `A ⊆ ℂ` is
uncountable and `D` is countable, then `A` has a condensation point outside `D`: a point `x ∉ D`
every open neighbourhood of which meets `A` uncountably. -/
theorem ucj_exists_condensationPt {A D : Set ℂ} (hD : D.Countable) (hA : ¬ A.Countable) :
    ∃ x : ℂ, x ∉ D ∧ ∀ U : Set ℂ, IsOpen U → x ∈ U → ¬ (A ∩ U).Countable :=
  exists_condensationPt_of_secondCountable hD hA

end Work.EQ
