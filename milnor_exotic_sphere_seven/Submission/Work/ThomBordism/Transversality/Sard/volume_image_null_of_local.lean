import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local nullity implies global nullity

If every point `x` of a set `S` has an open neighbourhood `N` with `f '' (S ∩ N)` of Lebesgue
measure zero, then `f '' S` has measure zero.  The ambient space `ℝ^{n+1}` is second countable,
hence hereditarily Lindelöf, so the cover of `S` by these neighbourhoods has a countable subcover;
`f '' S` is then a countable union of null sets.
-/

open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

noncomputable section

theorem volume_image_null_of_local {n m : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (n+1)))}
    {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin m)}
    (h : ∀ x ∈ S, ∃ N : Set (EuclideanSpace ℝ (Fin (n+1))), IsOpen N ∧ x ∈ N ∧
          MeasureTheory.volume (f '' (S ∩ N)) = 0) :
    MeasureTheory.volume (f '' S) = 0 := by
  classical
  let N : EuclideanSpace ℝ (Fin (n+1)) → Set (EuclideanSpace ℝ (Fin (n+1))) :=
    fun x => if hx : x ∈ S then Classical.choose (h x hx) else univ
  have hNopen : ∀ x ∈ S, IsOpen (N x) := by
    intro x hx
    simp only [N, dif_pos hx]
    exact (Classical.choose_spec (h x hx)).1
  have hNx : ∀ x ∈ S, x ∈ N x := by
    intro x hx
    simp only [N, dif_pos hx]
    exact (Classical.choose_spec (h x hx)).2.1
  have hNnull : ∀ x ∈ S, MeasureTheory.volume (f '' (S ∩ N x)) = 0 := by
    intro x hx
    simp only [N, dif_pos hx]
    exact (Classical.choose_spec (h x hx)).2.2
  obtain ⟨t, htc, htS, hcov⟩ :=
    HereditarilyLindelofSpace.isLindelof S |>.elim_nhds_subcover N
      (fun x hx => (hNopen x hx).mem_nhds (hNx x hx))
  have hct : Countable ↥t := countable_coe_iff.mpr htc
  refine measure_mono_null ?_ (measure_iUnion_null (μ := MeasureTheory.volume)
    (fun i : ↥t => hNnull i.1 (htS i.1 i.2)))
  rintro y ⟨z, hzS, rfl⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hcov hzS)
  obtain ⟨hxt, hzx⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨⟨x, hxt⟩, ⟨z, ⟨hzS, hzx⟩, rfl⟩⟩

end

end Work.ThomBordism.Transversality.Sard
