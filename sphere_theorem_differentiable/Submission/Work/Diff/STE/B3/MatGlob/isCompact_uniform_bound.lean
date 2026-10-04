import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.MatGlob

/-- A family `f : ι → X → ℝ` which is *locally* uniformly bounded (in `ι`) at every point of a
compact set `Kc` is *globally* uniformly bounded on `Kc`: choose for each `x ∈ Kc` an open
neighbourhood on which a bound holds (and make the bound nonnegative), extract a finite subcover,
and take the sum of the corresponding bounds. -/
theorem isCompact_uniform_bound
    {X : Type*} [TopologicalSpace X] {ι : Type*} {Kc : Set X} (hK : IsCompact Kc)
    {f : ι → X → ℝ}
    (hloc : ∀ x ∈ Kc, ∃ C : ℝ, ∃ u ∈ nhds x, ∀ y ∈ u, ∀ i : ι, |f i y| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ∀ x ∈ Kc, |f i x| ≤ C := by
  classical
  -- For each point of `Kc` choose an open neighbourhood carrying a nonnegative uniform bound.
  have key : ∀ x : Kc, ∃ p : ℝ × Set X, 0 ≤ p.1 ∧ IsOpen p.2 ∧ (x : X) ∈ p.2 ∧
      ∀ y ∈ p.2, ∀ i : ι, |f i y| ≤ p.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨C, u, hu, hb⟩ := hloc x hx
    obtain ⟨v, hvsub, hvopen, hxv⟩ := mem_nhds_iff.mp hu
    exact ⟨(max C 0, v), le_max_right _ _, hvopen, hxv,
      fun y hy i => (hb y (hvsub hy) i).trans (le_max_left _ _)⟩
  choose p hp using key
  -- The chosen open sets cover the compact set, so finitely many of them do.
  have hcover : Kc ⊆ ⋃ x : Kc, (p x).2 :=
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hp ⟨y, hy⟩).2.2.1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : Kc => (p x).2) (fun x => (hp x).2.1) hcover
  refine ⟨Finset.sum t (fun x => (p x).1), Finset.sum_nonneg fun x _ => (hp x).1, ?_⟩
  intro i y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
  exact ((hp x).2.2.2 y hyx i).trans (Finset.single_le_sum (fun z _ => (hp z).1) hxt)

end Work.Diff.STE.B3.MatGlob
