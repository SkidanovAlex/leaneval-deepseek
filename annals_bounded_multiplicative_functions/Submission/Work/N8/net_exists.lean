import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Given a symmetric "distance-like" function `d` with `d a a = 0` and any `r ≥ 0`,
every finite set `s` admits a maximal `r`-separated subset `Ω`: elements of `Ω` are
pairwise at distance `≥ r`, and every element of `s` is within distance `≤ r` of some
element of `Ω`. -/
theorem net_exists {Z : Type} [DecidableEq Z] (d : Z → Z → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hd_sym : ∀ a b, d a b = d b a) (hd_refl : ∀ a, d a a = 0) (s : Finset Z) :
    ∃ Ω : Finset Z, Ω ⊆ s ∧ (∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → r ≤ d z w) ∧
      ∀ z ∈ s, ∃ z₀ ∈ Ω, d z z₀ ≤ r := by
  classical
  -- The (finite) family of `r`-separated subsets of `s`.
  set F : Finset (Finset Z) :=
    s.powerset.filter (fun T => ∀ z ∈ T, ∀ w ∈ T, z ≠ w → r ≤ d z w) with hF
  have hne : F.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset s, by simp⟩
  -- Choose an element of `F` of maximal cardinality.
  obtain ⟨Ω, hΩF, hΩmax⟩ := Finset.exists_max_image F Finset.card hne
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hΩF
  obtain ⟨hΩsub, hΩsep⟩ := hΩF
  refine ⟨Ω, hΩsub, hΩsep, ?_⟩
  -- Covering property: otherwise `z` could be added to `Ω`, contradicting maximality.
  intro z hz
  by_contra hcon
  have hz_notin : z ∉ Ω := by
    intro hzin
    exact hcon ⟨z, hzin, by rw [hd_refl]; exact hr⟩
  have hTsub : insert z Ω ⊆ s := Finset.insert_subset hz hΩsub
  have hTsep : ∀ a ∈ insert z Ω, ∀ b ∈ insert z Ω, a ≠ b → r ≤ d a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with haz | haΩ
    · rcases Finset.mem_insert.mp hb with hbz | hbΩ
      · exact absurd (haz.trans hbz.symm) hab
      · rw [haz]
        exact le_of_lt (not_le.mp (fun h => hcon ⟨b, hbΩ, h⟩))
    · rcases Finset.mem_insert.mp hb with hbz | hbΩ
      · rw [hbz, hd_sym a z]
        exact le_of_lt (not_le.mp (fun h => hcon ⟨a, haΩ, h⟩))
      · exact hΩsep a haΩ b hbΩ hab
  have hTmemF : insert z Ω ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hTsub, hTsep⟩
  have hcard : (insert z Ω).card = Ω.card + 1 := Finset.card_insert_of_notMem hz_notin
  have hle := hΩmax (insert z Ω) hTmemF
  rw [hcard] at hle
  omega

end Work.N8
