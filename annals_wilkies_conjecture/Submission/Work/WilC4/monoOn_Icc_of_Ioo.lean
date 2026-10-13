import Mathlib

namespace Work.WilC4

open Set Filter TopologicalSpace Function

theorem monoOn_Icc_of_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b))
    (hc : ContinuousOn f (Set.Icc a b)) :
    MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b) := by
  -- A one-sided monotone function on the open interval, continuous up to the endpoints,
  -- is monotone on the closed interval.  Both endpoints are cluster points of `Ioo a b`,
  -- and `MonotoneOn.insert_of_continuousWithinAt` lets us glue an endpoint back on.
  have key : ∀ g : ℝ → ℝ, MonotoneOn g (Ioo a b) → ContinuousOn g (Icc a b) →
      MonotoneOn g (Icc a b) := by
    intro g hg hgc
    have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
    have hb_mem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
    have ha_cl : ClusterPt a (𝓟 (Ioo a b)) := by
      rw [← mem_closure_iff_clusterPt, closure_Ioo hab.ne]; exact ha_mem
    have hb_cl : ClusterPt b (𝓟 (Ioo a b)) := by
      rw [← mem_closure_iff_clusterPt, closure_Ioo hab.ne]; exact hb_mem
    have ha_c : ContinuousWithinAt g (Ioo a b) a :=
      (hgc.continuousWithinAt ha_mem).mono Ioo_subset_Icc_self
    have hsub : insert a (Ioo a b) ⊆ Icc a b := by
      intro x hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨le_of_lt h1, le_of_lt h2⟩
    have hb_cl' : ClusterPt b (𝓟 (insert a (Ioo a b))) :=
      hb_cl.mono (Filter.principal_mono.mpr (subset_insert a _))
    have hb_c' : ContinuousWithinAt g (insert a (Ioo a b)) b :=
      (hgc.continuousWithinAt hb_mem).mono hsub
    have h1 : MonotoneOn g (insert a (Ioo a b)) :=
      hg.insert_of_continuousWithinAt ha_cl ha_c
    have h2 : MonotoneOn g (insert b (insert a (Ioo a b))) :=
      h1.insert_of_continuousWithinAt hb_cl' hb_c'
    have hIcc : insert b (insert a (Ioo a b)) = Icc a b := by
      ext x
      simp only [mem_insert_iff, mem_Ioo, mem_Icc]
      constructor
      · rintro (rfl | rfl | ⟨h1, h2⟩)
        · exact ⟨hab.le, le_rfl⟩
        · exact ⟨le_rfl, hab.le⟩
        · exact ⟨le_of_lt h1, le_of_lt h2⟩
      · rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h1 with hh | rfl
        · rcases lt_or_eq_of_le h2 with hh' | rfl
          · exact Or.inr (Or.inr ⟨hh, hh'⟩)
          · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    rwa [hIcc] at h2
  rcases h with h | h
  · left
    exact key f h hc
  · -- the antitone case is the monotone case for `-f`
    right
    have hg : MonotoneOn (fun x => -f x) (Ioo a b) := by
      intro x hx y hy hxy
      exact neg_le_neg (h hx hy hxy)
    have hgc : ContinuousOn (fun x => -f x) (Icc a b) := hc.neg
    intro x hx y hy hxy
    exact neg_le_neg_iff.mp (key (fun x => -f x) hg hgc hx hy hxy)

end Work.WilC4
