import Mathlib

namespace Work.PL.Generic

/-- Combinatorial step for `Work.PL.Generic.affineSpan_eq_top_of_forall_avoid`.  If `T` is a finite
set of indices contained in `fz ∪ l.toFinset` (`l` a duplicate-free list), `u = l[j]` is not in `T`,
and `T` is *not* contained in the earlier prefix `fz ∪ l.take j`, then there is a later index
`m > j` with `l[m] ∈ T` such that removing `l[m]` from `T` and adding `u` keeps us inside the earlier
prefix `fz ∪ l.take m`: `(T.erase (l[m])) ∪ {u} ⊆ fz ∪ (l.take m).toFinset`. -/
theorem exists_index_step {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (l : List ι) (hl' : l.Nodup)
    {u : ι} {T : Finset ι} (hT : T ⊆ fz ∪ l.toFinset) (huT : u ∉ T)
    {j : ℕ} (hj : j < l.length) (hlj : l[j] = u)
    (hcase : ¬ T ⊆ fz ∪ (l.take j).toFinset) :
    ∃ (m : ℕ) (hmj : j < m) (hml : m < l.length), l[m] ∈ T ∧
      (T.erase (l[m]'hml) ∪ {u} ⊆ fz ∪ (l.take m).toFinset) := by
  classical
  -- membership in an initial segment of `l`
  have hmem_take : ∀ {m i : ℕ} (him : i < m) (hil : i < l.length),
      l[i]'hil ∈ (l.take m).toFinset := by
    intro m i him hil
    rw [List.mem_toFinset, List.getElem_take' hil him]
    exact List.getElem_mem _
  -- a witness in `T` lying beyond the prefix `l.take j`
  obtain ⟨t, htT, htnot⟩ := Finset.not_subset.mp hcase
  rw [Finset.mem_union, not_or] at htnot
  obtain ⟨htfz, htnp⟩ := htnot
  have htlin : t ∈ l.toFinset := by
    rcases Finset.mem_union.mp (hT htT) with h | h
    · exact absurd h htfz
    · exact h
  rw [List.mem_toFinset] at htlin
  obtain ⟨k, hkl, hk_eq⟩ := List.getElem_of_mem htlin
  -- the index of `t` is strictly beyond `j`
  have hkj : j < k := by
    rcases lt_trichotomy k j with h | h | h
    · exact absurd (by rw [← hk_eq]; exact hmem_take h hkl) htnp
    · exfalso
      have hgetD : l.getD k u = l.getD j u := by rw [h]
      have hut : u = t := by
        rw [← hlj, ← List.getD_eq_getElem l u hj, ← hgetD, List.getD_eq_getElem l u hkl, hk_eq]
      exact huT (by rw [hut]; exact htT)
    · exact h
  -- the largest index `m` with `l[m] ∈ T`
  let S : Finset ℕ := (Finset.range l.length).filter (fun k => l.getD k u ∈ T)
  have hkS : k ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkl, by rw [List.getD_eq_getElem l u hkl, hk_eq]; exact htT⟩
  let m : ℕ := S.max' ⟨k, hkS⟩
  have hmS : m ∈ S := S.max'_mem ⟨k, hkS⟩
  have hm_range : m < l.length := Finset.mem_range.mp (Finset.mem_filter.mp hmS).1
  have hm_getD : l.getD m u ∈ T := (Finset.mem_filter.mp hmS).2
  have hlmT : l[m] ∈ T := by
    rw [← List.getD_eq_getElem l u hm_range]
    exact hm_getD
  have hmj : j < m := lt_of_lt_of_le hkj (Finset.le_max' S k hkS)
  refine ⟨m, hmj, hm_range, hlmT, ?_⟩
  intro x hx
  rw [Finset.mem_union] at hx ⊢
  rcases hx with hx | hx
  · -- `x ∈ T.erase (l[m])`
    rw [Finset.mem_erase] at hx
    obtain ⟨hxne, hxT⟩ := hx
    rcases Finset.mem_union.mp (hT hxT) with hxfz | hxl
    · exact Or.inl hxfz
    · right
      rw [List.mem_toFinset] at hxl
      obtain ⟨k', hkl', hk'eq⟩ := List.getElem_of_mem hxl
      have hk'S : k' ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨hkl', by rw [List.getD_eq_getElem l u hkl', hk'eq]; exact hxT⟩
      have hk'm : k' ≤ m := Finset.le_max' S k' hk'S
      have hk'lt : k' < m := by
        rcases lt_or_eq_of_le hk'm with h | h
        · exact h
        · exfalso
          have hxg : l.getD k' u = x := by rw [List.getD_eq_getElem l u hkl', hk'eq]
          exact hxne (by rw [← hxg, h, List.getD_eq_getElem l u hm_range])
      rw [← hk'eq]
      exact hmem_take hk'lt hkl'
  · -- `x = u`
    rw [Finset.mem_singleton] at hx
    right
    rw [hx, ← hlj]
    exact hmem_take hmj hj

end Work.PL.Generic
