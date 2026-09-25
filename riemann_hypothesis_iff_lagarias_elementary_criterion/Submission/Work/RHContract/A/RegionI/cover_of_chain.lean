import Mathlib

namespace Work.RHContract.A.RegionI

set_option linter.unusedVariables false in
theorem cover_of_chain {n : ℕ} (F : Fin (n + 1) → ℝ)
    (hmono : ∀ i : Fin n, F ⟨i.val + 1, by omega⟩ < F ⟨i.val, by omega⟩)
    (ε : ℝ) (hlo : F ⟨n, Nat.lt_succ_self n⟩ < ε) (hhi : ε ≤ F ⟨0, Nat.succ_pos n⟩) :
    ∃ i : Fin n, F ⟨i.val + 1, by omega⟩ < ε ∧ ε ≤ F ⟨i.val, by omega⟩ := by
  classical
  -- The set of indices at which `F` is still `≥ ε`.
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => ε ≤ F i)
  have h0S : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhi⟩
  have hSne : S.Nonempty := ⟨_, h0S⟩
  -- `i` is the maximal such index.
  obtain ⟨i, hiS, himax⟩ : ∃ i ∈ S, ∀ j ∈ S, j ≤ i :=
    ⟨S.max' hSne, Finset.max'_mem S hSne, fun j hj => Finset.le_max' S j hj⟩
  have hile : ε ≤ F i := (Finset.mem_filter.mp hiS).2
  -- `i` is not the last index, since `F n < ε`.
  have hival : i.val < n := by
    have hnotlast : i ≠ ⟨n, Nat.lt_succ_self n⟩ := by
      intro h
      have hmem : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ∈ S := h ▸ hiS
      exact absurd (Finset.mem_filter.mp hmem).2 (not_le.mpr hlo)
    have hle : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    have hne : i.val ≠ n := fun h => hnotlast (Fin.ext h)
    omega
  -- The successor index is not in `S`, by maximality of `i`.
  let i1 : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have hi1lt : F i1 < ε := by
    have hnotmem : i1 ∉ S := by
      intro hmem
      have hle := himax i1 hmem
      rw [Fin.le_def] at hle
      rw [show i1.val = i.val + 1 from rfl] at hle
      omega
    exact not_le.mp (fun hle => hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩))
  refine ⟨⟨i.val, hival⟩, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_of_eq (congrArg F (Fin.ext rfl))) hi1lt
  · exact le_trans hile (le_of_eq (congrArg F (Fin.ext rfl)))

end Work.RHContract.A.RegionI
