import Mathlib
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false

namespace Work.WilE7

/-- Combinatorial covering lemma: if `L : Fin (m+1) → ℝ` is strictly increasing and
`t` lies between the first and the last level, then `t` is either one of the levels
(the graph case) or lies strictly between two consecutive levels (the band case). -/
theorem levels_cover {m : ℕ} {L : Fin (m+1) → ℝ} (hL : StrictMono L) {t : ℝ}
    (h0 : L 0 ≤ t) (h1 : t ≤ L (Fin.last m)) :
    (∃ i : Fin (m+1), L i = t) ∨
      (∃ i : Fin m, L (Fin.castSucc i) < t ∧ t < L i.succ) := by
  classical
  -- the largest index whose level is `≤ t`
  let K : Finset (Fin (m+1)) := Finset.univ.filter (fun i => L i ≤ t)
  have hKne : K.Nonempty := ⟨0, by simp [K, h0]⟩
  have hiK : K.max' hKne ∈ K := K.max'_mem hKne
  have hLi : L (K.max' hKne) ≤ t := by simpa [K] using hiK
  have hmax : ∀ j, L j ≤ t → j ≤ K.max' hKne := by
    intro j hj
    have hmem : j ∈ (K : Set (Fin (m+1))) := by simpa [K] using hj
    exact (Finset.isGreatest_max' K hKne).2 hmem
  rcases Fin.eq_castSucc_or_eq_last (K.max' hKne) with ⟨i', hi'⟩ | hlast
  · rw [hi'] at hLi hmax
    rcases eq_or_lt_of_le hLi with heq | hlt
    · exact Or.inl ⟨Fin.castSucc i', heq⟩
    · refine Or.inr ⟨i', hlt, ?_⟩
      have hnot : ¬ (L i'.succ ≤ t) := by
        intro hcon
        have hle := hmax i'.succ hcon
        have hlt' : (Fin.castSucc i' : Fin (m+1)) < i'.succ := by simp
        exact absurd hle (not_le.mpr hlt')
      exact lt_of_not_ge hnot
  · rw [hlast] at hLi
    exact Or.inl ⟨Fin.last m, le_antisymm hLi h1⟩

theorem decomp_cover {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hx : x ∈ C) (hmono : StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ j, |s j x| < 1) {t : ℝ} (ht : |t| ≤ 1) :
    Fin.snoc x t ∈ ⋃₀ (cfs C s : Set (Set (Fin (n+1) → ℝ))) := by
  have hL : StrictMono (lvl s x) := strictMono_lvl hmono hbnd
  have h0 : lvl s x 0 ≤ t := by simpa using (abs_le.mp ht).1
  have h1 : t ≤ lvl s x (Fin.last (q+1)) := by simpa using (abs_le.mp ht).2
  rcases levels_cover (m := q+1) (L := lvl s x) hL h0 h1 with ⟨i, hi⟩ | ⟨i, hlt1, hlt2⟩
  · -- `t` is one of the levels: `Fin.snoc x t` lies on the corresponding graph
    refine Set.mem_sUnion.mpr
      ⟨gr C (fun y => lvl s y i), mem_cfs.mpr (Or.inl ⟨i, rfl⟩), ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simpa using hi.symm
  · -- `t` lies strictly between two consecutive levels: the band case
    refine Set.mem_sUnion.mpr
      ⟨bd C (fun y => lvl s y (Fin.castSucc i)) (fun y => lvl s y i.succ),
        mem_cfs.mpr (Or.inr ⟨i, rfl⟩), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hx
    · simpa using hlt1
    · simpa using hlt2

end Work.WilE7
