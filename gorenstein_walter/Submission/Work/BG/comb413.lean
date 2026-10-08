/-
Work.BG.comb413 : the "COMB413" combinatorial lemma of Bender--Glauberman
(Bender, Glauberman, "Characters of finite groups with dihedral Sylow 2-subgroups",
J. Algebra 70 (1981), 200-215, p. 213, middle of the proof of Theorem 4.3).

Statement (see `Work.GW2.C23.Comb413Prop`): a finite family `v : J → ι → ℤ` of `{0,±1}`
vectors of support 4, pairwise orthogonal, all columns of size 0, 1 or 3, `F₂`-independent as
row vectors, with two rows sharing a coordinate, contains three rows `j₁ j₂ j₃` and a coordinate
`i₀` with support exactly `{j₁,j₂,j₃}`, and coordinates `p₁ p₂ p₃` whose support is exactly
`{j₁}`, `{j₂}`, `{j₃}` respectively.

The supporting definitions and the basic structure lemmas live in `Submission.Work.BG.C413Defs`;
the three local pieces of the case analysis are `c4_exists_alt`, `caseQ_false` and `caseP_false`.

Outline.  A row is *full* when all four of its columns are triple columns.  If `j` is full then
(`c4_exists_alt`) its four neighbours `a b c d` form a 4-cycle and the four edges have "second
columns" `u, y, z, x`.  If two adjacent second columns coincide (`u = x`, or after rotating the
4-cycle any of `u = y`, `y = z`, `z = x`) then (`caseQ_false`) the configuration is forced to be
the five-row configuration whose full rows meet every column evenly; otherwise all four vertices
`a, b, c, d` are full (`caseP_false`) and the configuration is forced to be the octahedron, whose
four middle rows meet every column evenly.  Both contradict the `F₂`-independence of the rows.
Hence no row is full, every row has at most three triple columns and therefore at least one
singleton column; taking the three rows of any triple column (which exists by the hypothesis that
two rows share a coordinate) gives the required configuration.
-/
import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.C413Defs
import Submission.Work.BG.c4_exists_alt
import Submission.Work.BG.caseQ_false
import Submission.Work.BG.caseP_false

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem comb413 : Work.GW2.C23.Comb413Prop := by
  intro ι J _ _ _ v h1 h2 h3 h4 h5
  classical
  -- **Step 1**: no row is full.
  have nofull : ∀ j : J, ¬ Full v j := by
    intro j hj
    obtain ⟨a, b, c, d, p, q, r, s, u, x, y, z, hD⟩ := c4_exists_alt v h1 h2 h3 h4 j hj
    by_cases hux : u = x
    · exact caseQ_false v h1 h2 h3 h4 hD hux
    · by_cases huy : u = y
      · exact caseQ_false v h1 h2 h3 h4 (C4Data.rotate1 v hD) huy.symm
      · by_cases hyz : y = z
        · exact caseQ_false v h1 h2 h3 h4 (C4Data.rotate2 v hD) hyz.symm
        · by_cases hzx : z = x
          · exact caseQ_false v h1 h2 h3 h4 (C4Data.rotate3 v hD) hzx.symm
          · exact caseP_false v h1 h2 h3 h4 hD hux huy hyz hzx
  -- **Step 2**: two rows share a coordinate, so we get a triple column.
  obtain ⟨j0, k0, i0, hjk, hj0i, hk0i⟩ := h5
  have hcol3 : (ColF v i0).card = 3 := by
    have hmemj : j0 ∈ ColF v i0 := (mem_ColF v j0 i0).mpr hj0i
    have hmemk : k0 ∈ ColF v i0 := (mem_ColF v k0 i0).mpr hk0i
    have h2le : 2 ≤ (ColF v i0).card := by
      have hsub : ({j0, k0} : Finset J) ⊆ ColF v i0 := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hmemj
        · rw [Finset.mem_singleton] at ht
          subst ht
          exact hmemk
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_pair hjk] at hle
    have hc := h3 i0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc | hc
    · rw [show (ColF v i0).card = 0 from hc] at h2le
      exact absurd h2le (by decide)
    · rw [show (ColF v i0).card = 1 from hc] at h2le
      exact absurd h2le (by decide)
    · exact show (ColF v i0).card = 3 from hc
  obtain ⟨j₁, j₂, j₃, hj₁₂, hj₁₃, hj₂₃, hEq⟩ := Finset.card_eq_three.mp hcol3
  refine ⟨j₁, j₂, j₃, hj₁₂, hj₁₃, hj₂₃, ⟨i0, ?_⟩, ?_⟩
  · intro j
    rw [← mem_ColF, hEq]
    simp
  · -- every row has a singleton column
    have hsing : ∀ j ∈ ({j₁, j₂, j₃} : Finset J),
        ∃ i : ι, v j i ≠ 0 ∧ (ColF v i).card = 1 := by
      intro j hj
      obtain ⟨i, hi, hc⟩ := exists_singleton_col v h1 h3 j (nofull j)
      exact ⟨i, (mem_Supp v j i).mp hi, hc⟩
    obtain ⟨p₁, hp₁, hp₁c⟩ := hsing j₁ (by simp)
    obtain ⟨p₂, hp₂, hp₂c⟩ := hsing j₂ (by simp)
    obtain ⟨p₃, hp₃, hp₃c⟩ := hsing j₃ (by simp)
    refine ⟨p₁, p₂, p₃, ?_, ?_, ?_⟩ <;> intro j
    · rw [← mem_ColF]
      have hmem : j₁ ∈ ColF v p₁ := by rw [mem_ColF]; exact hp₁
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₁c
      have hw' : ColF v p₁ = {j₁} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]
    · rw [← mem_ColF]
      have hmem : j₂ ∈ ColF v p₂ := by rw [mem_ColF]; exact hp₂
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₂c
      have hw' : ColF v p₂ = {j₂} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]
    · rw [← mem_ColF]
      have hmem : j₃ ∈ ColF v p₃ := by rw [mem_ColF]; exact hp₃
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hp₃c
      have hw' : ColF v p₃ = {j₃} := by
        rw [hw] at hmem
        rw [Finset.mem_singleton] at hmem
        rw [hw, hmem]
      rw [hw', Finset.mem_singleton]

end Work.BG
