import Mathlib
import Submission.Work.BG.C413Defs

namespace Work.BG

/-- At the vertex `b` of the 4-cycle: if the two "second columns" `u` (of the edge `ab`) and `y` (of the edge `bc`) are different, then the support of `b` is exactly `{p,q,u,y}`. -/
theorem caseP_supp_b {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (huy : u ≠ y) :
    Work.BG.Supp v b = ({p,q,u,y} : Finset ι) := by
  -- The four vertices of the 4-cycle are distinct.
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  -- `p, q, r, s` are distinct.
  have hpqrs : ({p,q,r,s} : Finset ι).card = 4 := by rw [← hD.hS]; exact (h1 j).1
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := ne_of_card_four hpqrs
  -- Membership of `p, u` (edge `ab`) and `q, y` (edge `bc`).
  have hua : u ∈ Supp v a := by
    have h : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    exact (Finset.mem_inter.mp h).1
  have hpb : p ∈ Supp v b := by
    have h : p ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    exact (Finset.mem_inter.mp h).2
  have hub : u ∈ Supp v b := by
    have h : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    exact (Finset.mem_inter.mp h).2
  have hqb : q ∈ Supp v b := by
    have h : q ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).1
  have hyb : y ∈ Supp v b := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).1
  have hyc : y ∈ Supp v c := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).2
  -- `u ≠ q` : else `a` would lie in `ColF v q = {j,b,c}`.
  have hqu : u ≠ q := by
    intro h
    have hqa : q ∈ Supp v a := h ▸ hua
    have hmem : a ∈ ColF v q := (mem_ColF v a q).mpr ((mem_Supp v a q).mp hqa)
    rw [hD.hq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hja h'.symm
    · exact hab h'
    · exact hac h'
  -- `p ≠ y` : else `c` would lie in `ColF v p = {j,a,b}`.
  have hpy : p ≠ y := by
    intro h
    have hpc : p ∈ Supp v c := h ▸ hyc
    have hmem : c ∈ ColF v p := (mem_ColF v c p).mpr ((mem_Supp v c p).mp hpc)
    rw [hD.hp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjc h'.symm
    · exact hac h'.symm
    · exact hbc h'.symm
  have hsub : ({p,q,u,y} : Finset ι) ⊆ Supp v b := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hpb
    · exact hqb
    · exact hub
    · exact hyb
  have hcard : ({p,q,u,y} : Finset ι).card = 4 := by
    have hnp : p ∉ ({q,u,y} : Finset ι) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpq, fun h => hD.hup h.symm, hpy⟩
    have hnq : q ∉ ({u,y} : Finset ι) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hqu h.symm, fun h => hD.hyq h.symm⟩
    have hnu : u ∉ ({y} : Finset ι) := by simpa using huy
    rw [Finset.card_insert_of_notMem hnp, Finset.card_insert_of_notMem hnq,
      Finset.card_insert_of_notMem hnu]
    simp
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard]
  exact le_of_eq (h1 b).1

end Work.BG
