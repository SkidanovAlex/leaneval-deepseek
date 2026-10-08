import Mathlib
import Submission.Work.BG.C413Defs
import Submission.Work.BG.CaseQAux

namespace Work.BG

/-- If a column has support exactly the triple `{x, y, z}` and `t` is a row outside that triple,
then every column occurring in the support of the row `t` is different from that column.

Indeed, if `i' = i` then `t ∈ ColF v i' = ColF v i = {x, y, z}`, contradicting `t ∉ {x, y, z}`. -/
theorem ne_colF_of_col_eq {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    {v : J → ι → ℤ} {i i' : ι} {x y z t : J}
    (hcol : ColF v i = {x, y, z}) (ht : t ∉ ({x, y, z} : Finset J)) (hi' : i' ∈ Supp v t) :
    i' ≠ i := by
  intro h
  have hmem : t ∈ ColF v i' := (mem_ColF_supp v t i').mpr hi'
  rw [h, hcol] at hmem
  exact ht hmem

/-- At the vertex `c` of the 4-cycle: if the two "second columns" `y` (of the edge `bc`) and `z` (of the edge `cd`) are different, then the support of `c` is exactly `{q,r,y,z}`. -/
theorem caseP_supp_c {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (hyz : y ≠ z) :
    Work.BG.Supp v c = ({q,r,y,z} : Finset ι) := by
  -- the five rows `j, a, b, c, d` of the configuration are pairwise distinct
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  -- the four expected columns of `c` do lie in its support
  have hqc : q ∈ Supp v c := by
    have h : q ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).2
  have hyc : y ∈ Supp v c := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).2
  have hrc : r ∈ Supp v c := by
    have h : r ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
    exact (Finset.mem_inter.mp h).1
  have hzc : z ∈ Supp v c := by
    have h : z ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
    exact (Finset.mem_inter.mp h).1
  -- ... and they are pairwise distinct
  have hdj : d ≠ j := fun h => hjd h.symm
  have hdb : d ≠ b := fun h => hbd h.symm
  have hdc : d ≠ c := fun h => hcd h.symm
  have hbj : b ≠ j := fun h => hjb h.symm
  -- `q` is a column of `b` and of `c`, so `ColF v q = {j,b,c}` does not contain `d`; and both the
  -- cycle column `r` and the second column `z` of the edge `cd` are columns of `d`
  have hqr : q ≠ r := by
    have hrd : r ∈ Supp v d := by
      have h : r ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
      exact (Finset.mem_inter.mp h).2
    exact (ne_colF_of_col_eq (v := v) hD.hq (by simp [hdj, hdb, hdc]) hrd).symm
  have hqz : q ≠ z := by
    have hzd : z ∈ Supp v d := by
      have h : z ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
      exact (Finset.mem_inter.mp h).2
    exact (ne_colF_of_col_eq (v := v) hD.hq (by simp [hdj, hdb, hdc]) hzd).symm
  -- `r` is a column of `d` and of `j`, so `ColF v r = {j,c,d}` does not contain `b`, while `y`
  -- is a column of `b`
  have hry : r ≠ y := by
    have hyb : y ∈ Supp v b := by
      have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
      exact (Finset.mem_inter.mp h).1
    exact (ne_colF_of_col_eq (v := v) hD.hr (by simp [hbj, hbc, hbd]) hyb).symm
  -- four distinct columns of the support of `c`, whose support has exactly four elements
  exact supp_eq_of_four v (h1 c).1 hqc hrc hyc hzc hqr hD.hyq.symm hqz hry hD.hzr.symm hyz

end Work.BG
