import Mathlib
import Submission.Work.BG.C413Defs

namespace Work.BG

/-- An explicit four-element set whose elements are pairwise distinct has cardinality four. -/
private theorem caseP_supp_d_card_four {α : Type*} [DecidableEq α] {r s z x : α}
    (hrs : r ≠ s) (hrz : r ≠ z) (hrx : r ≠ x) (hsz : s ≠ z) (hsx : s ≠ x) (hzx : z ≠ x) :
    ({r, s, z, x} : Finset α).card = 4 :=
  Finset.card_eq_four.mpr ⟨r, s, z, x, hrs, hrz, hrx, hsz, hsx, hzx, rfl⟩

/-- At the vertex `d` of the 4-cycle: if the two "second columns" `z` (of the edge `cd`) and `x` (of the edge `da`) are different, then the support of `d` is exactly `{r,s,z,x}`. -/
theorem caseP_supp_d {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (hzx : z ≠ x) :
    Work.BG.Supp v d = ({r,s,z,x} : Finset ι) := by
  -- distinctness of the five relevant vertices of the 4-cycle
  obtain ⟨hja, -, hjc, hjd, -, hac, had, -, -, hcd⟩ :=
    Work.BG.C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  -- distinctness of the four columns attached to `j`
  obtain ⟨-, -, -, -, -, hrs⟩ := Work.BG.C4Data.pqrs_distinct (v := v) h1 hD
  -- `r` and `s` are columns of `d` (they are columns of `j` of size `3` containing `d`)
  have hrd : r ∈ Work.BG.Supp v d := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hD.hr]; simp
  have hsd : s ∈ Work.BG.Supp v d := by
    rw [Work.BG.mem_Supp, ← Work.BG.mem_ColF, hD.hs]; simp
  -- `z` and `x` are columns shared by `d` with `c` resp. `a`
  have hzd : z ∈ Work.BG.Supp v d :=
    (Finset.mem_inter.mp (by rw [hD.hCD]; simp)).2
  have hxd : x ∈ Work.BG.Supp v d :=
    (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).1
  have hxa : x ∈ Work.BG.Supp v a :=
    (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).2
  have hzc : z ∈ Work.BG.Supp v c :=
    (Finset.mem_inter.mp (by rw [hD.hCD]; simp)).1
  -- the two columns of `d` other than `r` and `s` are distinct from them: otherwise the
  -- column in question would contain the four distinct rows `j, c, d, a`
  have hrx : r ≠ x := by
    intro h
    have ha : a ∈ Work.BG.ColF v r := by
      rw [h, Work.BG.mem_ColF]; rw [Work.BG.mem_Supp] at hxa; exact hxa
    rw [hD.hr] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h' | h' | h'
    · exact hja h'.symm
    · exact hac h'
    · exact had h'
  have hsz : s ≠ z := by
    intro h
    have hc : c ∈ Work.BG.ColF v s := by
      rw [h, Work.BG.mem_ColF]; rw [Work.BG.mem_Supp] at hzc; exact hzc
    rw [hD.hs] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h' | h' | h'
    · exact hjc h'.symm
    · exact hcd h'
    · exact hac h'.symm
  have hsub : ({r,s,z,x} : Finset ι) ⊆ Work.BG.Supp v d := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hrd
    · exact hsd
    · exact hzd
    · exact hxd
  have hcard : ({r,s,z,x} : Finset ι).card = 4 :=
    caseP_supp_d_card_four hrs hD.hzr.symm hrx hsz hD.hxs.symm hzx
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, (h1 d).1])).symm

end Work.BG
