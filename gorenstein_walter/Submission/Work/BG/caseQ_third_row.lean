import Mathlib
import Submission.Work.BG.CaseQAux
import Submission.Work.BG.caseP_supp_c

namespace Work.BG

/-- In the `u = x` configuration of `Work.BG.caseQ_false` with additionally `y ≠ z`, the column
`y` is a triple column whose third row `g` lies outside `{j,a,b,c,d}`.

`y ∈ Supp v b ∩ Supp v c = {q,y}` (`hD.hBC`) gives `b, c ∈ ColF v y`, and `h3 y` forces
`(ColF v y).card = 3`, so (`Work.BG.colF_eq_insert_third`, `Submission/Work/BG/CaseQAux.lean`)
`ColF v y = {b,c,g}` with `g ∉ {b,c}`.  Then `g ∉ {j,a,d}`:

* `g ≠ j`: `g = j` gives `y ∈ Supp v j = {p,q,r,s}` (`hD.hS`).  Now `y ≠ q` (`hD.hyq`),
  `y ≠ p` (else `ColF v p = {j,a,b}` gained by `c ∈ ColF v y` would contain `c`),
  `y ≠ r` (else `ColF v r = {j,c,d}` would contain `b ∈ ColF v y`) and
  `y ≠ s` (else `ColF v s = {j,d,a}` would contain `b`);
* `g ≠ a`: `g = a` gives `y ∈ Supp v a ∩ Supp v b = {p,u}` (`hD.hAB`), so `y = p` (excluded) or
  `y = u`, and `y = u` gives `c ∈ ColF v u = {a,b,d}`, where `u = x ∈ Supp v d ∩ Supp v a = {s,x}`
  together with `hD.hAB` gives `a,b,d ∈ ColF v u` and `h3 u` pins the column down — again a
  contradiction with `Work.BG.C4Data.jabcd_distinct`;
* `g ≠ d`: `g = d` gives `y ∈ Supp v c ∩ Supp v d = {r,z}` (`hD.hCD`), so `y = r` (excluded) or
  `y = z`, contradicting the hypothesis `y ≠ z`. -/
theorem caseQ_third_row {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z) (hu : u = x) (hyz : y ≠ z) :
    ∃ g : J, Work.BG.ColF v y = {b, c, g} ∧ g ∉ ({j, a, b, c, d} : Finset J) := by
  -- the five rows of the configuration are pairwise distinct
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  have hcj : c ≠ j := fun h => hjc h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have hbj : b ≠ j := fun h => hjb h.symm
  have hba : b ≠ a := fun h => hab h.symm
  -- `y` lies in the supports of `b` and of `c`
  have hyb : y ∈ Supp v b := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).1
  have hyc : y ∈ Supp v c := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).2
  have hbcol : b ∈ ColF v y := (mem_ColF_supp v b y).mpr hyb
  have hccol : c ∈ ColF v y := (mem_ColF_supp v c y).mpr hyc
  -- hence the column `y` has three rows
  have hcard3 : (ColF v y).card = 3 := by
    have h3y := h3 y
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3y
    have hsub : ({b, c} : Finset J) ⊆ ColF v y := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have h2le : ({b, c} : Finset J).card ≤ (ColF v y).card := Finset.card_le_card hsub
    rw [Finset.card_pair hbc] at h2le
    omega
  obtain ⟨g, hgeq, hgnbc⟩ := colF_eq_insert_third v hbcol hccol hbc hcard3
  have hgmem : g ∈ ColF v y := by rw [hgeq]; simp
  have hgb : g ≠ b := fun h => hgnbc (by simp [h])
  have hgc : g ≠ c := fun h => hgnbc (by simp [h])
  -- `y` is not one of the columns `p`, `r`, `s`
  have hyp : y ≠ p :=
    ne_colF_of_col_eq (v := v) (hcol := hD.hp) (ht := by simp [hcj, hca, hcb]) (hi' := hyc)
  have hyr : y ≠ r :=
    ne_colF_of_col_eq (v := v) (hcol := hD.hr) (ht := by simp [hbj, hbc, hbd]) (hi' := hyb)
  have hys : y ≠ s :=
    ne_colF_of_col_eq (v := v) (hcol := hD.hs) (ht := by simp [hbj, hbd, hba]) (hi' := hyb)
  -- `y ≠ u`, since `y = u` would put `c` in the column `{a,b,d}` of `u`
  have huy : y ≠ u := by
    intro hyu
    have hcu : c ∈ ColF v u := by rw [← hyu]; exact hccol
    have hux : u ∈ Supp v d ∩ Supp v a := by rw [hD.hDA]; simp [hu]
    have huu : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    have hua : u ∈ Supp v a := (Finset.mem_inter.mp hux).2
    have hud : u ∈ Supp v d := (Finset.mem_inter.mp hux).1
    have hub : u ∈ Supp v b := (Finset.mem_inter.mp huu).2
    have hcolu : ColF v u = {a, b, d} :=
      colF_eq_of_three v (h3 u) ((mem_ColF_supp v a u).mpr hua)
        ((mem_ColF_supp v b u).mpr hub) ((mem_ColF_supp v d u).mpr hud) hab had hbd
    rw [hcolu] at hcu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcu
    rcases hcu with h | h | h
    · exact hac h.symm
    · exact hbc h.symm
    · exact hcd h
  -- the three exclusions
  have hgj_ne : g ≠ j := by
    intro hgj
    have hyj : y ∈ Supp v j := by
      have : j ∈ ColF v y := by rw [← hgj]; exact hgmem
      exact (mem_ColF_supp v j y).mp this
    have hyS : y ∈ ({p, q, r, s} : Finset ι) := by rw [← hD.hS]; exact hyj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with h | h | h | h
    · exact hyp h
    · exact hD.hyq h
    · exact hyr h
    · exact hys h
  have hga_ne : g ≠ a := by
    intro hga
    have hya : y ∈ Supp v a := by
      have : a ∈ ColF v y := by rw [← hga]; exact hgmem
      exact (mem_ColF_supp v a y).mp this
    have hyAB : y ∈ Supp v a ∩ Supp v b := Finset.mem_inter.mpr ⟨hya, hyb⟩
    have hyS : y ∈ ({p, u} : Finset ι) := by rw [← hD.hAB]; exact hyAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with h | h
    · exact hyp h
    · exact huy h
  have hgd_ne : g ≠ d := by
    intro hgd
    have hyd : y ∈ Supp v d := by
      have : d ∈ ColF v y := by rw [← hgd]; exact hgmem
      exact (mem_ColF_supp v d y).mp this
    have hyCD : y ∈ Supp v c ∩ Supp v d := Finset.mem_inter.mpr ⟨hyc, hyd⟩
    have hyS : y ∈ ({r, z} : Finset ι) := by rw [← hD.hCD]; exact hyCD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
    rcases hyS with h | h
    · exact hyr h
    · exact hyz h
  refine ⟨g, hgeq, ?_⟩
  intro hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h
  · exact hgj_ne h
  · exact hga_ne h
  · exact hgb h
  · exact hgc h
  · exact hgd_ne h

end Work.BG
