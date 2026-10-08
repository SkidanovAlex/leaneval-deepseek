import Mathlib
import Submission.Work.BG.CaseQAux

namespace Work.BG

/-- In the `u = x` configuration of `Work.BG.caseQ_false` (a `Work.BG.C4Data` configuration with
`u = x`), the support of the row `b` is exactly `{p,q,u,y}`.

`p ∈ Supp v b` and `u ∈ Supp v b` come from `hD.hAB : Supp v a ∩ Supp v b = {p,u}`; `q ∈ Supp v b`
and `y ∈ Supp v b` come from `hD.hBC : Supp v b ∩ Supp v c = {q,y}`.  Since
`(Supp v b).card = 4` (from `h1`), it suffices that the four elements are pairwise distinct:
`p ≠ q` (`Work.BG.C4Data.pqrs_distinct`), `p ≠ u` (`hD.hup`), `q ≠ y` (`hD.hyq`), and the three
less immediate ones, all of the shape "an element of a known column support equals an element of
another known column support":

* `p ≠ y`: otherwise `ColF v y = ColF v p = {j,a,b}` (using `hD.hp`) would contain `c`, because
  `y ∈ Supp v c`;
* `q ≠ u`: `u ∈ Supp v a`, so `u = q` gives `a ∈ ColF v q = {j,b,c}` (using `hD.hq`);
* `u ≠ y`: `y ∈ Supp v c`, so `u = y` gives `c ∈ ColF v u`; here
  `u = x ∈ Supp v d ∩ Supp v a = {s,x}` together with `hD.hAB` gives `a,b,d ∈ ColF v u`, and
  `h3 u` then forces `ColF v u = {a,b,d}`.

Each of the three contradictions is with `Work.BG.C4Data.jabcd_distinct`.  Finish with
`Work.BG.supp_eq_of_four` from `Submission/Work/BG/CaseQAux.lean`. -/
theorem caseQ_supp_b {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z) (hu : u = x) :
    Work.BG.Supp v b = {p, q, u, y} := by
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ :=
    ne_of_card_four (C4Data.pqrs_card (v := v) h1 hD)
  -- memberships in `Supp v b`, from the two edge equations
  have hpb : p ∈ Supp v b :=
    (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).2
  have hub : u ∈ Supp v b :=
    (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).2
  have hqb : q ∈ Supp v b :=
    (Finset.mem_inter.mp (by rw [hD.hBC]; simp)).1
  have hyb : y ∈ Supp v b :=
    (Finset.mem_inter.mp (by rw [hD.hBC]; simp)).1
  -- the same elements in the neighbouring rows
  have hua : u ∈ Supp v a :=
    (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).1
  have hyc : y ∈ Supp v c :=
    (Finset.mem_inter.mp (by rw [hD.hBC]; simp)).2
  have hxd : x ∈ Supp v d :=
    (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).1
  have hud : u ∈ Supp v d := by rw [hu]; exact hxd
  -- pairwise distinctness of `p, q, u, y`
  have hpu : p ≠ u := fun h => hD.hup h.symm
  have hqy : q ≠ y := fun h => hD.hyq h.symm
  have hpy : p ≠ y := by
    intro h
    have hpc : p ∈ Supp v c := h ▸ hyc
    have hmem : c ∈ ColF v p := (mem_ColF_supp v c p).mpr hpc
    rw [hD.hp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjc h'.symm
    · exact hac h'.symm
    · exact hbc h'.symm
  have hqu : q ≠ u := by
    intro h
    have hqa : q ∈ Supp v a := h ▸ hua
    have hmem : a ∈ ColF v q := (mem_ColF_supp v a q).mpr hqa
    rw [hD.hq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hja h'.symm
    · exact hab h'
    · exact hac h'
  have huy : u ≠ y := by
    intro h
    have hcu : c ∈ ColF v u := (mem_ColF_supp v c u).mpr (by rw [h]; exact hyc)
    have hau : a ∈ ColF v u := (mem_ColF_supp v a u).mpr hua
    have hbu : b ∈ ColF v u := (mem_ColF_supp v b u).mpr hub
    have hdu : d ∈ ColF v u := (mem_ColF_supp v d u).mpr hud
    have heq : ColF v u = {a, b, d} := colF_eq_of_three v (h3 u) hau hbu hdu hab had hbd
    rw [heq] at hcu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcu
    rcases hcu with h' | h' | h'
    · exact hac h'.symm
    · exact hbc h'.symm
    · exact hcd h'
  exact supp_eq_of_four v (h1 b).1 hpb hqb hub hyb hpq hpu hpy hqu hqy huy

end Work.BG
