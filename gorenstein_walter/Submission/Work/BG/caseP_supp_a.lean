import Mathlib
import Submission.Work.BG.CaseQAux

namespace Work.BG

/-- At the vertex `a` of the 4-cycle: if the two "second columns" `u` (of the edge `ab`) and `x` (of the edge `da`) are different, then the support of `a` is exactly `{p,s,u,x}`.

`p, u ∈ Supp v a` come from `hD.hAB : Supp v a ∩ Supp v b = {p,u}` and `s, x ∈ Supp v a` from
`hD.hDA : Supp v d ∩ Supp v a = {s,x}`.  Since `(Supp v a).card = 4` (`h1`), it suffices that the
four elements are pairwise distinct: `p ≠ s` (`Work.BG.C4Data.pqrs_distinct`), `p ≠ u`
(`hD.hup`), `s ≠ x` (`hD.hxs`), `u ≠ x` (the hypothesis), and the two less immediate ones, both
of the shape "an element of the known column support of one of the four cycle edges equals an
element of another such support":

* `p ≠ x`: otherwise `p ∈ Supp v d` (as `x` is), so `d ∈ ColF v p = {j,a,b}` (`hD.hp`), against
  `Work.BG.C4Data.jabcd_distinct`;
* `s ≠ u`: `u ∈ Supp v b`, so `u = s` would give `b ∈ ColF v u = ColF v s = {j,d,a}` (`hD.hs`),
  again against `Work.BG.C4Data.jabcd_distinct`.

Finish with `Work.BG.supp_eq_of_four` from `Submission/Work/BG/CaseQAux.lean`. -/
theorem caseP_supp_a {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (hux : u ≠ x) :
    Work.BG.Supp v a = ({p,s,u,x} : Finset ι) := by
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ :=
    ne_of_card_four (C4Data.pqrs_card (v := v) h1 hD)
  -- memberships in `Supp v a`, from the two edge equations through `a`
  have hpa : p ∈ Supp v a := (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).1
  have hua : u ∈ Supp v a := (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).1
  have hsa : s ∈ Supp v a := (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).2
  have hxa : x ∈ Supp v a := (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).2
  -- the same elements in the neighbouring rows
  have hub : u ∈ Supp v b := (Finset.mem_inter.mp (by rw [hD.hAB]; simp)).2
  have hxd : x ∈ Supp v d := (Finset.mem_inter.mp (by rw [hD.hDA]; simp)).1
  -- pairwise distinctness of `p, s, u, x`
  have hpu : p ≠ u := fun h => hD.hup h.symm
  have hsx : s ≠ x := fun h => hD.hxs h.symm
  have hpx : p ≠ x := by
    intro h
    have hpd : p ∈ Supp v d := by rw [h]; exact hxd
    have hmem : d ∈ ColF v p := (mem_ColF_supp v d p).mpr hpd
    rw [hD.hp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjd h'.symm
    · exact had h'.symm
    · exact hbd h'.symm
  have hsu : s ≠ u := by
    intro h
    have hbu : b ∈ ColF v u := (mem_ColF_supp v b u).mpr hub
    rw [← h, hD.hs] at hbu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbu
    rcases hbu with h' | h' | h'
    · exact hjb h'.symm
    · exact hbd h'
    · exact hab h'.symm
  exact supp_eq_of_four v (h1 a).1 hpa hsa hua hxa hps hpu hpx hsu hsx hux

end Work.BG
