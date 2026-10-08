import Mathlib
import Submission.Work.BG.C413Defs
import Submission.Work.BG.CaseQAux
import Submission.Work.BG.caseQ_supp_b
import Submission.Work.BG.caseQ_third_row

namespace Work.BG

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

/-! ## Helpers for the evenness computation -/

/-- If a finset `S` contains `x` and `y`, both satisfy `P`, and every other element of `S` fails
`P`, then `S.filter P = {x, y}`. -/
theorem filter_eq_pair_of_subset {α : Type*} [DecidableEq α] {P : α → Prop} [DecidablePred P]
    {S : Finset α} {x y : α} (hxS : x ∈ S) (hyS : y ∈ S) (hPx : P x) (hPy : P y)
    (hxy : x ≠ y) (hother : ∀ z ∈ S, z ≠ x → z ≠ y → ¬ P z) :
    S.filter P = {x, y} := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hPt⟩
    by_cases htx : t = x
    · exact Or.inl htx
    · by_cases hty : t = y
      · exact Or.inr hty
      · exact absurd hPt (hother t ht htx hty)
  · rintro (rfl | rfl)
    · exact ⟨hxS, hPx⟩
    · exact ⟨hyS, hPy⟩

/-- If two adjacent "second columns" of the 4-cycle coincide (`u = x`, the case where the vertex
`a` is not full), the structure is forced to be the 5-row configuration whose full rows `{j,b,d}`
meet every column in an even number of rows, contradicting `F₂`-independence
(`Work.BG.even_set_contra`).

Proof sketch: `u = x` gives `ColF v u = {a,b,d}` (using `h3` and the distinctness of `a,b,d`).
Let `X` be the fourth column of `a`, so `Supp v a = {p,s,u,X}`.  If `X` were a triple column,
`ColF v X = {a,e,f}`, then `a` would be full and every neighbour of `a` would lie in exactly two
of the columns of `a` (`inter_card_cases`); the neighbour `e` already lies in `X`, and its second
column would have to be `p`, `s` or `u` (giving `e ∈ {j,b}`, `{j,d}` or `{b,d}` respectively), so
`e,f ∈ {j,b,d}` and then `ColF v X` equals `ColF v p`, `ColF v s` or `ColF v u`, contradicting
`no_repeat`.  Hence `X` is a singleton.  Next `b` is full (`NB v b` contains the four distinct
rows `j,a,c,d`), and its fourth column `Y` satisfies `ColF v Y = {b,c,d}`: the two other rows of
`Y` lie in `NB v b = {j,a,c,d}`, while `j ∉ ColF v Y` (else `Y` would be one of `p,q`), and
`a ∉ ColF v Y` (else `Y ∈ Supp v a ∩ Supp v b = {p,u}`); similarly for `d`.  Consequently
`Supp v j = {p,q,r,s}`, `Supp v b = {p,q,u,Y}` and `Supp v d = {r,s,Y,u}`, the columns
`p,q,r,s,u,Y` all meet `n = {j,b,d}` in exactly two rows, and every other column avoids `{j,b,d}`
entirely; `Work.BG.even_set_contra` with `n = {j,b,d}` gives a contradiction. -/
theorem caseQ_false {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z) (hu : u = x) : False := by
  classical
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ := C4Data.jabcd_distinct h1 h2 h4 hD
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := C4Data.pqrs_distinct h1 hD
  have hup : u ≠ p := hD.hup
  have hyq : y ≠ q := hD.hyq
  have hzr : z ≠ r := hD.hzr
  have hxs : x ≠ s := hD.hxs
  -- memberships of the special columns in the four edge-intersections
  have hp_ab : p ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
  have hq_bc : q ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
  have hr_cd : r ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
  have hs_da : s ∈ Supp v d ∩ Supp v a := by rw [hD.hDA]; simp
  have hu_ab : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
  have hy_bc : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
  have hz_cd : z ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
  have hx_da : x ∈ Supp v d ∩ Supp v a := by rw [hD.hDA]; simp
  have hp_a : p ∈ Supp v a := (Finset.mem_inter.mp hp_ab).1
  have hp_b : p ∈ Supp v b := (Finset.mem_inter.mp hp_ab).2
  have hq_b : q ∈ Supp v b := (Finset.mem_inter.mp hq_bc).1
  have hq_c : q ∈ Supp v c := (Finset.mem_inter.mp hq_bc).2
  have hr_c : r ∈ Supp v c := (Finset.mem_inter.mp hr_cd).1
  have hr_d : r ∈ Supp v d := (Finset.mem_inter.mp hr_cd).2
  have hs_d : s ∈ Supp v d := (Finset.mem_inter.mp hs_da).1
  have hs_a : s ∈ Supp v a := (Finset.mem_inter.mp hs_da).2
  have hu_a : u ∈ Supp v a := (Finset.mem_inter.mp hu_ab).1
  have hu_b : u ∈ Supp v b := (Finset.mem_inter.mp hu_ab).2
  have hy_b : y ∈ Supp v b := (Finset.mem_inter.mp hy_bc).1
  have hy_c : y ∈ Supp v c := (Finset.mem_inter.mp hy_bc).2
  have hz_c : z ∈ Supp v c := (Finset.mem_inter.mp hz_cd).1
  have hz_d : z ∈ Supp v d := (Finset.mem_inter.mp hz_cd).2
  have hx_d : x ∈ Supp v d := (Finset.mem_inter.mp hx_da).1
  -- **Step 1**: the column `u` has support exactly `{a,b,d}`.
  have hcolu : ColF v u = {a, b, d} := by
    refine colF_eq_of_three v (h3 u) ?_ ?_ ?_ hab had hbd
    · exact (mem_ColF_supp v a u).mpr hu_a
    · exact (mem_ColF_supp v b u).mpr hu_b
    · exact (mem_ColF_supp v d u).mpr (by rw [hu]; exact hx_d)
  -- **Step 2**: the extra distinctness facts about `y` and `u`.
  have hy_ne_p : y ≠ p := by
    intro h
    have hmem : c ∈ ColF v p := (mem_ColF_supp v c p).mpr (h ▸ hy_c)
    rw [hD.hp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjc h'.symm
    · exact hac h'.symm
    · exact hbc h'.symm
  have hq_ne_u : q ≠ u := by
    intro h
    have hmem : a ∈ ColF v q := (mem_ColF_supp v a q).mpr (by rw [h]; exact hu_a)
    rw [hD.hq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hja h'.symm
    · exact hab h'
    · exact hac h'
  have hy_ne_u : y ≠ u := by
    intro h
    have hmem : c ∈ ColF v u := (mem_ColF_supp v c u).mpr (by rw [← h]; exact hy_c)
    rw [hcolu] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hac h'.symm
    · exact hbc h'.symm
    · exact hcd h'
  have hu_ne_r : u ≠ r := by
    intro h
    have hmem : j ∈ ColF v r := by rw [hD.hr]; simp
    have he : ColF v r = ColF v u := by rw [← h]
    rw [he, hcolu] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hja h'
    · exact hjb h'
    · exact hjd h'
  have hy_ne_r : y ≠ r := by
    intro h
    have hmem : b ∈ ColF v r := (mem_ColF_supp v b r).mpr (by rw [← h]; exact hy_b)
    rw [hD.hr] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjb h'.symm
    · exact hbc h'
    · exact hbd h'
  have hy_ne_s : y ≠ s := by
    intro h
    have hmem : b ∈ ColF v s := (mem_ColF_supp v b s).mpr (by rw [← h]; exact hy_b)
    rw [hD.hs] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjb h'.symm
    · exact hbd h'
    · exact hab h'.symm
  have hs_ne_u : s ≠ u := fun h => hxs (hu ▸ h.symm)
  have hs_ne_z : s ≠ z := by
    intro h
    have hmem : c ∈ ColF v s := (mem_ColF_supp v c s).mpr (by rw [h]; exact hz_c)
    rw [hD.hs] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hjc h'.symm
    · exact hcd h'
    · exact hac h'.symm
  have hu_ne_z : u ≠ z := by
    intro h
    have hmem : c ∈ ColF v u := (mem_ColF_supp v c u).mpr (by rw [h]; exact hz_c)
    rw [hcolu] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h'
    · exact hac h'.symm
    · exact hbc h'.symm
    · exact hcd h'
  -- **Step 3**: the supports of `b` and `d`.
  have hSb : Supp v b = {p, q, u, y} := caseQ_supp_b v h1 h2 h3 h4 hD hu
  have hSd : Supp v d = {r, s, u, z} :=
    supp_eq_of_four v (h1 d).1 hr_d hs_d (by rw [hu]; exact hx_d) hz_d
      hrs hu_ne_r.symm hzr.symm hs_ne_u hs_ne_z hu_ne_z
  -- **Step 4**: the case split.
  by_cases hyz : y = z
  · -- **Case `y = z`**: every column meets `{j,b,d}` in an even number of rows.
    have hSd' : Supp v d = {r, s, u, y} := by rw [hyz]; exact hSd
    have heven : ∀ i : ι, Even ((({j, b, d} : Finset J).filter (fun x => v x i ≠ 0)).card) := by
      intro i
      by_cases hi : i ∈ ({p, q, r, s, u, y} : Finset ι)
      · have hi' := hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
        rcases hi' with hcase | hcase | hcase | hcase | hcase | hcase
        · -- i = p
          rw [hcase]
          have hPd : ¬ (v d p ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hSd' (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hpr h
              · exact hps h
              · exact hup.symm h
              · exact hy_ne_p.symm h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x p ≠ 0)) = {j, b} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := j) (y := b)
              (by simp) (by simp) (by rw [← mem_Supp, hD.hS]; simp)
              (by rw [← mem_Supp, hSb]; simp) hjb
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · exact absurd h hzx
                · exact absurd h hzy
                · rw [h]; exact hPd)
          rw [hfil, Finset.card_pair hjb]
          exact ⟨1, by norm_num⟩
        · -- i = q
          rw [hcase]
          have hPd : ¬ (v d q ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hSd' (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hqr h
              · exact hqs h
              · exact hq_ne_u h
              · exact hyq.symm h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x q ≠ 0)) = {j, b} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := j) (y := b)
              (by simp) (by simp) (by rw [← mem_Supp, hD.hS]; simp)
              (by rw [← mem_Supp, hSb]; simp) hjb
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · exact absurd h hzx
                · exact absurd h hzy
                · rw [h]; exact hPd)
          rw [hfil, Finset.card_pair hjb]
          exact ⟨1, by norm_num⟩
        · -- i = r
          rw [hcase]
          have hPb : ¬ (v b r ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hSb (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hpr.symm h
              · exact hqr.symm h
              · exact hu_ne_r.symm h
              · exact hy_ne_r.symm h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x r ≠ 0)) = {j, d} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := j) (y := d)
              (by simp) (by simp) (by rw [← mem_Supp, hD.hS]; simp)
              (by rw [← mem_Supp, hSd']; simp) hjd
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · exact absurd h hzx
                · rw [h]; exact hPb
                · exact absurd h hzy)
          rw [hfil, Finset.card_pair hjd]
          exact ⟨1, by norm_num⟩
        · -- i = s
          rw [hcase]
          have hPb : ¬ (v b s ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hSb (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hps.symm h
              · exact hqs.symm h
              · exact hs_ne_u h
              · exact hy_ne_s.symm h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x s ≠ 0)) = {j, d} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := j) (y := d)
              (by simp) (by simp) (by rw [← mem_Supp, hD.hS]; simp)
              (by rw [← mem_Supp, hSd']; simp) hjd
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · exact absurd h hzx
                · rw [h]; exact hPb
                · exact absurd h hzy)
          rw [hfil, Finset.card_pair hjd]
          exact ⟨1, by norm_num⟩
        · -- i = u
          rw [hcase]
          have hPj : ¬ (v j u ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hD.hS (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hup h
              · exact hq_ne_u.symm h
              · exact hu_ne_r h
              · exact hs_ne_u.symm h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x u ≠ 0)) = {b, d} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := b) (y := d)
              (by simp) (by simp) (by rw [← mem_Supp, hSb]; simp)
              (by rw [← mem_Supp, hSd']; simp) hbd
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · rw [h]; exact hPj
                · exact absurd h hzx
                · exact absurd h hzy)
          rw [hfil, Finset.card_pair hbd]
          exact ⟨1, by norm_num⟩
        · -- i = y
          rw [hcase]
          have hPj : ¬ (v j y ≠ 0) := fun hc =>
            hc (zero_of_not_mem_supp v hD.hS (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h)
              · exact hy_ne_p h
              · exact hyq h
              · exact hy_ne_r h
              · exact hy_ne_s h))
          have hfil : (({j, b, d} : Finset J).filter (fun x => v x y ≠ 0)) = {b, d} :=
            filter_eq_pair_of_subset (S := ({j, b, d} : Finset J)) (x := b) (y := d)
              (by simp) (by simp) (by rw [← mem_Supp, hSb]; simp)
              (by rw [← mem_Supp, hSd']; simp) hbd
              (by
                intro z hz hzx hzy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with h | h | h
                · rw [h]; exact hPj
                · exact absurd h hzx
                · exact absurd h hzy)
          rw [hfil, Finset.card_pair hbd]
          exact ⟨1, by norm_num⟩
      · -- i is none of the six columns
        have hfill : (({j, b, d} : Finset J).filter (fun x => v x i ≠ 0)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx hpx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · exact hi (by
              have hmem : i ∈ Supp v j := (mem_Supp v j i).mpr (h ▸ hpx)
              rw [hD.hS] at hmem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
              tauto)
          · exact hi (by
              have hmem : i ∈ Supp v b := (mem_Supp v b i).mpr (h ▸ hpx)
              rw [hSb] at hmem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
              tauto)
          · exact hi (by
              have hmem : i ∈ Supp v d := (mem_Supp v d i).mpr (h ▸ hpx)
              rw [hSd'] at hmem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
              tauto)
        rw [hfill, Finset.card_empty]
        exact ⟨0, rfl⟩
    exact even_set_contra v h1 h4 {j, b, d} ⟨j, by simp⟩ heven
  · -- **Case `y ≠ z`**: the third row of the column `y` is outside every known column support.
    obtain ⟨g, hgy, hgnot⟩ := caseQ_third_row v h1 h2 h3 h4 hD hu hyz
    have hg_ne_j : g ≠ j := fun h => hgnot (by simp [h])
    have hg_ne_a : g ≠ a := fun h => hgnot (by simp [h])
    have hg_ne_b : g ≠ b := fun h => hgnot (by simp [h])
    have hg_ne_c : g ≠ c := fun h => hgnot (by simp [h])
    have hg_ne_d : g ≠ d := fun h => hgnot (by simp [h])
    have hyg : y ∈ Supp v g := (mem_ColF_supp v g y).mp (by rw [hgy]; simp)
    -- `Supp v b ∩ Supp v g` is a two-element set containing `y`.
    have hinter : (Supp v b ∩ Supp v g).card = 2 := by
      have hne : (Supp v b ∩ Supp v g).Nonempty :=
        ⟨y, Finset.mem_inter.mpr ⟨hy_b, hyg⟩⟩
      rcases inter_card_cases v h1 h2 h4 hg_ne_b.symm with h0 | htwo
      · exfalso
        rw [Finset.card_eq_zero] at h0
        obtain ⟨t, ht⟩ := hne
        rw [h0] at ht
        simp at ht
      · exact htwo
    obtain ⟨w, hwne, hweq⟩ :=
      exists_other_of_card_two (S := Supp v b ∩ Supp v g) (i := y)
        (Finset.mem_inter.mpr ⟨hy_b, hyg⟩) hinter
    have hw_b : w ∈ Supp v b := by
      have hmem : w ∈ Supp v b ∩ Supp v g := by rw [hweq]; simp
      exact (Finset.mem_inter.mp hmem).1
    have hw_g : w ∈ Supp v g := by
      have hmem : w ∈ Supp v b ∩ Supp v g := by rw [hweq]; simp
      exact (Finset.mem_inter.mp hmem).2
    have hw_cases : w = p ∨ w = q ∨ w = u := by
      have hwS : w ∈ ({p, q, u, y} : Finset ι) := by rw [← hSb]; exact hw_b
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
      tauto
    rcases hw_cases with hwp | hwq | hwu
    · have hmem : g ∈ ColF v p := (mem_ColF_supp v g p).mpr (hwp ▸ hw_g)
      rw [hD.hp] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h' | h'
      · exact hg_ne_j h'
      · exact hg_ne_a h'
      · exact hg_ne_b h'
    · have hmem : g ∈ ColF v q := (mem_ColF_supp v g q).mpr (hwq ▸ hw_g)
      rw [hD.hq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h' | h'
      · exact hg_ne_j h'
      · exact hg_ne_b h'
      · exact hg_ne_c h'
    · have hmem : g ∈ ColF v u := (mem_ColF_supp v g u).mpr (hwu ▸ hw_g)
      rw [hcolu] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h' | h'
      · exact hg_ne_a h'
      · exact hg_ne_b h'
      · exact hg_ne_d h'

end Work.BG
