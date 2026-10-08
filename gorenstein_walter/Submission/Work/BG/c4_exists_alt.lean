/-
The extraction of the 4-cycle data (`Work.BG.C4Data`) around a *full* row, i.e. a row all of
whose four columns are triple columns.  This is the combinatorial input for the two local
contradictions `caseQ_false` / `caseP_false`.

If `j` is full then (counting identity `tc_card_eq_nb_card`) it has exactly four neighbours, each
of which lies in exactly two of the four columns of `j`; no two columns have the same support
(`no_repeat`), so the incidence structure of the four neighbours against the four columns is a
4-cycle, giving `C4Data`.
-/
import Mathlib
import Submission.Work.BG.C413Defs

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.BG

namespace Comb413Aux

theorem exists_eq_three {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 3)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ S = {x, y, z} := by
  have hsub : ({x, y} : Finset α) ⊆ S := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  have h1 : (S \ ({x, y} : Finset α)).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair hxy, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
  have hzmem : z ∈ S \ ({x, y} : Finset α) := by rw [hz]; simp
  obtain ⟨hzS, hznot⟩ := Finset.mem_sdiff.mp hzmem
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h; exact hznot (by rw [h]; simp)
  · intro h; exact hznot (by rw [h]; simp)
  · apply Finset.Subset.antisymm
    · intro t ht
      by_cases h : t ∈ ({x, y} : Finset α)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto
      · have : t ∈ S \ ({x, y} : Finset α) := Finset.mem_sdiff.mpr ⟨ht, h⟩
        rw [hz, Finset.mem_singleton] at this
        rw [this]; simp
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hzS

theorem exists_eq_two {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 2)
    {x : α} (hx : x ∈ S) : ∃ y, y ≠ x ∧ S = {x, y} := by
  have hsub : ({x} : Finset α) ⊆ S := by
    intro t ht
    rw [Finset.mem_singleton] at ht
    rw [ht]; exact hx
  have h1 : (S \ ({x} : Finset α)).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_singleton, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
  have hymem : y ∈ S \ ({x} : Finset α) := by rw [hy]; simp
  obtain ⟨hyS, hynot⟩ := Finset.mem_sdiff.mp hymem
  have hyx : y ≠ x := by intro h; exact hynot (by rw [h]; simp)
  refine ⟨y, hyx, ?_⟩
  apply Finset.Subset.antisymm
  · intro t ht
    by_cases h : t = x
    · rw [h]; simp
    · have ht2 : t ∈ S \ ({x} : Finset α) :=
        Finset.mem_sdiff.mpr ⟨ht, by simpa [Finset.mem_singleton] using h⟩
      rw [hy, Finset.mem_singleton] at ht2
      rw [ht2]; simp
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hx
    · exact hyS



end Comb413Aux

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

theorem c4_exists_alt (v : J → ι → ℤ)
    (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    (j : J) (hj : Full v j) :
    ∃ a b c d p q r s u x y z, C4Data v j a b c d p q r s u x y z := by
  have hnb : (NB v j).card = 4 := by
    rw [← tc_card_eq_nb_card v h1 h2 h3 h4 j]; exact hj
  have hSupp : Supp v j = TC v j := by
    have h : TC v j = Supp v j :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hj, (h1 j).1])
    exact h.symm
  have hcol3 : ∀ i ∈ Supp v j, (ColF v i).card = 3 := by
    intro i hi
    have hi' : i ∈ TC v j := by rw [← hSupp]; exact hi
    rw [TC, Finset.mem_filter] at hi'
    exact hi'.2
  have hnb2 : ∀ k ∈ NB v j, (Supp v j ∩ Supp v k).card = 2 := by
    intro k hk
    have hk' : k ≠ j ∧ (Supp v j ∩ Supp v k).Nonempty := by simpa [NB] using hk
    rcases inter_card_cases v h1 h2 h4 (Ne.symm hk'.1) with h | h
    · rw [Finset.card_eq_zero] at h
      exact absurd hk'.2 (Finset.not_nonempty_iff_eq_empty.mpr h)
    · exact h
  have memNB : ∀ k : J, k ∈ NB v j ↔ k ≠ j ∧ (Supp v j ∩ Supp v k).Nonempty := by
    intro k; simp [NB]
  -- choose a neighbour a
  obtain ⟨a, ha⟩ : ∃ a : J, a ∈ NB v j := Finset.card_pos.mp (by rw [hnb]; norm_num)
  have haj : a ≠ j := ((memNB a).mp ha).1
  -- the two columns of j through a
  obtain ⟨p, s, hps, hEqps⟩ : ∃ p s : ι, p ≠ s ∧ Supp v j ∩ Supp v a = {p, s} :=
    Finset.card_eq_two.mp (hnb2 a ha)
  have hp_mem : p ∈ Supp v j :=
    (Finset.mem_inter.mp (by rw [hEqps]; simp)).1
  have hs_mem : s ∈ Supp v j :=
    (Finset.mem_inter.mp (by rw [hEqps]; simp)).1
  have hp_a : p ∈ Supp v a :=
    (Finset.mem_inter.mp (by rw [hEqps]; simp)).2
  have hs_a : s ∈ Supp v a :=
    (Finset.mem_inter.mp (by rw [hEqps]; simp)).2
  have hj_p : j ∈ ColF v p := (mem_ColF v j p).mpr ((mem_Supp v j p).mp hp_mem)
  have ha_p : a ∈ ColF v p := (mem_ColF_supp v a p).mpr hp_a
  have hj_s : j ∈ ColF v s := (mem_ColF v j s).mpr ((mem_Supp v j s).mp hs_mem)
  have ha_s : a ∈ ColF v s := (mem_ColF_supp v a s).mpr hs_a
  obtain ⟨b, hbj, hba, hEqb⟩ := Comb413Aux.exists_eq_three (hcol3 p hp_mem) hj_p ha_p haj.symm
  obtain ⟨d, hdj, hda, hEqd⟩ := Comb413Aux.exists_eq_three (hcol3 s hs_mem) hj_s ha_s haj.symm
  have hbd : b ≠ d := by
    intro h
    exact no_repeat v h1 h2 h4 hps (by rw [hEqb, hEqd, h]) (hcol3 p hp_mem)
  -- b, d are neighbours of j
  have hb_p : b ∈ ColF v p := by rw [hEqb]; simp
  have hd_s : d ∈ ColF v s := by rw [hEqd]; simp
  have hbNB : b ∈ NB v j := by
    rw [memNB]
    exact ⟨hbj, ⟨p, Finset.mem_inter.mpr ⟨hp_mem, (mem_ColF_supp v b p).mp hb_p⟩⟩⟩
  have hdNB : d ∈ NB v j := by
    rw [memNB]
    exact ⟨hdj, ⟨s, Finset.mem_inter.mpr ⟨hs_mem, (mem_ColF_supp v d s).mp hd_s⟩⟩⟩
  -- the remaining neighbour c
  have hbd_sub : ({a, b, d} : Finset J) ⊆ NB v j := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact ha
    · exact hbNB
    · exact hdNB
  have hbd_card : ({a, b, d} : Finset J).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, d, hba.symm, hda.symm, hbd, rfl⟩
  have hcnt : (NB v j \ ({a, b, d} : Finset J)).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbd_sub, hbd_card, hnb]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcnt
  have hcmem : c ∈ NB v j \ ({a, b, d} : Finset J) := by rw [hc]; simp
  obtain ⟨hcNB, hcnot⟩ := Finset.mem_sdiff.mp hcmem
  have hc_ne_a : c ≠ a := by intro h; exact hcnot (by rw [h]; simp)
  have hc_ne_b : c ≠ b := by intro h; exact hcnot (by rw [h]; simp)
  have hc_ne_d : c ≠ d := by intro h; exact hcnot (by rw [h]; simp)
  have hc_ne_j : c ≠ j := ((memNB c).mp hcNB).1
  -- the second column through b
  have hb_int_card : (Supp v j ∩ Supp v b).card = 2 := hnb2 b hbNB
  have hp_b : p ∈ Supp v b := (mem_ColF_supp v b p).mp hb_p
  obtain ⟨q, hqp, hEqpq⟩ : ∃ q, q ≠ p ∧ Supp v j ∩ Supp v b = {p, q} :=
    Comb413Aux.exists_eq_two hb_int_card (Finset.mem_inter.mpr ⟨hp_mem, hp_b⟩)
  have hq_mem : q ∈ Supp v j :=
    (Finset.mem_inter.mp (by rw [hEqpq]; simp)).1
  have hq_b : q ∈ Supp v b :=
    (Finset.mem_inter.mp (by rw [hEqpq]; simp)).2
  have hq_s : q ≠ s := by
    intro h
    have hmem : s ∈ Supp v b := by rw [← h]; exact hq_b
    have hbs : b ∈ ColF v s := (mem_ColF_supp v b s).mpr hmem
    rw [hEqd] at hbs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbs
    rcases hbs with h1 | h1 | h1
    · exact hbj h1
    · exact hba h1
    · exact hbd h1
  -- the fourth column r
  have hpsq_sub : ({p, s, q} : Finset ι) ⊆ Supp v j := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hp_mem
    · exact hs_mem
    · exact hq_mem
  have hpsq_card : ({p, s, q} : Finset ι).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨p, s, q, hps, hqp.symm, hq_s.symm, rfl⟩
  have hcnt2 : (Supp v j \ ({p, s, q} : Finset ι)).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpsq_sub, hpsq_card, (h1 j).1]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcnt2
  have hrmem : r ∈ Supp v j \ ({p, s, q} : Finset ι) := by rw [hr]; simp
  obtain ⟨hr_mem, hrnot⟩ := Finset.mem_sdiff.mp hrmem
  have hr_ne_p : r ≠ p := by intro h; exact hrnot (by rw [h]; simp)
  have hr_ne_s : r ≠ s := by intro h; exact hrnot (by rw [h]; simp)
  have hr_ne_q : r ≠ q := by intro h; exact hrnot (by rw [h]; simp)
  have hqr : q ≠ r := hr_ne_q.symm
  -- basic facts about the four columns at j
  have hSuppj : Supp v j = {p, q, r, s} := by
    apply Finset.Subset.antisymm
    · intro t ht
      by_cases h : t ∈ ({p, s, q} : Finset ι)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
        tauto
      · have : t ∈ Supp v j \ ({p, s, q} : Finset ι) := Finset.mem_sdiff.mpr ⟨ht, h⟩
        rw [hr, Finset.mem_singleton] at this
        rw [this]
        simp
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hp_mem
      · exact hq_mem
      · exact hr_mem
      · exact hs_mem
  have hj_q : j ∈ ColF v q := (mem_ColF v j q).mpr ((mem_Supp v j q).mp hq_mem)
  have hj_r : j ∈ ColF v r := (mem_ColF v j r).mpr ((mem_Supp v j r).mp hr_mem)
  have hb_q : b ∈ ColF v q := (mem_ColF_supp v b q).mpr hq_b
  -- c avoids the columns p and s
  have hc_not_p : c ∉ ColF v p := by
    intro h
    rw [hEqb] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h1 | h1
    · exact hc_ne_j h1
    · exact hc_ne_a h1
    · exact hc_ne_b h1
  have hc_not_s : c ∉ ColF v s := by
    intro h
    rw [hEqd] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h1 | h1
    · exact hc_ne_j h1
    · exact hc_ne_a h1
    · exact hc_ne_d h1
  -- the two columns of j through c are q and r
  have hc_cols : Supp v j ∩ Supp v c = {q, r} := by
    have hcard : (Supp v j ∩ Supp v c).card = 2 := hnb2 c hcNB
    have hsub : Supp v j ∩ Supp v c ⊆ ({q, r} : Finset ι) := by
      intro t ht
      obtain ⟨htj, htc⟩ := Finset.mem_inter.mp ht
      have htne_p : t ≠ p := by
        intro h; rw [h] at htc; exact hc_not_p ((mem_ColF_supp v c p).mpr htc)
      have htne_s : t ≠ s := by
        intro h; rw [h] at htc; exact hc_not_s ((mem_ColF_supp v c s).mpr htc)
      by_cases htsq : t ∈ ({p, s, q} : Finset ι)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at htsq ⊢
        rcases htsq with h | h | h
        · exact absurd h htne_p
        · exact absurd h htne_s
        · exact Or.inl h
      · have h2 : t ∈ Supp v j \ ({p, s, q} : Finset ι) :=
          Finset.mem_sdiff.mpr ⟨htj, htsq⟩
        rw [hr, Finset.mem_singleton] at h2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr h2
    have hqr_card : ({q, r} : Finset ι).card = 2 := Finset.card_pair hqr
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hqr_card, hcard])
  have hrs : r ≠ s := hr_ne_s
  have hq_c : q ∈ Supp v c := by
    have h : q ∈ Supp v j ∩ Supp v c := by rw [hc_cols]; simp
    exact (Finset.mem_inter.mp h).2
  have hr_c : r ∈ Supp v c := by
    have h : r ∈ Supp v j ∩ Supp v c := by rw [hc_cols]; simp
    exact (Finset.mem_inter.mp h).2
  have hc_q : c ∈ ColF v q := (mem_ColF_supp v c q).mpr hq_c
  have hc_r : c ∈ ColF v r := (mem_ColF_supp v c r).mpr hr_c
  have hqr : q ≠ r := hqr
  -- columns of q and r
  have hcolq : ColF v q = {j, b, c} := by
    obtain ⟨x, hxj, hxb, hEqx⟩ := Comb413Aux.exists_eq_three (hcol3 q hq_mem) hj_q hb_q hbj.symm
    have : c ∈ ColF v q := hc_q
    rw [hEqx] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact absurd h1 hc_ne_j
    · exact absurd h1 hc_ne_b
    · rw [hEqx, h1]
  have hd_not_q : d ∉ ColF v q := by
    intro h
    rw [hcolq] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h1 | h1
    · exact hdj h1
    · exact hbd h1.symm
    · exact hc_ne_d h1.symm
  have hd_cols : Supp v j ∩ Supp v d = {s, r} := by
    have hcard : (Supp v j ∩ Supp v d).card = 2 := hnb2 d hdNB
    have hs_d : s ∈ Supp v d := (mem_ColF_supp v d s).mp hd_s
    have hsub : Supp v j ∩ Supp v d ⊆ ({s, r} : Finset ι) := by
      intro t ht
      obtain ⟨htj, htd⟩ := Finset.mem_inter.mp ht
      have htne_p : t ≠ p := by
        intro h
        rw [h] at htd
        have h3 : d ∈ ColF v p := (mem_ColF_supp v d p).mpr htd
        rw [hEqb] at h3
        simp only [Finset.mem_insert, Finset.mem_singleton] at h3
        rcases h3 with h2 | h2 | h2
        · exact hdj h2
        · exact hda h2
        · exact hbd h2.symm
      have htne_q : t ≠ q := by
        intro h
        rw [h] at htd
        exact hd_not_q ((mem_ColF_supp v d q).mpr htd)
      by_cases htsq : t ∈ ({p, s, q} : Finset ι)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at htsq ⊢
        rcases htsq with h | h | h
        · exact absurd h htne_p
        · exact Or.inl h
        · exact absurd h htne_q
      · have h2 : t ∈ Supp v j \ ({p, s, q} : Finset ι) :=
          Finset.mem_sdiff.mpr ⟨htj, htsq⟩
        rw [hr, Finset.mem_singleton] at h2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr h2
    have hsr_card : ({s, r} : Finset ι).card = 2 := Finset.card_pair hrs.symm
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hsr_card, hcard])
  have hr_d : r ∈ Supp v d := by
    have h : r ∈ Supp v j ∩ Supp v d := by rw [hd_cols]; simp
    exact (Finset.mem_inter.mp h).2
  have hd_r : d ∈ ColF v r := (mem_ColF_supp v d r).mpr hr_d
  have hcolr : ColF v r = {j, c, d} := by
    obtain ⟨y, hyj, hyc, hEqy⟩ := Comb413Aux.exists_eq_three (hcol3 r hr_mem) hj_r hc_r (Ne.symm hc_ne_j)
    have : d ∈ ColF v r := hd_r
    rw [hEqy] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact absurd h1 hdj
    · exact absurd h1 hc_ne_d.symm
    · rw [hEqy, h1]
  have hEqr : ColF v r = {j, c, d} := hcolr
  have hEqc : ColF v q = {j, b, c} := hcolq
  -- the second columns
  have hs_a' : s ∈ Supp v a := hs_a
  have hp_ab : p ∈ Supp v a ∩ Supp v b :=
    Finset.mem_inter.mpr ⟨hp_a, hp_b⟩
  have hab_card : (Supp v a ∩ Supp v b).card = 2 := by
    rcases inter_card_cases v h1 h2 h4 (by intro h; exact hba h.symm) with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      exact (Finset.not_nonempty_iff_eq_empty.mpr h)
        ⟨p, Finset.mem_inter.mpr ⟨hp_a, hp_b⟩⟩
    · exact h
  obtain ⟨u, hup, hEqu⟩ : ∃ u, u ≠ p ∧ Supp v a ∩ Supp v b = {p, u} :=
    Comb413Aux.exists_eq_two hab_card hp_ab
  have hq_bc : q ∈ Supp v b ∩ Supp v c :=
    Finset.mem_inter.mpr ⟨hq_b, (mem_ColF_supp v c q).mp hc_q⟩
  have hbc_card : (Supp v b ∩ Supp v c).card = 2 := by
    rcases inter_card_cases v h1 h2 h4 (by intro h; exact hc_ne_b.symm h) with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      exact (Finset.not_nonempty_iff_eq_empty.mpr h)
        ⟨q, Finset.mem_inter.mpr ⟨hq_b, hq_c⟩⟩
    · exact h
  obtain ⟨y, hyq, hEqy'⟩ : ∃ y, y ≠ q ∧ Supp v b ∩ Supp v c = {q, y} :=
    Comb413Aux.exists_eq_two hbc_card hq_bc
  have hr_cd : r ∈ Supp v c ∩ Supp v d :=
    Finset.mem_inter.mpr ⟨(mem_ColF_supp v c r).mp hc_r, (mem_ColF_supp v d r).mp hd_r⟩
  have hcd_card : (Supp v c ∩ Supp v d).card = 2 := by
    rcases inter_card_cases v h1 h2 h4 (by intro h; exact hc_ne_d h) with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      exact (Finset.not_nonempty_iff_eq_empty.mpr h)
        ⟨r, Finset.mem_inter.mpr ⟨hr_c, hr_d⟩⟩
    · exact h
  obtain ⟨z, hzr, hEqz⟩ : ∃ z, z ≠ r ∧ Supp v c ∩ Supp v d = {r, z} :=
    Comb413Aux.exists_eq_two hcd_card hr_cd
  have hs_d : s ∈ Supp v d := (mem_ColF_supp v d s).mp hd_s
  have hs_da : s ∈ Supp v d ∩ Supp v a :=
    Finset.mem_inter.mpr ⟨hs_d, hs_a⟩
  have hda_card : (Supp v d ∩ Supp v a).card = 2 := by
    rcases inter_card_cases v h1 h2 h4 (by intro h; exact hda h) with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      exact (Finset.not_nonempty_iff_eq_empty.mpr h)
        ⟨s, Finset.mem_inter.mpr ⟨hs_d, hs_a⟩⟩
    · exact h
  obtain ⟨x, hxs, hEqx'⟩ : ∃ x, x ≠ s ∧ Supp v d ∩ Supp v a = {s, x} :=
    Comb413Aux.exists_eq_two hda_card hs_da
  refine ⟨a, b, c, d, p, q, r, s, u, x, y, z, ?_⟩
  have hEqd' : ColF v s = {j, d, a} := by
    rw [hEqd]
    ext t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact ⟨hEqb, hEqc, hEqr, hEqd', hcol3 p hp_mem, hcol3 q hq_mem, hcol3 r hr_mem,
    hcol3 s hs_mem, hSuppj, hEqu, hEqy', hEqz, hEqx', hup, hyq, hzr, hxs⟩



end Work.BG
