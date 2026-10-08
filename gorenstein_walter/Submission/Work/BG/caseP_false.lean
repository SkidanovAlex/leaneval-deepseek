import Mathlib
import Submission.Work.BG.C413Defs
import Submission.Work.BG.caseP_supp_a
import Submission.Work.BG.caseP_supp_b
import Submission.Work.BG.caseP_supp_c
import Submission.Work.BG.caseP_supp_d

namespace Work.BG

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- If `r` belongs to the column `w` and `ColF v w' = {i1,i2,i3}` with `i1,i2,i3 ≠ r`, then
`w ≠ w'`: two columns with different row-supports are different. -/
theorem caseP_col_ne {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ) {w w' : ι} {r i1 i2 i3 : J}
    (hr : r ∈ ColF v w) (hs : ColF v w' = ({i1, i2, i3} : Finset J))
    (h1 : i1 ≠ r) (h2 : i2 ≠ r) (h3 : i3 ≠ r) : w ≠ w' := by
  intro h
  rw [h] at hr
  rw [hs] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  exact hr.elim (fun hh => h1 hh.symm)
    (fun hh => hh.elim (fun hh => h2 hh.symm) (fun hh => h3 hh.symm))

/-- The parity core of `caseP_false`: once the four supports are known to be the octahedron faces,
every column meets `{a,b,c,d}` in an even number of rows. -/
theorem caseP_even {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (hsa : Work.BG.Supp v a = ({p,s,u,x}:Finset ι))
    (hsb : Work.BG.Supp v b = ({p,q,u,y}:Finset ι))
    (hsc : Work.BG.Supp v c = ({q,r,y,z}:Finset ι))
    (hsd : Work.BG.Supp v d = ({r,s,z,x}:Finset ι))
    (hux : u ≠ x) (huy : u ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    ∀ w, Even (({a,b,c,d}:Finset J).filter (fun r => w ∈ Work.BG.Supp v r)).card := by
  obtain ⟨hja, hjb, hjc, hjd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Work.BG.C4Data.jabcd_distinct (v := v) h1 h2 h4 hD
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := Work.BG.C4Data.pqrs_distinct (v := v) h1 hD
  have hcardS : ({a,b,c,d}:Finset J).card = 4 :=
    (Finset.card_eq_four).mpr ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩
  -- membership facts (`a,b ∈ ColF u`, `b,c ∈ ColF y`, `c,d ∈ ColF z`, `d,a ∈ ColF x`)
  have hua : u ∈ Supp v a := by
    have h : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    exact (Finset.mem_inter.mp h).1
  have hub : u ∈ Supp v b := by
    have h : u ∈ Supp v a ∩ Supp v b := by rw [hD.hAB]; simp
    exact (Finset.mem_inter.mp h).2
  have hyb : y ∈ Supp v b := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).1
  have hyc : y ∈ Supp v c := by
    have h : y ∈ Supp v b ∩ Supp v c := by rw [hD.hBC]; simp
    exact (Finset.mem_inter.mp h).2
  have hzc : z ∈ Supp v c := by
    have h : z ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
    exact (Finset.mem_inter.mp h).1
  have hzd : z ∈ Supp v d := by
    have h : z ∈ Supp v c ∩ Supp v d := by rw [hD.hCD]; simp
    exact (Finset.mem_inter.mp h).2
  have hxa : x ∈ Supp v a := by
    have h : x ∈ Supp v d ∩ Supp v a := by rw [hD.hDA]; simp
    exact (Finset.mem_inter.mp h).2
  have hxd : x ∈ Supp v d := by
    have h : x ∈ Supp v d ∩ Supp v a := by rw [hD.hDA]; simp
    exact (Finset.mem_inter.mp h).1
  have ha_u : a ∈ ColF v u := (mem_ColF v a u).mpr ((mem_Supp v a u).mp hua)
  have hb_u : b ∈ ColF v u := (mem_ColF v b u).mpr ((mem_Supp v b u).mp hub)
  have hb_y : b ∈ ColF v y := (mem_ColF v b y).mpr ((mem_Supp v b y).mp hyb)
  have hc_y : c ∈ ColF v y := (mem_ColF v c y).mpr ((mem_Supp v c y).mp hyc)
  have hc_z : c ∈ ColF v z := (mem_ColF v c z).mpr ((mem_Supp v c z).mp hzc)
  have hd_z : d ∈ ColF v z := (mem_ColF v d z).mpr ((mem_Supp v d z).mp hzd)
  have ha_x : a ∈ ColF v x := (mem_ColF v a x).mpr ((mem_Supp v a x).mp hxa)
  have hd_x : d ∈ ColF v x := (mem_ColF v d x).mpr ((mem_Supp v d x).mp hxd)
  -- distinctness of the eight columns
  have hpu : p ≠ u := hD.hup.symm
  have hqy : q ≠ y := hD.hyq.symm
  have hrz : r ≠ z := hD.hzr.symm
  have hsx : s ≠ x := hD.hxs.symm
  have hxz : x ≠ z := hzx.symm
  have hpx : p ≠ x := (caseP_col_ne v hd_x hD.hp hjd had hbd).symm
  have hpy : p ≠ y := (caseP_col_ne v hc_y hD.hp hjc hac hbc).symm
  have hpz : p ≠ z := (caseP_col_ne v hc_z hD.hp hjc hac hbc).symm
  have hqu : q ≠ u := (caseP_col_ne v ha_u hD.hq hja hab.symm hac.symm).symm
  have hqx : q ≠ x := (caseP_col_ne v hd_x hD.hq hjd hbd hcd).symm
  have hqz : q ≠ z := (caseP_col_ne v hd_z hD.hq hjd hbd hcd).symm
  have hru : r ≠ u := (caseP_col_ne v ha_u hD.hr hja hac.symm had.symm).symm
  have hrx : r ≠ x := (caseP_col_ne v ha_x hD.hr hja hac.symm had.symm).symm
  have hry : r ≠ y := (caseP_col_ne v hb_y hD.hr hjb hbc.symm hbd.symm).symm
  have hsu : s ≠ u := (caseP_col_ne v hb_u hD.hs hjb hbd.symm hab).symm
  have hsy : s ≠ y := (caseP_col_ne v hc_y hD.hs hjc hcd.symm hac).symm
  have hsz : s ≠ z := (caseP_col_ne v hc_z hD.hs hjc hcd.symm hac).symm
  have huz : u ≠ z := by
    intro huz
    have hc : c ∈ ColF v u := by rw [huz]; exact hc_z
    have hd : d ∈ ColF v u := by rw [huz]; exact hd_z
    have hsub : ({a,b,c,d}:Finset J) ⊆ ColF v u := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl|rfl|rfl|rfl
      · exact ha_u
      · exact hb_u
      · exact hc
      · exact hd
    have h4le : 4 ≤ (ColF v u).card := by
      have := Finset.card_le_card hsub
      rwa [hcardS] at this
    have hu3 := h3 u
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu3
    omega
  have hxy : x ≠ y := by
    intro hxy
    have hb : b ∈ ColF v x := by rw [hxy]; exact hb_y
    have hc : c ∈ ColF v x := by rw [hxy]; exact hc_y
    have hsub : ({a,b,c,d}:Finset J) ⊆ ColF v x := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl|rfl|rfl|rfl
      · exact ha_x
      · exact hb
      · exact hc
      · exact hd_x
    have h4le : 4 ≤ (ColF v x).card := by
      have := Finset.card_le_card hsub
      rwa [hcardS] at this
    have hx3 := h3 x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx3
    omega
  -- reverse orientations used in the case analysis
  have h_rp : r ≠ p := hpr.symm
  have h_xp : x ≠ p := hpx.symm
  have h_yp : y ≠ p := hpy.symm
  have h_zp : z ≠ p := hpz.symm
  have h_rq : r ≠ q := hqr.symm
  have h_sq : s ≠ q := hqs.symm
  have h_uq : u ≠ q := hqu.symm
  have h_xq : x ≠ q := hqx.symm
  have h_zq : z ≠ q := hqz.symm
  have h_sr : s ≠ r := hrs.symm
  have h_ur : u ≠ r := hru.symm
  have h_xr : x ≠ r := hrx.symm
  have h_yr : y ≠ r := hry.symm
  have h_us : u ≠ s := hsu.symm
  have h_xs : x ≠ s := hsx.symm
  have h_ys : y ≠ s := hsy.symm
  have h_zs : z ≠ s := hsz.symm
  have h_xu : x ≠ u := hux.symm
  have h_yu : y ≠ u := huy.symm
  have h_zu : z ≠ u := huz.symm
  have h_zx : z ≠ x := hxz.symm
  have h_yx : y ≠ x := hxy.symm
  have h_zy : z ≠ y := hyz.symm
  intro w
  rcases em (w ∈ ({p,q,r,s,u,x,y,z} : Finset ι)) with hw | hw
  · have hw' : w = p ∨ w = q ∨ w = r ∨ w = s ∨ w = u ∨ w = x ∨ w = y ∨ w = z := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    rcases hw' with hw1 | hw2 | hw3 | hw4 | hw5 | hw6 | hw7 | hw8
    · rw [hw1]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => p ∈ Work.BG.Supp v r) = {a,b} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
          · subst h; exfalso; rw [hsc] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim hpq (fun h => h.elim hpr (fun h => h.elim hpy hpz))
          · subst h; exfalso; rw [hsd] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim hpr (fun h => h.elim hps (fun h => h.elim hpz hpx))
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsa]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsb]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hab]⟩
    · rw [hw2]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => q ∈ Work.BG.Supp v r) = {b,c} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exfalso; rw [hsa] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim hpq.symm (fun h => h.elim hqs (fun h => h.elim hqu hqx))
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
          · subst h; exfalso; rw [hsd] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim hqr (fun h => h.elim hqs (fun h => h.elim hqz hqx))
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsb]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsc]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hbc]⟩
    · rw [hw3]
      have hset : ({a,b,c,d}:Finset J).filter (fun r'' => r ∈ Work.BG.Supp v r'') = {c,d} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exfalso; rw [hsa] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_rp (fun h => h.elim hrs (fun h => h.elim hru hrx))
          · subst h; exfalso; rw [hsb] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_rp (fun h => h.elim h_rq (fun h => h.elim hru hry))
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsc]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsd]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hcd]⟩
    · rw [hw4]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => s ∈ Work.BG.Supp v r) = {a,d} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exact Or.inl rfl
          · subst h; exfalso; rw [hsb] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim hps.symm (fun h => h.elim h_sq (fun h => h.elim hsu hsy))
          · subst h; exfalso; rw [hsc] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_sq (fun h => h.elim h_sr (fun h => h.elim hsy hsz))
          · subst h; exact Or.inr rfl
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsa]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsd]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair had]⟩
    · rw [hw5]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => u ∈ Work.BG.Supp v r) = {a,b} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
          · subst h; exfalso; rw [hsc] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_uq (fun h => h.elim h_ur (fun h => h.elim huy huz))
          · subst h; exfalso; rw [hsd] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_ur (fun h => h.elim h_us (fun h => h.elim huz hux))
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsa]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsb]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hab]⟩
    · rw [hw6]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => x ∈ Work.BG.Supp v r) = {a,d} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exact Or.inl rfl
          · subst h; exfalso; rw [hsb] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_xp (fun h => h.elim h_xq (fun h => h.elim h_xu hxy))
          · subst h; exfalso; rw [hsc] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_xq (fun h => h.elim h_xr (fun h => h.elim hxy hxz))
          · subst h; exact Or.inr rfl
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsa]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsd]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair had]⟩
    · rw [hw7]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => y ∈ Work.BG.Supp v r) = {b,c} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exfalso; rw [hsa] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_yp (fun h => h.elim h_ys (fun h => h.elim h_yu h_yx))
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
          · subst h; exfalso; rw [hsd] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_yr (fun h => h.elim h_ys (fun h => h.elim hyz h_yx))
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsb]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsc]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hbc]⟩
    · rw [hw8]
      have hset : ({a,b,c,d}:Finset J).filter (fun r => z ∈ Work.BG.Supp v r) = {c,d} := by
        apply Finset.ext; intro r'
        rw [Finset.mem_filter]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hq⟩
          rcases hr with h|h|h|h
          · subst h; exfalso; rw [hsa] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_zp (fun h => h.elim h_zs (fun h => h.elim h_zu h_zx))
          · subst h; exfalso; rw [hsb] at hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            exact hq.elim h_zp (fun h => h.elim h_zq (fun h => h.elim h_zu h_zy))
          · subst h; exact Or.inl rfl
          · subst h; exact Or.inr rfl
        · rintro (h|h)
          · subst h; exact ⟨by simp, by rw [hsc]; simp⟩
          · subst h; exact ⟨by simp, by rw [hsd]; simp⟩
      rw [hset]; exact ⟨1, by rw [Finset.card_pair hcd]⟩
  · have hnil : ({a,b,c,d}:Finset J).filter (fun r => w ∈ Work.BG.Supp v r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r' hr'
      rw [Finset.mem_filter] at hr'
      obtain ⟨hr'S, hr'w⟩ := hr'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr'S
      rcases hr'S with h|h|h|h
      · subst h; rw [hsa] at hr'w
        exact hw (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr'w ⊢; tauto)
      · subst h; rw [hsb] at hr'w
        exact hw (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr'w ⊢; tauto)
      · subst h; rw [hsc] at hr'w
        exact hw (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr'w ⊢; tauto)
      · subst h; rw [hsd] at hr'w
        exact hw (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr'w ⊢; tauto)
    rw [hnil, Finset.card_empty]; exact ⟨0, rfl⟩

/-- The "all four vertices of the 4-cycle are full" case is impossible: the data is forced to be
the octahedron, whose four middle rows `a,b,c,d` meet every column in an even number of rows,
contradicting `F₂`-independence (`Work.BG.even_set_contra`).

Proof sketch: `u ≠ x` means the two second columns at `a` are different, so `a` has four distinct
columns `p, s, u, x`, hence (with `Work.BG.tc_card_eq_nb_card`, `(NB v a).card = 4`) `a` is full
and every neighbour of `a` occurs in exactly two of the columns of `a` (`inter_card_cases`).
Writing `ColF v u = {a,b,e}` and `ColF v x = {a,d,f}`, the four pairs `{j,b}, {j,d}, {b,e}, {d,f}`
cut out on `NB v a` must give every vertex degree two, so `e = f` and `e ∉ {j,a,b,d}`.  At `b`
(using `u ≠ y`) the same argument gives `ColF v y = {b,c,e}` with the same `e`, at `c` (using
`y ≠ z`) it gives `ColF v z = {c,d,e}`, and at `d` (using `z ≠ x`) it is consistent with
`ColF v x = {a,d,e}`.  Hence the eight columns are `{j,a,b}, {j,b,c}, {j,c,d}, {j,d,a}`,
`{a,b,e}, {b,c,e}, {c,d,e}, {d,a,e}`; every column of each of `a,b,c,d` is one of them, so every
column meets `{a,b,c,d}` in exactly two rows (or none, if it avoids those rows); then
`Work.BG.even_set_contra` applied to `n = {a,b,c,d}` gives a contradiction. -/
theorem caseP_false {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
    (v : J → ι → ℤ)
    (h1 : ∀ j, (Work.BG.Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (Work.BG.ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j a b c d : J} {p q r s u x y z : ι}
    (hD : Work.BG.C4Data v j a b c d p q r s u x y z)
    (hux : u ≠ x) (huy : u ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) : False := by
  have hsa := caseP_supp_a v h1 h2 h3 h4 hD hux
  have hsb := caseP_supp_b v h1 h2 h3 h4 hD huy
  have hsc := caseP_supp_c v h1 h2 h3 h4 hD hyz
  have hsd := caseP_supp_d v h1 h2 h3 h4 hD hzx
  have heven := caseP_even v h1 h2 h3 h4 hD hsa hsb hsc hsd hux huy hyz hzx
  refine even_set_contra v h1 h4 ({a,b,c,d}:Finset J) ⟨a, by simp⟩ ?_
  intro i
  have hconv : ({a,b,c,d}:Finset J).filter (fun r => v r i ≠ 0)
      = ({a,b,c,d}:Finset J).filter (fun r => i ∈ Work.BG.Supp v r) := by
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => (mem_Supp v r i).mpr h, fun h => (mem_Supp v r i).mp h⟩
  rw [hconv]
  exact heven i

end Work.BG
