import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs

namespace Work.RPB1a.Caratheodory.Brouwer

set_option autoImplicit false

open Set Metric

/-- The path `u ↦ PJc (lineMap sl sm u)`, running along the sub-arc `PJc '' [sl, sm]` of `Jc`
from `PJc sl` to `PJc sm`. -/
noncomputable def arcPath (PJc : ℝ → ℝ × ℝ) (sl sm : ℝ) (l m : ℝ × ℝ)
    (hcont : Continuous PJc) (hsl : PJc sl = l) (hsm : PJc sm = m) : Path l m where
  toFun := fun u => PJc (AffineMap.lineMap sl sm (u : ℝ))
  continuous_toFun := hcont.comp (by fun_prop)
  source' := by simp [hsl]
  target' := by simp [hsm]

/-- The range of the arc path lies in `PJc '' (sl, sm)`, provided `sl, sm ∈ (-1, 1)`. -/
lemma range_arcPath_subset (PJc : ℝ → ℝ × ℝ) {sl sm : ℝ} {l m : ℝ × ℝ}
    (hcont : Continuous PJc) (hsl : PJc sl = l) (hsm : PJc sm = m)
    (hslI : sl ∈ Set.Ioo (-1 : ℝ) 1) (hsmI : sm ∈ Set.Ioo (-1 : ℝ) 1) :
    Set.range (arcPath PJc sl sm l m hcont hsl hsm) ⊆ PJc '' Set.Ioo (-1 : ℝ) 1 := by
  rintro p ⟨u, rfl⟩
  refine ⟨AffineMap.lineMap sl sm (u : ℝ), ?_, rfl⟩
  have hmem : AffineMap.lineMap sl sm (u : ℝ) ∈ segment ℝ sl sm := by
    rw [segment_eq_image_lineMap]
    exact ⟨(u : ℝ), u.2, rfl⟩
  exact (convex_Ioo (-1) 1).segment_subset hslI hsmI hmem

/-- The segment from `l` to `d = (0,-2)` meets the second arc `Jd`. -/
theorem exists_inter_segment_ld_Jd
    (γ : Circle → ℝ × ℝ) (hsub : Set.range γ ⊆ Work.RPB1a.Caratheodory.Brouwer.rect)
    (Jc Jd : Set (ℝ × ℝ)) (PJc PJd : ℝ → ℝ × ℝ)
    (hPJc_cont : Continuous PJc) (hPJd_cont : Continuous PJd)
    (hPJc_inj : Set.InjOn PJc (Set.Icc (-1 : ℝ) 1))
    (hPJd_inj : Set.InjOn PJd (Set.Icc (-1 : ℝ) 1))
    (hPJc_left : PJc (-1) = ((-1 : ℝ), (0 : ℝ)))
    (hPJc_right : PJc 1 = ((1 : ℝ), (0 : ℝ)))
    (hPJd_left : PJd (-1) = ((-1 : ℝ), (0 : ℝ)))
    (hPJd_right : PJd 1 = ((1 : ℝ), (0 : ℝ)))
    (hPJc_mem : ∀ t, PJc t ∈ Set.range γ) (hPJd_mem : ∀ t, PJd t ∈ Set.range γ)
    (hJc_eq : PJc '' Set.Icc (-1 : ℝ) 1 = Jc) (hJd_eq : PJd '' Set.Icc (-1 : ℝ) 1 = Jd)
    (hunion : Jc ∪ Jd = Set.range γ)
    (hinter : Jc ∩ Jd = {((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))})
    (m l : ℝ × ℝ) (hmJc : m ∈ Jc) (hm0 : m.1 = 0) (hlJc : l ∈ Jc) (hl0 : l.1 = 0)
    (hmtop : ∀ p ∈ Set.range γ, p.1 = 0 → p.2 ≤ m.2)
    (hlbot : ∀ p ∈ Jc, p.1 = 0 → l.2 ≤ p.2) :
    ∃ q : ℝ × ℝ, q ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) ∧ q ∈ Jd := by
  -- parameters of `l` and `m` along the arc `Jc`
  have hmJc' : m ∈ PJc '' Set.Icc (-1 : ℝ) 1 := by rw [hJc_eq]; exact hmJc
  have hlJc' : l ∈ PJc '' Set.Icc (-1 : ℝ) 1 := by rw [hJc_eq]; exact hlJc
  obtain ⟨sm, hsm_mem, hsm_eq⟩ := hmJc'
  obtain ⟨sl, hsl_mem, hsl_eq⟩ := hlJc'
  -- `sl` and `sm` are interior parameters
  have hsmI : sm ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne hsm_mem.1 (Ne.symm ?_)
      intro hh
      have hm1 : m.1 = -1 := by rw [← hsm_eq, hh, hPJc_left]
      linarith [hm0, hm1]
    · refine lt_of_le_of_ne hsm_mem.2 ?_
      intro hh
      have hm1 : m.1 = 1 := by rw [← hsm_eq, hh, hPJc_right]
      linarith [hm0, hm1]
  have hslI : sl ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne hsl_mem.1 (Ne.symm ?_)
      intro hh
      have hl1 : l.1 = -1 := by rw [← hsl_eq, hh, hPJc_left]
      linarith [hl0, hl1]
    · refine lt_of_le_of_ne hsl_mem.2 ?_
      intro hh
      have hl1 : l.1 = 1 := by rw [← hsl_eq, hh, hPJc_right]
      linarith [hl0, hl1]
  -- `Jc`, `Jd` lie in `range γ` and in `rect`
  have hJc_sub : Jc ⊆ Set.range γ := by
    rw [← hunion]; exact Set.subset_union_left
  have hJd_sub : Jd ⊆ Set.range γ := by
    rw [← hunion]; exact Set.subset_union_right
  have hJc_rect : Jc ⊆ rect := fun p hp => hsub (hJc_sub hp)
  have hl_rect : l ∈ rect := hJc_rect hlJc
  have hm_rect : m ∈ rect := hJc_rect hmJc
  -- the three pieces of the broken path `d ~ l + (Jc arc from l to m) + m ~ c`
  let P1 : Path ((0 : ℝ), (-2 : ℝ)) l := Path.segment _ _
  let P2 : Path l m := arcPath PJc sl sm l m hPJc_cont hsl_eq hsm_eq
  let P3 : Path m ((0 : ℝ), (2 : ℝ)) := Path.segment _ _
  let q : Path ((0 : ℝ), (-2 : ℝ)) ((0 : ℝ), (2 : ℝ)) := P1.trans (P2.trans P3)
  let v : ℝ → ℝ × ℝ := fun t => q.extend ((t + 1) / 2)
  have hP2range : Set.range P2 ⊆ PJc '' Set.Ioo (-1 : ℝ) 1 :=
    range_arcPath_subset PJc hPJc_cont hsl_eq hsm_eq hslI hsmI
  have hrange_v : Set.range v = Set.range q := by
    apply Set.Subset.antisymm
    · rintro p ⟨t, rfl⟩
      have hmem : q.extend ((t + 1) / 2) ∈ Set.range q.extend := ⟨(t + 1) / 2, rfl⟩
      rwa [Path.extend_range q] at hmem
    · rintro p ⟨s, hs⟩
      refine ⟨2 * (s : ℝ) - 1, ?_⟩
      show q.extend (((2 * (s : ℝ) - 1) + 1) / 2) = p
      have h2 : ((2 * (s : ℝ) - 1) + 1) / 2 = (s : ℝ) := by ring
      rw [h2, Path.extend_extends' q s, hs]
  have hrange_q : Set.range q ⊆ Set.range P1 ∪ Set.range P2 ∪ Set.range P3 := by
    have hq : q = P1.trans (P2.trans P3) := rfl
    rw [hq, Path.trans_range P1 (P2.trans P3), Path.trans_range P2 P3]
    intro p hp
    simp only [Set.mem_union] at hp ⊢
    tauto
  have hv_cont : Continuous v := by
    show Continuous (fun t : ℝ => q.extend ((t + 1) / 2))
    exact q.continuous_extend.comp (by fun_prop)
  have hv_neg : v (-1) = ((0 : ℝ), (-2 : ℝ)) := by
    show q.extend (((-1 : ℝ) + 1) / 2) = _
    have h : ((-1 : ℝ) + 1) / 2 = 0 := by norm_num
    rw [h, Path.extend_zero]
  have hv_pos : v 1 = ((0 : ℝ), (2 : ℝ)) := by
    show q.extend (((1 : ℝ) + 1) / 2) = _
    have h : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
    rw [h, Path.extend_one]
  -- the range of the pieces
  have hP1seg : Set.range P1 ⊆ segment ℝ ((0 : ℝ), (-2 : ℝ)) l := by
    have h : P1 = Path.segment ((0 : ℝ), (-2 : ℝ)) l := rfl
    rw [h, Path.range_segment]
  have hP3seg : Set.range P3 ⊆ segment ℝ m ((0 : ℝ), (2 : ℝ)) := by
    have h : P3 = Path.segment m ((0 : ℝ), (2 : ℝ)) := rfl
    rw [h, Path.range_segment]
  have hd_rect : ((0 : ℝ), (-2 : ℝ)) ∈ rect := by norm_num [mem_rect]
  have hc_rect : ((0 : ℝ), (2 : ℝ)) ∈ rect := by norm_num [mem_rect]
  have hrange_v_rect : Set.range v ⊆ rect := by
    intro p hp
    rw [hrange_v] at hp
    rcases hrange_q hp with h12 | h3
    · rcases h12 with h1 | h2
      · exact rect_convex.segment_subset hd_rect hl_rect (hP1seg h1)
      · have hp2 : p ∈ PJc '' Set.Icc (-1 : ℝ) 1 :=
          Set.image_mono Set.Ioo_subset_Icc_self (hP2range h2)
        exact hJc_rect (by rw [← hJc_eq]; exact hp2)
    · exact rect_convex.segment_subset hm_rect hc_rect (hP3seg h3)
  -- crossing lemma
  obtain ⟨s, _hs_mem, t, _ht_mem, hst⟩ :=
    crossing_lemma_rect_of_Icc hPJd_cont hv_cont
      (fun t _ => hsub (hPJd_mem t))
      (fun t _ => hrange_v_rect ⟨t, rfl⟩)
      (by rw [hPJd_left])
      (by rw [hPJd_right])
      (by rw [hv_neg])
      (by rw [hv_pos])
  have hpJd : PJd s ∈ Jd := by rw [← hJd_eq]; exact ⟨s, _hs_mem, rfl⟩
  have hvt_q : v t ∈ Set.range q := by rw [← hrange_v]; exact ⟨t, rfl⟩
  -- case analysis on the piece of the path containing the intersection point
  have hvt_Jd : v t ∈ Jd := by rw [← hst]; exact hpJd
  have hvt_cases : v t ∈ Set.range P1 ∨ v t ∈ Set.range P2 ∨ v t ∈ Set.range P3 := by
    rcases hrange_q hvt_q with h12 | h3
    · rcases h12 with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  rcases hvt_cases with h1 | h2 | h3
  · -- the intersection lies on the first segment `d ~ l`: this is the desired conclusion
    have hp1 : v t ∈ segment ℝ ((0 : ℝ), (-2 : ℝ)) l := hP1seg h1
    refine ⟨v t, ?_, hvt_Jd⟩
    rw [← segment_symm ℝ ((0 : ℝ), (-2 : ℝ)) l]
    exact hp1
  · -- the intersection lies on the arc `Jc`; but `Jc ∩ Jd = {a, b}` and the arc avoids `a, b`
    obtain ⟨w, hwIoo, hw_eq⟩ := hP2range h2
    have hwIcc : w ∈ Set.Icc (-1 : ℝ) 1 := ⟨hwIoo.1.le, hwIoo.2.le⟩
    have hwt_Jc : v t ∈ Jc := by
      rw [← hw_eq, ← hJc_eq]
      exact ⟨w, hwIcc, rfl⟩
    have hmem : v t ∈ ({((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
      rw [← hinter]; exact ⟨hwt_Jc, hvt_Jd⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hneg1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hpos1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
    rcases hmem with hmem | hmem
    · have : w = -1 := by
        apply hPJc_inj hwIcc hneg1
        rw [hw_eq, hmem, hPJc_left]
      linarith [hwIoo.1, this]
    · have : w = 1 := by
        apply hPJc_inj hwIcc hpos1
        rw [hw_eq, hmem, hPJc_right]
      linarith [hwIoo.2, this]
  · -- the intersection lies on the last segment `m ~ c`, forcing `v t = m`, impossible
    have hp3 : v t ∈ segment ℝ m ((0 : ℝ), (2 : ℝ)) := hP3seg h3
    obtain ⟨a1, b1, ha1, hb1, hab, hsum⟩ := hp3
    have hc1 : ((0 : ℝ), (2 : ℝ)).1 = 0 := rfl
    have hc2 : ((0 : ℝ), (2 : ℝ)).2 = 2 := rfl
    have hfst : (v t).1 = 0 := by
      rw [← hsum, Prod.fst_add, Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul,
        hm0, hc1]
      ring
    have hge2 : m.2 ≤ (v t).2 := by
      have h2eq : (v t).2 = a1 * m.2 + b1 * 2 := by
        rw [← hsum, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul, hc2]
      rw [h2eq]
      have hm2 : m.2 ≤ 2 := (mem_rect.mp hm_rect).2.2.2
      nlinarith [ha1, hb1, hab, hm2]
    have hle2 : (v t).2 ≤ m.2 := hmtop (v t) (hJd_sub hvt_Jd) hfst
    have hvt_eq_m : v t = m := Prod.ext (by rw [hfst, hm0]) (le_antisymm hle2 hge2)
    have hm_mem : m ∈ ({((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
      rw [← hinter]; exact ⟨hmJc, by rw [← hvt_eq_m]; exact hvt_Jd⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_mem
    rcases hm_mem with hm_mem | hm_mem
    · have : m.1 = -1 := by rw [hm_mem]
      linarith [hm0, this]
    · have : m.1 = 1 := by rw [hm_mem]
      linarith [hm0, this]

end Work.RPB1a.Caratheodory.Brouwer
