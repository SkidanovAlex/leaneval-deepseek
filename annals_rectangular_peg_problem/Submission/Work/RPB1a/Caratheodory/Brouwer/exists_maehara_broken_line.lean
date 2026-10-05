import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_exp_shift
import Submission.Work.RPB1a.Caratheodory.Brouwer.exp_arc_cover
import Submission.Work.RPB1a.Caratheodory.Brouwer.exp_arc_inter
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_inter_segment_ld_Jd
import Submission.Work.RPB1a.Caratheodory.Brouwer.not_isBounded_componentIn_above
import Submission.Work.RPB1a.Caratheodory.Brouwer.not_isBounded_componentIn_below
import Submission.Work.RPB1a.Caratheodory.Brouwer.mem_connectedComponentIn_midpoint

set_option autoImplicit false

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric
open scoped Topology

/-! ### Two elementary helpers -/

/-- Membership in a vertical segment. -/
theorem maehara_mem_segment_vert {a b : ℝ} (hab : a ≤ b) {p : ℝ × ℝ} :
    p ∈ segment ℝ ((0 : ℝ), a) ((0 : ℝ), b) ↔ p.1 = 0 ∧ a ≤ p.2 ∧ p.2 ≤ b := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨h1, h2⟩ := hθ
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine ⟨by ring, ?_, ?_⟩ <;> nlinarith [h1, h2]
  · rintro ⟨h1, h2, h3⟩
    have hf : Continuous fun θ : ℝ => (1 - θ) * a + θ * b := by fun_prop
    have hsub := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      (f := fun θ : ℝ => (1 - θ) * a + θ * b) hf.continuousOn
    have hmem : p.2 ∈ Set.Icc ((1 - 0) * a + 0 * b) ((1 - 1) * a + 1 * b) := by
      constructor <;> linarith [h2, h3]
    obtain ⟨θ, hθ, hθeq⟩ := hsub hmem
    refine ⟨θ, hθ, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; simp [h1]
    · simpa using hθeq

/-- The convex combination `u + (v - u) * s` of two points of `(-1,1)` with `s ∈ [0,1]` is again
in `(-1,1)`. -/
theorem maehara_convex_mem {u v s : ℝ} (hu1 : -1 < u) (hu2 : u < 1) (hv1 : -1 < v) (hv2 : v < 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    -1 < u + (v - u) * s ∧ u + (v - u) * s < 1 := by
  constructor
  · have h1 : 0 ≤ (1 - s) * (u + 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ s * (v + 1) := mul_nonneg hs0 (by linarith)
    nlinarith
  · have h1 : 0 ≤ (1 - s) * (1 - u) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ s * (1 - v) := mul_nonneg hs0 (by linarith)
    nlinarith

/-! ### The broken line, given the two arcs -/

/-- **The Maehara broken line**, assembled from the two arcs `Jc`, `Jd` of the curve, the topmost
point `m` of the curve on the vertical line `x = 0` and the remaining auxiliary points.  This is the
technical heart of `exists_maehara_broken_line`; the existence of the arcs and of `m` is supplied by
the caller. -/
theorem maehara_broken_line_of_arcs
    (γ : Circle → ℝ × ℝ) (hsub : Set.range γ ⊆ rect)
    (Jc Jd : Set (ℝ × ℝ)) (PJc PJd : ℝ → ℝ × ℝ) (m : ℝ × ℝ)
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
    (hmJc : m ∈ Jc) (hm0 : m.1 = 0)
    (hmtop : ∀ p ∈ Set.range γ, p.1 = 0 → p.2 ≤ m.2) :
    ∃ (β : ℝ → ℝ × ℝ) (x : ℝ × ℝ),
      Continuous β ∧ β (-1) = ((0 : ℝ), (2 : ℝ)) ∧ β 1 = ((0 : ℝ), (-2 : ℝ)) ∧
      (∀ t, β t ∈ rect) ∧
      (((-1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1) ∧
      (((1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1) ∧
      x ∉ Set.range γ ∧
      (∀ w ∈ β '' Set.Icc (-1 : ℝ) 1, w ∉ Set.range γ →
        w ∈ connectedComponentIn ((Set.range γ)ᶜ) x ∨
        ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) w)) := by
  classical
  -- ## basic containments
  have hJc_sub : Jc ⊆ Set.range γ := by rw [← hunion]; exact subset_union_left
  have hJd_sub : Jd ⊆ Set.range γ := by rw [← hunion]; exact subset_union_right
  have hJc_comp : IsCompact Jc := by
    rw [← hJc_eq]; exact isCompact_Icc.image hPJc_cont
  have hJd_comp : IsCompact Jd := by
    rw [← hJd_eq]; exact isCompact_Icc.image hPJd_cont
  have hmem_rect : ∀ p ∈ Set.range γ, p ∈ rect := fun p hp => hsub hp
  have hp_ge : ∀ p ∈ Set.range γ, (-2 : ℝ) ≤ p.2 := by
    intro p hp
    have h := hsub hp
    rw [mem_rect] at h
    exact h.2.2.1
  have hm_rect : m ∈ rect := hsub (hJc_sub hmJc)
  have hm_le : m.2 ≤ 2 := by
    have h := hm_rect; rw [mem_rect] at h; exact h.2.2.2
  have hm_eq : m = ((0 : ℝ), m.2) := Prod.ext hm0 rfl

  -- ## the bottom point `l` of `Jc ∩ {x = 0}`
  have hcl_ne : (Jc ∩ {p : ℝ × ℝ | p.1 = 0}).Nonempty := ⟨m, hmJc, hm0⟩
  have hcl_comp : IsCompact (Jc ∩ {p : ℝ × ℝ | p.1 = 0}) :=
    hJc_comp.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨l, hl_mem, hl_min⟩ := hcl_comp.exists_isMinOn hcl_ne continuous_snd.continuousOn
  have hlJc : l ∈ Jc := hl_mem.1
  have hl0 : l.1 = 0 := hl_mem.2
  have hlbot : ∀ p ∈ Jc, p.1 = 0 → l.2 ≤ p.2 := fun p hp hp0 => hl_min ⟨hp, hp0⟩
  have hl_rect : l ∈ rect := hsub (hJc_sub hlJc)
  have hl_ge : (-2 : ℝ) ≤ l.2 := by
    have h := hl_rect; rw [mem_rect] at h; exact h.2.2.1
  have hl_eq : l = ((0 : ℝ), l.2) := Prod.ext hl0 rfl
  have hl_not_pair : l ∉ ({((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
    intro h
    rcases h with h | h
    · have : l.1 = -1 := by rw [h]
      linarith [hl0]
    · have : l.1 = 1 := by rw [h]
      linarith [hl0]
  have hl_not_Jd : l ∉ Jd := by
    intro hld
    exact hl_not_pair (hinter ▸ ⟨hlJc, hld⟩)

  -- ## the segment `ld` meets `Jd`
  obtain ⟨q, hq_seg, hq_Jd⟩ := exists_inter_segment_ld_Jd γ hsub Jc Jd PJc PJd
    hPJc_cont hPJd_cont hPJc_inj hPJd_inj hPJc_left hPJc_right hPJd_left hPJd_right
    hPJc_mem hPJd_mem hJc_eq hJd_eq hunion hinter m l hmJc hm0 hlJc hl0 hmtop hlbot

  -- ## the top and bottom points `k`, `j` of `ld ∩ Jd`
  have hld_comp : IsCompact (segment ℝ l ((0 : ℝ), (-2 : ℝ))) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image
      (by fun_prop : Continuous fun θ : ℝ => (1 - θ) • l + θ • ((0 : ℝ), (-2 : ℝ)))
  have hSd_comp : IsCompact (segment ℝ l ((0 : ℝ), (-2 : ℝ)) ∩ Jd) := hld_comp.inter hJd_comp
  have hSd_ne : (segment ℝ l ((0 : ℝ), (-2 : ℝ)) ∩ Jd).Nonempty := ⟨q, hq_seg, hq_Jd⟩
  obtain ⟨k, hk_mem, hk_max⟩ := hSd_comp.exists_isMaxOn hSd_ne continuous_snd.continuousOn
  obtain ⟨j, hj_mem, hj_min⟩ := hSd_comp.exists_isMinOn hSd_ne continuous_snd.continuousOn
  have hk_seg : k ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) := hk_mem.1
  have hkJd : k ∈ Jd := hk_mem.2
  have hj_seg : j ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) := hj_mem.1
  have hjJd : j ∈ Jd := hj_mem.2
  have hkmax : ∀ p ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) ∩ Jd, p.2 ≤ k.2 := fun p hp => hk_max hp
  have hjmin : ∀ p ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) ∩ Jd, j.2 ≤ p.2 := fun p hp => hj_min hp
  have hseg_facts : ∀ p ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)),
      p.1 = 0 ∧ (-2 : ℝ) ≤ p.2 ∧ p.2 ≤ l.2 := by
    intro p hp
    rw [segment_eq_image] at hp
    rw [hl_eq] at hp
    obtain ⟨θ, hθ, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := hθ
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine ⟨by ring, ?_, ?_⟩ <;> nlinarith [hl_ge, h1, h2]
  have hk_eq : k = ((0 : ℝ), k.2) := Prod.ext (hseg_facts k hk_seg).1 rfl
  have hj_eq : j = ((0 : ℝ), j.2) := Prod.ext (hseg_facts j hj_seg).1 rfl
  have hk0 : k.1 = 0 := (hseg_facts k hk_seg).1
  have hk_ge : (-2 : ℝ) ≤ k.2 := (hseg_facts k hk_seg).2.1
  have hk_le_l : k.2 ≤ l.2 := (hseg_facts k hk_seg).2.2
  have hj0 : j.1 = 0 := (hseg_facts j hj_seg).1
  have hj_ge : (-2 : ℝ) ≤ j.2 := (hseg_facts j hj_seg).2.1
  have hj_le_l : j.2 ≤ l.2 := (hseg_facts j hj_seg).2.2
  have hkl_lt : k.2 < l.2 := by
    rcases lt_or_eq_of_le hk_le_l with h | h
    · exact h
    · exfalso
      have hkeq : k = l := Prod.ext (by rw [hk0, hl0]) h
      exact hl_not_Jd (hkeq ▸ hkJd)

  -- ## the curve on the line `x = 0` lies between `j` and `m`
  have hkey : ∀ p ∈ Set.range γ, p.1 = 0 → j.2 ≤ p.2 ∧ p.2 ≤ m.2 := by
    intro p hp hp0
    refine ⟨?_, hmtop p hp hp0⟩
    have hpU : p ∈ Jc ∪ Jd := by rw [hunion]; exact hp
    rcases hpU with hpJc | hpJd
    · linarith [hlbot p hpJc hp0, hj_le_l]
    · by_cases hpl : p.2 ≤ l.2
      · have hp_seg : p ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) := by
          rw [hl_eq, segment_symm]
          exact (maehara_mem_segment_vert hl_ge).mpr ⟨hp0, hp_ge p hp, hpl⟩
        linarith [hjmin p ⟨hp_seg, hpJd⟩]
      · linarith
  have hfree_mid : ∀ p ∈ Set.range γ, p.1 = 0 → k.2 < p.2 → p.2 < l.2 → False := by
    intro p hp hp0 hpk hpl
    have hpU : p ∈ Jc ∪ Jd := by rw [hunion]; exact hp
    rcases hpU with hpJc | hpJd
    · linarith [hlbot p hpJc hp0]
    · have hp_seg : p ∈ segment ℝ l ((0 : ℝ), (-2 : ℝ)) := by
        rw [hl_eq, segment_symm]
        exact (maehara_mem_segment_vert hl_ge).mpr ⟨hp0, hp_ge p hp, le_of_lt hpl⟩
      linarith [hkmax p ⟨hp_seg, hpJd⟩]

  -- ## parameters of `m`, `l` on `Jc`
  have hmJc' : m ∈ PJc '' Set.Icc (-1 : ℝ) 1 := by rw [hJc_eq]; exact hmJc
  obtain ⟨μm, hμm_mem, hμm_eq⟩ := hmJc'
  have hlJc' : l ∈ PJc '' Set.Icc (-1 : ℝ) 1 := by rw [hJc_eq]; exact hlJc
  obtain ⟨νl, hνl_mem, hνl_eq⟩ := hlJc'
  have hμm_gt : (-1 : ℝ) < μm := by
    rcases lt_or_eq_of_le hμm_mem.1 with h | h
    · exact h
    · exfalso
      have : m = ((-1 : ℝ), (0 : ℝ)) := by rw [← hμm_eq, ← h]; exact hPJc_left
      linarith [hm0, congrArg Prod.fst this]
  have hμm_lt : μm < 1 := by
    rcases lt_or_eq_of_le hμm_mem.2 with h | h
    · exact h
    · exfalso
      have : m = ((1 : ℝ), (0 : ℝ)) := by rw [← hμm_eq, h]; exact hPJc_right
      linarith [hm0, congrArg Prod.fst this]
  have hνl_gt : (-1 : ℝ) < νl := by
    rcases lt_or_eq_of_le hνl_mem.1 with h | h
    · exact h
    · exfalso
      have : l = ((-1 : ℝ), (0 : ℝ)) := by rw [← hνl_eq, ← h]; exact hPJc_left
      linarith [hl0, congrArg Prod.fst this]
  have hνl_lt : νl < 1 := by
    rcases lt_or_eq_of_le hνl_mem.2 with h | h
    · exact h
    · exfalso
      have : l = ((1 : ℝ), (0 : ℝ)) := by rw [← hνl_eq, h]; exact hPJc_right
      linarith [hl0, congrArg Prod.fst this]

  -- ## parameters of `k`, `j` on `Jd`
  have hkJd' : k ∈ PJd '' Set.Icc (-1 : ℝ) 1 := by rw [hJd_eq]; exact hkJd
  obtain ⟨κ, hκ_mem, hκ_eq⟩ := hkJd'
  have hjJd' : j ∈ PJd '' Set.Icc (-1 : ℝ) 1 := by rw [hJd_eq]; exact hjJd
  obtain ⟨ι, hι_mem, hι_eq⟩ := hjJd'
  have hκ_gt : (-1 : ℝ) < κ := by
    rcases lt_or_eq_of_le hκ_mem.1 with h | h
    · exact h
    · exfalso
      have : k = ((-1 : ℝ), (0 : ℝ)) := by rw [← hκ_eq, ← h]; exact hPJd_left
      linarith [hk0, congrArg Prod.fst this]
  have hκ_lt : κ < 1 := by
    rcases lt_or_eq_of_le hκ_mem.2 with h | h
    · exact h
    · exfalso
      have : k = ((1 : ℝ), (0 : ℝ)) := by rw [← hκ_eq, h]; exact hPJd_right
      linarith [hk0, congrArg Prod.fst this]
  have hι_gt : (-1 : ℝ) < ι := by
    rcases lt_or_eq_of_le hι_mem.1 with h | h
    · exact h
    · exfalso
      have : j = ((-1 : ℝ), (0 : ℝ)) := by rw [← hι_eq, ← h]; exact hPJd_left
      linarith [hj0, congrArg Prod.fst this]
  have hι_lt : ι < 1 := by
    rcases lt_or_eq_of_le hι_mem.2 with h | h
    · exact h
    · exfalso
      have : j = ((1 : ℝ), (0 : ℝ)) := by rw [← hι_eq, h]; exact hPJd_right
      linarith [hj0, congrArg Prod.fst this]

  -- ## the five pieces of the broken line
  let arcML : Path m l := Path.ofLine
    (f := fun t : ℝ => PJc (μm + (νl - μm) * t))
    ((hPJc_cont.comp (by fun_prop)).continuousOn)
    (by simp [hμm_eq])
    (by show PJc (μm + (νl - μm) * (1 : ℝ)) = l
        rw [show μm + (νl - μm) * (1 : ℝ) = νl by ring]
        exact hνl_eq)
  let arcKJ : Path k j := Path.ofLine
    (f := fun t : ℝ => PJd (κ + (ι - κ) * t))
    ((hPJd_cont.comp (by fun_prop)).continuousOn)
    (by simp [hκ_eq])
    (by show PJd (κ + (ι - κ) * (1 : ℝ)) = j
        rw [show κ + (ι - κ) * (1 : ℝ) = ι by ring]
        exact hι_eq)
  have harcML_mem : ∀ t, arcML t ∈ Set.range γ := by
    intro t
    show PJc (μm + (νl - μm) * (t : ℝ)) ∈ Set.range γ
    exact hPJc_mem _
  have harcKJ_mem : ∀ t, arcKJ t ∈ Set.range γ := by
    intro t
    show PJd (κ + (ι - κ) * (t : ℝ)) ∈ Set.range γ
    exact hPJd_mem _
  have harcML_sub : Set.range (⇑arcML) ⊆ Set.range γ := fun z ⟨u, hu⟩ => hu ▸ harcML_mem u
  have harcKJ_sub : Set.range (⇑arcKJ) ⊆ Set.range γ := fun z ⟨u, hu⟩ => hu ▸ harcKJ_mem u
  have harcML_ne_a : ∀ t, arcML t ≠ ((-1 : ℝ), (0 : ℝ)) := by
    intro t h
    obtain ⟨hlow, hhigh⟩ := maehara_convex_mem hμm_gt hμm_lt hνl_gt hνl_lt t.2.1 t.2.2
    have hmem : μm + (νl - μm) * (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_of_lt hlow, le_of_lt hhigh⟩
    have heq : PJc (μm + (νl - μm) * (t : ℝ)) = PJc (-1) := by
      rw [hPJc_left]; exact h
    exact absurd (hPJc_inj hmem (by norm_num) heq) (by linarith)
  have harcML_ne_b : ∀ t, arcML t ≠ ((1 : ℝ), (0 : ℝ)) := by
    intro t h
    obtain ⟨hlow, hhigh⟩ := maehara_convex_mem hμm_gt hμm_lt hνl_gt hνl_lt t.2.1 t.2.2
    have hmem : μm + (νl - μm) * (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_of_lt hlow, le_of_lt hhigh⟩
    have heq : PJc (μm + (νl - μm) * (t : ℝ)) = PJc 1 := by
      rw [hPJc_right]; exact h
    exact absurd (hPJc_inj hmem (by norm_num) heq) (by linarith)
  have harcKJ_ne_a : ∀ t, arcKJ t ≠ ((-1 : ℝ), (0 : ℝ)) := by
    intro t h
    obtain ⟨hlow, hhigh⟩ := maehara_convex_mem hκ_gt hκ_lt hι_gt hι_lt t.2.1 t.2.2
    have hmem : κ + (ι - κ) * (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_of_lt hlow, le_of_lt hhigh⟩
    have heq : PJd (κ + (ι - κ) * (t : ℝ)) = PJd (-1) := by
      rw [hPJd_left]; exact h
    exact absurd (hPJd_inj hmem (by norm_num) heq) (by linarith)
  have harcKJ_ne_b : ∀ t, arcKJ t ≠ ((1 : ℝ), (0 : ℝ)) := by
    intro t h
    obtain ⟨hlow, hhigh⟩ := maehara_convex_mem hκ_gt hκ_lt hι_gt hι_lt t.2.1 t.2.2
    have hmem : κ + (ι - κ) * (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_of_lt hlow, le_of_lt hhigh⟩
    have heq : PJd (κ + (ι - κ) * (t : ℝ)) = PJd 1 := by
      rw [hPJd_right]; exact h
    exact absurd (hPJd_inj hmem (by norm_num) heq) (by linarith)

  -- ## the vertical segment characterisations
  have hseg_top : ∀ z ∈ segment ℝ ((0 : ℝ), (2 : ℝ)) m,
      z.1 = 0 ∧ m.2 ≤ z.2 ∧ z.2 ≤ 2 := by
    intro z hz
    rw [hm_eq, segment_symm] at hz
    exact (maehara_mem_segment_vert hm_le).mp hz
  have hseg_mid : ∀ z ∈ segment ℝ l k, z.1 = 0 ∧ k.2 ≤ z.2 ∧ z.2 ≤ l.2 := by
    intro z hz
    rw [hl_eq, hk_eq, segment_symm] at hz
    exact (maehara_mem_segment_vert hk_le_l).mp hz
  have hseg_bot : ∀ z ∈ segment ℝ j ((0 : ℝ), (-2 : ℝ)),
      z.1 = 0 ∧ (-2 : ℝ) ≤ z.2 ∧ z.2 ≤ j.2 := by
    intro z hz
    rw [hj_eq, segment_symm] at hz
    exact (maehara_mem_segment_vert hj_ge).mp hz

  -- ## the broken line
  let p : Path ((0 : ℝ), (2 : ℝ)) ((0 : ℝ), (-2 : ℝ)) :=
    (Path.segment ((0 : ℝ), (2 : ℝ)) m).trans
      (arcML.trans ((Path.segment l k).trans (arcKJ.trans (Path.segment j ((0 : ℝ), (-2 : ℝ))))))
  let β : ℝ → ℝ × ℝ := fun t => p.extend t
  have hβcont : Continuous β := p.continuous_extend
  have hβsrc : β (-1) = ((0 : ℝ), (2 : ℝ)) := by
    show p.extend (-1) = _
    rw [Path.extend_of_le_zero p (by norm_num)]
  have hβtgt : β 1 = ((0 : ℝ), (-2 : ℝ)) := by
    show p.extend 1 = _
    rw [Path.extend_of_one_le p le_rfl]
  have hβimg : β '' Set.Icc (-1 : ℝ) 1 = Set.range (⇑p) :=
    Path.image_extend_of_subset p (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hrange_p : Set.range (⇑p) =
      segment ℝ ((0 : ℝ), (2 : ℝ)) m ∪
        (Set.range (⇑arcML) ∪
          (segment ℝ l k ∪ (Set.range (⇑arcKJ) ∪ segment ℝ j ((0 : ℝ), (-2 : ℝ))))) := by
    simp only [p, Path.trans_range, Path.range_segment]
  have hc_rect : ((0 : ℝ), (2 : ℝ)) ∈ rect := by rw [mem_rect]; norm_num
  have hd_rect : ((0 : ℝ), (-2 : ℝ)) ∈ rect := by rw [mem_rect]; norm_num
  have hk_rect : k ∈ rect := hsub (hJd_sub hkJd)
  have hj_rect : j ∈ rect := hsub (hJd_sub hjJd)
  have hp_rect : ∀ u : unitInterval, p u ∈ rect := by
    intro u
    have hmem : p u ∈ Set.range (⇑p) := ⟨u, rfl⟩
    rw [hrange_p] at hmem
    rcases hmem with h | h | h | h | h
    · exact rect_convex.segment_subset hc_rect hm_rect h
    · obtain ⟨u', hu'⟩ := h
      exact hsub (hu' ▸ harcML_mem u')
    · exact rect_convex.segment_subset hl_rect hk_rect h
    · obtain ⟨u', hu'⟩ := h
      exact hsub (hu' ▸ harcKJ_mem u')
    · exact rect_convex.segment_subset hj_rect hd_rect h
  have hβrect : ∀ t, β t ∈ rect := by
    intro t
    rcases le_total t 0 with ht | ht
    · show p.extend t ∈ rect
      rw [Path.extend_of_le_zero p ht]
      exact hc_rect
    · rcases le_total t 1 with ht1 | ht1
      · have hti : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        show p.extend t ∈ rect
        rw [Path.extend_apply p hti]
        exact hp_rect _
      · show p.extend t ∈ rect
        rw [Path.extend_of_one_le p ht1]
        exact hd_rect
  have ha_not : ((-1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1 := by
    rw [hβimg]
    intro hmem
    rw [hrange_p] at hmem
    rcases hmem with h | h | h | h | h
    · linarith [(hseg_top _ h).1]
    · obtain ⟨u, hu⟩ := h
      exact harcML_ne_a u hu
    · linarith [(hseg_mid _ h).1]
    · obtain ⟨u, hu⟩ := h
      exact harcKJ_ne_a u hu
    · linarith [(hseg_bot _ h).1]
  have hb_not : ((1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1 := by
    rw [hβimg]
    intro hmem
    rw [hrange_p] at hmem
    rcases hmem with h | h | h | h | h
    · linarith [(hseg_top _ h).1]
    · obtain ⟨u, hu⟩ := h
      exact harcML_ne_b u hu
    · linarith [(hseg_mid _ h).1]
    · obtain ⟨u, hu⟩ := h
      exact harcKJ_ne_b u hu
    · linarith [(hseg_bot _ h).1]
  refine ⟨β, ((0 : ℝ), (k.2 + l.2) / 2), hβcont, hβsrc, hβtgt, hβrect, ha_not, hb_not, ?_, ?_⟩
  · intro hmem
    exact hfree_mid _ hmem rfl (by linarith) (by linarith)
  · intro w hw hwγ
    rw [hβimg] at hw
    rw [hrange_p] at hw
    rcases hw with h | h | h | h | h
    · -- the piece from `c` down to `m`
      obtain ⟨hw1, hwm, -⟩ := hseg_top _ h
      right
      have hmlt : m.2 < w.2 := by
        rcases lt_or_eq_of_le hwm with hh | hh
        · exact hh
        · exfalso
          have : w = m := Prod.ext (by rw [hw1, hm0]) hh.symm
          exact hwγ (hJc_sub (this ▸ hmJc))
      exact not_isBounded_componentIn_above (Set.range γ) hsub m w
        (fun p hp hp0 => hmtop p hp hp0) hw1 hmlt hwγ
    · obtain ⟨u, hu⟩ := h
      exact absurd (hu ▸ harcML_mem u) hwγ
    · -- the piece from `l` down to `k`
      obtain ⟨hw1, hwk, hwl⟩ := hseg_mid _ h
      have hwlt : k.2 < w.2 := by
        rcases lt_or_eq_of_le hwk with hh | hh
        · exact hh
        · exfalso
          have : w = k := Prod.ext (by rw [hw1, hk0]) hh.symm
          exact hwγ (hJd_sub (this ▸ hkJd))
      have hwlt2 : w.2 < l.2 := by
        rcases lt_or_eq_of_le hwl with hh | hh
        · exact hh
        · exfalso
          have : w = l := Prod.ext (by rw [hw1, hl0]) hh
          exact hwγ (hJc_sub (this ▸ hlJc))
      left
      exact mem_connectedComponentIn_midpoint (Set.range γ) k l w ((0 : ℝ), (k.2 + l.2) / 2)
        hk0 hl0 hkl_lt rfl rfl hw1 hwlt hwlt2 hwγ hfree_mid
    · obtain ⟨u, hu⟩ := h
      exact absurd (hu ▸ harcKJ_mem u) hwγ
    · -- the piece from `j` down to `d`
      obtain ⟨hw1, -, hwj⟩ := hseg_bot _ h
      right
      have hjlt : w.2 < j.2 := by
        rcases lt_or_eq_of_le hwj with hh | hh
        · exact hh
        · exfalso
          have : w = j := Prod.ext (by rw [hw1, hj0]) hh
          exact hwγ (hJd_sub (this ▸ hjJd))
      exact not_isBounded_componentIn_below (Set.range γ) hsub j w
        (fun p hp hp0 => (hkey p hp hp0).1) hw1 hjlt hwγ

/-! ### The Maehara broken line -/

end Work.RPB1a.Caratheodory.Brouwer
