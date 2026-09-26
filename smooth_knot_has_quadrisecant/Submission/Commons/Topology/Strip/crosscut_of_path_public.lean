import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Order.ProjIcc

namespace Commons.Topology.Strip

open Set

/-- **First crossing from below.** If `f` is continuous on `[a,b]`, `f a < c` and `c < f b`, then
there is a *first* point `T ∈ (a,b]` at which `f` reaches the level `c`, i.e. `f T = c` and
`f t < c` for every `t ∈ [a, T)`. -/
theorem first_crossing_up {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a < c) (hb : c < f b) :
    ∃ T : ℝ, a < T ∧ T ≤ b ∧ f T = c ∧ ∀ t, a ≤ t → t < T → f t < c := by
  set S : Set ℝ := Set.Icc a b ∩ f ⁻¹' {c} with hSdef
  have hS_mem : ∀ x, x ∈ S ↔ a ≤ x ∧ x ≤ b ∧ f x = c := by
    intro x
    rw [hSdef]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hxI, hxf⟩ :=
      (intermediate_value_Icc hab hf)
        (show c ∈ Set.Icc (f a) (f b) from ⟨le_of_lt ha, le_of_lt hb⟩)
    exact ⟨x, (hS_mem x).2 ⟨hxI.1, hxI.2, hxf⟩⟩
  have hS_closed : IsClosed S :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_bdd : BddBelow S := ⟨a, fun x hx => ((hS_mem x).1 hx).1⟩
  have hT_mem : sInf S ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd
  have hfT : f (sInf S) = c := ((hS_mem _).1 hT_mem).2.2
  have ha_le_T : a ≤ sInf S := le_csInf hS_nonempty (fun x hx => ((hS_mem x).1 hx).1)
  have hT_le_b : sInf S ≤ b := by
    obtain ⟨x, hx⟩ := hS_nonempty
    exact le_trans (csInf_le hS_bdd hx) ((hS_mem x).1 hx).2.1
  refine ⟨sInf S, ?_, hT_le_b, hfT, ?_⟩
  · rcases lt_or_eq_of_le ha_le_T with h | h
    · exact h
    · exact absurd (h ▸ hfT) (ne_of_lt ha)
  · intro t hat htT
    by_contra hcon
    push Not at hcon
    have htb : t ≤ b := le_trans (le_of_lt htT) hT_le_b
    have hcont : ContinuousOn f (Set.Icc a t) := hf.mono (Set.Icc_subset_Icc_right htb)
    obtain ⟨s, hsI, hsf⟩ :=
      (intermediate_value_Icc hat hcont)
        (show c ∈ Set.Icc (f a) (f t) from ⟨le_of_lt ha, hcon⟩)
    have hsS : s ∈ S := (hS_mem s).2 ⟨hsI.1, le_trans hsI.2 htb, hsf⟩
    exact absurd (lt_of_le_of_lt (le_trans (csInf_le hS_bdd hsS) hsI.2) htT) (lt_irrefl _)

/-- **Last crossing from below.** If `f` is continuous on `[a,b]`, `f a < c` and `c < f b`, then
there is a *last* point `T ∈ [a,b)` at which `f` reaches the level `c`, i.e. `f T = c` and
`f t > c` for every `t ∈ (T, b]`. -/
theorem last_crossing_up {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a < c) (hb : c < f b) :
    ∃ T : ℝ, a ≤ T ∧ T < b ∧ f T = c ∧ ∀ t, T < t → t ≤ b → c < f t := by
  set S : Set ℝ := Set.Icc a b ∩ f ⁻¹' {c} with hSdef
  have hS_mem : ∀ x, x ∈ S ↔ a ≤ x ∧ x ≤ b ∧ f x = c := by
    intro x
    rw [hSdef]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hxI, hxf⟩ :=
      (intermediate_value_Icc hab hf)
        (show c ∈ Set.Icc (f a) (f b) from ⟨le_of_lt ha, le_of_lt hb⟩)
    exact ⟨x, (hS_mem x).2 ⟨hxI.1, hxI.2, hxf⟩⟩
  have hS_closed : IsClosed S :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_bdd : BddAbove S := ⟨b, fun x hx => ((hS_mem x).1 hx).2.1⟩
  have hT_mem : sSup S ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd
  have hfT : f (sSup S) = c := ((hS_mem _).1 hT_mem).2.2
  have hT_ge_a : a ≤ sSup S := by
    obtain ⟨x, hx⟩ := hS_nonempty
    exact le_trans ((hS_mem x).1 hx).1 (le_csSup hS_bdd hx)
  have hT_le_b : sSup S ≤ b := csSup_le hS_nonempty (fun x hx => ((hS_mem x).1 hx).2.1)
  have hT_lt_b : sSup S < b := by
    rcases lt_or_eq_of_le hT_le_b with h | h
    · exact h
    · exact absurd (h ▸ hfT).symm (ne_of_lt hb)
  refine ⟨sSup S, hT_ge_a, hT_lt_b, hfT, ?_⟩
  intro t hTt htb
  by_contra hcon
  push Not at hcon
  have hat : a ≤ t := le_trans hT_ge_a (le_of_lt hTt)
  have hcont : ContinuousOn f (Set.Icc t b) := hf.mono (Set.Icc_subset_Icc_left hat)
  obtain ⟨s, hsI, hsf⟩ :=
    (intermediate_value_Icc htb hcont)
      (show c ∈ Set.Icc (f t) (f b) from ⟨hcon, le_of_lt hb⟩)
  have hsS : s ∈ S := (hS_mem s).2 ⟨le_trans hat hsI.1, hsI.2, hsf⟩
  have hbad : sSup S < sSup S :=
    lt_of_lt_of_le hTt (le_trans hsI.1 (le_csSup hS_bdd hsS))
  exact absurd hbad (lt_irrefl _)

/-- A path in the plane from `(0,-1)` to `(0,2)` avoiding `F` yields a strip crosscut: reparametrising
so that the first crossing of the line `{y = 0}` is the new start and the last crossing of the line
`{y = 1}` is the new end. -/
theorem crosscut_of_path_public (F : Set (ℝ × ℝ)) (ρ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hρ0 : ρ 0 = (((0:ℝ),(-1:ℝ)) : ℝ × ℝ)) (hρ1 : ρ 1 = (((0:ℝ),(2:ℝ)) : ℝ × ℝ))
    (hρF : ∀ t, ρ t ∉ F) :
    ∃ γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ),
      (γ 0).2 = 0 ∧ (γ 1).2 = 1 ∧
      (∀ t : Set.Icc (0:ℝ) 1, 0 < (t:ℝ) → (t:ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < 1 ∧ γ t ∉ F) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  -- The `y`-coordinate of `ρ`, extended to all of `ℝ` by clipping the argument to `[0,1]`.
  let g : ℝ → ℝ := fun t => (ρ (Set.projIcc 0 1 h01 t)).2
  have hg_cont : Continuous g := (ρ.continuous.comp continuous_projIcc).snd
  have hg_eq : ∀ (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1),
      g x = (ρ (⟨x, hx⟩ : Set.Icc (0:ℝ) 1)).2 := by
    intro x hx
    simp only [g]
    rw [Set.projIcc_of_mem h01 hx]
  have hg0 : g 0 = -1 := by
    have h1 : g 0 = (ρ (0 : Set.Icc (0:ℝ) 1)).2 := by
      simp only [g]
      rw [Set.projIcc_of_mem h01 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl 0, h01⟩)]
      exact congrArg Prod.snd (congrArg ρ (Subtype.ext rfl))
    rw [h1, hρ0]
  have hg1 : g 1 = 2 := by
    have h1 : g 1 = (ρ (1 : Set.Icc (0:ℝ) 1)).2 := by
      simp only [g]
      rw [Set.projIcc_of_mem h01 (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨h01, le_refl 1⟩)]
      exact congrArg Prod.snd (congrArg ρ (Subtype.ext rfl))
    rw [h1, hρ1]
  -- First time the path reaches height `1`.
  obtain ⟨bT, hbT_pos, hbT_le1, hbT_eq, hbT_first⟩ :=
    first_crossing_up (f := g) (a := 0) (b := 1) (c := 1) h01 hg_cont.continuousOn
      (by rw [hg0]; norm_num) (by rw [hg1]; norm_num)
  -- Last time (before `bT`) the path is at height `0`.
  obtain ⟨aT, haT_nonneg, haT_lt_bT, haT_eq, haT_last⟩ :=
    last_crossing_up (f := g) (a := 0) (b := bT) (c := 0) (le_of_lt hbT_pos)
      hg_cont.continuousOn (by rw [hg0]; norm_num) (by rw [hbT_eq]; norm_num)
  have haT_le_bT : aT ≤ bT := le_of_lt haT_lt_bT
  have hd : 0 ≤ bT - aT := sub_nonneg.mpr haT_le_bT
  have hd' : 0 < bT - aT := sub_pos.mpr haT_lt_bT
  -- The reparametrisation `s t = aT + t * (bT - aT)`.
  let s : Set.Icc (0:ℝ) 1 → ℝ := fun t => aT + (t:ℝ) * (bT - aT)
  have hs_mem : ∀ t : Set.Icc (0:ℝ) 1, s t ∈ Set.Icc (0:ℝ) 1 := by
    intro t
    simp only [s]
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_⟩
    · exact add_nonneg haT_nonneg (mul_nonneg ht0 hd)
    · have h1 : (t:ℝ) * (bT - aT) ≤ 1 * (bT - aT) := mul_le_mul_of_nonneg_right ht1 hd
      nlinarith [h1, haT_le_bT, hbT_le1]
  have hs_cont : Continuous s := by
    simp only [s]
    exact continuous_const.add (continuous_subtype_val.mul continuous_const)
  let γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) :=
    ⟨fun t => ρ ⟨s t, hs_mem t⟩, ρ.continuous.comp (Continuous.subtype_mk hs_cont hs_mem)⟩
  have hγg : ∀ t : Set.Icc (0:ℝ) 1, (γ t).2 = g (s t) := by
    intro t
    have h : (ρ (⟨s t, hs_mem t⟩ : Set.Icc (0:ℝ) 1)).2 = g (s t) :=
      (hg_eq (s t) (hs_mem t)).symm
    simpa only [γ, ContinuousMap.coe_mk] using h
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [hγg 0]
    have hs0 : s 0 = aT := by
      simp only [s]
      rw [show ((0 : Set.Icc (0:ℝ) 1) : ℝ) = 0 from rfl]
      ring
    rw [hs0, haT_eq]
  · rw [hγg 1]
    have hs1 : s 1 = bT := by
      simp only [s]
      rw [show ((1 : Set.Icc (0:ℝ) 1) : ℝ) = 1 from rfl]
      ring
    rw [hs1, hbT_eq]
  · intro t ht0 ht1
    have ht0' : (0:ℝ) < (t:ℝ) := ht0
    have ht1' : (t:ℝ) < 1 := ht1
    have hs_gt : aT < s t := by
      have hpos : 0 < (t:ℝ) * (bT - aT) := mul_pos ht0' hd'
      simp only [s]
      linarith
    have hs_lt : s t < bT := by
      have hlt : (t:ℝ) * (bT - aT) < 1 * (bT - aT) := mul_lt_mul_of_pos_right ht1' hd'
      simp only [s]
      linarith
    have hs_nn : (0:ℝ) ≤ s t := le_trans haT_nonneg (le_of_lt hs_gt)
    refine ⟨?_, ?_, ?_⟩
    · rw [hγg t]
      exact haT_last (s t) hs_gt (le_of_lt hs_lt)
    · rw [hγg t]
      exact hbT_first (s t) hs_nn hs_lt
    · show ρ ⟨s t, hs_mem t⟩ ∉ F
      exact hρF ⟨s t, hs_mem t⟩

end Commons.Topology.Strip