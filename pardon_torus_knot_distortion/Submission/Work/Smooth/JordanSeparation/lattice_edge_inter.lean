import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic

/-!
# Intersections of unit lattice edges

Two unit edges of the scaled lattice `c·(ℤ × ℤ)` meet only in a common endpoint, unless they are
the same set.  This is the local fact behind the injectivity of the polygon parametrisation of a
simple closed lattice walk.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

theorem real_eq_zero_or_one_of_eq_int {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) {m : ℤ}
    (h : t = (m : ℝ)) : t = 0 ∨ t = 1 := by
  have ht0 : (0:ℝ) ≤ (m:ℝ) := by rw [← h]; exact ht.1
  have ht1 : (m:ℝ) ≤ 1 := by rw [← h]; exact ht.2
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast ht0
  have hm1 : m ≤ 1 := by exact_mod_cast ht1
  have : m = 0 ∨ m = 1 := by omega
  rcases this with h0 | h1
  · left; rw [h, h0]; norm_num
  · right; rw [h, h1]; norm_num

theorem real_eq_neg_one_or_zero_or_one_of_eq_int {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) {m : ℤ}
    (h : t = (m : ℝ)) : t = -1 ∨ t = 0 ∨ t = 1 := by
  have ht0 : (-1:ℝ) ≤ (m:ℝ) := by rw [← h]; exact ht.1
  have ht1 : (m:ℝ) ≤ 1 := by rw [← h]; exact ht.2
  have hm0 : (-1 : ℤ) ≤ m := by exact_mod_cast ht0
  have hm1 : m ≤ 1 := by exact_mod_cast ht1
  have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases this with h0 | h0 | h0
  · left; rw [h, h0]; norm_num
  · right; left; rw [h, h0]; norm_num
  · right; right; rw [h, h0]; norm_num

theorem real_eq_zero_or_one_or_two_of_eq_int {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 2) {m : ℤ}
    (h : t = (m : ℝ)) : t = 0 ∨ t = 1 ∨ t = 2 := by
  have ht0 : (0:ℝ) ≤ (m:ℝ) := by rw [← h]; exact ht.1
  have ht1 : (m:ℝ) ≤ 2 := by rw [← h]; exact ht.2
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast ht0
  have hm1 : m ≤ 2 := by exact_mod_cast ht1
  have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases this with h0 | h0 | h0
  · left; rw [h, h0]; norm_num
  · right; left; rw [h, h0]; norm_num
  · right; right; rw [h, h0]; norm_num

/-- The real and imaginary coordinates of a segment membership: for a lattice edge from `p` to `q`
the point `z` has coordinates `p.1 + t (q.1 - p.1)`, `p.2 + t (q.2 - p.2)` with `t ∈ [0,1]`. -/
theorem exists_param_of_mem_segment {p q : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ segment ℝ (gpt p) (gpt q)) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, z = (1-t) • gpt p + t • gpt q ∧
      z.re = (p.1 : ℝ) + t * ((q.1 : ℝ) - (p.1 : ℝ)) ∧
      z.im = (p.2 : ℝ) + t * ((q.2 : ℝ) - (p.2 : ℝ)) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, htz⟩ := hz
  refine ⟨t, ht, htz.symm, ?_, ?_⟩
  · have hh := congrArg Complex.re htz
    simp only [Complex.add_re, Complex.smul_re, gpt, Complex.intCast_re, Complex.intCast_im,
      smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at hh
    linarith [hh]
  · have hh := congrArg Complex.im htz
    simp only [Complex.add_im, Complex.smul_im, gpt, Complex.intCast_re, Complex.intCast_im,
      smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero] at hh
    linarith [hh]

theorem gridStep_ne {p q : ℤ × ℤ} (h : GridStep p q) : p ≠ q := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> intro hpq <;> simp [hpq] at h1 h2

theorem sub_mem_Icc {t s : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    t - s ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩

theorem add_mem_Icc {t s : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    t + s ∈ Set.Icc (0:ℝ) 2 :=
  ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩

theorem segParam_eq_left {p q : ℤ × ℤ} (hpq : GridStep p q) {t : ℝ} :
    (1-t) • gpt p + t • gpt q = gpt p ↔ t = 0 := by
  have hne : gpt q - gpt p ≠ 0 := by
    intro h
    exact gridStep_ne hpq ((gpt_injective (sub_eq_zero.mp h)).symm)
  constructor
  · intro h
    have h2 : t • (gpt q - gpt p) = 0 := by
      have h3 : (1-t) • gpt p + t • gpt q - gpt p = 0 := by rw [h]; abel
      rw [← h3]; module
    rcases smul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · exact absurd h4 hne
  · intro h; rw [h]; simp

theorem segParam_eq_right {p q : ℤ × ℤ} (hpq : GridStep p q) {t : ℝ} :
    (1-t) • gpt p + t • gpt q = gpt q ↔ t = 1 := by
  have hne : gpt p - gpt q ≠ 0 := by
    intro h
    exact gridStep_ne hpq (gpt_injective (sub_eq_zero.mp h))
  constructor
  · intro h
    have h2 : (1-t) • (gpt p - gpt q) = 0 := by
      rw [smul_sub]
      have h3 : (1-t) • gpt p + t • gpt q - gpt q = 0 := by rw [h]; abel
      rw [← h3]; module
    rcases smul_eq_zero.mp h2 with h4 | h4
    · linarith
    · exact absurd h4 hne
  · intro h; rw [h]; simp

theorem gridStep_vert_or_horiz {p q : ℤ × ℤ} (h : GridStep p q) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ((q.1 = p.1 ∧ q.2 = p.2 + s) ∨ (q.2 = p.2 ∧ q.1 = p.1 + s)) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact ⟨1, Or.inl rfl, Or.inl ⟨h1.symm, h2⟩⟩
  · exact ⟨-1, Or.inr rfl, Or.inl ⟨h1.symm, by omega⟩⟩
  · exact ⟨1, Or.inl rfl, Or.inr ⟨h1.symm, h2⟩⟩
  · exact ⟨-1, Or.inr rfl, Or.inr ⟨h1.symm, by omega⟩⟩

/-- Two unit intervals with integer endpoints meet in a common endpoint, unless they are equal. -/
theorem oneD_generic {a1 a2 b1 b2 : ℤ} (ha : a2 = a1 + 1) (hb : b2 = b1 + 1) {x : ℝ}
    (hx1 : (a1:ℝ) ≤ x ∧ x ≤ (a2:ℝ)) (hx2 : (b1:ℝ) ≤ x ∧ x ≤ (b2:ℝ)) :
    (x = (a1:ℝ) ∨ x = (a2:ℝ)) ∧ (x = (b1:ℝ) ∨ x = (b2:ℝ)) ∨ (a1 = b1) := by
  have ha' : (a2:ℝ) = (a1:ℝ) + 1 := by rw [ha]; push_cast; ring
  have hb' : (b2:ℝ) = (b1:ℝ) + 1 := by rw [hb]; push_cast; ring
  have h1 : (b1:ℤ) ≤ a1 + 1 := by
    exact_mod_cast (by linarith [hx2.1, hx1.2, ha'] : (b1:ℝ) ≤ (a1:ℝ) + 1)
  have h2 : (a1:ℤ) ≤ b1 + 1 := by
    exact_mod_cast (by linarith [hx1.1, hx2.2, hb'] : (a1:ℝ) ≤ (b1:ℝ) + 1)
  have hcase : b1 = a1 ∨ b1 = a1 + 1 ∨ a1 = b1 + 1 := by omega
  rcases hcase with h | h | h
  · exact Or.inr h.symm
  · have hxa : x ≤ (a1:ℝ) + 1 := by rw [← ha']; exact hx1.2
    have h2' : (a1:ℝ) + 1 ≤ x :=
      le_trans (by exact_mod_cast (by omega : a1 + 1 ≤ b1)) hx2.1
    have hx : x = (a1:ℝ) + 1 := le_antisymm hxa h2'
    exact Or.inl ⟨Or.inr (by rw [hx]; exact ha'.symm), Or.inl (by rw [hx]; exact_mod_cast h.symm)⟩
  · have hxb : x ≤ (b1:ℝ) + 1 := by rw [← hb']; exact hx2.2
    have h2' : (b1:ℝ) + 1 ≤ x :=
      le_trans (by exact_mod_cast (by omega : b1 + 1 ≤ a1)) hx1.1
    have hx : x = (b1:ℝ) + 1 := le_antisymm hxb h2'
    exact Or.inl ⟨Or.inl (by rw [hx]; exact_mod_cast h.symm), Or.inr (by rw [hx]; exact hb'.symm)⟩

/-- One-dimensional intersection of two unit intervals with integer endpoints. -/
theorem oneD_inter {a b s1 s2 : ℤ} (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1)
    {x : ℝ} (hx1 : (a:ℝ) + (min 0 s1 : ℝ) ≤ x ∧ x ≤ (a:ℝ) + (max 0 s1 : ℝ))
    (hx2 : (b:ℝ) + (min 0 s2 : ℝ) ≤ x ∧ x ≤ (b:ℝ) + (max 0 s2 : ℝ)) :
    ((x = (a:ℝ) ∨ x = (a:ℝ) + s1) ∧ (x = (b:ℝ) ∨ x = (b:ℝ) + s2)) ∨
      (a = b ∧ s1 = s2) ∨ (a = b + s2 ∧ s1 = -s2) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> subst h1 <;> subst h2 <;>
    norm_num at hx1 hx2
  · have h := oneD_generic (a1 := a) (a2 := a + 1) (b1 := b) (b2 := b + 1) rfl rfl
      (by push_cast; exact ⟨by simpa using hx1.1, by simpa using hx1.2⟩)
      (by push_cast; exact ⟨by simpa using hx2.1, by simpa using hx2.2⟩)
    rcases h with ⟨ha, hb⟩ | h
    · exact Or.inl ⟨by simpa using ha, by simpa using hb⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · have h := oneD_generic (a1 := a) (a2 := a + 1) (b1 := b - 1) (b2 := b) rfl (by ring)
      (by push_cast; exact ⟨by simpa using hx1.1, by simpa using hx1.2⟩)
      (by push_cast; exact ⟨by simpa using hx2.1, by simpa using hx2.2⟩)
    rcases h with ⟨ha, hb⟩ | h
    · refine Or.inl ⟨by simpa using ha, ?_⟩
      rcases hb with hh | hh
      · exact Or.inr (by rw [hh]; push_cast; ring)
      · exact Or.inl hh
    · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
  · have h := oneD_generic (a1 := a - 1) (a2 := a) (b1 := b) (b2 := b + 1) (by ring) rfl
      (by push_cast; exact ⟨by simpa using hx1.1, by simpa using hx1.2⟩)
      (by push_cast; exact ⟨by simpa using hx2.1, by simpa using hx2.2⟩)
    rcases h with ⟨ha, hb⟩ | h
    · refine Or.inl ⟨?_, by simpa using hb⟩
      rcases ha with hh | hh
      · exact Or.inr (by rw [hh]; push_cast; ring)
      · exact Or.inl hh
    · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
  · have h := oneD_generic (a1 := a - 1) (a2 := a) (b1 := b - 1) (b2 := b) (by ring) (by ring)
      (by push_cast; exact ⟨by simpa using hx1.1, by simpa using hx1.2⟩)
      (by push_cast; exact ⟨by simpa using hx2.1, by simpa using hx2.2⟩)
    rcases h with ⟨ha, hb⟩ | h
    · refine Or.inl ⟨?_, ?_⟩
      · rcases ha with hh | hh
        · exact Or.inr (by rw [hh]; push_cast; ring)
        · exact Or.inl hh
      · rcases hb with hh | hh
        · exact Or.inr (by rw [hh]; push_cast; ring)
        · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)

theorem mul_signed_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (min 0 s : ℝ) ≤ t * (s:ℝ) ∧ t * (s:ℝ) ≤ (max 0 s : ℝ) := by
  rcases hs with rfl | rfl
  · refine ⟨?_, ?_⟩ <;> norm_num <;> linarith [ht.1, ht.2]
  · refine ⟨?_, ?_⟩ <;> norm_num <;> linarith [ht.1, ht.2]

theorem signed_int {c : ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1) {m : ℤ} (h : c * (s:ℝ) = (m:ℝ))
    (hc : c ∈ Set.Icc (0:ℝ) 1) : c = 0 ∨ c = 1 := by
  rcases hs with rfl | rfl
  · exact real_eq_zero_or_one_of_eq_int (m := m) hc (by simpa using h)
  · refine real_eq_zero_or_one_of_eq_int (m := -m) hc ?_
    have h2 : c = (((-m):ℤ):ℝ) := by
      have h1 : c * ((-1:ℤ):ℝ) = (m:ℝ) := h
      push_cast at h1
      ring_nf at h1
      have hh : c = -((m:ℤ):ℝ) := by linarith [h1]
      rw [hh]; push_cast; ring
    exact h2

theorem eq_gpt_of_coords {p : ℤ × ℤ} {z : ℂ} (hr : z.re = (p.1:ℝ)) (hi : z.im = (p.2:ℝ)) :
    z = gpt p := by
  apply Complex.ext
  · rw [hr]; simp [gpt]
  · rw [hi]; simp [gpt]

theorem lattice_edge_inter {p q p' q' : ℤ × ℤ} (hpq : GridStep p q) (hp'q' : GridStep p' q')
    {z : ℂ} (hz : z ∈ segment ℝ (gpt p) (gpt q) ∩ segment ℝ (gpt p') (gpt q')) :
    ((z = gpt p ∨ z = gpt q) ∧ (z = gpt p' ∨ z = gpt q')) ∨
      (gpt p = gpt p' ∧ gpt q = gpt q') ∨ (gpt p = gpt q' ∧ gpt q = gpt p') := by
  obtain ⟨t, ht, htz, ht1, ht2⟩ := exists_param_of_mem_segment hz.1
  obtain ⟨s, hs, hsz, hs1, hs2⟩ := exists_param_of_mem_segment hz.2
  obtain ⟨s1, hs1', hstep1⟩ := gridStep_vert_or_horiz hpq
  obtain ⟨s2, hs2', hstep2⟩ := gridStep_vert_or_horiz hp'q'
  have keyt0 : z = gpt p ↔ t = 0 := by rw [htz]; exact segParam_eq_left hpq
  have keyt1 : z = gpt q ↔ t = 1 := by rw [htz]; exact segParam_eq_right hpq
  have keys0 : z = gpt p' ↔ s = 0 := by rw [hsz]; exact segParam_eq_left hp'q'
  have keys1 : z = gpt q' ↔ s = 1 := by rw [hsz]; exact segParam_eq_right hp'q'
  have hg : Function.Injective gpt := gpt_injective
  rcases hstep1 with ⟨hA1, hB1⟩ | ⟨hA1, hB1⟩ <;> rcases hstep2 with ⟨hA2, hB2⟩ | ⟨hA2, hB2⟩
  · -- both vertical: q.1 = p.1, q.2 = p.2 + s1; q'.1 = p'.1, q'.2 = p'.2 + s2
    have hzr : z.re = (p.1:ℝ) := by rw [ht1, hA1]; ring
    have hzr' : z.re = (p'.1:ℝ) := by rw [hs1, hA2]; ring
    have hpp1 : (p.1:ℝ) = (p'.1:ℝ) := by linarith [hzr, hzr']
    have hpp1z : p.1 = p'.1 := by exact_mod_cast hpp1
    have hzi : z.im = (p.2:ℝ) + t * (s1:ℝ) := by rw [ht2, hB1]; push_cast; ring
    have hzi' : z.im = (p'.2:ℝ) + s * (s2:ℝ) := by rw [hs2, hB2]; push_cast; ring
    have hb1 : (p.2:ℝ) + (min 0 s1 : ℝ) ≤ z.im ∧ z.im ≤ (p.2:ℝ) + (max 0 s1 : ℝ) := by
      obtain ⟨h1,h2⟩ := mul_signed_mem_Icc ht hs1'
      rw [hzi]; exact ⟨add_le_add (le_refl _) h1, add_le_add (le_refl _) h2⟩
    have hb2 : (p'.2:ℝ) + (min 0 s2 : ℝ) ≤ z.im ∧ z.im ≤ (p'.2:ℝ) + (max 0 s2 : ℝ) := by
      obtain ⟨h1,h2⟩ := mul_signed_mem_Icc hs hs2'
      rw [hzi']; exact ⟨add_le_add (le_refl _) h1, add_le_add (le_refl _) h2⟩
    rcases oneD_inter hs1' hs2' hb1 hb2 with ⟨hz1, hz2⟩ | ⟨hab, hs12⟩ | ⟨hab, hs12⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rcases hz1 with h | h
        · exact Or.inl (eq_gpt_of_coords hzr h)
        · exact Or.inr (eq_gpt_of_coords (by rw [hA1]; exact hzr) (by rw [hB1]; push_cast; exact h))
      · rcases hz2 with h | h
        · exact Or.inl (eq_gpt_of_coords hzr' h)
        · exact Or.inr (eq_gpt_of_coords (by rw [hA2]; exact hzr') (by rw [hB2]; push_cast; exact h))
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [hg.eq_iff]; exact Prod.ext hpp1z hab
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)
  · -- vertical then horizontal
    have hzr : z.re = (p.1:ℝ) := by rw [ht1, hA1]; ring
    have hzr' : z.re = (p'.1:ℝ) + s * (s2:ℝ) := by rw [hs1, hB2]; push_cast; ring
    have hzi : z.im = (p.2:ℝ) + t * (s1:ℝ) := by rw [ht2, hB1]; push_cast; ring
    have hzi' : z.im = (p'.2:ℝ) := by rw [hs2, hA2]; ring
    have ht_int : t = ((s1 * (p'.2 - p.2) : ℤ) : ℝ) := by
      have hc : ((s1 * (p'.2 - p.2) : ℤ) : ℝ) = (s1:ℝ) * ((p'.2:ℝ) - (p.2:ℝ)) := by push_cast; ring
      rw [hc]
      have h : t * (s1:ℝ) = (p'.2:ℝ) - (p.2:ℝ) := by
        rw [hzi] at hzi'; linarith
      rcases hs1' with h1 | h1 <;> rw [h1] at h ⊢ <;> norm_num at h ⊢ <;> nlinarith
    have hs_int : s = ((s2 * (p.1 - p'.1) : ℤ) : ℝ) := by
      have hc : ((s2 * (p.1 - p'.1) : ℤ) : ℝ) = (s2:ℝ) * ((p.1:ℝ) - (p'.1:ℝ)) := by push_cast; ring
      rw [hc]
      have h : s * (s2:ℝ) = (p.1:ℝ) - (p'.1:ℝ) := by
        rw [hzr] at hzr'; linarith
      rcases hs2' with h1 | h1 <;> rw [h1] at h ⊢ <;> norm_num at h ⊢ <;> nlinarith
    have ht01 := real_eq_zero_or_one_of_eq_int ht ht_int
    have hs01 := real_eq_zero_or_one_of_eq_int hs hs_int
    rcases ht01 with h | h <;> rcases hs01 with h' | h'
    · exact Or.inl ⟨Or.inl (keyt0.mpr h), Or.inl (keys0.mpr h')⟩
    · exact Or.inl ⟨Or.inl (keyt0.mpr h), Or.inr (keys1.mpr h')⟩
    · exact Or.inl ⟨Or.inr (keyt1.mpr h), Or.inl (keys0.mpr h')⟩
    · exact Or.inl ⟨Or.inr (keyt1.mpr h), Or.inr (keys1.mpr h')⟩
  · -- horizontal then vertical
    have hzr : z.re = (p.1:ℝ) + t * (s1:ℝ) := by rw [ht1, hB1]; push_cast; ring
    have hzr' : z.re = (p'.1:ℝ) := by rw [hs1, hA2]; ring
    have hzi : z.im = (p.2:ℝ) := by rw [ht2, hA1]; ring
    have hzi' : z.im = (p'.2:ℝ) + s * (s2:ℝ) := by rw [hs2, hB2]; push_cast; ring
    have ht_int : t = ((s1 * (p'.1 - p.1) : ℤ) : ℝ) := by
      have hc : ((s1 * (p'.1 - p.1) : ℤ) : ℝ) = (s1:ℝ) * ((p'.1:ℝ) - (p.1:ℝ)) := by push_cast; ring
      rw [hc]
      have h : t * (s1:ℝ) = (p'.1:ℝ) - (p.1:ℝ) := by
        rw [hzr] at hzr'; linarith
      rcases hs1' with h1 | h1 <;> rw [h1] at h ⊢ <;> norm_num at h ⊢ <;> nlinarith
    have hs_int : s = ((s2 * (p.2 - p'.2) : ℤ) : ℝ) := by
      have hc : ((s2 * (p.2 - p'.2) : ℤ) : ℝ) = (s2:ℝ) * ((p.2:ℝ) - (p'.2:ℝ)) := by push_cast; ring
      rw [hc]
      have h : s * (s2:ℝ) = (p.2:ℝ) - (p'.2:ℝ) := by
        rw [hzi] at hzi'; linarith
      rcases hs2' with h1 | h1 <;> rw [h1] at h ⊢ <;> norm_num at h ⊢ <;> nlinarith
    have ht01 := real_eq_zero_or_one_of_eq_int ht ht_int
    have hs01 := real_eq_zero_or_one_of_eq_int hs hs_int
    rcases ht01 with h | h <;> rcases hs01 with h' | h'
    · exact Or.inl ⟨Or.inl (keyt0.mpr h), Or.inl (keys0.mpr h')⟩
    · exact Or.inl ⟨Or.inl (keyt0.mpr h), Or.inr (keys1.mpr h')⟩
    · exact Or.inl ⟨Or.inr (keyt1.mpr h), Or.inl (keys0.mpr h')⟩
    · exact Or.inl ⟨Or.inr (keyt1.mpr h), Or.inr (keys1.mpr h')⟩
  · -- both horizontal: q.2 = p.2, q.1 = p.1 + s1; q'.2 = p'.2, q'.1 = p'.1 + s2
    have hzi : z.im = (p.2:ℝ) := by rw [ht2, hA1]; ring
    have hzi' : z.im = (p'.2:ℝ) := by rw [hs2, hA2]; ring
    have hpp2 : (p.2:ℝ) = (p'.2:ℝ) := by linarith [hzi, hzi']
    have hpp2z : p.2 = p'.2 := by exact_mod_cast hpp2
    have hzr : z.re = (p.1:ℝ) + t * (s1:ℝ) := by rw [ht1, hB1]; push_cast; ring
    have hzr' : z.re = (p'.1:ℝ) + s * (s2:ℝ) := by rw [hs1, hB2]; push_cast; ring
    have hb1 : (p.1:ℝ) + (min 0 s1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1:ℝ) + (max 0 s1 : ℝ) := by
      obtain ⟨h1,h2⟩ := mul_signed_mem_Icc ht hs1'
      rw [hzr]; exact ⟨add_le_add (le_refl _) h1, add_le_add (le_refl _) h2⟩
    have hb2 : (p'.1:ℝ) + (min 0 s2 : ℝ) ≤ z.re ∧ z.re ≤ (p'.1:ℝ) + (max 0 s2 : ℝ) := by
      obtain ⟨h1,h2⟩ := mul_signed_mem_Icc hs hs2'
      rw [hzr']; exact ⟨add_le_add (le_refl _) h1, add_le_add (le_refl _) h2⟩
    rcases oneD_inter hs1' hs2' hb1 hb2 with ⟨hz1, hz2⟩ | ⟨hab, hs12⟩ | ⟨hab, hs12⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rcases hz1 with h | h
        · exact Or.inl (eq_gpt_of_coords h hzi)
        · exact Or.inr (eq_gpt_of_coords (by rw [hB1]; push_cast; exact h) (by rw [hA1]; exact hzi))
      · rcases hz2 with h | h
        · exact Or.inl (eq_gpt_of_coords h hzi')
        · exact Or.inr (eq_gpt_of_coords (by rw [hB2]; push_cast; exact h) (by rw [hA2]; exact hzi'))
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [hg.eq_iff]; exact Prod.ext hab hpp2z
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)
      · rw [hg.eq_iff]; exact Prod.ext (by omega) (by omega)

end

end Work.Smooth.JordanSeparation