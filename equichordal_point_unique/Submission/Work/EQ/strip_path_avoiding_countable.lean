import Mathlib
import Submission.Work.EQ.isPreconnected_ball_diff_countable

namespace Work.EQ

open Set

/-- A convex combination of two points of an open interval lies in the interval. -/
lemma convex_combo_mem_Ioo {a b x y θ : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : (1 - θ) * x + θ * y ∈ Ioo a b := by
  have hmem : (1 - θ) * x + θ * y ∈ segment ℝ x y := by
    rw [segment_eq_image']
    exact ⟨θ, ⟨h0, h1⟩, by ring⟩
  exact (convex_Ioo a b).segment_subset hx hy hmem

/-- The horizontal slice `{im = c}` of the vertical strip `a < re < b` is uncountable. -/
lemma not_countable_im_strip_slice {a b c : ℝ} (hab : a < b) :
    ¬ ({z : ℂ | z.im = c} ∩ {z : ℂ | z.re ∈ Ioo a b}).Countable := by
  intro hcount
  have hinj : Set.InjOn (fun t : ℝ => Complex.mk t c) (Ioo a b) := by
    intro t₁ _ t₂ _ h
    exact congrArg Complex.re h
  have himg : ((fun t : ℝ => Complex.mk t c) '' Ioo a b).Countable :=
    hcount.mono (by rintro z ⟨t, ht, rfl⟩; exact ⟨rfl, ht⟩)
  have hcountable : (Ioo a b).Countable :=
    Set.countable_of_injective_of_countable_image hinj himg
  have := Cardinal.Real.Ioo_countable_iff.mp hcountable
  linarith

/-- Given `c` different from `u.im` and `v.im`, and `u`, `v` in the vertical strip
`a < re < b`, there is a point `z` of the strip with `z.im = c` such that the closed
segments `[u,z]` (for points of `Q \ {u}`) and `[v,z]` (for points of `Q`) avoid `Q`. -/
lemma exists_good_strip_point {a b c : ℝ} (hab : a < b) {Q : Set ℂ} (hQ : Q.Countable)
    {u v : ℂ} (hu : u.re ∈ Ioo a b) (hv : v.re ∈ Ioo a b) (hvQ : v ∉ Q)
    (hcu : c ≠ u.im) (hcv : c ≠ v.im) :
    ∃ z : ℂ, z.re ∈ Ioo a b ∧ z.im = c ∧
      (∀ d ∈ Q \ {u}, d ∉ segment ℝ u z) ∧ (∀ d ∈ Q, d ∉ segment ℝ v z) := by
  have hbad_u : {z : ℂ | z.im = c ∧ ∃ d ∈ Q \ {u}, d ∈ segment ℝ u z}.Countable :=
    countable_segment_im_slice (hQ.mono (fun x hx => hx.1)) hcu (by simp)
  have hbad_v : {z : ℂ | z.im = c ∧ ∃ d ∈ Q, d ∈ segment ℝ v z}.Countable :=
    countable_segment_im_slice hQ hcv hvQ
  have hnot : ¬ ({z : ℂ | z.im = c} ∩ {z : ℂ | z.re ∈ Ioo a b}).Countable :=
    not_countable_im_strip_slice hab
  have hne : (({z : ℂ | z.im = c} ∩ {z : ℂ | z.re ∈ Ioo a b}) \
      ({z : ℂ | z.im = c ∧ ∃ d ∈ Q \ {u}, d ∈ segment ℝ u z} ∪
       {z : ℂ | z.im = c ∧ ∃ d ∈ Q, d ∈ segment ℝ v z})).Nonempty := by
    by_contra h
    exact hnot ((hbad_u.union hbad_v).mono
      (fun z hz => by by_contra hzb; exact h ⟨z, hz, hzb⟩))
  obtain ⟨z, hzS, hzbad⟩ := hne
  have hznotbad := not_or.mp hzbad
  exact ⟨z, hzS.2, hzS.1,
    (fun d hd hdseg => hznotbad.1 ⟨hzS.1, ⟨d, hd, hdseg⟩⟩),
    (fun d hd hdseg => hznotbad.2 ⟨hzS.1, ⟨d, hd, hdseg⟩⟩)⟩

theorem strip_path_avoiding_countable {a b : ℝ} (hab : a < b) {Q : Set ℂ} (hQ : Q.Countable)
    {u v : ℂ} (hu : a < u.re ∧ u.re < b) (hv : a < v.re ∧ v.re < b) (hvQ : v ∉ Q) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = u ∧ γ 1 = v ∧
      (∀ t ∈ Set.Icc 0 1, a < (γ t).re ∧ (γ t).re < b) ∧
      (∀ t ∈ Set.Ioo 0 1, γ t ∉ Q) := by
  have huI : u.re ∈ Ioo a b := hu
  have hvI : v.re ∈ Ioo a b := hv
  have hcu : max u.im v.im + 1 ≠ u.im := by
    have h : u.im ≤ max u.im v.im := le_max_left _ _
    intro hh; linarith
  have hcv : max u.im v.im + 1 ≠ v.im := by
    have h : v.im ≤ max u.im v.im := le_max_right _ _
    intro hh; linarith
  obtain ⟨z, hzre, hzim, hzu, hzv⟩ :=
    exists_good_strip_point hab hQ huI hvI hvQ hcu hcv
  have hzQ : z ∉ Q := fun hzQ => hzv z hzQ (right_mem_segment ℝ v z)
  -- the open segments to/from `z` avoid `Q`
  have hzu_open : ∀ d ∈ Q, d ∉ openSegment ℝ u z := by
    intro d hd hdopen
    by_cases hdu : d = u
    · rw [hdu] at hdopen
      rw [openSegment_eq_image'] at hdopen
      obtain ⟨θ, hθ, hθeq⟩ := hdopen
      have h0 : θ • (z - u) = 0 := by
        have := congrArg (· - u) hθeq
        simpa using this
      have hzne : θ ≠ 0 := ne_of_gt hθ.1
      have hzu_eq : z = u := by
        have : z - u = 0 := (smul_eq_zero.mp h0).resolve_left hzne
        exact sub_eq_zero.mp this
      rw [hzu_eq] at hzim
      exact hcu hzim.symm
    · have hdseg : d ∈ segment ℝ u z := openSegment_subset_segment ℝ u z hdopen
      exact hzu d ⟨hd, by simpa using hdu⟩ hdseg
  have hzv_open : ∀ d ∈ Q, d ∉ openSegment ℝ z v := by
    intro d hd hdopen
    have hdseg : d ∈ segment ℝ z v := openSegment_subset_segment ℝ z v hdopen
    rw [segment_symm] at hdseg
    exact hzv d hd hdseg
  refine ⟨fun t => u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z),
    ?_, ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun t : ℝ =>
        u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)) := by fun_prop
    exact hcont.continuousOn
  · norm_num
  · norm_num
  · intro t ht
    rcases le_total t (1/2) with htle | hge
    · have hA : min (2*t) 1 = 2*t := min_eq_left (by linarith)
      have hB : max (2*t - 1) 0 = 0 := max_eq_right (by linarith)
      have hθ0 : 0 ≤ 2*t := by linarith [ht.1]
      have hθ1 : 2*t ≤ 1 := by linarith
      have hmem : (1 - 2*t) * u.re + 2*t * z.re ∈ Ioo a b :=
        convex_combo_mem_Ioo huI hzre hθ0 hθ1
      have hre : (u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)).re
          = (1 - 2*t) * u.re + 2*t * z.re := by
        rw [hA, hB, zero_smul, add_zero]
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.sub_re]
        ring
      rw [hre]; exact Set.mem_Ioo.mp hmem
    · have hA : min (2*t) 1 = 1 := min_eq_right (by linarith [hge])
      have hB : max (2*t - 1) 0 = 2*t - 1 := max_eq_left (by linarith [hge])
      have hθ0 : 0 ≤ 2*t - 1 := by linarith [hge]
      have hθ1 : 2*t - 1 ≤ 1 := by linarith [ht.2]
      have hmem : (1 - (2*t - 1)) * z.re + (2*t - 1) * v.re ∈ Ioo a b :=
        convex_combo_mem_Ioo hzre hvI hθ0 hθ1
      have hre : (u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)).re
          = (1 - (2*t - 1)) * z.re + (2*t - 1) * v.re := by
        rw [hA, hB, one_smul]
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.sub_re]
        ring
      rw [hre]; exact Set.mem_Ioo.mp hmem
  · intro t ht
    rcases lt_trichotomy t (1/2) with hlt | heq | hgt
    · have hA : min (2*t) 1 = 2*t := min_eq_left (by linarith [hlt.le])
      have hB : max (2*t - 1) 0 = 0 := max_eq_right (by linarith [hlt.le])
      have h2t : 2*t ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
      have hmem : u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)
          ∈ openSegment ℝ u z := by
        rw [openSegment_eq_image']
        exact ⟨2*t, h2t, by rw [hA, hB, zero_smul, add_zero]⟩
      intro hQγ
      exact hzu_open _ hQγ hmem
    · have hA : min (2*t) 1 = 1 := by rw [heq]; norm_num
      have hB : max (2*t - 1) 0 = 0 := by rw [heq]; norm_num
      have hval : u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z) = z := by
        rw [hA, hB, one_smul, zero_smul, add_zero, add_sub_cancel]
      change (u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)) ∉ Q
      rw [hval]; exact hzQ
    · have hA : min (2*t) 1 = 1 := min_eq_right (by linarith [hgt.le])
      have hB : max (2*t - 1) 0 = 2*t - 1 := max_eq_left (by linarith [hgt.le])
      have h2t : 2*t - 1 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hgt.le], by linarith [ht.2]⟩
      have hmem : z + (2*t - 1) • (v - z) ∈ openSegment ℝ z v := by
        rw [openSegment_eq_image']
        exact ⟨2*t - 1, h2t, rfl⟩
      have hval : u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)
          = z + (2*t - 1) • (v - z) := by
        rw [hA, hB, one_smul, add_sub_cancel]
      change (u + (min (2*t) 1) • (z - u) + (max (2*t - 1) 0) • (v - z)) ∉ Q
      intro hQγ
      rw [hval] at hQγ
      exact hzv_open _ hQγ hmem

end Work.EQ
