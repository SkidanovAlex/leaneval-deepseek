import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic

namespace Work.OddVolterra.RowIdentity

/-- **A fixed interval containing all sections near `s`.**

The sections `(-x σ, y σ)` for `σ ∈ (0,1]` stay inside `(-1,1)` (`hint` on `[a,1]`, and by
continuity of `x`, `y` at `a` for `σ` slightly below `a`), and on `[a,1]` the functions are
antitone (`hxdec`, `hydec` with `antitoneOn_of_deriv_nonpos`, using `ContinuousOn` on `Icc a 1`
and `DifferentiableOn` on its interior from `hx`, `hy`), so `x σ ∈ [x 1, x a]` and
`y σ ∈ [y 1, y a]`, whence `-(x σ) ≥ -(x a) > -1` and `y σ ≤ y a < 1` by `hint` at `a`.  A small
margin around `a` supplied by continuity handles `σ ∈ (s-δ, a)`, and the strict inequalities at
the ends give `c < d` inside `(-1,1)`.

The point is to produce a single interval `[c,d] ⊆ (-1,1)` containing every section
`(-x σ, y σ)`, `σ ∈ [s-δ,1]`, so that `momentIntegrand n h f u` is continuous on `[c,d]`
(`H.hf` smoothness of `f` on `Ioo (-1) 1`) and the local Leibniz rule
`Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW` applies.  Note the direction of the
inequalities: `c < -(x σ) ≤ d` and `c ≤ y σ < d`. -/
theorem section_box (H : Setup) {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) :
    ∃ δ > 0, ∃ c d : ℝ, -1 < c ∧ c < d ∧ d < 1 ∧
      ∀ σ ∈ Set.Icc (s - δ) 1,
        c < -(H.x σ) ∧ -(H.x σ) ≤ d ∧ c ≤ H.y σ ∧ H.y σ < d := by
  have ha_lt_one : H.a < 1 := lt_of_le_of_lt H.hac H.hc1
  have ha_mem : H.a ∈ Set.Icc H.a 1 := ⟨le_rfl, ha_lt_one.le⟩
  have h1_mem : (1:ℝ) ∈ Set.Icc H.a 1 := ⟨ha_lt_one.le, le_rfl⟩
  have hIcc_sub : Set.Icc H.a 1 ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_of_lt_of_le H.ha ht.1
  have hIoo_sub : Set.Ioo H.a 1 ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_of_lt_of_le H.ha ht.1.le
  have hcont_x : ContinuousOn H.x (Set.Icc H.a 1) := H.hx.continuousOn.mono hIcc_sub
  have hcont_y : ContinuousOn H.y (Set.Icc H.a 1) := H.hy.continuousOn.mono hIcc_sub
  have hanti_x : AntitoneOn H.x (Set.Icc H.a 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont_x ?_ ?_
    · rw [interior_Icc]; exact (H.hx.differentiableOn (by simp)).mono hIoo_sub
    · intro t ht; rw [interior_Icc] at ht; exact H.hxdec t ht
  have hanti_y : AntitoneOn H.y (Set.Icc H.a 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont_y ?_ ?_
    · rw [interior_Icc]; exact (H.hy.differentiableOn (by simp)).mono hIoo_sub
    · intro t ht; rw [interior_Icc] at ht; exact H.hydec t ht
  have hxa_lo : -1 < -(H.x H.a) := (H.hint H.a ha_mem).1.1
  have hya_hi : H.y H.a < 1 := (H.hint H.a ha_mem).2.2
  have hx1_hi : -(H.x 1) < 1 := (H.hint 1 h1_mem).1.2
  have hy1_pos : 0 < H.y 1 := by rw [H.hyb]; exact profileX_one_pos
  have hx1_le_xa : H.x 1 ≤ H.x H.a := hanti_x ha_mem h1_mem ha_lt_one.le
  have hy1_le_ya : H.y 1 ≤ H.y H.a := hanti_y ha_mem h1_mem ha_lt_one.le
  set c : ℝ := (-1 + min (-(H.x H.a)) (H.y 1)) / 2 with hc
  set d : ℝ := (1 + max (-(H.x 1)) (H.y H.a)) / 2 with hd
  have hc_gt : -1 < c := by rw [hc]; linarith [lt_min hxa_lo (by linarith : (-1:ℝ) < H.y 1)]
  have hd_lt : d < 1 := by rw [hd]; linarith [max_lt hx1_hi hya_hi]
  have hc_lt_nx_a : c < -(H.x H.a) := by
    rw [hc]; linarith [min_le_left (-(H.x H.a)) (H.y 1)]
  have hc_lt_y1 : c < H.y 1 := by
    rw [hc]; linarith [min_le_right (-(H.x H.a)) (H.y 1)]
  have hc_lt_ya : c < H.y H.a := lt_of_lt_of_le hc_lt_y1 hy1_le_ya
  have hnx_a_lt_d : -(H.x H.a) < d := by
    rw [hd]; linarith [le_max_left (-(H.x 1)) (H.y H.a), neg_le_neg hx1_le_xa]
  have hx1_lt_d : -(H.x 1) < d := by
    rw [hd]; linarith [le_max_left (-(H.x 1)) (H.y H.a)]
  have hya_lt_d : H.y H.a < d := by
    rw [hd]; linarith [le_max_right (-(H.x 1)) (H.y H.a)]
  have hcd : c < d := by linarith [hc_lt_nx_a, hx1_lt_d, neg_le_neg hx1_le_xa]
  have hcx : ContinuousAt H.x H.a := H.hx.continuousOn.continuousAt (isOpen_Ioi.mem_nhds H.ha)
  have hcy : ContinuousAt H.y H.a := H.hy.continuousOn.continuousAt (isOpen_Ioi.mem_nhds H.ha)
  obtain ⟨e1, he1, h1⟩ : ∃ e > 0, ∀ σ, |σ - H.a| < e → c < -(H.x σ) := by
    have hmem := hcx.neg.preimage_mem_nhds (isOpen_Ioi.mem_nhds hc_lt_nx_a)
    obtain ⟨e, he, hb⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e, he, fun σ hσ => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hσ)⟩
  obtain ⟨e2, he2, h2⟩ : ∃ e > 0, ∀ σ, |σ - H.a| < e → -(H.x σ) < d := by
    have hmem := hcx.neg.preimage_mem_nhds (isOpen_Iio.mem_nhds hnx_a_lt_d)
    obtain ⟨e, he, hb⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e, he, fun σ hσ => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hσ)⟩
  obtain ⟨e3, he3, h3⟩ : ∃ e > 0, ∀ σ, |σ - H.a| < e → c < H.y σ := by
    have hmem := hcy.preimage_mem_nhds (isOpen_Ioi.mem_nhds hc_lt_ya)
    obtain ⟨e, he, hb⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e, he, fun σ hσ => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hσ)⟩
  obtain ⟨e4, he4, h4⟩ : ∃ e > 0, ∀ σ, |σ - H.a| < e → H.y σ < d := by
    have hmem := hcy.preimage_mem_nhds (isOpen_Iio.mem_nhds hya_lt_d)
    obtain ⟨e, he, hb⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e, he, fun σ hσ => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hσ)⟩
  set m : ℝ := min (min e1 e2) (min e3 e4) with hm
  set δ : ℝ := m / 2 with hδ
  have hmpos : 0 < m := by rw [hm]; exact lt_min (lt_min he1 he2) (lt_min he3 he4)
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hme1 : m ≤ e1 := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hme2 : m ≤ e2 := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hme3 : m ≤ e3 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hme4 : m ≤ e4 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδe1 : δ ≤ e1 / 2 := by rw [hδ]; linarith
  have hδe2 : δ ≤ e2 / 2 := by rw [hδ]; linarith
  have hδe3 : δ ≤ e3 / 2 := by rw [hδ]; linarith
  have hδe4 : δ ≤ e4 / 2 := by rw [hδ]; linarith
  refine ⟨δ, hδpos, c, d, hc_gt, hcd, hd_lt, ?_⟩
  intro σ hσ
  have hσ_ge : s - δ ≤ σ := hσ.1
  have hσ_le : σ ≤ 1 := hσ.2
  have hs_ge : H.a ≤ s := hs.1
  have hle : H.a - σ ≤ δ := by linarith
  rcases lt_or_ge σ H.a with hσa | hσa
  · have habs1 : |σ - H.a| < e1 := by
      rw [abs_of_neg (by linarith : σ - H.a < 0)]; linarith [hδe1, he1]
    have habs2 : |σ - H.a| < e2 := by
      rw [abs_of_neg (by linarith : σ - H.a < 0)]; linarith [hδe2, he2]
    have habs3 : |σ - H.a| < e3 := by
      rw [abs_of_neg (by linarith : σ - H.a < 0)]; linarith [hδe3, he3]
    have habs4 : |σ - H.a| < e4 := by
      rw [abs_of_neg (by linarith : σ - H.a < 0)]; linarith [hδe4, he4]
    exact ⟨h1 σ habs1, (h2 σ habs2).le, (h3 σ habs3).le, h4 σ habs4⟩
  · have hσmem : σ ∈ Set.Icc H.a 1 := ⟨hσa, hσ_le⟩
    have hxσ_le : H.x σ ≤ H.x H.a := hanti_x ha_mem hσmem hσa
    have hx1_le : H.x 1 ≤ H.x σ := hanti_x hσmem h1_mem hσ_le
    have hyσ_le : H.y σ ≤ H.y H.a := hanti_y ha_mem hσmem hσa
    have hy1_le : H.y 1 ≤ H.y σ := hanti_y hσmem h1_mem hσ_le
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Work.OddVolterra.RowIdentity
