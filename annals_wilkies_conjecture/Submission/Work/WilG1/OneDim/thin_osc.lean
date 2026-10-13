import Submission.Work.WilG1.OneDim.thin_ev

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 5. The oscillation, corner and infinite-derivative sets -/

theorem not_mem_evRle_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∉ evRle g q ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ q < dq g x y := by
  simp only [evRle, Set.mem_setOf_eq]
  push_neg
  constructor
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (lt_dq_iff hy1).mpr hy3⟩
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (lt_dq_iff hy1).mp hy3⟩

theorem not_mem_evRge_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∉ evRge g q ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ dq g x y < q := by
  simp only [evRge, Set.mem_setOf_eq]
  push_neg
  constructor
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (dq_lt_iff hy1).mpr hy3⟩
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (dq_lt_iff hy1).mp hy3⟩

theorem not_mem_evLge_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∉ evLge g q ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ dq g x y < q := by
  simp only [evLge, Set.mem_setOf_eq]
  push_neg
  constructor
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (dq_lt_iff_of_lt hy2).mpr hy3⟩
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (dq_lt_iff_of_lt hy2).mp hy3⟩

theorem not_mem_evLle_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∉ evLle g q ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ q < dq g x y := by
  simp only [evLle, Set.mem_setOf_eq]
  push_neg
  constructor
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (lt_dq_iff_of_lt hy2).mpr hy3⟩
  · intro h δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    exact ⟨y, hy1, hy2, (lt_dq_iff_of_lt hy2).mp hy3⟩

theorem mem_oscR_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ oscR g q ↔ x ∉ evRle g q ∧ x ∉ evRge g q := by
  rw [oscR]
  simp only [Set.mem_setOf_eq]
  rw [not_mem_evRle_iff, not_mem_evRge_iff]

theorem mem_oscL_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ oscL g q ↔ x ∉ evLle g q ∧ x ∉ evLge g q := by
  rw [oscL]
  simp only [Set.mem_setOf_eq]
  rw [not_mem_evLle_iff, not_mem_evLge_iff]

theorem cornerMax_eq (g : ℝ → ℝ) (q : ℝ) : cornerMax g q = evRlt g q ∩ evLgt g q := by
  ext x
  simp only [cornerMax, evRlt, evLgt, Set.mem_setOf_eq, Set.mem_inter_iff]

theorem cornerMin_eq (g : ℝ → ℝ) (q : ℝ) : cornerMin g q = evRgt g q ∩ evLlt g q := by
  ext x
  simp only [cornerMin, evRgt, evLlt, Set.mem_setOf_eq, Set.mem_inter_iff]

/-! ## 6. The infinite-derivative sets -/

theorem mem_infDeriv_one_iff {g : ℝ → ℝ} {x : ℝ} :
    x ∈ infDeriv g 1 ↔ ∀ M : ℝ, 1 < M → x ∈ evRgt g M ∧ x ∈ evLgt g M := by
  simp only [infDeriv, evRgt, evLgt, Set.mem_setOf_eq]
  constructor
  · intro h M hM
    obtain ⟨δ, hδ, h'⟩ := h M hM
    constructor
    · refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
      have habs : |y - x| < δ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < y - x)]; linarith
      exact (lt_dq_iff hy1).mp (by simpa using h' y (ne_of_gt hy1) habs)
    · refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
      have habs : |y - x| < δ := by
        rw [abs_of_neg (by linarith : y - x < 0)]; linarith
      exact (lt_dq_iff_of_lt hy2).mp (by simpa using h' y (ne_of_lt hy2) habs)
  · intro h M hM
    obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := h M hM
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hyne hy => ?_⟩
    rcases lt_or_gt_of_ne (Ne.symm hyne) with hyx | hyx
    · have hmem : y < x + δ₁ := by
        have hlt : |y - x| < δ₁ := lt_of_lt_of_le hy (min_le_left δ₁ δ₂)
        rw [abs_of_pos (by linarith : (0:ℝ) < y - x)] at hlt
        linarith
      have hlt2 := (lt_dq_iff hyx).mpr (h₁ y hyx hmem)
      simpa using hlt2
    · have hmem : x - δ₂ < y := by
        have hlt : |y - x| < δ₂ := lt_of_lt_of_le hy (min_le_right δ₁ δ₂)
        rw [abs_of_neg (by linarith : y - x < 0)] at hlt
        linarith
      have hlt2 := (lt_dq_iff_of_lt hyx).mpr (h₂ y hmem hyx)
      simpa using hlt2

theorem mem_infDeriv_neg_one_iff {g : ℝ → ℝ} {x : ℝ} :
    x ∈ infDeriv g (-1) ↔ ∀ M : ℝ, 1 < M → x ∈ evRlt g (-M) ∧ x ∈ evLlt g (-M) := by
  simp only [infDeriv, evRlt, evLlt, Set.mem_setOf_eq]
  constructor
  · intro h M hM
    obtain ⟨δ, hδ, h'⟩ := h M hM
    constructor
    · refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
      have habs : |y - x| < δ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < y - x)]; linarith
      have h1 := h' y (ne_of_gt hy1) habs
      have h2 : dq g x y < -M := by nlinarith [h1]
      exact (dq_lt_iff hy1).mp h2
    · refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
      have habs : |y - x| < δ := by
        rw [abs_of_neg (by linarith : y - x < 0)]; linarith
      have h1 := h' y (ne_of_lt hy2) habs
      have h2 : dq g x y < -M := by nlinarith [h1]
      exact (dq_lt_iff_of_lt hy2).mp h2
  · intro h M hM
    obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := h M hM
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hyne hy => ?_⟩
    rcases lt_or_gt_of_ne (Ne.symm hyne) with hyx | hyx
    · have hmem : y < x + δ₁ := by
        have hlt : |y - x| < δ₁ := lt_of_lt_of_le hy (min_le_left δ₁ δ₂)
        rw [abs_of_pos (by linarith : (0:ℝ) < y - x)] at hlt
        linarith
      have hd := (dq_lt_iff hyx).mpr (h₁ y hyx hmem)
      have : M < -(1:ℝ) * dq g x y := by nlinarith [hd]
      simpa using this
    · have hmem : x - δ₂ < y := by
        have hlt : |y - x| < δ₂ := lt_of_lt_of_le hy (min_le_right δ₁ δ₂)
        rw [abs_of_neg (by linarith : y - x < 0)] at hlt
        linarith
      have hd := (dq_lt_iff_of_lt hyx).mpr (h₂ y hmem hyx)
      have : M < -(1:ℝ) * dq g x y := by nlinarith [hd]
      simpa using this

theorem evRgt_of_rat {g : ℝ → ℝ} {x : ℝ} (h : ∀ M : ℚ, 0 < M → x ∈ evRgt g (M : ℝ)) :
    ∀ M : ℝ, 0 < M → x ∈ evRgt g M := by
  intro M hM
  obtain ⟨q, hq⟩ := exists_rat_gt M
  exact evRgt_anti (le_of_lt hq) (h q (by exact_mod_cast lt_trans hM hq))

theorem evLgt_of_rat {g : ℝ → ℝ} {x : ℝ} (h : ∀ M : ℚ, 0 < M → x ∈ evLgt g (M : ℝ)) :
    ∀ M : ℝ, 0 < M → x ∈ evLgt g M := by
  intro M hM
  obtain ⟨q, hq⟩ := exists_rat_gt M
  exact evLgt_anti (le_of_lt hq) (h q (by exact_mod_cast lt_trans hM hq))

theorem infDeriv_one_of {g : ℝ → ℝ} {x : ℝ}
    (hR : ∀ M : ℚ, 0 < M → x ∈ evRgt g (M : ℝ))
    (hL : ∀ M : ℚ, 0 < M → x ∈ evLgt g (M : ℝ)) : x ∈ infDeriv g 1 := by
  rw [mem_infDeriv_one_iff]
  intro M hM
  exact ⟨evRgt_of_rat hR M (by linarith), evLgt_of_rat hL M (by linarith)⟩

theorem infDeriv_neg_one_of {g : ℝ → ℝ} {x : ℝ}
    (hR : ∀ M : ℚ, 0 < M → x ∈ evRlt g (-(M : ℝ)))
    (hL : ∀ M : ℚ, 0 < M → x ∈ evLlt g (-(M : ℝ))) : x ∈ infDeriv g (-1) := by
  rw [mem_infDeriv_neg_one_iff]
  intro M hM
  obtain ⟨q, hq⟩ := exists_rat_gt M
  have hq0 : (0:ℚ) < q := by
    have hq0' : (0:ℝ) < (q:ℝ) := lt_trans (by linarith : (0:ℝ) < M) hq
    exact_mod_cast hq0'
  constructor
  · refine evRlt_mono ?_ (hR q hq0)
    linarith
  · refine evLlt_mono ?_ (hL q hq0)
    linarith

/-! ## 7. Comparison of the two trichotomies -/

theorem evRle_of_right_limit {g : ℝ → ℝ} {x L : ℝ}
    (h : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evRge g (r:ℝ) ∧ x ∈ evRle g (s:ℝ))
    {s : ℚ} (hs : L < (s:ℝ)) : x ∈ evRle g (s:ℝ) := by
  obtain ⟨r, hr⟩ := exists_rat_lt L
  exact (h r s hr hs).2

theorem evRge_of_right_limit {g : ℝ → ℝ} {x L : ℝ}
    (h : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evRge g (r:ℝ) ∧ x ∈ evRle g (s:ℝ))
    {r : ℚ} (hr : (r:ℝ) < L) : x ∈ evRge g (r:ℝ) := by
  obtain ⟨s, hs⟩ := exists_rat_gt L
  exact (h r s hr hs).1

theorem evLle_of_left_limit {g : ℝ → ℝ} {x L : ℝ}
    (h : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evLge g (r:ℝ) ∧ x ∈ evLle g (s:ℝ))
    {s : ℚ} (hs : L < (s:ℝ)) : x ∈ evLle g (s:ℝ) := by
  obtain ⟨r, hr⟩ := exists_rat_lt L
  exact (h r s hr hs).2

theorem evLge_of_left_limit {g : ℝ → ℝ} {x L : ℝ}
    (h : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evLge g (r:ℝ) ∧ x ∈ evLle g (s:ℝ))
    {r : ℚ} (hr : (r:ℝ) < L) : x ∈ evLge g (r:ℝ) := by
  obtain ⟨s, hs⟩ := exists_rat_gt L
  exact (h r s hr hs).1

/-- **Finite limits agree.**  If the right and the left difference quotients converge to the
same finite value, then `g` is differentiable at `x`. -/
theorem differentiableAt_of_same_limit {g : ℝ → ℝ} {x L : ℝ}
    (hR : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evRge g (r:ℝ) ∧ x ∈ evRle g (s:ℝ))
    (hL : ∀ r s : ℚ, (r:ℝ) < L → L < (s:ℝ) → x ∈ evLge g (r:ℝ) ∧ x ∈ evLle g (s:ℝ)) :
    DifferentiableAt ℝ g x := by
  have hlim : Filter.Tendsto (slope g x) (nhdsWithin x {x}ᶜ) (nhds L) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show L - ε < L by linarith)
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show L < L + ε by linarith)
    obtain ⟨δ₁, hδ₁, h₁⟩ := evRge_of_right_limit hR hr2
    obtain ⟨δ₂, hδ₂, h₂⟩ := evRle_of_right_limit hR hs1
    obtain ⟨δ₃, hδ₃, h₃⟩ := evLge_of_left_limit hL hr2
    obtain ⟨δ₄, hδ₄, h₄⟩ := evLle_of_left_limit hL hs1
    have hδ : 0 < min (min δ₁ δ₂) (min δ₃ δ₄) := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)
    have hle1 : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hle2 : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hle3 : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₃ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hle4 : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₄ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    filter_upwards [self_mem_nhdsWithin (s := {x}ᶜ), nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
      with y hyne hyball
    have hyx : |y - x| < min (min δ₁ δ₂) (min δ₃ δ₄) := by
      rw [← Real.dist_eq]; exact hyball
    have hbounds : (r:ℝ) ≤ dq g x y ∧ dq g x y ≤ (s:ℝ) := by
      rcases lt_or_gt_of_ne (Ne.symm hyne) with hlt | hlt
      · -- x < y
        have h3' : y < x + δ₁ := by
          have hlt' : |y - x| < δ₁ := lt_of_lt_of_le hyx hle1
          rw [abs_of_pos (by linarith : (0:ℝ) < y - x)] at hlt'
          linarith
        have h4' : y < x + δ₂ := by
          have hlt' : |y - x| < δ₂ := lt_of_lt_of_le hyx hle2
          rw [abs_of_pos (by linarith : (0:ℝ) < y - x)] at hlt'
          linarith
        exact ⟨(le_dq_iff hlt).mpr (h₁ y hlt h3'), (dq_le_iff hlt).mpr (h₂ y hlt h4')⟩
      · -- y < x
        have h3' : x - δ₃ < y := by
          have hlt' : |y - x| < δ₃ := lt_of_lt_of_le hyx hle3
          rw [abs_of_neg (by linarith : y - x < 0)] at hlt'
          linarith
        have h4' : x - δ₄ < y := by
          have hlt' : |y - x| < δ₄ := lt_of_lt_of_le hyx hle4
          rw [abs_of_neg (by linarith : y - x < 0)] at hlt'
          linarith
        exact ⟨(le_dq_iff_of_lt hlt).mpr (h₃ y h3' hlt), (dq_le_iff_of_lt hlt).mpr (h₄ y h4' hlt)⟩
    have hslope : slope g x y = dq g x y := by
      rw [slope, dq, smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]
      ring
    rw [Real.dist_eq, hslope, abs_lt]
    constructor <;> linarith [hbounds.1, hbounds.2, hr1, hs2]
  exact (hasDerivAt_iff_tendsto_slope.mpr hlim).differentiableAt

end Work.WilG1.OneDim
