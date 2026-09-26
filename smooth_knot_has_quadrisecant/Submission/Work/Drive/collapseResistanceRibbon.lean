import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.collapseResistanceDefs
import Submission.Work.Drive.collapseBase
import Submission.Work.Drive.collapseTools
import Submission.Work.Drive.secantDiskAPI
import Submission.Work.Drive.knotSeparation
import Submission.Helpers

/-!
# Collapse resistance: the ribbon (Kuperberg §6, fig. 4)

This file proves `Work.Drive.CollapseResistance` (the statement fixed in
`Submission/Work/Drive/collapseResistanceDefs.lean`).

The architecture is the one recorded in `NOTES_spreadQuadrisecantClose.md` §"the ribbon":

* fix a secant `(A,B)` of a knot `r'` that is short and narrow and interior-free;
* lift `A`, `B` to reals `a < b` with `b - a = dist A B`;
* let `base` be the *fibre base map* of the reference knot `r` (the unique zero in a fixed
  window of `x ↦ ⟪q - r x, velocity r x⟫`, `Work.Drive.baseWindow`);
* the base map along the short arc of `r'` is `σ t = base (r' t)`, and along the chord it is
  `β u = base ((1-u) • r' a + u • r' b)`; both are continuous injective (the second because the
  chord direction is transversal to every fibre, `chordDirPos`), hence both are strictly monotone;
* matching the chord to the arc in the common fibre gives a continuous `t : I → [a,b]` with
  `σ (t u) = β u`, and the **ribbon**
  `D (u,v) = (1-v) • r' (t u) + v • ((1-u) • r' a + u • r' b)`
  spans the chord by the short arc of `r'`;
* an interior point of the ribbon lies in the fibre through `base` of its bottom point, where the
  knot `r'` meets the fibre in the single arc point `r' (t u)` (`Work.Drive.sectionLocal`, using
  the uniform separation of far parameters to exclude the far part of `r'`); hence the interior of
  the ribbon misses the knot.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

/-! ## 1. Ordered lifts of a pair of points of the parameter circle -/

/-- Any two points of the parameter circle have real representatives realising their distance. -/
lemma exists_repr_dist (a b : AddCircle period) :
    ∃ t s : ℝ, (t : AddCircle period) = a ∧ (s : AddCircle period) = b ∧ |t - s| = dist a b := by
  obtain ⟨s₀, -, hs₀⟩ := AddCircle.eq_coe_Ico b
  obtain ⟨x, -, hx⟩ := AddCircle.eq_coe_Ico (a - b)
  refine ⟨s₀ + (x - (round (period⁻¹ * x) : ℝ) * period), s₀, ?_, hs₀, ?_⟩
  · have hks : (((round (period⁻¹ * x) : ℝ) * period : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round (period⁻¹ * x), by simp⟩
    rw [AddCircle.coe_add, AddCircle.coe_sub, hks, hx, hs₀]
    abel
  · simp only [add_sub_cancel_left]
    rw [dist_eq_norm, ← hx, AddCircle.norm_eq]

/-- **Ordered representatives of a pair of distinct parameters.**  Two distinct classes modulo
the period have real lifts `a < b` realising the circular distance, in either order. -/
lemma exists_order_lift {A B : AddCircle period} (hne : A ≠ B) :
    ∃ a b : ℝ, a < b ∧ b - a = dist A B ∧
      (((a : AddCircle period) = A ∧ (b : AddCircle period) = B) ∨
       ((a : AddCircle period) = B ∧ (b : AddCircle period) = A)) := by
  obtain ⟨t, s, ht, hs, hts⟩ := exists_repr_dist A B
  have hne' : t ≠ s := fun h => hne (by rw [← ht, ← hs, h])
  rcases lt_or_gt_of_ne hne' with h | h
  · refine ⟨t, s, h, ?_, Or.inl ⟨ht, hs⟩⟩
    rw [← hts, abs_of_neg (sub_neg.mpr h)]
    ring
  · refine ⟨s, t, h, ?_, Or.inr ⟨hs, ht⟩⟩
    rw [← hts, abs_of_pos (sub_pos.mpr h)]

/-! ## 2. The chord direction is transversal to the fibres -/

/-- **The chord direction is transversal to the fibres.**  If the velocity of `r` varies by less
than `c ^ 2 / (2 * Lv)` on the window, the velocity of `r'` is `ε`-close to that of `r` with
`ε * Lv < c ^ 2 / 2`, and `|t - x| < ηv` for all `t ∈ [a,b]`, then `r' b - r' a` has positive
inner product with `velocity r x`: the function `t ↦ ⟪r' t - r' a, velocity r x⟫` vanishes at
`t = a` and is strictly increasing on `[a,b]`. -/
lemma chordDirPos {r r' : ℝ → Space} {c Lv ε ηv a b x : ℝ}
    (hc : 0 < c) (hLv : 0 < Lv)
    (hcle : ∀ t : ℝ, c ≤ ‖velocity r t‖)
    (hLvle : ∀ t : ℝ, ‖velocity r t‖ ≤ Lv)
    (hr'diff : Differentiable ℝ r')
    (hUC : ∀ y z : ℝ, dist y z < ηv → dist (velocity r y) (velocity r z) < c ^ 2 / (2 * Lv))
    (hεpos : 0 < ε) (hεLv : ε * Lv < c ^ 2 / 2)
    (hvel : ∀ t : ℝ, ‖velocity r' t - velocity r t‖ < ε)
    (hab : a < b) (hx : ∀ t : ℝ, t ∈ Set.Icc a b → |t - x| < ηv) :
    0 < inner ℝ (r' b - r' a) (velocity r x) := by
  set G : ℝ → ℝ := fun t => inner ℝ (r' t - r' a) (velocity r x) with hG
  have hGderiv : ∀ t : ℝ, HasDerivAt G (inner ℝ (velocity r' t) (velocity r x)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => r' t - r' a) (velocity r' t) t :=
      (hr'diff t).hasDerivAt.sub_const (r' a)
    have h2 : HasDerivAt (fun _ : ℝ => velocity r x) 0 t := hasDerivAt_const t _
    have h3 := h1.inner ℝ h2
    simpa [hG, inner_zero_right, add_zero] using h3
  have hGpos : ∀ t ∈ Set.Icc a b, 0 < inner ℝ (velocity r' t) (velocity r x) := by
    intro t ht
    have h1 : dist t x < ηv := by
      rw [Real.dist_eq]
      exact hx t ht
    have h2 : ‖velocity r t - velocity r x‖ < c ^ 2 / (2 * Lv) := by
      have := hUC t x h1
      rwa [dist_eq_norm] at this
    have h3 : c ≤ ‖velocity r x‖ := hcle x
    have h4 : ‖velocity r x‖ ≤ Lv := hLvle x
    have h5 : (c ^ 2 / 2) ≤ inner ℝ (velocity r t) (velocity r x) := by
      have hadd : velocity r t = velocity r x + (velocity r t - velocity r x) := by abel
      have h6 : inner ℝ (velocity r t) (velocity r x)
          = ‖velocity r x‖ ^ 2 + inner ℝ (velocity r t - velocity r x) (velocity r x) := by
        conv_lhs => rw [hadd]
        rw [inner_add_left, real_inner_self_eq_norm_sq]
      have h7 : -(‖velocity r t - velocity r x‖ * ‖velocity r x‖)
          ≤ inner ℝ (velocity r t - velocity r x) (velocity r x) := by
        have ha := neg_abs_le (inner ℝ (velocity r t - velocity r x) (velocity r x))
        have hb := abs_real_inner_le_norm (velocity r t - velocity r x) (velocity r x)
        linarith
      have h8 : ‖velocity r t - velocity r x‖ * ‖velocity r x‖
          < (c ^ 2 / (2 * Lv)) * Lv :=
        mul_lt_mul h2 h4 (lt_of_lt_of_le hc h3) (by positivity)
      have h9 : (c ^ 2 / (2 * Lv)) * Lv = c ^ 2 / 2 := by field_simp
      rw [h6]
      nlinarith [h7, h8, h9, h3, hc, sq_nonneg c]
    have h10 : inner ℝ (velocity r' t) (velocity r x)
        = inner ℝ (velocity r t) (velocity r x)
          + inner ℝ (velocity r' t - velocity r t) (velocity r x) := by
      rw [← inner_add_left]
      congr 1
      abel
    have h11 : -(‖velocity r' t - velocity r t‖ * ‖velocity r x‖)
        ≤ inner ℝ (velocity r' t - velocity r t) (velocity r x) := by
      have ha := neg_abs_le (inner ℝ (velocity r' t - velocity r t) (velocity r x))
      have hb := abs_real_inner_le_norm (velocity r' t - velocity r t) (velocity r x)
      linarith
    have h12 : ‖velocity r' t - velocity r t‖ * ‖velocity r x‖ < ε * Lv :=
      mul_lt_mul (hvel t) h4 (lt_of_lt_of_le hc h3) (le_of_lt hεpos)
    rw [h10]
    linarith [h5, h11, h12, hεLv]
  have hcontG : ContinuousOn G (Set.Icc a b) := fun t _ =>
    (hGderiv t).continuousAt.continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc a b) hcontG (fun t ht => by
    rw [interior_Icc] at ht
    rw [(hGderiv t).deriv]
    exact hGpos t ⟨ht.1.le, ht.2.le⟩)
  have h := hmono (Set.left_mem_Icc.mpr (le_of_lt hab)) (Set.right_mem_Icc.mpr (le_of_lt hab)) hab
  have hGa : G a = 0 := by simp [hG]
  rw [hGa] at h
  simpa [hG] using h


/-! ## 3. Elementary facts used by the ribbon construction -/

/-- The period is bigger than `1` (it is `2 * π`). -/
lemma period_gt_one : 1 < period := by
  rw [period]
  nlinarith [Real.pi_gt_three]

/-- Two real lifts of the same point of the circle at distance less than a period coincide. -/
lemma coe_eq_of_abs_lt {x y : ℝ} (h : (x : AddCircle period) = (y : AddCircle period))
    (hxy : |x - y| < period) : x = y := by
  have h0 : ((x - y : ℝ) : AddCircle period) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff period).1 h0
  have h1 : x - y = (n : ℝ) * period := by rw [← hn, zsmul_eq_mul]
  have h2 : |x - y| = |(n : ℝ)| * period := by rw [h1, abs_mul, abs_of_pos period_pos]
  have h3 : |(n : ℝ)| < 1 := by
    have hp := period_pos
    have hlt : |(n : ℝ)| * period < 1 * period := by
      rw [one_mul]; rw [h2] at hxy; exact hxy
    exact lt_of_mul_lt_mul_right hlt hp.le
  have h5 : n = 0 := by
    have h6 : (-1 : ℤ) < n ∧ n < (1 : ℤ) := by
      rw [abs_lt] at h3
      exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩
    omega
  have h7 : x - y = 0 := by rw [h1, h5]; simp
  linarith

/-- **Uniform separation of a `C¹`-neighbourhood.**  A knot `r'` that is `C¹`-close to a smooth
knot `r` and whose parameters are at distance at least `η` on the circle stays at distance at
least `sg / 2` in space. -/
lemma separation_of_close {r : ℝ → Space} (hr : IsSmoothKnot r) {η : ℝ} (hη : 0 < η) :
    ∃ sg : ℝ, 0 < sg ∧ ∀ r' : ℝ → Space, IsSmoothKnot r' →
      (∀ t : ℝ, ‖r' t - r t‖ < sg / 4 ∧ ‖velocity r' t - velocity r t‖ < sg / 4) →
      ∀ a b : AddCircle period, η ≤ dist a b → sg / 2 ≤ ‖knotMap r' a - knotMap r' b‖ := by
  obtain ⟨sg, hsgpos, hsg⟩ := knotSeparation hr hη
  refine ⟨sg, hsgpos, ?_⟩
  intro r' hr' hclose a b hab
  obtain ⟨t, s, ht, hs, hts⟩ := exists_repr_dist a b
  have h1 : knotMap r' a = r' t := by rw [← ht]; exact knotMap_coe_of_periodic hr'.periodic t
  have h2 : knotMap r' b = r' s := by rw [← hs]; exact knotMap_coe_of_periodic hr'.periodic s
  have h3 : η ≤ dist (t : AddCircle period) (s : AddCircle period) := by rw [ht, hs]; exact hab
  have h4 : sg ≤ ‖r t - r s‖ := hsg t s h3
  have h5 : ‖r t - r s‖ ≤ ‖r' t - r' s‖ + (‖r' t - r t‖ + ‖r' s - r s‖) := by
    have hsp : r t - r s = (r' t - r' s) - ((r' t - r t) - (r' s - r s)) := by abel
    have h6 : ‖r t - r s‖ ≤ ‖r' t - r' s‖ + ‖(r' t - r t) - (r' s - r s)‖ := by
      rw [hsp]; exact norm_sub_le _ _
    have h7 : ‖(r' t - r t) - (r' s - r s)‖ ≤ ‖r' t - r t‖ + ‖r' s - r s‖ :=
      norm_sub_le _ _
    linarith
  rw [h1, h2]
  have h8 := (hclose t).1
  have h9 := (hclose s).1
  linarith

/-- A convex combination (with coefficients in `[0,1]`) is bounded by the maximum of the norms. -/
lemma norm_convex_combo_le {X Y : Space} {v : ℝ} (hv : v ∈ Set.Icc (0:ℝ) 1) :
    ‖(1 - v) • X + v • Y‖ ≤ max ‖X‖ ‖Y‖ := by
  have h1 : 0 ≤ 1 - v := by linarith [hv.2]
  calc ‖(1 - v) • X + v • Y‖ ≤ ‖(1 - v) • X‖ + ‖v • Y‖ := norm_add_le _ _
    _ = (1 - v) * ‖X‖ + v * ‖Y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1, Real.norm_of_nonneg hv.1]
    _ ≤ (1 - v) * max ‖X‖ ‖Y‖ + v * max ‖X‖ ‖Y‖ := by
        have hX : ‖X‖ ≤ max ‖X‖ ‖Y‖ := le_max_left _ _
        have hY : ‖Y‖ ≤ max ‖X‖ ‖Y‖ := le_max_right _ _
        have hA := mul_le_mul_of_nonneg_left hX h1
        have hB := mul_le_mul_of_nonneg_left hY hv.1
        linarith
    _ = max ‖X‖ ‖Y‖ := by ring

/-- **The image of an interval under a continuous injective real function** is the interval
spanned by the endpoint values. -/
lemma image_Icc_eq_min_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b)) (hinj : Set.InjOn f (Set.Icc a b)) :
    f '' Set.Icc a b = Set.Icc (min (f a) (f b)) (max (f a) (f b)) := by
  refine Set.Subset.antisymm (fun y hy => ?_) (image_Icc_subset_min_max hab hcont)
  rcases hy with ⟨u, hu, rfl⟩
  exact noOvershoot_real hab hcont hinj hu

/-- **The fibre base map.**  From the window statement `hwin` (the conclusion of
`Work.Drive.baseWindow`) there is a function `base` on `Space` whose values on the ball
`‖q - r mid‖ ≤ Θ` are the unique zeros in `(mid - T, mid + T)` of `x ↦ ⟪q - r x, velocity r x⟫`. -/
lemma exists_base_function {r : ℝ → Space} {mid T N κ ηb Θ : ℝ}
    (hT : 0 < T) (hΘpos : 0 < Θ) (hΘηb : Θ ≤ ηb)
    (hwin : ∀ c₀ Θ' : ℝ, 0 < Θ' → Θ' ≤ ηb → ∀ t₀ : ℝ, |t₀ - c₀| ≤ T / 4 →
      ∀ q : Space, ‖q - r t₀‖ ≤ Θ' →
        ∃ x : ℝ, (x ∈ Set.Ioo (c₀ - T) (c₀ + T) ∧
            inner ℝ (q - r x) (velocity r x) = 0 ∧
            |x - t₀| ≤ N * Θ' ∧ ‖q - r x‖ ≤ κ * Θ') ∧
          (∀ y : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            inner ℝ (q - r y) (velocity r y) = 0 → y = x) ∧
          (∀ y z : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → z ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            y < z → inner ℝ (q - r z) (velocity r z) < inner ℝ (q - r y) (velocity r y))) :
    ∃ base : Space → ℝ,
      (∀ q : Space, ‖q - r mid‖ ≤ Θ →
        base q ∈ Set.Ioo (mid - T) (mid + T) ∧
          inner ℝ (q - r (base q)) (velocity r (base q)) = 0 ∧
          |base q - mid| ≤ N * Θ ∧ ‖q - r (base q)‖ ≤ κ * Θ) ∧
      (∀ q : Space, ‖q - r mid‖ ≤ Θ → ∀ y : ℝ, y ∈ Set.Ioo (mid - T) (mid + T) →
        inner ℝ (q - r y) (velocity r y) = 0 → y = base q) ∧
      (∀ q : Space, ‖q - r mid‖ ≤ Θ → ∀ y z : ℝ, y ∈ Set.Ioo (mid - T) (mid + T) →
        z ∈ Set.Ioo (mid - T) (mid + T) → y < z →
        inner ℝ (q - r z) (velocity r z) < inner ℝ (q - r y) (velocity r y)) := by
  classical
  have hex : ∀ q : Space, ∃ x : ℝ,
      (‖q - r mid‖ ≤ Θ → x ∈ Set.Ioo (mid - T) (mid + T) ∧
          inner ℝ (q - r x) (velocity r x) = 0 ∧ |x - mid| ≤ N * Θ ∧ ‖q - r x‖ ≤ κ * Θ) ∧
      (‖q - r mid‖ ≤ Θ → ∀ y : ℝ, y ∈ Set.Ioo (mid - T) (mid + T) →
          inner ℝ (q - r y) (velocity r y) = 0 → y = x) ∧
      (‖q - r mid‖ ≤ Θ → ∀ y z : ℝ, y ∈ Set.Ioo (mid - T) (mid + T) →
          z ∈ Set.Ioo (mid - T) (mid + T) → y < z →
            inner ℝ (q - r z) (velocity r z) < inner ℝ (q - r y) (velocity r y)) := by
    intro q
    by_cases hq : ‖q - r mid‖ ≤ Θ
    · obtain ⟨x, h1, h2, h3⟩ :=
        hwin mid Θ hΘpos hΘηb mid (by rw [sub_self, abs_zero]; linarith) q hq
      exact ⟨x, fun _ => h1, fun _ => h2, fun _ => h3⟩
    · exact ⟨mid, fun h => absurd h hq, fun h => absurd h hq, fun h => absurd h hq⟩
  exact ⟨fun q => Classical.choose (hex q),
    fun q hq => (Classical.choose_spec (hex q)).1 hq,
    fun q hq => (Classical.choose_spec (hex q)).2.1 hq,
    fun q hq => (Classical.choose_spec (hex q)).2.2 hq⟩

theorem collapseResistanceRibbon : Work.Drive.CollapseResistance := by
  intro r hr
  obtain ⟨vlo, vhi, Kv, hvlo, hvhi, hKv, hvlole, hvhiup, hKvlip⟩ := knotC2Bounds hr
  obtain ⟨T, N, κ, ηb, hT, hN, hκ, hηb, hwin⟩ := baseWindow hr
  obtain ⟨η', hη'pos, ε₁, hε₁pos, hsec⟩ := sectionLocal hr
  obtain ⟨sg, hsgpos, hsg⟩ := separation_of_close hr hη'pos
  -- velocity of the reference knot, uniformly continuous at the scale used in `chordDirPos`
  have hUCv : ∀ y z : ℝ, dist y z < vlo ^ 2 / (2 * vhi * Kv) →
      dist (velocity r y) (velocity r z) < vlo ^ 2 / (2 * vhi) := by
    intro y z hyz
    rw [dist_eq_norm] at hyz ⊢
    have h1 : ‖velocity r y - velocity r z‖ ≤ Kv * |y - z| := by
      simpa [abs_sub_comm] using hKvlip y z
    have h2 : Kv * |y - z| < Kv * (vlo ^ 2 / (2 * vhi * Kv)) := mul_lt_mul_of_pos_left hyz hKv
    have h3 : Kv * (vlo ^ 2 / (2 * vhi * Kv)) = vlo ^ 2 / (2 * vhi) := by
      field_simp
    linarith
  have hηvpos : 0 < vlo ^ 2 / (2 * vhi * Kv) := by positivity
  set ηm : ℝ := min η' (min (vlo ^ 2 / (2 * vhi * Kv)) T) with hηmdef
  have hηmpos : 0 < ηm := lt_min hη'pos (lt_min hηvpos hT)
  have hηmη' : ηm ≤ η' := le_trans (min_le_left _ _) le_rfl
  have hηmηv : ηm ≤ vlo ^ 2 / (2 * vhi * Kv) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηmT : ηm ≤ T := le_trans (min_le_right _ _) (min_le_right _ _)
  set Np : ℝ := max N 1 with hNpdef
  set κp : ℝ := max κ 1 with hκpdef
  have hNppos : 0 < Np := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκppos : 0 < κp := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hNleNp : N ≤ Np := le_max_left _ _
  have hκleκp : κ ≤ κp := le_max_left _ _
  have hNp1 : (1 : ℝ) ≤ Np := le_max_right _ _
  have hκp1 : (1 : ℝ) ≤ κp := le_max_right _ _
  -- the single small scale
  set sc : ℝ := min 1 (min (ηb / (4 * (vhi + 2))) (min ε₁ (min (ηm / (4 * Np * (vhi + 2)))
      (min (sg / (16 * κp * (vhi + 2))) (vlo ^ 2 / (4 * vhi * (vhi + 2))))))) with hscdef
  have hscpos : 0 < sc := by
    rw [hscdef]
    exact lt_min one_pos (lt_min (div_pos hηb (by positivity)) (lt_min hε₁pos
      (lt_min (div_pos hηmpos (by positivity)) (lt_min (div_pos hsgpos (by positivity))
        (div_pos (by positivity) (by positivity))))))
  have hsc1 : sc ≤ 1 := by rw [hscdef]; exact min_le_left _ _
  have hscηb : sc ≤ ηb / (4 * (vhi + 2)) := by
    rw [hscdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hscε₁ : sc ≤ ε₁ := by
    rw [hscdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hscηm : sc ≤ ηm / (4 * Np * (vhi + 2)) := by
    rw [hscdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hscsg : sc ≤ sg / (16 * κp * (vhi + 2)) := by
    rw [hscdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hscvlo : sc ≤ vlo ^ 2 / (4 * vhi * (vhi + 2)) := by
    rw [hscdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hscηb' : sc ≤ ηb := by
    have h1 : ηb / (4 * (vhi + 2)) ≤ ηb := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hηb.le, hvhi.le]
    linarith
  have hscsg4 : sc ≤ sg / 4 := by
    have h1 : (4 : ℝ) ≤ 16 * κp * (vhi + 2) := by nlinarith [hκp1, hvhi.le]
    have h2 : sg / (16 * κp * (vhi + 2)) ≤ sg / 4 :=
      div_le_div_of_nonneg_left hsgpos.le (by norm_num) h1
    linarith
  have hscvhi : sc * vhi < vlo ^ 2 / 2 := by
    have h1 : sc * vhi ≤ (vlo ^ 2 / (4 * vhi * (vhi + 2))) * vhi :=
      mul_le_mul_of_nonneg_right hscvlo hvhi.le
    have h2 : (vlo ^ 2 / (4 * vhi * (vhi + 2))) * vhi = vlo ^ 2 / (4 * (vhi + 2)) := by
      field_simp
    have h3 : vlo ^ 2 / (4 * (vhi + 2)) ≤ vlo ^ 2 / 4 := by
      have h4 : (4 : ℝ) ≤ 4 * (vhi + 2) := by nlinarith [hvhi.le]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h4
    have h5 : vlo ^ 2 / 4 < vlo ^ 2 / 2 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hvlo]
    linarith
  have hvhi2 : (1 : ℝ) + vhi / 2 ≤ vhi + 2 := by linarith [hvhi.le]
  -- the ball radius of the fibre construction
  set Th : ℝ := sc + vhi * (sc / 2) with hThdef
  have hTh_eq : Th = sc * (1 + vhi / 2) := by rw [hThdef]; ring
  have hThpos : 0 < Th := by rw [hTh_eq]; positivity
  have hThle : sc ≤ Th := by rw [hThdef]; nlinarith [hscpos, hvhi.le]
  have hThle₂ : Th ≤ sc * (vhi + 2) := by
    rw [hTh_eq]; exact mul_le_mul_of_nonneg_left hvhi2 hscpos.le
  have hThηb : Th ≤ ηb := by
    have h3 : sc * (vhi + 2) ≤ ηb / 4 := by
      have h4 : sc * (vhi + 2) ≤ (ηb / (4 * (vhi + 2))) * (vhi + 2) :=
        mul_le_mul_of_nonneg_right hscηb (by linarith [hvhi.le])
      have h5 : (ηb / (4 * (vhi + 2))) * (vhi + 2) = ηb / 4 := by field_simp
      linarith
    linarith [hThle₂, h3, hηb.le]
  have hNThδ : N * Th + sc / 2 ≤ ηm := by
    have h2 : N * Th ≤ Np * sc * (vhi + 2) := by
      have h2a : N * Th ≤ N * (sc * (vhi + 2)) := mul_le_mul_of_nonneg_left hThle₂ hN.le
      have h2b : N * (sc * (vhi + 2)) ≤ Np * (sc * (vhi + 2)) :=
        mul_le_mul_of_nonneg_right hNleNp (by positivity)
      linarith
    have h3 : Np * sc * (vhi + 2) ≤ ηm / 4 := by
      have h4 : Np * sc * (vhi + 2) ≤ Np * (ηm / (4 * Np * (vhi + 2))) * (vhi + 2) := by
        have h5 : sc * (vhi + 2) ≤ (ηm / (4 * Np * (vhi + 2))) * (vhi + 2) :=
          mul_le_mul_of_nonneg_right hscηm (by linarith [hvhi.le])
        nlinarith [h5, hNppos]
      have h6 : Np * (ηm / (4 * Np * (vhi + 2))) * (vhi + 2) = ηm / 4 := by
        field_simp
      linarith
    have h7 : sc / 2 ≤ ηm / 8 := by
      have h9 : (1 : ℝ) ≤ Np * (vhi + 2) := by nlinarith [hNp1, hvhi.le]
      have h10 : ηm / (4 * Np * (vhi + 2)) ≤ ηm / 4 :=
        div_le_div_of_nonneg_left hηmpos.le (by norm_num) (by nlinarith [h9])
      linarith
    linarith
  have hκTh : κ * Th + sc < sg / 2 := by
    have h2 : κ * Th ≤ κp * sc * (vhi + 2) := by
      have h2a : κ * Th ≤ κ * (sc * (vhi + 2)) := mul_le_mul_of_nonneg_left hThle₂ hκ.le
      have h2b : κ * (sc * (vhi + 2)) ≤ κp * (sc * (vhi + 2)) :=
        mul_le_mul_of_nonneg_right hκleκp (by positivity)
      linarith
    have h3 : κp * sc * (vhi + 2) ≤ sg / 16 := by
      have h4 : κp * sc * (vhi + 2) ≤ κp * (sg / (16 * κp * (vhi + 2))) * (vhi + 2) := by
        have h5 : sc * (vhi + 2) ≤ (sg / (16 * κp * (vhi + 2))) * (vhi + 2) :=
          mul_le_mul_of_nonneg_right hscsg (by linarith [hvhi.le])
        nlinarith [h5, hκppos]
      have h6 : κp * (sg / (16 * κp * (vhi + 2))) * (vhi + 2) = sg / 16 := by
        field_simp
      linarith
    have h7 : sc ≤ sg / 16 := by
      have h8 : (16 : ℝ) ≤ 16 * κp * (vhi + 2) := by nlinarith [hκp1, hvhi.le]
      have h9 : sg / (16 * κp * (vhi + 2)) ≤ sg / 16 :=
        div_le_div_of_nonneg_left hsgpos.le (by norm_num) h8
      linarith
    linarith
  refine ⟨sc, hscpos, sc, hscpos, ?_⟩
  intro r' hr' hclose A B hdist hshort hif
  have hAB : A ≠ B := by
    intro hAB
    subst hAB
    exact hif A (by simp [IsMiddleOnOpenChord, openSegment_same])
  obtain ⟨a, b, hab, hba, hcases⟩ := exists_order_lift hAB
  have core : ∀ (a b : ℝ) (A B : AddCircle period), a < b → b - a = dist A B →
      (a : AddCircle period) = A → (b : AddCircle period) = B → dist A B < sc →
      ‖knotMap r' A - knotMap r' B‖ < sc → ChordInteriorFree r' A B → TrivialSecant r' A B := by
    intro a b A B hab hba haA hbB hdist _hshort hif
    have hell : b - a < sc := by rw [hba]; exact hdist
    have hellpos : 0 < b - a := by linarith
    set mid : ℝ := (a + b) / 2 with hmiddef
    have habs : ∀ t : ℝ, t ∈ Set.Icc a b → |t - mid| ≤ (b - a) / 2 := by
      intro t ht
      rw [abs_le, hmiddef]
      constructor <;> linarith [ht.1, ht.2]
    -- the arc of `r'` lies in the ball of the fibre construction
    have hball : ∀ t ∈ Set.Icc a b, ‖r' t - r mid‖ < Th := by
      intro t ht
      have h1 : ‖r' t - r t‖ < sc := (hclose t).1
      have h2 : ‖r t - r mid‖ ≤ vhi * |t - mid| :=
        norm_sub_le_of_velocity_bound_mul (hr.smooth.differentiable (by simp)) hvhiup t mid
      have h3 : |t - mid| ≤ (b - a) / 2 := habs t ht
      have h4 : vhi * |t - mid| ≤ vhi * ((b - a) / 2) := mul_le_mul_of_nonneg_left h3 hvhi.le
      have h5 : vhi * ((b - a) / 2) < vhi * (sc / 2) := by
        have h6 : (b - a) / 2 < sc / 2 := by linarith
        exact mul_lt_mul_of_pos_left h6 hvhi
      calc ‖r' t - r mid‖ ≤ ‖r' t - r t‖ + ‖r t - r mid‖ := by
            rw [show r' t - r mid = (r' t - r t) + (r t - r mid) by abel]
            exact norm_add_le _ _
        _ ≤ sc + vhi * |t - mid| := by linarith
        _ ≤ sc + vhi * ((b - a) / 2) := by linarith
        _ < sc + vhi * (sc / 2) := by linarith
        _ = Th := by rw [hThdef]
    -- the chord
    set P : ℝ → Space := fun u => (1 - u) • r' a + u • r' b with hPdef
    have hPcont : Continuous (fun u : ℝ => P u) := by rw [hPdef]; fun_prop
    have hPball : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖P u - r mid‖ < Th := by
      intro u hu
      have hA : ‖r' a - r mid‖ < Th := hball a ⟨le_rfl, hab.le⟩
      have hB : ‖r' b - r mid‖ < Th := hball b ⟨hab.le, le_rfl⟩
      have hmem : P u - r mid = (1 - u) • (r' a - r mid) + u • (r' b - r mid) := by
        rw [hPdef]; simp only; module
      rw [hmem]
      exact lt_of_le_of_lt (norm_convex_combo_le hu) (max_lt hA hB)
    -- the fibre base map on the ball
    obtain ⟨base, hbase_spec, hbase_uniq, hbase_strict⟩ :=
      exists_base_function (r := r) (mid := mid) (Θ := Th) hT hThpos hThηb hwin
    have hbasecont : ContinuousOn base {q : Space | ‖q - r mid‖ ≤ Th} :=
      baseMap_continuousOn (T := T) (N := N) (κ := κ) (ηb := ηb) (Θ := Th) (a := mid)
        hbase_spec hbase_uniq
        (fun q hq y hy z hz hyz => hbase_strict q hq y z hy hz hyz) hvhi hvhiup
        (fun q => (continuous_const.sub hr.smooth.continuous).inner
          (hr.smooth.continuous_deriv le_top))
    -- the base along the arc
    set sgm : ℝ → ℝ := fun t => base (r' t) with hsgmdef
    have hsgmcont : ContinuousOn sgm (Set.Icc a b) := by
      have hmap : Set.MapsTo (fun t : ℝ => r' t) (Set.Icc a b)
          {q : Space | ‖q - r mid‖ ≤ Th} := fun t ht => le_of_lt (hball t ht)
      have h := hbasecont.comp hr'.smooth.continuous.continuousOn hmap
      simpa [hsgmdef, Function.comp_def] using h
    have hsgmclose : ∀ t ∈ Set.Icc a b, |sgm t - t| ≤ N * sc := by
      intro t ht
      obtain ⟨x, hx1, hx2, hx3⟩ := hwin t sc hscpos hscηb' t
        (by rw [sub_self, abs_zero]; linarith [hT]) (r' t) (le_of_lt (hclose t).1)
      have hxmem : x ∈ Set.Ioo (mid - T) (mid + T) := by
        have h1 : |x - t| ≤ N * sc := hx1.2.2.1
        have h2 : |x - mid| ≤ |x - t| + |t - mid| := abs_sub_le x t mid
        have h3a : |t - mid| ≤ (b - a) / 2 := habs t ht
        have h3b : (b - a) / 2 < sc / 2 := by linarith
        have h3c : N * sc ≤ N * Th := mul_le_mul_of_nonneg_left hThle hN.le
        have h3 : |x - mid| < T := by linarith [h1, h2, h3a, h3b, h3c, hNThδ, hηmT]
        rw [abs_lt] at h3
        rw [Set.mem_Ioo]
        constructor <;> linarith [h3.1, h3.2]
      have hxbase : x = base (r' t) :=
        hbase_uniq (r' t) (le_of_lt (hball t ht)) x hxmem hx1.2.1
      have hsgmx : sgm t = x := by rw [hsgmdef]; exact hxbase.symm
      rw [hsgmx]
      exact hx1.2.2.1
    have hsgminj : Set.InjOn sgm (Set.Icc a b) := by
      intro s hs t ht hst
      have h1c : N * sc ≤ N * Th := mul_le_mul_of_nonneg_left hThle hN.le
      have hs' : |s - sgm s| ≤ η' := by
        have h := hsgmclose s hs
        rw [abs_sub_comm] at h
        linarith [h, h1c, hNThδ, hηmη']
      have ht' : |t - sgm s| ≤ η' := by
        have h2 := hsgmclose t ht
        rw [abs_sub_comm, ← hst] at h2
        linarith [h2, h1c, hNThδ, hηmη']
      have h1 : inner ℝ (r' s - r (sgm s)) (velocity r (sgm s)) = 0 :=
        (hbase_spec (r' s) (le_of_lt (hball s hs))).2.1
      have h2 : inner ℝ (r' t - r (sgm s)) (velocity r (sgm s)) = 0 := by
        have h3 : inner ℝ (r' t - r (sgm t)) (velocity r (sgm t)) = 0 :=
          (hbase_spec (r' t) (le_of_lt (hball t ht))).2.1
        rwa [← hst] at h3
      exact hsec r' (hr'.smooth.differentiable (by simp))
        (fun u => lt_of_lt_of_le (hclose u).2 hscε₁) s t (sgm s) hs' ht' h1 h2
    -- the base along the chord
    set β : ℝ → ℝ := fun u => base (P u) with hβdef
    have hβcont : ContinuousOn β (Set.Icc (0:ℝ) 1) := by
      have hmap : Set.MapsTo (fun u : ℝ => P u) (Set.Icc (0:ℝ) 1)
          {q : Space | ‖q - r mid‖ ≤ Th} := fun u hu => le_of_lt (hPball u hu)
      have h := hbasecont.comp hPcont.continuousOn hmap
      simpa [hβdef, Function.comp_def] using h
    have hβ0 : β 0 = sgm a := by
      have h : P 0 = r' a := by rw [hPdef]; simp
      show base (P 0) = base (r' a)
      rw [h]
    have hβ1 : β 1 = sgm b := by
      have h : P 1 = r' b := by rw [hPdef]; simp
      show base (P 1) = base (r' b)
      rw [h]
    have hPwall : ∀ u : ℝ, P u = knotMap r' A + u • (knotMap r' B - knotMap r' A) := by
      intro u
      rw [hPdef, ← haA, ← hbB, knotMap_coe_of_periodic hr'.periodic,
        knotMap_coe_of_periodic hr'.periodic]
      module
    have hβinj : Set.InjOn β (Set.Icc (0:ℝ) 1) := by
      intro u hu v hv huv
      have hPu : inner ℝ (P u - r (β u)) (velocity r (β u)) = 0 :=
        (hbase_spec (P u) (le_of_lt (hPball u hu))).2.1
      have hPv : inner ℝ (P v - r (β u)) (velocity r (β u)) = 0 := by
        have h := (hbase_spec (P v) (le_of_lt (hPball v hv))).2.1
        have huv' : base (P u) = base (P v) := huv
        rw [← huv'] at h
        exact h
      have hzero : inner ℝ ((u - v) • (r' b - r' a)) (velocity r (β u)) = 0 := by
        have h : inner ℝ (P u - P v) (velocity r (β u)) = 0 := by
          rw [show P u - P v = (P u - r (β u)) - (P v - r (β u)) by abel, inner_sub_left,
            hPu, hPv, sub_zero]
        have h2 : P u - P v = (u - v) • (r' b - r' a) := by rw [hPdef]; simp only; module
        rwa [h2] at h
      have hdir : 0 < inner ℝ (r' b - r' a) (velocity r (β u)) := by
        have hb3 : |β u - mid| ≤ N * Th :=
          (hbase_spec (P u) (le_of_lt (hPball u hu))).2.2.1
        refine chordDirPos (c := vlo) (Lv := vhi) (ε := sc) (ηv := vlo ^ 2 / (2 * vhi * Kv))
          (a := a) (b := b) (x := β u) hvlo hvhi hvlole hvhiup
          (hr'.smooth.differentiable (by simp)) hUCv hscpos hscvhi (fun t => (hclose t).2) hab ?_
        intro t ht
        have h1 : |t - β u| ≤ |t - mid| + |mid - β u| := abs_sub_le t mid (β u)
        have h2 : |t - mid| ≤ (b - a) / 2 := habs t ht
        have h3 : |mid - β u| ≤ N * Th := by rw [abs_sub_comm]; exact hb3
        have h4 : (b - a) / 2 < sc / 2 := by linarith
        linarith [h1, h2, h3, h4, hNThδ, hηmηv]
      have hmul : (u - v) * inner ℝ (r' b - r' a) (velocity r (β u)) = 0 := by
        rw [inner_smul_left] at hzero
        simpa using hzero
      have huv0 : u - v = 0 := by
        rcases mul_eq_zero.mp hmul with h | h
        · exact h
        · exact absurd h (ne_of_gt hdir)
      linarith
    -- matching the chord to the arc in the common fibre
    have hβimg : β '' Set.Icc (0:ℝ) 1 = Set.Icc (min (β 0) (β 1)) (max (β 0) (β 1)) :=
      image_Icc_eq_min_max zero_le_one hβcont hβinj
    have hsgmimg : sgm '' Set.Icc a b = Set.Icc (min (sgm a) (sgm b)) (max (sgm a) (sgm b)) :=
      image_Icc_eq_min_max hab.le hsgmcont hsgminj
    have hβinjI : Function.Injective (fun u : I => β (u : ℝ)) := by
      intro u v huv
      exact Subtype.ext (hβinj u.2 v.2 huv)
    have hmem : ∀ u : I, ∃ x : Set.Icc a b, sgm (x : ℝ) = β (u : ℝ) := by
      intro u
      have h1 : β (u : ℝ) ∈ β '' Set.Icc (0:ℝ) 1 := ⟨(u : ℝ), u.2, rfl⟩
      rw [hβimg, hβ0, hβ1] at h1
      have h2 : β (u : ℝ) ∈ sgm '' Set.Icc a b := by rw [hsgmimg]; exact h1
      obtain ⟨x, hx, hxeq⟩ := h2
      exact ⟨⟨x, hx⟩, hxeq⟩
    have hxi : Continuous (fun u : I => β (u : ℝ)) :=
      hβcont.comp_continuous continuous_subtype_val (fun u => u.2)
    obtain ⟨tfun, htcont, htmem, htsigma, ht0, ht1, htinj⟩ :=
      exists_continuous_lift hab.le hsgmcont hsgminj hxi hβinjI hmem hβ0 hβ1
    -- the ribbon
    let arc : I → Space := fun u => r' (tfun u)
    have harcval : ∀ u : I, arc u = r' (tfun u) := fun u => rfl
    have harccont : Continuous arc := hr'.smooth.continuous.comp htcont
    have harcinj : Function.Injective arc := by
      intro u v huv
      have h1 : ((tfun u : ℝ) : AddCircle period) = ((tfun v : ℝ) : AddCircle period) := by
        apply knotMap_injective hr'
        rw [knotMap_coe_of_periodic hr'.periodic, knotMap_coe_of_periodic hr'.periodic]
        exact huv
      have h2 : |tfun u - tfun v| < period := by
        have h3 : |tfun u - tfun v| ≤ b - a := by
          have h4 : tfun u ∈ Set.Icc a b := htmem u
          have h5 : tfun v ∈ Set.Icc a b := htmem v
          rw [abs_le]
          constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
        linarith [h3, hell, hsc1, period_gt_one]
      exact htinj (coe_eq_of_abs_lt h1 h2)
    have harcmem : ∀ u : I, arc u ∈ Set.range (knotMap r') := fun u =>
      ⟨((tfun u : ℝ) : AddCircle period), by rw [harcval, knotMap_coe_of_periodic hr'.periodic]⟩
    let α : Path (knotMap r' A) (knotMap r' B) :=
      { toFun := arc
        continuous_toFun := harccont
        source' := by
          show arc 0 = knotMap r' A
          rw [harcval, ht0, ← haA, knotMap_coe_of_periodic hr'.periodic]
        target' := by
          show arc 1 = knotMap r' B
          rw [harcval, ht1, ← hbB, knotMap_coe_of_periodic hr'.periodic] }
    have hchordP : ∀ u : I, (chordPath r' A B) u = P (u : ℝ) := by
      intro u
      show chordMap r' A B u = P (u : ℝ)
      rw [hPdef]
      simp only [chordMap]
      rw [← haA, ← hbB, knotMap_coe_of_periodic hr'.periodic, knotMap_coe_of_periodic hr'.periodic]
      module
    let Dfun : I × I → Space :=
      fun p => (1 - (p.2 : ℝ)) • arc p.1 + (p.2 : ℝ) • (chordPath r' A B) p.1
    have hDval : ∀ p : I × I,
        Dfun p = (1 - (p.2 : ℝ)) • arc p.1 + (p.2 : ℝ) • (chordPath r' A B) p.1 := fun p => rfl
    have hDcont : Continuous Dfun := by
      rw [show Dfun = fun p : I × I =>
          (1 - (p.2 : ℝ)) • arc p.1 + (p.2 : ℝ) • (chordPath r' A B) p.1 from rfl]
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
          (harccont.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_snd).smul
          ((chordPath r' A B).continuous.comp continuous_fst))
    refine ⟨α, hif, ⟨harcinj, harcmem⟩, ⟨⟨Dfun, hDcont⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro s
      show (1 - ((0 : I) : ℝ)) • arc s + ((0 : I) : ℝ) • (chordPath r' A B) s = arc s
      simp
    · intro s
      show (1 - ((1 : I) : ℝ)) • arc s + ((1 : I) : ℝ) • (chordPath r' A B) s = (chordPath r' A B) s
      simp
    · intro t
      show (1 - (t : ℝ)) • arc (0 : I) + (t : ℝ) • (chordPath r' A B) (0 : I) = knotMap r' A
      have h1 : arc (0 : I) = knotMap r' A := by
        rw [harcval, ht0, ← haA, knotMap_coe_of_periodic hr'.periodic]
      have h2 : (chordPath r' A B) (0 : I) = knotMap r' A := by
        change chordMap r' A B (0 : I) = knotMap r' A
        exact chordMap_zero r' A B
      rw [h1, h2]
      module
    · intro t
      show (1 - (t : ℝ)) • arc (1 : I) + (t : ℝ) • (chordPath r' A B) (1 : I) = knotMap r' B
      have h1 : arc (1 : I) = knotMap r' B := by
        rw [harcval, ht1, ← hbB, knotMap_coe_of_periodic hr'.periodic]
      have h2 : (chordPath r' A B) (1 : I) = knotMap r' B := by
        change chordMap r' A B (1 : I) = knotMap r' B
        exact chordMap_one r' A B
      rw [h1, h2]
      module
    · intro u v hu0 hu1 hv0 hv1 hmemK
      obtain ⟨w, hw⟩ := hmemK
      obtain ⟨w0, _, hw0eq⟩ := AddCircle.eq_coe_Ico (p := period) w
      have hw0 : r' w0 = Dfun (u, v) := by
        have hk : knotMap r' (w0 : AddCircle period) = Dfun (u, v) := by rw [hw0eq]; exact hw
        rw [← knotMap_coe_of_periodic hr'.periodic w0]
        exact hk
      set x : ℝ := sgm (tfun u) with hxdef
      have hxβ : x = β (u : ℝ) := by rw [hxdef, htsigma u]
      have hxarc : inner ℝ (arc u - r x) (velocity r x) = 0 :=
        (hbase_spec (r' (tfun u)) (le_of_lt (hball (tfun u) (htmem u)))).2.1
      have hxchord : inner ℝ ((chordPath r' A B) u - r x) (velocity r x) = 0 := by
        have h := (hbase_spec (P (u : ℝ)) (le_of_lt (hPball (u : ℝ) u.2))).2.1
        have hxβ' : x = base (P (u : ℝ)) := hxβ
        rw [← hxβ'] at h
        rw [← hchordP u] at h
        exact h
      have hDfib : inner ℝ (Dfun (u, v) - r x) (velocity r x) = 0 := by
        rw [hDval]
        exact inner_fiber_smul_add hxarc hxchord ((v : I) : ℝ)
      have hDnorm : ‖Dfun (u, v) - r x‖ ≤ κ * Th := by
        have h1 : ‖arc u - r x‖ ≤ κ * Th :=
          (hbase_spec (r' (tfun u)) (le_of_lt (hball (tfun u) (htmem u)))).2.2.2
        have h2 : ‖(chordPath r' A B) u - r x‖ ≤ κ * Th := by
          have h := (hbase_spec (P (u : ℝ)) (le_of_lt (hPball (u : ℝ) u.2))).2.2.2
          have hxβ' : x = base (P (u : ℝ)) := hxβ
          rw [← hxβ'] at h
          rw [← hchordP u] at h
          exact h
        rw [hDval]
        have heq : (1 - ((v : I) : ℝ)) • arc u + ((v : I) : ℝ) • (chordPath r' A B) u - r x
            = (1 - ((v : I) : ℝ)) • (arc u - r x) + ((v : I) : ℝ) • ((chordPath r' A B) u - r x) := by
          module
        rw [heq]
        exact le_trans (norm_convex_combo_le v.2) (max_le h1 h2)
      have hxbound : ‖r' w0 - r' x‖ ≤ κ * Th + sc := by
        calc ‖r' w0 - r' x‖ = ‖Dfun (u, v) - r' x‖ := by rw [hw0]
          _ ≤ ‖Dfun (u, v) - r x‖ + ‖r x - r' x‖ := by
              rw [show Dfun (u, v) - r' x = (Dfun (u, v) - r x) + (r x - r' x) by abel]
              exact norm_add_le _ _
          _ ≤ κ * Th + sc := by
              rw [norm_sub_rev (r x) (r' x)]
              have h := (hclose x).1
              linarith [hDnorm, h]
      have hwx : dist (w0 : AddCircle period) (x : AddCircle period) < η' := by
        by_contra hge
        have h1 : η' ≤ dist (w0 : AddCircle period) (x : AddCircle period) := le_of_not_gt hge
        have h2 : sg / 2 ≤
            ‖knotMap r' (w0 : AddCircle period) - knotMap r' (x : AddCircle period)‖ :=
          hsg r' hr' (fun t => ⟨lt_of_lt_of_le (hclose t).1 hscsg4,
            lt_of_lt_of_le (hclose t).2 hscsg4⟩) _ _ h1
        rw [knotMap_coe_of_periodic hr'.periodic, knotMap_coe_of_periodic hr'.periodic] at h2
        linarith [h2, hxbound, hκTh]
      obtain ⟨k, hk⟩ := addCircle_dist_eq_shift w0 x
      set w1 : ℝ := w0 - k * period with hw1def
      have hw1x : |w1 - x| < η' := by rw [hw1def]; rw [hk]; exact hwx
      have hw1r : r' w1 = r' w0 := by
        calc r' w1 = r' (w1 + k • period) := (hr'.periodic.zsmul k w1).symm
          _ = r' w0 := by
              congr 1
              rw [hw1def, zsmul_eq_mul]; ring
      have htx : |tfun u - x| ≤ η' := by
        have h1 : |tfun u - sgm (tfun u)| ≤ N * sc := by
          have h := hsgmclose (tfun u) (htmem u)
          rwa [abs_sub_comm] at h
        rw [← hxdef] at h1
        have h2 : N * sc ≤ N * Th := mul_le_mul_of_nonneg_left hThle hN.le
        linarith [h1, h2, hNThδ, hηmη']
      have hfinal : r' (tfun u) = Dfun (u, v) := by
        have h1 : r' w1 = Dfun (u, v) := hw1r.trans hw0
        have h2 : inner ℝ (r' w1 - r x) (velocity r x) = 0 := by rw [h1]; exact hDfib
        have h3 : inner ℝ (r' (tfun u) - r x) (velocity r x) = 0 := hxarc
        have h4 : tfun u = w1 :=
          hsec r' (hr'.smooth.differentiable (by simp))
            (fun s => lt_of_lt_of_le (hclose s).2 hscε₁) (tfun u) w1 x htx (le_of_lt hw1x) h3 h2
        rw [h4, h1]
      have herr : ((v : I) : ℝ) • ((chordPath r' A B) u - r' (tfun u)) = 0 := by
        have hD : Dfun (u, v)
            = (1 - ((v : I) : ℝ)) • r' (tfun u) + ((v : I) : ℝ) • (chordPath r' A B) u := by
          rw [hDval]
        rw [hD] at hfinal
        have h : (1 - ((v : I) : ℝ)) • r' (tfun u) + ((v : I) : ℝ) • (chordPath r' A B) u
            - r' (tfun u) = 0 := by rw [← hfinal]; abel
        rw [show (1 - ((v : I) : ℝ)) • r' (tfun u) + ((v : I) : ℝ) • (chordPath r' A B) u
            - r' (tfun u) = ((v : I) : ℝ) • ((chordPath r' A B) u - r' (tfun u)) by module] at h
        exact h
      have hvne : ((v : I) : ℝ) ≠ 0 := hv0
      have hchord_eq : (chordPath r' A B) u = r' (tfun u) := by
        rcases smul_eq_zero.mp herr with h | h
        · exact absurd h hvne
        · exact sub_eq_zero.mp h
      have hmid_on : IsMiddleOnOpenChord r' A B ((tfun u : ℝ) : AddCircle period) := by
        have h1 : r' (tfun u) = P (u : ℝ) := by rw [← hchord_eq, hchordP u]
        have hA : knotMap r' A = r' a := by rw [← haA, knotMap_coe_of_periodic hr'.periodic]
        have hB : knotMap r' B = r' b := by rw [← hbB, knotMap_coe_of_periodic hr'.periodic]
        rw [IsMiddleOnOpenChord, knotMap_coe_of_periodic hr'.periodic, h1, hA, hB, hPdef, openSegment]
        have hu_pos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
        have hu_lt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu1
        exact ⟨1 - (u : ℝ), (u : ℝ), by linarith, by exact hu_pos, by ring, by module⟩
      exact hif _ hmid_on
  rcases hcases with ⟨haA, hbB⟩ | ⟨haB, hbA⟩
  · exact core a b A B hab hba haA hbB hdist hshort hif
  · exact (TrivialSecant_swap r' A B).mpr
      (core a b B A hab (by rw [hba, dist_comm]) haB hbA (by rwa [dist_comm])
        (by rwa [norm_sub_rev]) (ChordInteriorFree_symm r' A B hif))

end

end Work.Drive
