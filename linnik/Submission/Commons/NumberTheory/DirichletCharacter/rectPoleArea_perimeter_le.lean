import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.MeasureTheory.measurePreserving_swap

open MeasureTheory ENNReal
open scoped ENNReal Real Topology Interval

noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

private lemma volume_abs_le_real (c r : ℝ) :
    (volume : Measure ℝ) {y : ℝ | |y - c| ≤ r} = ENNReal.ofReal (2 * r) := by
  have hset : ({y : ℝ | |y - c| ≤ r} : Set ℝ) = Metric.closedBall c r := by
    ext y
    simp [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
  rw [hset]
  rw [Real.volume_closedBall]

private lemma lintegral_Icc_indicator_abs_le (c r lo hi : ℝ) :
    (∫⁻ y : ℝ in Set.Icc lo hi,
        (Set.indicator {y : ℝ | |y - c| ≤ r} (fun _ : ℝ => (1 : ℝ≥0∞))) y) ≤
      ENNReal.ofReal (2 * r) := by
  let C : Set ℝ := {y : ℝ | |y - c| ≤ r}
  have hC : MeasurableSet C := by
    dsimp [C]
    measurability
  calc
    (∫⁻ y : ℝ in Set.Icc lo hi,
        (Set.indicator {y : ℝ | |y - c| ≤ r} (fun _ : ℝ => (1 : ℝ≥0∞))) y)
        = ∫⁻ y : ℝ, (Set.indicator C (fun _ : ℝ => (1 : ℝ≥0∞))) y
            ∂(volume.restrict (Set.Icc lo hi)) := rfl
    _ = (∫⁻ y : ℝ in C, (1 : ℝ≥0∞) ∂(volume.restrict (Set.Icc lo hi))) := by
            rw [lintegral_indicator hC]
    _ = (volume.restrict (Set.Icc lo hi)) C := by simp
    _ = (volume : Measure ℝ) (C ∩ Set.Icc lo hi) := by
            rw [Measure.restrict_apply hC]
    _ ≤ (volume : Measure ℝ) C := measure_mono Set.inter_subset_left
    _ = ENNReal.ofReal (2 * r) := by
            dsimp [C]
            rw [volume_abs_le_real]

private lemma ofReal_inv_mul_two_mul_le_two {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal (a⁻¹) * ENNReal.ofReal (2 * a) ≤ ENNReal.ofReal 2 := by
  by_cases ha0 : a = 0
  · subst a
    simp
  · have hapos : 0 < a := lt_of_le_of_ne ha (fun h => ha0 h.symm)
    have hcalc : ENNReal.ofReal (a⁻¹) * ENNReal.ofReal (2 * a) = ENNReal.ofReal 2 := by
      have hmul : ENNReal.ofReal (a⁻¹ * (2 * a)) =
          ENNReal.ofReal (a⁻¹) * ENNReal.ofReal (2 * a) :=
        ENNReal.ofReal_mul (inv_nonneg.mpr ha)
      rw [← hmul]
      congr 1
      field_simp [ha0]
    exact le_of_eq hcalc

private lemma lintegral_box_iteratedX {x0 x1 y0 y1 : ℝ}
    (h : ℝ × ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ p : ℝ × ℝ, h p
        ∂(volume.restrict (Set.Icc x0 x1 ×ˢ Set.Icc y0 y1))) =
      ∫⁻ x : ℝ in Set.Icc x0 x1,
        ∫⁻ y : ℝ in Set.Icc y0 y1, h (x, y) ∂volume ∂volume := by
  let s : Set ℝ := Set.Icc x0 x1
  let t : Set ℝ := Set.Icc y0 y1
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  calc
    (∫⁻ p : ℝ × ℝ, h p ∂(volume.restrict (s ×ˢ t)))
        = ∫⁻ p : ℝ × ℝ in s ×ˢ t, h p ∂volume := rfl
    _ = ∫⁻ x : ℝ in s, ∫⁻ y : ℝ in t, h (x, y) ∂volume ∂volume := by
            rw [hvol]
            simpa [s, t] using
              (setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
                (s := s) (t := t) (f := h) (by simpa [hvol] using hh.aemeasurable))

private lemma lintegral_restrict_swap {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p : ℝ × ℝ, F p ∂(volume.restrict (s ×ˢ t))) =
      (∫⁻ q : ℝ × ℝ, F (q.2, q.1) ∂(volume.restrict (t ×ˢ s))) := by
  let sw : ℝ × ℝ → ℝ × ℝ := fun p => (p.2, p.1)
  have hmp : MeasurePreserving sw volume volume := by
    dsimp [sw]
    exact Commons.Analysis.MeasureTheory.measurePreserving_swap
  calc
    (∫⁻ p : ℝ × ℝ, F p ∂(volume.restrict (s ×ˢ t)))
        = ∫⁻ p : ℝ × ℝ, (s ×ˢ t).indicator F p ∂volume := by
            rw [lintegral_indicator (hs.prod ht)]
    _ = ∫⁻ p : ℝ × ℝ, ((s ×ˢ t).indicator F) (p.2, p.1) ∂volume := by
            have hmeas : Measurable ((s ×ˢ t).indicator F) := Measurable.indicator hF (hs.prod ht)
            have h := hmp.lintegral_comp (f := (s ×ˢ t).indicator F) hmeas
            simpa [sw] using h.symm
    _ = ∫⁻ p : ℝ × ℝ, (t ×ˢ s).indicator (fun r : ℝ × ℝ => F (r.2, r.1)) p ∂volume := by
            apply lintegral_congr
            intro q
            by_cases hq : q ∈ t ×ˢ s
            · have hq' : (q.2, q.1) ∈ s ×ˢ t := by
                rcases hq with ⟨hqt, hqs⟩
                exact ⟨hqs, hqt⟩
              simp [hq, hq']
            · have hqn : (q.2, q.1) ∉ s ×ˢ t := by
                intro hx
                apply hq
                exact ⟨hx.2, hx.1⟩
              simp [hq, hqn]
    _ = ∫⁻ q : ℝ × ℝ, F (q.2, q.1) ∂(volume.restrict (t ×ˢ s)) := by
            rw [lintegral_indicator (ht.prod hs)]

private lemma ofReal_inv_norm_le_of_sum (a b : ℝ) (p : ℝ × ℝ) :
    ENNReal.ofReal ‖(p.1 - a, p.2 - b)‖⁻¹ ≤
      (Set.indicator {q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|}
          (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - a|⁻¹))) p +
      (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
          (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p := by
  classical
  by_cases h : |p.2 - b| ≤ |p.1 - a|
  · have hmem : p ∈ ({q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|} : Set (ℝ × ℝ)) := by
      simpa using h
    calc
      ENNReal.ofReal ‖(p.1 - a, p.2 - b)‖⁻¹
          = ENNReal.ofReal ((max (|p.1 - a|) (|p.2 - b|))⁻¹) := by
              simp [Prod.norm_def, Real.norm_eq_abs]
      _ = ENNReal.ofReal (|p.1 - a|⁻¹) := by
              congr 1
              rw [max_eq_left h]
      _ ≤ (Set.indicator {q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|}
              (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - a|⁻¹))) p +
          (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
              (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p := by
              have h1 : (Set.indicator {q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|}
                  (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - a|⁻¹))) p =
                  ENNReal.ofReal (|p.1 - a|⁻¹) := by
                simp [hmem]
              rw [h1]
              exact le_add_of_nonneg_right zero_le
  · have hle : |p.1 - a| ≤ |p.2 - b| := le_of_lt (lt_of_not_ge h)
    have hmem : p ∈ ({q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|} : Set (ℝ × ℝ)) := by
      simpa using hle
    calc
      ENNReal.ofReal ‖(p.1 - a, p.2 - b)‖⁻¹
          = ENNReal.ofReal ((max (|p.1 - a|) (|p.2 - b|))⁻¹) := by
              simp [Prod.norm_def, Real.norm_eq_abs]
      _ = ENNReal.ofReal (|p.2 - b|⁻¹) := by
              congr 1
              rw [max_eq_right hle]
      _ ≤ (Set.indicator {q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|}
              (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - a|⁻¹))) p +
          (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
              (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p := by
              have h2 : (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
                  (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p =
                  ENNReal.ofReal (|p.2 - b|⁻¹) := by
                simp [hmem]
              rw [h2]
              exact le_add_of_nonneg_left zero_le

private lemma lintegral_axisX_le (p0 p1 q0 q1 c1 c2 : ℝ) :
    (∫⁻ p : ℝ × ℝ,
        (Set.indicator {q : ℝ × ℝ | |q.2 - c2| ≤ |q.1 - c1|}
            (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - c1|⁻¹))) p
        ∂(volume.restrict (Set.Icc p0 p1 ×ˢ Set.Icc q0 q1))) ≤
      ENNReal.ofReal (2 * (p1 - p0)) := by
  classical
  let s : Set ℝ := Set.Icc p0 p1
  let t : Set ℝ := Set.Icc q0 q1
  let C : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.2 - c2| ≤ |q.1 - c1|}
  let h : ℝ × ℝ → ℝ≥0∞ := fun q : ℝ × ℝ => C.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - c1|⁻¹)) q
  have hmeas_C : MeasurableSet C := by
    dsimp [C]
    measurability
  have hmeas_h : Measurable h := by
    dsimp [h]
    exact Measurable.indicator (by measurability) hmeas_C
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Icc
  have ht : MeasurableSet t := by
    dsimp [t]
    exact measurableSet_Icc
  have hpoint : ∀ x : ℝ, (∫⁻ y : ℝ in t, h (x, y) ∂volume) ≤ ENNReal.ofReal 2 := by
    intro x
    let Cx : Set ℝ := {y : ℝ | |y - c2| ≤ |x - c1|}
    have hmeas_Cx : MeasurableSet Cx := by
      dsimp [Cx]
      measurability
    have hxy_eq : ∀ y : ℝ,
        h (x, y) = ENNReal.ofReal (|x - c1|⁻¹) * (Cx.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) y := by
      intro y
      dsimp [h, Cx, C]
      by_cases hcy : |y - c2| ≤ |x - c1|
      · simp [hcy]
      · simp [hcy]
    calc
      (∫⁻ y : ℝ in t, h (x, y) ∂volume)
          = ∫⁻ y : ℝ in t,
              ENNReal.ofReal (|x - c1|⁻¹) * (Cx.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) y ∂volume := by
              apply lintegral_congr
              intro y
              exact hxy_eq y
      _ = ENNReal.ofReal (|x - c1|⁻¹) *
            (∫⁻ y : ℝ in t, (Cx.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) y ∂volume) := by
            rw [lintegral_const_mul]
            exact Measurable.indicator measurable_const hmeas_Cx
      _ ≤ ENNReal.ofReal (|x - c1|⁻¹) * ENNReal.ofReal (2 * |x - c1|) := by
            exact mul_le_mul_of_nonneg_left
              (lintegral_Icc_indicator_abs_le c2 (|x - c1|) q0 q1) zero_le
      _ ≤ ENNReal.ofReal 2 := by
            exact ofReal_inv_mul_two_mul_le_two (abs_nonneg (x - c1))
  calc
    (∫⁻ p : ℝ × ℝ,
        (Set.indicator {q : ℝ × ℝ | |q.2 - c2| ≤ |q.1 - c1|}
            (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - c1|⁻¹))) p
        ∂(volume.restrict (Set.Icc p0 p1 ×ˢ Set.Icc q0 q1)))
        = ∫⁻ p : ℝ × ℝ, h p
            ∂(volume.restrict (Set.Icc p0 p1 ×ˢ Set.Icc q0 q1)) := by
            simp [h, C]
    _ = ∫⁻ x : ℝ in s, ∫⁻ y : ℝ in t, h (x, y) ∂volume ∂volume := by
            exact lintegral_box_iteratedX (x0 := p0) (x1 := p1) (y0 := q0) (y1 := q1) h hmeas_h
    _ ≤ ∫⁻ x : ℝ in s, ENNReal.ofReal 2 ∂volume := by
            exact lintegral_mono (fun x => hpoint x)
    _ = ENNReal.ofReal 2 * volume s := by
            simp
    _ = ENNReal.ofReal (2 * (p1 - p0)) := by
            have hvols : volume s = ENNReal.ofReal (p1 - p0) := by
              dsimp [s]
              rw [Real.volume_Icc]
            rw [hvols]
            exact (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm

private lemma lintegral_axisY_le (x0 x1 y0 y1 a b : ℝ) :
    (∫⁻ p : ℝ × ℝ,
        (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
            (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p
        ∂(volume.restrict (Set.Icc x0 x1 ×ˢ Set.Icc y0 y1))) ≤
      ENNReal.ofReal (2 * (y1 - y0)) := by
  classical
  let s : Set ℝ := Set.Icc x0 x1
  let t : Set ℝ := Set.Icc y0 y1
  let F : ℝ × ℝ → ℝ≥0∞ := fun p : ℝ × ℝ =>
    (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
        (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Icc
  have ht : MeasurableSet t := by
    dsimp [t]
    exact measurableSet_Icc
  have hF : Measurable F := by
    dsimp [F]
    exact Measurable.indicator (by measurability) (by measurability)
  have hswap := lintegral_restrict_swap hs ht hF
  have hX := lintegral_axisX_le y0 y1 x0 x1 b a
  have hEq : (fun q : ℝ × ℝ => F (q.2, q.1)) =
      fun q : ℝ × ℝ => (Set.indicator {r : ℝ × ℝ | |r.2 - a| ≤ |r.1 - b|}
          (fun r : ℝ × ℝ => ENNReal.ofReal (|r.1 - b|⁻¹))) q := by
    funext q
    dsimp [F]
    by_cases hq : |q.2 - a| ≤ |q.1 - b|
    · simp [hq]
    · simp [hq]
  calc
    (∫⁻ p : ℝ × ℝ,
        (Set.indicator {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
            (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p
        ∂(volume.restrict (s ×ˢ t)))
        = ∫⁻ p : ℝ × ℝ, F p ∂(volume.restrict (s ×ˢ t)) := by
            simp [F]
    _ = ∫⁻ q : ℝ × ℝ, F (q.2, q.1) ∂(volume.restrict (t ×ˢ s)) := hswap
    _ = ∫⁻ q : ℝ × ℝ,
        (Set.indicator {r : ℝ × ℝ | |r.2 - a| ≤ |r.1 - b|}
            (fun r : ℝ × ℝ => ENNReal.ofReal (|r.1 - b|⁻¹))) q
        ∂(volume.restrict (t ×ˢ s)) := by
            rw [hEq]
    _ ≤ ENNReal.ofReal (2 * (y1 - y0)) := by
            simpa [t, s] using hX

/-- **Bound on the singular `1/‖p‖` integral over an arbitrary rectangle.** -/
theorem lintegral_inv_norm_rect_le {x0 x1 y0 y1 a b : ℝ} :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ‖(p.1 - a, p.2 - b)‖⁻¹
        ∂(MeasureTheory.volume.restrict
          (Set.Icc x0 x1 ×ˢ Set.Icc y0 y1))) ≤
      ENNReal.ofReal (2 * (x1 - x0)) + ENNReal.ofReal (2 * (y1 - y0)) := by
  classical
  let s : Set ℝ := Set.Icc x0 x1
  let t : Set ℝ := Set.Icc y0 y1
  let C1 : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.2 - b| ≤ |q.1 - a|}
  let C2 : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.1 - a| ≤ |q.2 - b|}
  let f0 : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ‖(p.1 - a, p.2 - b)‖⁻¹
  let g1 : ℝ × ℝ → ℝ≥0∞ := fun p =>
    (C1.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (|q.1 - a|⁻¹))) p
  let g2 : ℝ × ℝ → ℝ≥0∞ := fun p =>
    (C2.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (|q.2 - b|⁻¹))) p
  have hmeas_g1 : Measurable g1 := by
    dsimp [g1, C1]
    exact Measurable.indicator (by measurability) (by measurability)
  have hpt : f0 ≤ fun p : ℝ × ℝ => g1 p + g2 p := by
    intro p
    exact ofReal_inv_norm_le_of_sum a b p
  have hx := lintegral_axisX_le x0 x1 y0 y1 a b
  have hy := lintegral_axisY_le x0 x1 y0 y1 a b
  calc
    (∫⁻ p : ℝ × ℝ, f0 p ∂(volume.restrict (s ×ˢ t)))
        ≤ ∫⁻ p : ℝ × ℝ, (g1 p + g2 p) ∂(volume.restrict (s ×ˢ t)) := by
            exact lintegral_mono hpt
    _ = (∫⁻ p : ℝ × ℝ, g1 p ∂(volume.restrict (s ×ˢ t))) +
        (∫⁻ p : ℝ × ℝ, g2 p ∂(volume.restrict (s ×ˢ t))) := by
            rw [lintegral_add_left hmeas_g1]
    _ ≤ ENNReal.ofReal (2 * (x1 - x0)) + ENNReal.ofReal (2 * (y1 - y0)) := by
            dsimp [g1, g2, C1, C2, s, t]
            exact add_le_add hx hy


/-- the Euclidean reciprocal kernel of the pole `u` on coordinates `(x, T)`. -/
private def kern (u : ℂ) (x T : ℝ) : ℝ :=
  (Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2))⁻¹

private lemma kern_nonneg {x T : ℝ} {u : ℂ} : 0 ≤ kern u x T := by
  unfold kern
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private lemma kern_le_sup {x T : ℝ} {u : ℂ} :
    kern u x T ≤ ‖(T - u.im, x - u.re)‖⁻¹ := by
  unfold kern
  have hsqrt_ge1 : |x - u.re| ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
    calc
      |x - u.re| = Real.sqrt ((x - u.re) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
        exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqrt_ge2 : |T - u.im| ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
    calc
      |T - u.im| = Real.sqrt ((T - u.im) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
        exact Real.sqrt_le_sqrt (by nlinarith)
  have hsup_ge : max ‖T - u.im‖ ‖x - u.re‖ ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
    exact max_le (by simpa [Real.norm_eq_abs] using hsqrt_ge2)
      (by simpa [Real.norm_eq_abs] using hsqrt_ge1)
  have hsup_le_sqrt : ‖(T - u.im, x - u.re)‖ ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
    simpa [Prod.norm_def] using hsup_ge
  by_cases hpos : 0 < ‖(T - u.im, x - u.re)‖
  · simpa using (one_div_le_one_div_of_le hpos hsup_le_sqrt)
  · have hn0 : ‖(T - u.im, x - u.re)‖ = 0 := by linarith [norm_nonneg (T - u.im, x - u.re)]
    have hpair : (T - u.im, x - u.re) = (0, 0) := by
      simpa using (norm_eq_zero.mp hn0)
    have hp1 : T - u.im = 0 := by simpa using congrArg Prod.fst hpair
    have hp2 : x - u.re = 0 := by simpa using congrArg Prod.snd hpair
    simp [hp1, hp2]

private lemma measurable_kern {u : ℂ} : Measurable (fun p : ℝ × ℝ => kern u p.1 p.2) := by
  unfold kern
  fun_prop

private lemma indicator_eq_zero {α β : Type*} [Zero β] {s : Set α} {a : α} (ha : a ∉ s)
    (f : α → β) : s.indicator f a = 0 := by
  simp [ha]

private lemma ofReal_indicator' {α : Type*} {s : Set α} {a : α} (f : α → ℝ) :
    ENNReal.ofReal (s.indicator f a) = s.indicator (fun a => ENNReal.ofReal (f a)) a := by
  by_cases ha : a ∈ s
  · simp [ha]
  · simp [ha]

private lemma toReal_mono_of_le {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≠ ∞) : a.toReal ≤ b.toReal := by
  have ha : a ≠ ∞ := by
    intro ha_eq
    apply hb
    exact le_antisymm le_top (by simpa [ha_eq] using hab)
  exact (ENNReal.toReal_le_toReal ha hb).2 hab

private def gprod (u : ℂ) (y0 y1 x0 x1 : ℝ) : ℝ × ℝ → ℝ :=
  fun z => ((Set.Ioc y0 y1) ×ˢ (Set.Ioc x0 x1)).indicator (fun z => kern u z.2 z.1) z

private def supk (u : ℂ) : ℝ × ℝ → ℝ := fun z => ‖(z.1 - u.im, z.2 - u.re)‖⁻¹

private def supmaj (u : ℂ) (y0 y1 x0 x1 : ℝ) : ℝ × ℝ → ℝ :=
  fun z => ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)).indicator (fun z => supk u z) z

private lemma gprod_nonneg (u : ℂ) (y0 y1 x0 x1 : ℝ) (z : ℝ × ℝ) : 0 ≤ gprod u y0 y1 x0 x1 z := by
  unfold gprod
  by_cases hz : z ∈ (Set.Ioc y0 y1) ×ˢ (Set.Ioc x0 x1)
  · rw [Set.indicator_of_mem hz]
    exact kern_nonneg
  · rw [indicator_eq_zero hz]

private lemma supmaj_nonneg (u : ℂ) (y0 y1 x0 x1 : ℝ) (z : ℝ × ℝ) : 0 ≤ supmaj u y0 y1 x0 x1 z := by
  unfold supmaj
  by_cases hz : z ∈ (Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)
  · rw [Set.indicator_of_mem hz]
    exact inv_nonneg.mpr (norm_nonneg _)
  · rw [indicator_eq_zero hz]

private lemma gprod_le_supmaj (u : ℂ) (y0 y1 x0 x1 : ℝ) (z : ℝ × ℝ) :
    gprod u y0 y1 x0 x1 z ≤ supmaj u y0 y1 x0 x1 z := by
  unfold gprod supmaj
  by_cases hz : z ∈ (Set.Ioc y0 y1) ×ˢ (Set.Ioc x0 x1)
  · have hT0 : z.1 ∈ Set.Ioc y0 y1 := hz.1
    have hx0 : z.2 ∈ Set.Ioc x0 x1 := hz.2
    have hz' : z ∈ (Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1) :=
      ⟨Set.Ioc_subset_Icc_self hT0, Set.Ioc_subset_Icc_self hx0⟩
    rw [Set.indicator_of_mem hz]
    rw [Set.indicator_of_mem hz']
    exact kern_le_sup
  · rw [indicator_eq_zero hz]
    exact supmaj_nonneg u y0 y1 x0 x1 z

private lemma measurable_supk {u : ℂ} : Measurable (supk u) := by
  unfold supk
  fun_prop

private lemma measurable_supmaj (u : ℂ) (y0 y1 x0 x1 : ℝ) : Measurable (supmaj u y0 y1 x0 x1) := by
  unfold supmaj
  exact Measurable.indicator measurable_supk (by measurability)

private lemma measurable_gprod (u : ℂ) (y0 y1 x0 x1 : ℝ) : Measurable (gprod u y0 y1 x0 x1) := by
  unfold gprod
  exact Measurable.indicator (measurable_kern.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => (p.2, p.1))))
    (by measurability)

private lemma lintegral_supmaj_eq (u : ℂ) (y0 y1 x0 x1 : ℝ) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
      = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supk u z)
          ∂((volume : Measure (ℝ × ℝ)).restrict ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)))) := by
  calc
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
        = (∫⁻ z : ℝ × ℝ,
            ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)).indicator
              (fun z : ℝ × ℝ => ENNReal.ofReal (supk u z)) z
            ∂(volume : Measure (ℝ × ℝ))) := by
            apply lintegral_congr
            intro z
            unfold supmaj
            rw [ofReal_indicator' (fun w : ℝ × ℝ => supk u w)]
    _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supk u z)
          ∂((volume : Measure (ℝ × ℝ)).restrict ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)))) := by
            rw [lintegral_indicator]
            measurability

private lemma integrable_supmaj (u : ℂ) (y0 y1 x0 x1 : ℝ) :
    Integrable (supmaj u y0 y1 x0 x1) (volume : Measure (ℝ × ℝ)) := by
  constructor
  · exact (measurable_supmaj u y0 y1 x0 x1).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    calc
      (∫⁻ z, ENNReal.ofReal ‖supmaj u y0 y1 x0 x1 z‖ ∂(volume : Measure (ℝ × ℝ)))
          = (∫⁻ z, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ))) := by
            apply lintegral_congr_ae
            filter_upwards with z
            rw [Real.norm_eq_abs, abs_of_nonneg (supmaj_nonneg u y0 y1 x0 x1 z)]
      _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supk u z)
          ∂((volume : Measure (ℝ × ℝ)).restrict ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)))) :=
            lintegral_supmaj_eq u y0 y1 x0 x1
      _ ≤ ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0)) := by
            unfold supk
            simpa using (lintegral_inv_norm_rect_le (x0 := y0) (x1 := y1) (y0 := x0) (y1 := x1)
              (a := u.im) (b := u.re))
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

private lemma integrable_gprod (u : ℂ) (y0 y1 x0 x1 : ℝ) :
    Integrable (gprod u y0 y1 x0 x1) (volume : Measure (ℝ × ℝ)) := by
  exact Integrable.mono' (integrable_supmaj u y0 y1 x0 x1)
    (measurable_gprod u y0 y1 x0 x1).aestronglyMeasurable (by
      filter_upwards with z
      have hnn := gprod_nonneg u y0 y1 x0 x1 z
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact gprod_le_supmaj u y0 y1 x0 x1 z)

/-- Boxed kernel real integral bounded by `2·(y1−y0) + 2·(x1−x0)` (coordinates `(T,x)`). -/
private lemma box_integral_le (u : ℂ) (y0 y1 x0 x1 : ℝ)
    (hy : y0 ≤ y1) (hx : x0 ≤ x1) :
    (∫ z : ℝ × ℝ, gprod u y0 y1 x0 x1 z) ≤ 2 * (y1 - y0) + 2 * (x1 - x0) := by
  have hmeas : AEStronglyMeasurable (gprod u y0 y1 x0 x1) (volume : Measure (ℝ × ℝ)) :=
    (measurable_gprod u y0 y1 x0 x1).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] gprod u y0 y1 x0 x1 := by
    filter_upwards with z
    exact gprod_nonneg u y0 y1 x0 x1 z
  have hmain :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
          ≤ ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0)) := by
    calc
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
          = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supk u z)
              ∂((volume : Measure (ℝ × ℝ)).restrict ((Set.Icc y0 y1) ×ˢ (Set.Icc x0 x1)))) :=
              lintegral_supmaj_eq u y0 y1 x0 x1
      _ ≤ ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0)) := by
              unfold supk
              simpa using (lintegral_inv_norm_rect_le (x0 := y0) (x1 := y1) (y0 := x0) (y1 := x1)
                (a := u.im) (b := u.re))
  have hbnd_top : ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0)) ≠ ∞ := by
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hsuplint :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
          ≠ ∞ := ne_of_lt (lt_of_le_of_lt hmain (ENNReal.add_lt_top.mpr
            ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
  have hmono :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (gprod u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ)))
          ≤ (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z) ∂(volume : Measure (ℝ × ℝ))) := by
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (gprod_le_supmaj u y0 y1 x0 x1 z)
  have hbounded2 : (ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0))).toReal
      = 2 * (y1 - y0) + 2 * (x1 - x0) := by
    have hy' : 0 ≤ y1 - y0 := sub_nonneg.mpr hy
    have hx' : 0 ≤ x1 - x0 := sub_nonneg.mpr hx
    have h2y : 0 ≤ 2 * (y1 - y0) := mul_nonneg (by norm_num) hy'
    have h2x : 0 ≤ 2 * (x1 - x0) := mul_nonneg (by norm_num) hx'
    rw [ENNReal.toReal_add (a := ENNReal.ofReal (2 * (y1 - y0)))
      (b := ENNReal.ofReal (2 * (x1 - x0))) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal h2y, ENNReal.toReal_ofReal h2x]
  calc
    (∫ z : ℝ × ℝ, gprod u y0 y1 x0 x1 z)
        = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (gprod u y0 y1 x0 x1 z)
            ∂(volume : Measure (ℝ × ℝ))).toReal := by
            exact (integral_eq_lintegral_of_nonneg_ae hnn hmeas)
    _ ≤ (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (supmaj u y0 y1 x0 x1 z)
          ∂(volume : Measure (ℝ × ℝ))).toReal := by
          exact toReal_mono_of_le hmono hsuplint
    _ ≤ (ENNReal.ofReal (2 * (y1 - y0)) + ENNReal.ofReal (2 * (x1 - x0))).toReal := by
          exact toReal_mono_of_le hmain hbnd_top
    _ = 2 * (y1 - y0) + 2 * (x1 - x0) := hbounded2


private lemma indicator_integral_eq {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ) :
    (∫ x : ℝ in s, f x) = ∫ x : ℝ, (s.indicator (fun _ : ℝ => (1 : ℝ))) x * f x := by
  rw [← integral_indicator hs]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

private lemma box_indicator_eq_fun (s t : Set ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ((s ×ˢ t).indicator f z) =
      (s.indicator (fun _ : ℝ => (1 : ℝ)) z.1) * ((t.indicator (fun _ : ℝ => (1 : ℝ)) z.2) * f z) := by
  by_cases h1 : z.1 ∈ s <;> by_cases h2 : z.2 ∈ t <;> simp [h1, h2]

/-- boxed kernel on (T,x)-coords -/
private def gbox (u : ℂ) (y0 y1 x0 x1 : ℝ) : ℝ × ℝ → ℝ :=
  fun z => ((Set.Ioc y0 y1) ×ˢ (Set.Ioc x0 x1)).indicator (fun z => kern u z.2 z.1) z


/-- the boxed kernel on `(T,x)`-coordinates equals `gprod` (definitional). -/
private lemma gbox_eq_gprod (u : ℂ) (y0 y1 x0 x1 : ℝ) : gbox u y0 y1 x0 x1 = gprod u y0 y1 x0 x1 := by
  funext z
  rfl

private lemma gbox_integrable (u : ℂ) (y0 y1 x0 x1 : ℝ) :
    Integrable (gbox u y0 y1 x0 x1) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  simpa [hvol, gbox_eq_gprod u y0 y1 x0 x1] using (integrable_gprod u y0 y1 x0 x1)

private lemma interval_double_eq_gbox (u : ℂ) {x0 x1 y0 y1 : ℝ}
    (hxle : x0 ≤ x1) (hyle : y0 ≤ y1) :
    (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1, kern u x T)
      = ∫ z : ℝ × ℝ, gbox u y0 y1 x0 x1 z := by
  -- define the two-variable function
  let f2 : ℝ → ℝ → ℝ := fun T x =>
    (Set.Ioc y0 y1).indicator (fun _ : ℝ => (1 : ℝ)) T *
      ((Set.Ioc x0 x1).indicator (fun _ : ℝ => (1 : ℝ)) x * kern u x T)
  have hA : (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1, kern u x T)
      = ∫ T : ℝ, ∫ x : ℝ, f2 T x ∂volume ∂volume := by
    calc
      (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1, kern u x T)
          = ∫ T : ℝ in Set.Ioc y0 y1, ∫ x : ℝ in x0..x1, kern u x T := by
              rw [intervalIntegral.integral_of_le hyle]
      _ = ∫ T : ℝ in Set.Ioc y0 y1, ∫ x : ℝ in Set.Ioc x0 x1, kern u x T := by
              apply congrArg (fun g : ℝ → ℝ => ∫ T : ℝ in Set.Ioc y0 y1, g T)
              funext T
              rw [intervalIntegral.integral_of_le hxle]
      _ = ∫ T : ℝ, (Set.Ioc y0 y1).indicator (fun _ : ℝ => (1 : ℝ)) T *
            (∫ x : ℝ in Set.Ioc x0 x1, kern u x T) := by
            exact indicator_integral_eq measurableSet_Ioc
              (fun T => ∫ x : ℝ in Set.Ioc x0 x1, kern u x T)
      _ = ∫ T : ℝ, (Set.Ioc y0 y1).indicator (fun _ : ℝ => (1 : ℝ)) T *
            (∫ x : ℝ, (Set.Ioc x0 x1).indicator (fun _ : ℝ => (1 : ℝ)) x * kern u x T) := by
            apply congrArg (fun h : ℝ → ℝ => ∫ T : ℝ, (Set.Ioc y0 y1).indicator (fun _ : ℝ => (1 : ℝ)) T * h T)
            funext T
            exact indicator_integral_eq measurableSet_Ioc (fun x => kern u x T)
      _ = ∫ T : ℝ, ∫ x : ℝ, f2 T x ∂volume ∂volume := by
            apply congrArg (fun h : ℝ → ℝ => ∫ T : ℝ, h T)
            funext T
            rw [MeasureTheory.integral_const_mul
              (r := (Set.Ioc y0 y1).indicator (fun _ : ℝ => (1 : ℝ)) T)
              (f := fun x : ℝ => (Set.Ioc x0 x1).indicator (fun _ : ℝ => (1 : ℝ)) x * kern u x T)]
  -- Fubini
  have hFub : (∫ T : ℝ, ∫ x : ℝ, f2 T x ∂volume ∂volume)
      = ∫ z : ℝ × ℝ, f2 z.1 z.2 ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    apply MeasureTheory.integral_integral
    -- integrability of uncurry f2
    have hgz : Function.uncurry f2 = gbox u y0 y1 x0 x1 := by
      funext z
      dsimp [Function.uncurry, f2, gbox]
      exact (box_indicator_eq_fun (Set.Ioc y0 y1) (Set.Ioc x0 x1) (fun w : ℝ × ℝ => kern u w.2 w.1) z).symm
    -- integrable gbox w.r.t product measure
    exact (by
      have hg := gbox_integrable u y0 y1 x0 x1
      simpa [hgz] using hg)
  -- combine with pointwise conversion to gbox over volume
  calc
    (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1, kern u x T)
        = ∫ T : ℝ, ∫ x : ℝ, f2 T x ∂volume ∂volume := hA
    _ = ∫ z : ℝ × ℝ, f2 z.1 z.2 ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := hFub
    _ = ∫ z : ℝ × ℝ, gbox u y0 y1 x0 x1 z := by
            -- volume.prod volume = volume on ℝ×ℝ by rfl
            have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
            rw [← hvol]
            congr 1
            funext z
            dsimp [Function.uncurry, f2, gbox]
            exact (box_indicator_eq_fun (Set.Ioc y0 y1) (Set.Ioc x0 x1) (fun w : ℝ × ℝ => kern u w.2 w.1) z).symm

private lemma norm_eq_sqrt {x T : ℝ} {u : ℂ} :
    ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)‖ =
      Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hsq : (‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)‖) ^ 2 =
      ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    have hre : (((x : ℂ) + Complex.I * (T : ℂ)) - u).re = x - u.re := by simp
    have him : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
    rw [hre, him]
    ring
  have h2 : 0 ≤ (x - u.re) ^ 2 + (T - u.im) ^ 2 := by positivity
  have hmain : ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)‖ ^ 2 =
      (Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2)) ^ 2 := by
    rw [hsq, Real.sq_sqrt h2]
  have hnn : 0 ≤ Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) := Real.sqrt_nonneg _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmain with h | h
  · exact h
  · have hs0 : Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) = 0 := by
      have hle0 : Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2) ≤ 0 := by
        calc Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2)
            = -‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)‖ := by linarith
          _ ≤ 0 := by linarith [norm_nonneg ((((x : ℂ) + Complex.I * (T : ℂ)) - u))]
      linarith
    linarith

private lemma fR_eq_kern {x T : ℝ} {u : ℂ} :
    ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)⁻¹‖ = kern u x T := by
  unfold kern
  calc
    ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)⁻¹‖
        = ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)‖⁻¹ := by rw [norm_inv]
    _ = (Real.sqrt ((x - u.re) ^ 2 + (T - u.im) ^ 2))⁻¹ := by rw [norm_eq_sqrt]

/-- **Pole-area bound.**  For a pole `u` strictly inside the rectangle
`[x0,x1] × [y0,y1]`, the 2-D area integral of `1/|z−u|` over the rectangle
(built as the iterated interval integral, `T`-outer and `x`-inner) is at most the
rectangle's perimeter `2·((x1−x0)+(y1−y0))`. -/
theorem rectPoleArea_perimeter_le {x0 x1 y0 y1 : ℝ} {u : ℂ}
    (hw : 0 < x1 - x0) (hh : 0 < y1 - y0)
    (hux : x0 < u.re) (hux2 : u.re < x1)
    (huy : y0 < u.im) (huy2 : u.im < y1) :
    (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1,
        ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)⁻¹‖) ≤
      2 * ((x1 - x0) + (y1 - y0)) := by
  have hxle : x0 ≤ x1 := le_of_lt (sub_pos.mp hw)
  have hyle : y0 ≤ y1 := le_of_lt (sub_pos.mp hh)
  calc
    (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1,
        ‖(((x : ℂ) + Complex.I * (T : ℂ)) - u)⁻¹‖)
        = (∫ T : ℝ in y0..y1, ∫ x : ℝ in x0..x1, kern u x T) := by
            apply intervalIntegral.integral_congr
            intro T hT
            apply intervalIntegral.integral_congr
            intro x hx
            exact fR_eq_kern (x := x) (T := T) (u := u)
    _ = ∫ z : ℝ × ℝ, gbox u y0 y1 x0 x1 z := by
            exact interval_double_eq_gbox u hxle hyle
    _ = ∫ z : ℝ × ℝ, gprod u y0 y1 x0 x1 z := by
            rw [gbox_eq_gprod u y0 y1 x0 x1]
    _ ≤ 2 * (y1 - y0) + 2 * (x1 - x0) := by
            exact box_integral_le u y0 y1 x0 x1 hyle hxle
    _ = 2 * ((x1 - x0) + (y1 - y0)) := by ring


end Commons.NumberTheory.DirichletCharacter