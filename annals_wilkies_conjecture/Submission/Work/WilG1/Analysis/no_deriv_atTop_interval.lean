import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Analysis

open Filter

/-!
## A function with infinite derivative `+∞` everywhere on an interval

If `f : ℝ → ℝ` is continuous on an order-connected set `I ⊆ ℝ` and the difference
quotient `(f y - f x)/(y - x)` tends to `+∞` as `y → x` (punctured) for every `x ∈ I`,
then `I` is a subsingleton.

The proof proceeds in three steps.

* `local_increase_through`: at each point the infinite slope forces `f` to pass strictly
  upwards through that point, i.e. `f x < f y` for `y` just to the right of `x` and
  `f y < f x` for `y` just to the left.
* `strictMonoOn_of_increase_through`: a continuous function on an order-connected set that
  passes strictly upwards through each of its points is strictly increasing.
* Finally, applying the second step to `f` gives strict increase, while applying it to
  `f - M·id` (whose difference quotient again tends to `+∞`) gives `f b - M b > f a - M a`
  for every `M`, i.e. `f b - f a > M (b - a)`, impossible for large `M` when `a < b`.
-/

/-- At a point where the difference quotient of `f` tends to `+∞`, the function passes
strictly upwards through that point. -/
private theorem local_increase_through {f : ℝ → ℝ} {x : ℝ}
    (hlim : Filter.Tendsto (fun y : ℝ => (f y - f x) / (y - x)) (nhdsWithin x {x}ᶜ) atTop) :
    ∃ δ > 0, ∀ y, |y - x| < δ → y ≠ x →
      ((x < y → f x < f y) ∧ (y < x → f y < f x)) := by
  have hpos : ∃ δ > 0, ∀ y, |y - x| < δ → y ≠ x → 0 < (f y - f x) / (y - x) := by
    have hev : ∀ᶠ y in nhdsWithin x ({x}ᶜ), (1 : ℝ) ≤ (f y - f x) / (y - x) :=
      (tendsto_atTop.1 hlim) 1
    rw [eventually_nhdsWithin_iff] at hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, h⟩ := hev
    exact ⟨ε, hε, fun y hy hyne => by
      have hd : dist y x < ε := by rw [Real.dist_eq]; exact hy
      have := h hd hyne
      linarith⟩
  obtain ⟨δ, hδpos, hδ⟩ := hpos
  refine ⟨δ, hδpos, fun y hy hyne => ?_⟩
  have hq : 0 < (f y - f x) / (y - x) := hδ y hy hyne
  constructor
  · intro hxy
    have hyx : 0 < y - x := sub_pos.2 hxy
    have hmul : (f y - f x) / (y - x) * (y - x) > 0 := mul_pos hq hyx
    rw [div_mul_cancel₀ _ (ne_of_gt hyx)] at hmul
    linarith
  · intro hyx
    have hneg : y - x < 0 := sub_neg.2 hyx
    have heq : (f y - f x) / (y - x) * (y - x) = f y - f x :=
      div_mul_cancel₀ _ (ne_of_lt hneg)
    nlinarith [hq, hneg, heq]

/-- A continuous function on an order-connected set that passes strictly upwards through
each of its points is strictly increasing. -/
private theorem strictMonoOn_of_increase_through {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hcont : ∀ x ∈ I, ContinuousAt f x)
    (hinc : ∀ x ∈ I, ∃ δ > 0, ∀ y, |y - x| < δ → y ≠ x →
      ((x < y → f x < f y) ∧ (y < x → f y < f x))) :
    StrictMonoOn f I := by
  intro a ha b hb hab
  -- `f` attains its maximum on the compact interval `[a, b]`.
  have hcont_on : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hcont x (hI.out ha hb hx)).continuousWithinAt
  obtain ⟨m, hmab, hmmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab.le⟩ hcont_on
  -- the maximum is attained at `b`: an interior maximizer would be contradicted by the
  -- upward passage through it.
  have hmb : m = b := by
    by_contra hne
    have hmlt : m < b := lt_of_le_of_ne hmab.2 hne
    obtain ⟨δ, hδpos, hδ⟩ := hinc m (hI.out ha hb hmab)
    set c := min δ (b - m) with hc
    set y := m + c / 2 with hy
    have hym : m < y := by rw [hy]; have := lt_min hδpos (sub_pos.2 hmlt); linarith
    have hyb : y < b := by rw [hy, hc]; have := min_le_right δ (b - m); linarith
    have hya : a ≤ y := le_trans hmab.1 hym.le
    have hdist : |y - m| < δ := by
      rw [abs_lt]; constructor <;> rw [hy, hc] <;> have := min_le_left δ (b - m) <;> linarith
    have hlt : f m < f y := (hδ y hdist (ne_of_gt hym)).1 hym
    have hle : f y ≤ f m := hmmax ⟨hya, hyb.le⟩
    linarith
  have hbmax : ∀ y ∈ Set.Icc a b, f y ≤ f b := by
    intro y hy
    have := hmmax hy
    rwa [hmb] at this
  -- now `f b` is the maximum, and `f` passes upward through `a`, so `f a < f b`.
  obtain ⟨δ, hδpos, hδ⟩ := hinc a ha
  set c := min δ (b - a) with hc
  set y := a + c / 2 with hy
  have hay : a < y := by rw [hy]; have := lt_min hδpos (sub_pos.2 hab); linarith
  have hyb : y < b := by rw [hy, hc]; have := min_le_right δ (b - a); linarith
  have hdist : |y - a| < δ := by
    rw [abs_lt]; constructor <;> rw [hy, hc] <;> have := min_le_left δ (b - a) <;> linarith
  have hfy : f a < f y := (hδ y hdist (ne_of_gt hay)).1 hay
  have : f y ≤ f b := hbmax y ⟨hay.le, hyb.le⟩
  linarith

theorem no_deriv_atTop_interval {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hcont : ∀ x ∈ I, ContinuousAt f x)
    (hlim : ∀ x ∈ I, Filter.Tendsto (fun y : ℝ => (f y - f x) / (y - x)) (nhdsWithin x {x}ᶜ) atTop) :
    I.Subsingleton := by
  intro a ha b hb
  -- No two distinct points of `I` can be ordered.
  have contra : ∀ ⦃a b : ℝ⦄, a ∈ I → b ∈ I → a < b → False := by
    intro a b ha hb hab
    have hinc_f : ∀ x ∈ I, ∃ δ > 0, ∀ y, |y - x| < δ → y ≠ x →
        ((x < y → f x < f y) ∧ (y < x → f y < f x)) :=
      fun x hx => local_increase_through (hlim x hx)
    have hlt_f : f a < f b := strictMonoOn_of_increase_through hI hcont hinc_f ha hb hab
    -- Consider `g = f - M·id` with `M` above the secant slope over `[a,b]`.
    set M := (f b - f a) / (b - a) + 1 with hM
    have hcont_g : ∀ x ∈ I, ContinuousAt (fun y : ℝ => f y - M * y) x := by
      intro x hx
      exact (hcont x hx).sub ((continuous_const.mul continuous_id).continuousAt)
    have hlim_g : ∀ x ∈ I,
        Filter.Tendsto (fun y : ℝ => ((f y - M * y) - (f x - M * x)) / (y - x))
          (nhdsWithin x {x}ᶜ) atTop := by
      intro x hx
      rw [Filter.tendsto_atTop]
      intro A
      have h := (Filter.tendsto_atTop.1 (hlim x hx)) (A + M)
      filter_upwards [h, self_mem_nhdsWithin] with y hy hyne
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
      have hid : ((f y - M * y) - (f x - M * x)) / (y - x) = (f y - f x) / (y - x) - M := by
        field_simp
        ring
      rw [hid]; linarith
    have hinc_g : ∀ x ∈ I, ∃ δ > 0, ∀ y, |y - x| < δ → y ≠ x →
        ((x < y → (fun y : ℝ => f y - M * y) x < (fun y : ℝ => f y - M * y) y) ∧
         (y < x → (fun y : ℝ => f y - M * y) y < (fun y : ℝ => f y - M * y) x)) :=
      fun x hx => local_increase_through (hlim_g x hx)
    have hlt_g : (fun y : ℝ => f y - M * y) a < (fun y : ℝ => f y - M * y) b :=
      strictMonoOn_of_increase_through hI hcont_g hinc_g ha hb hab
    have hlt_g' : f a - M * a < f b - M * b := hlt_g
    have hba : (b - a) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    have hMb : M * (b - a) = (f b - f a) + (b - a) := by
      rw [hM]; field_simp
    nlinarith [hlt_g', hMb, hab]
  rcases lt_trichotomy a b with hab | hab | hba
  · exact absurd hab (contra ha hb)
  · exact hab
  · exact absurd hba (contra hb ha)

end Work.WilG1.Analysis
