import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

variable {F : ℂ → ℂ} {φ φ' : ℝ → ℝ} {c a b : ℝ}

lemma abs_sub_le_of_mem_uIcc {x L u : ℝ} (hx : x ∈ Set.uIcc L u) : |x - L| ≤ |u - L| := by
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - L), abs_of_nonneg (by linarith : 0 ≤ u - L)]
    linarith
  · rw [abs_of_nonpos (by linarith : x - L ≤ 0), abs_of_nonpos (by linarith : u - L ≤ 0)]
    linarith

lemma norm_le_norm_add_norm_sub' (x y : ℂ) : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
  have := norm_add_le (x - y) y
  rw [sub_add_cancel] at this
  linarith



/-- The closed "graph region" `{a ≤ im ≤ b, φ im ≤ re ≤ c}`. -/
def graphRegion (φ : ℝ → ℝ) (c a b : ℝ) : Set ℂ :=
  {z : ℂ | z.im ∈ Set.Icc a b ∧ z.re ∈ Set.Icc (φ z.im) c}

lemma mem_graphRegion {z : ℂ} :
    z ∈ graphRegion φ c a b ↔ a ≤ z.im ∧ z.im ≤ b ∧ φ z.im ≤ z.re ∧ z.re ≤ c := by
  simp only [graphRegion, Set.mem_ofPred_eq, mem_Icc]; tauto

lemma continuousOn_F_graphRegion
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z) :
    ContinuousOn F (graphRegion φ c a b) := by
  rintro z hz
  rw [mem_graphRegion] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact (hF z h1 h2 h3 h4).continuousAt.continuousWithinAt

/-- Continuity of `t ↦ F (x + t i)` when the whole vertical segment lies in the region. -/
lemma continuousOn_F_vert
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {x : ℝ} {s : Set ℝ} (hs : ∀ t ∈ s, a ≤ t ∧ t ≤ b ∧ φ t ≤ x ∧ x ≤ c) :
    ContinuousOn (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) s := by
  refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := hs t ht
  exact (mem_graphRegion).mpr ⟨by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4⟩

/-- Continuity of `x ↦ F (x + y i)` on `[φ y, c]` for `y ∈ [a,b]`. -/
lemma continuousOn_F_horiz
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y : ℝ} (hy : y ∈ Set.Icc a b) :
    ContinuousOn (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) (Set.Icc (φ y) c) := by
  refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  exact (mem_graphRegion).mpr ⟨by simpa using hy.1, by simpa using hy.2, by simpa using h1,
    by simpa using h2⟩

/-- Continuity of `t ↦ F (φ t + t i)` along the boundary curve. -/
lemma continuousOn_F_curve
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c) (hφcont : ContinuousOn φ (Set.Icc a b)) :
    ContinuousOn (fun t : ℝ => F ((φ t : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc a b) := by
  refine (continuousOn_F_graphRegion hF).comp ?_ ?_
  · have h1 : ContinuousOn (fun t : ℝ => (φ t : ℂ)) (Set.Icc a b) :=
      Complex.ofRealCLM.continuous.comp_continuousOn hφcont
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn continuousOn_id
    exact h1.add (h2.mul continuousOn_const)
  · intro t ht
    exact (mem_graphRegion).mpr ⟨by simpa using ht.1, by simpa using ht.2,
      by simpa using (le_rfl : φ t ≤ φ t), by simpa using hφc t ht⟩

/-- Cauchy's theorem for the rectangle with corners `φ y + y₀ i` and `c + y i`, valid when
`a ≤ y₀ ≤ y ≤ b`. -/
lemma rect_identity_le
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ y : ℝ} (hy₀ : a ≤ y₀) (hy : y ≤ b) (hle : y₀ ≤ y) :
    (∫ x : ℝ in φ y..c, (F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((x : ℂ) + (y₀ : ℂ) * Complex.I)))
      = Complex.I * ∫ y' : ℝ in y₀..y,
          (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I)) := by
  have hay : a ≤ y := hy₀.trans hle
  have hφyc : φ y ≤ c := hφc y ⟨hay, hy⟩
  set z0 : ℂ := (φ y : ℂ) + (y₀ : ℂ) * Complex.I with hz0
  set w0 : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hw0
  have hz0re : z0.re = φ y := by simp [z0]
  have hz0im : z0.im = y₀ := by simp [z0]
  have hw0re : w0.re = c := by simp [w0]
  have hw0im : w0.im = y := by simp [w0]
  have hd : DifferentiableOn ℂ F (Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im) := by
    rw [hz0re, hw0re, hz0im, hw0im]
    intro z hz
    rw [Complex.mem_reProdIm, uIcc_of_le hφyc, uIcc_of_le hle] at hz
    obtain ⟨hzr, hzi⟩ := hz
    have hzim : z.im ∈ Set.Icc a b := ⟨hy₀.trans hzi.1, hzi.2.trans hy⟩
    have hle' : φ z.im ≤ φ y := hmono hzim ⟨hay, hy⟩ hzi.2
    exact (hF z hzim.1 hzim.2 (hle'.trans hzr.1) hzr.2).differentiableWithinAt
  have hint1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hφyc]
    exact continuousOn_F_horiz hF ⟨hay, hy⟩
  have hint2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) volume (φ y) c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hφyc]
    refine (continuousOn_F_horiz hF ⟨hy₀, hle.trans hy⟩).mono ?_
    exact Set.Icc_subset_Icc (hmono ⟨hy₀, hle.trans hy⟩ ⟨hay, hy⟩ hle) le_rfl
  have hint3 : IntervalIntegrable (fun y' : ℝ => F ((c : ℂ) + (y' : ℂ) * Complex.I)) volume y₀ y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact continuousOn_F_vert hF (s := Set.Icc y₀ y) (fun t ht => ⟨hy₀.trans ht.1, ht.2.trans hy,
      (hmono (show t ∈ Set.Icc a b from ⟨hy₀.trans ht.1, ht.2.trans hy⟩)
        (show y ∈ Set.Icc a b from ⟨hay, hy⟩) ht.2).trans hφyc, le_rfl⟩)
  have hint4 : IntervalIntegrable (fun y' : ℝ => F ((φ y : ℂ) + (y' : ℂ) * Complex.I)) volume y₀ y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact continuousOn_F_vert hF (s := Set.Icc y₀ y) (fun t ht => ⟨hy₀.trans ht.1, ht.2.trans hy,
      hmono (show t ∈ Set.Icc a b from ⟨hy₀.trans ht.1, ht.2.trans hy⟩)
        (show y ∈ Set.Icc a b from ⟨hay, hy⟩) ht.2,
      hφc y ⟨hay, hy⟩⟩)
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z0 w0 hd
  rw [hz0re, hw0re, hz0im, hw0im, smul_eq_mul, smul_eq_mul] at key
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_sub hint3 hint4]
  rw [mul_sub]
  linear_combination -key

/-- Cauchy's theorem for the rectangle with corners `φ y₀ + y i` and `c + y₀ i`, valid when
`a ≤ y ≤ y₀ ≤ b`. -/
lemma rect_identity_ge
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y y₀ : ℝ} (hy : a ≤ y) (hy₀ : y₀ ≤ b) (hle : y ≤ y₀) :
    (∫ x : ℝ in φ y₀..c, (F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((x : ℂ) + (y₀ : ℂ) * Complex.I)))
      = Complex.I * ∫ y' : ℝ in y₀..y,
          (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I)) := by
  have hy₀b : y₀ ≤ b := hy₀
  have hay₀ : a ≤ y₀ := hy.trans hle
  have hφy₀c : φ y₀ ≤ c := hφc y₀ ⟨hay₀, hy₀b⟩
  have hay : a ≤ y := hy
  have hyb : y ≤ b := hle.trans hy₀b
  set z0 : ℂ := (φ y₀ : ℂ) + (y : ℂ) * Complex.I with hz0
  set w0 : ℂ := (c : ℂ) + (y₀ : ℂ) * Complex.I with hw0
  have hz0re : z0.re = φ y₀ := by simp [z0]
  have hz0im : z0.im = y := by simp [z0]
  have hw0re : w0.re = c := by simp [w0]
  have hw0im : w0.im = y₀ := by simp [w0]
  have hd : DifferentiableOn ℂ F (Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im) := by
    rw [hz0re, hw0re, hz0im, hw0im]
    intro z hz
    rw [Complex.mem_reProdIm, uIcc_of_le hφy₀c, uIcc_of_le hle] at hz
    obtain ⟨hzr, hzi⟩ := hz
    have hzim : z.im ∈ Set.Icc a b := ⟨hay.trans hzi.1, hzi.2.trans hy₀b⟩
    have hle' : φ z.im ≤ φ y₀ := hmono hzim ⟨hay₀, hy₀b⟩ hzi.2
    exact (hF z hzim.1 hzim.2 (hle'.trans hzr.1) hzr.2).differentiableWithinAt
  have hint1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y₀) c := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφy₀c]
    exact (continuousOn_F_horiz hF ⟨hay, hyb⟩).mono (Set.Icc_subset_Icc (hmono ⟨hay,hyb⟩ ⟨hay₀,hy₀b⟩ hle) le_rfl)
  have hint2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) volume (φ y₀) c := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφy₀c]
    exact continuousOn_F_horiz hF ⟨hay₀, hy₀b⟩
  have hint3 : IntervalIntegrable (fun y' : ℝ => F ((c : ℂ) + (y' : ℂ) * Complex.I)) volume y y₀ := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hle]
    exact continuousOn_F_vert hF (s := Set.Icc y y₀) (fun t ht => ⟨hay.trans ht.1, ht.2.trans hy₀b,
      (hmono (⟨hay.trans ht.1, ht.2.trans hy₀b⟩ : _ ∈ Set.Icc a b) ⟨hay₀, hy₀b⟩ ht.2).trans hφy₀c, le_rfl⟩)
  have hint4 : IntervalIntegrable (fun y' : ℝ => F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I)) volume y y₀ := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hle]
    exact continuousOn_F_vert hF (s := Set.Icc y y₀) (fun t ht => ⟨hay.trans ht.1, ht.2.trans hy₀b,
      hmono (⟨hay.trans ht.1, ht.2.trans hy₀b⟩ : _ ∈ Set.Icc a b) ⟨hay₀, hy₀b⟩ ht.2, hφy₀c⟩)
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z0 w0 hd
  rw [hz0re, hw0re, hz0im, hw0im, smul_eq_mul, smul_eq_mul] at key
  have hA : (∫ (x : ℝ) in φ y₀..c, F (↑x + ↑y * Complex.I))
      - (∫ (x : ℝ) in φ y₀..c, F (↑x + ↑y₀ * Complex.I))
      = Complex.I * (∫ (y' : ℝ) in y..y₀, F (↑(φ y₀) + ↑y' * Complex.I))
        - Complex.I * (∫ (y' : ℝ) in y..y₀, F (↑c + ↑y' * Complex.I)) := by
    linear_combination key
  rw [intervalIntegral.integral_sub hint1 hint2]
  rw [hA, intervalIntegral.integral_sub (hint3.symm) (hint4.symm),
      intervalIntegral.integral_symm y y₀, intervalIntegral.integral_symm y y₀]
  ring

/-- If `W y` converges to the constant `c` uniformly on `[0,1]` as `y → y₀` along `l`, and each
`W y` is continuous on `[0,1]`, then `∫_0^1 W y s ds → c`. -/
lemma tendsto_integral_unit {l : Filter ℝ} {W : ℝ → ℝ → ℂ} {c : ℂ}
    (hcont : ∀ᶠ y in l, ContinuousOn (W y) (Set.Icc 0 1))
    (hunif : ∀ ε > 0, ∀ᶠ y in l, ∀ s ∈ Set.Icc (0:ℝ) 1, dist (W y s) c ≤ ε) :
    Tendsto (fun y => ∫ s in (0:ℝ)..1, W y s) l (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0:ℝ) < ε/2 := by linarith
  filter_upwards [hcont, hunif (ε/2) hε2] with y hcy hun
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hint : IntervalIntegrable (fun s => W y s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le h01]; exact hcy
  have hintc : IntervalIntegrable (fun s : ℝ => W y s - c) volume 0 1 :=
    hint.sub intervalIntegrable_const
  have hkey : (∫ s in (0:ℝ)..1, W y s) - c = ∫ s in (0:ℝ)..1, (W y s - c) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [dist_eq_norm, hkey]
  calc ‖∫ s in (0:ℝ)..1, (W y s - c)‖
      ≤ ∫ s in (0:ℝ)..1, ‖W y s - c‖ := intervalIntegral.norm_integral_le_integral_norm h01
    _ ≤ ∫ _s in (0:ℝ)..1, (ε/2) := by
        apply intervalIntegral.integral_mono_on h01
        · exact hintc.norm
        · exact intervalIntegrable_const
        · intro s hs
          rw [← dist_eq_norm]
          exact hun s hs
    _ = ε/2 * 1 := by rw [intervalIntegral.integral_const]; simp
    _ < ε := by linarith


/-- The "moving upper limit" average: `(∫_{φ y₀}^{φ y} F(x + y₀ i)) / (y - y₀) → F(φ y₀ + y₀ i) * φ' y₀`
as `y → y₀⁺`. -/
lemma tendsto_moving_upper
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo a b) :
    Tendsto (fun y => (∫ x in φ y₀..φ y, F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) / (y - y₀))
      (𝓝[>] y₀) (𝓝 (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * φ' y₀)) := by
  have hy₀a : a ≤ y₀ := hy₀.1.le
  have hy₀b : y₀ ≤ b := hy₀.2.le
  have hy₀Icc : y₀ ∈ Set.Icc a b := ⟨hy₀a, hy₀b⟩
  have hφy₀c : φ y₀ ≤ c := hφc y₀ hy₀Icc
  have hFc : ContinuousAt F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using (le_rfl : φ y₀ ≤ φ y₀)) (by simpa using hφy₀c)).continuousAt
  have hφcAt : ContinuousAt φ y₀ := (hderiv y₀ hy₀).continuousAt
  have hslope : Tendsto (fun y => (φ y - φ y₀) / (y - y₀)) (𝓝[>] y₀) (𝓝 (φ' y₀)) := by
    have h := (hderiv y₀ hy₀).tendsto_slope
    rw [slope_fun_def_field] at h
    exact h.mono_left (nhdsGT_le_nhdsNE y₀)
  set W : ℝ → ℝ → ℂ := fun y s =>
    F (((φ y₀ + (φ y - φ y₀) * s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I) with hW
  have hWlim : Tendsto (fun y => ∫ s in (0:ℝ)..1, W y s) (𝓝[>] y₀)
      (𝓝 (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
    apply tendsto_integral_unit
    · filter_upwards [Ioo_mem_nhdsGT hy₀.2] with y hy
      refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hyIcc : y ∈ Set.Icc a b := ⟨hy₀a.trans hy.1.le, hy.2.le⟩
      have hφyb : φ y ≤ c := hφc y hyIcc
      have hφyge : φ y₀ ≤ φ y := hmono hy₀Icc hyIcc hy.1.le
      refine (mem_graphRegion).mpr ⟨by simpa using hy₀a, by simpa using hy₀b, ?_, ?_⟩
      · have h1 : φ y₀ ≤ φ y₀ + (φ y - φ y₀) * s := by nlinarith [hs1, hφyge]
        simpa using h1
      · have h2 : φ y₀ + (φ y - φ y₀) * s ≤ c := by nlinarith [hs1, hs2, hφyge, hφyb]
        simpa using h2
    · intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc) ε hε)
      filter_upwards [((Metric.tendsto_nhds.mp hφcAt) δ hδ).filter_mono nhdsWithin_le_nhds]
        with y hy
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hdist : dist (((φ y₀ + (φ y - φ y₀) * s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I)
          ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) < δ := by
        rw [dist_eq_norm]
        have heq : ((φ y₀ + (φ y - φ y₀) * s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I
            - ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) = (((φ y - φ y₀) * s : ℝ) : ℂ) := by
          push_cast; ring_nf
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs1]
        calc |φ y - φ y₀| * s ≤ |φ y - φ y₀| * 1 :=
              mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)
          _ = |φ y - φ y₀| := by ring
          _ < δ := by simpa [dist_eq_norm, Real.norm_eq_abs] using hy
      show dist (W y s) (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≤ ε
      rw [hW]
      exact le_of_lt (hδb (Metric.mem_ball.mpr hdist))
  have hsub : ∀ y, (∫ x in φ y₀..φ y, F ((x : ℂ) + (y₀ : ℂ) * Complex.I))
      = (φ y - φ y₀) • ∫ s in (0:ℝ)..1, W y s := by
    intro y
    rw [hW]
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := (1:ℝ))
      (c := φ y - φ y₀) (d := φ y₀) (f := fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I))
    simp only [mul_zero, mul_one, add_zero] at h
    rw [show φ y₀ + (φ y - φ y₀) = φ y from by ring] at h
    rw [h]
  have hslopeC : Tendsto (fun y => (((φ y - φ y₀) / (y - y₀) : ℝ) : ℂ)) (𝓝[>] y₀)
      (𝓝 ((φ' y₀ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hslope
  have hprod : Tendsto (fun y => (((φ y - φ y₀) / (y - y₀) : ℝ) : ℂ) * ∫ s in (0:ℝ)..1, W y s)
      (𝓝[>] y₀) (𝓝 (((φ' y₀ : ℝ) : ℂ) * F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) :=
    hslopeC.mul hWlim
  rw [show F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * φ' y₀
      = ((φ' y₀ : ℝ) : ℂ) * F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) from by push_cast; ring_nf]
  refine hprod.congr' (Eventually.of_forall fun y => ?_)
  change (((φ y - φ y₀) / (y - y₀) : ℝ) : ℂ) * (∫ s in (0:ℝ)..1, W y s)
      = (∫ x in φ y₀..φ y, F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) / ((y : ℂ) - (y₀ : ℂ))
  rw [hsub, Complex.real_smul]
  push_cast
  ring

/-- The "moving lower limit" average. -/
lemma tendsto_moving_lower
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo a b) :
    Tendsto (fun y : ℝ => (∫ x in φ y..φ y₀, F ((x : ℂ) + (y : ℂ) * Complex.I)) / (y - y₀))
      (𝓝[<] y₀) (𝓝 (-(F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) * φ' y₀)) := by
  have hy₀a : a ≤ y₀ := hy₀.1.le
  have hy₀b : y₀ ≤ b := hy₀.2.le
  have hy₀Icc : y₀ ∈ Set.Icc a b := ⟨hy₀a, hy₀b⟩
  have hφy₀c : φ y₀ ≤ c := hφc y₀ hy₀Icc
  have hFc : ContinuousAt F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using (le_rfl : φ y₀ ≤ φ y₀)) (by simpa using hφy₀c)).continuousAt
  have hφcAt : ContinuousAt φ y₀ := (hderiv y₀ hy₀).continuousAt
  have hslope : Tendsto (fun y : ℝ => (φ y₀ - φ y) / (y - y₀)) (𝓝[<] y₀) (𝓝 (-(φ' y₀))) := by
    have hh : Tendsto (fun y : ℝ => (φ y - φ y₀) / (y - y₀)) (𝓝[<] y₀) (𝓝 (φ' y₀)) := by
      have h := (hderiv y₀ hy₀).tendsto_slope
      rw [slope_fun_def_field] at h
      exact h.mono_left (nhdsLT_le_nhdsNE y₀)
    have h2 := hh.neg
    have hfun : (fun y : ℝ => -((φ y - φ y₀) / (y - y₀))) = fun y : ℝ => (φ y₀ - φ y) / (y - y₀) := by
      funext y; ring
    rwa [hfun] at h2
  set W : ℝ → ℝ → ℂ := fun y s =>
    F (((φ y + (φ y₀ - φ y) * s : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hW
  have hWlim : Tendsto (fun y : ℝ => ∫ s in (0:ℝ)..1, W y s) (𝓝[<] y₀)
      (𝓝 (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
    apply tendsto_integral_unit
    · filter_upwards [Ioo_mem_nhdsLT hy₀.1] with y hy
      have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le.trans hy₀b⟩
      have hφyb : φ y ≤ c := hφc y hyIcc
      have hφyle : φ y ≤ φ y₀ := hmono hyIcc hy₀Icc hy.2.le
      refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      refine (mem_graphRegion).mpr ⟨by simpa using hy.1.le, by simpa using (hy.2.le.trans hy₀b), ?_, ?_⟩
      · have h1 : φ y ≤ φ y + (φ y₀ - φ y) * s := by nlinarith [hs1, hφyle]
        simpa using h1
      · have h2 : φ y + (φ y₀ - φ y) * s ≤ c := by nlinarith [hs1, hs2, hφyle, hφyb]
        simpa using h2
    · intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc) ε hε)
      have hδ2 : (0:ℝ) < δ/2 := by linarith
      have hφev : ∀ᶠ y in 𝓝 y₀, dist (φ y) (φ y₀) < δ/2 :=
        (Metric.tendsto_nhds.mp hφcAt) (δ/2) hδ2
      filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds y₀ hδ2),
        Eventually.filter_mono nhdsWithin_le_nhds hφev] with y hyb hyφ
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hyl : |y - y₀| < δ/2 := by
        have hmem : y ∈ Metric.ball y₀ (δ/2) := hyb
        rwa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hmem
      have hφl : |φ y - φ y₀| < δ/2 := by simpa [dist_eq_norm, Real.norm_eq_abs] using hyφ
      have hdist : dist (((φ y + (φ y₀ - φ y) * s : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) < δ := by
        rw [dist_eq_norm]
        have heq : ((φ y + (φ y₀ - φ y) * s : ℝ) : ℂ) + (y : ℂ) * Complex.I
            - ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)
            = (((φ y - φ y₀) * (1 - s) : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf
        rw [heq]
        have hna : ‖(((φ y - φ y₀) * (1 - s) : ℝ) : ℂ)‖ = |φ y - φ y₀| * (1 - s) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (show (0:ℝ) ≤ 1 - s by linarith)]
        have hnb : ‖(((y - y₀ : ℝ) : ℂ) * Complex.I)‖ = |y - y₀| := by
          rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
        have h1 : ‖(((φ y - φ y₀) * (1 - s) : ℝ) : ℂ) + ((y - y₀ : ℝ) : ℂ) * Complex.I‖
            ≤ |φ y - φ y₀| * (1 - s) + |y - y₀| := by
          rw [← hna, ← hnb]
          exact norm_add_le _ _
        have hb1 : |φ y - φ y₀| * (1 - s) ≤ |φ y - φ y₀| := by
          simpa using mul_le_mul_of_nonneg_left (show (1 - s) ≤ 1 by linarith)
            (abs_nonneg (φ y - φ y₀))
        have hb : |φ y - φ y₀| * (1 - s) + |y - y₀| < δ := by linarith
        linarith [h1, hb]
      show dist (W y s) (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≤ ε
      rw [hW]
      exact le_of_lt (hδb (Metric.mem_ball.mpr hdist))
  have hsub : ∀ y : ℝ, (∫ x in φ y..φ y₀, F ((x : ℂ) + (y : ℂ) * Complex.I))
      = (φ y₀ - φ y) • ∫ s in (0:ℝ)..1, W y s := by
    intro y
    rw [hW]
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := (1:ℝ))
      (c := φ y₀ - φ y) (d := φ y) (f := fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
    simp only [mul_zero, mul_one, add_zero] at h
    rw [show φ y + (φ y₀ - φ y) = φ y₀ from by ring] at h
    rw [h]
  have hslopeC : Tendsto (fun y : ℝ => (((φ y₀ - φ y) / (y - y₀) : ℝ) : ℂ)) (𝓝[<] y₀)
      (𝓝 (((-(φ' y₀)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hslope
  have hprod : Tendsto (fun y : ℝ => (((φ y₀ - φ y) / (y - y₀) : ℝ) : ℂ) * ∫ s in (0:ℝ)..1, W y s)
      (𝓝[<] y₀) (𝓝 ((((-(φ' y₀)) : ℝ) : ℂ) * F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) :=
    hslopeC.mul hWlim
  rw [show -(F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) * φ' y₀
      = (((-(φ' y₀)) : ℝ) : ℂ) * F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) from by push_cast; ring_nf]
  refine hprod.congr' (Eventually.of_forall fun y => ?_)
  change (((φ y₀ - φ y) / (y - y₀) : ℝ) : ℂ) * (∫ s in (0:ℝ)..1, W y s)
      = (∫ x in φ y..φ y₀, F ((x : ℂ) + (y : ℂ) * Complex.I)) / ((y : ℂ) - (y₀ : ℂ))
  rw [hsub, Complex.real_smul]
  push_cast
  ring

/-- For `y → y₀⁺`, the vertical-slice difference quotient tends to the slice value at `y₀`. -/
lemma tendsto_param_right
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo a b) :
    Tendsto (fun y : ℝ => (∫ y' in y₀..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I))) / (y - y₀))
      (𝓝[>] y₀)
      (𝓝 (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
  have hy₀a : a ≤ y₀ := hy₀.1.le
  have hy₀b : y₀ ≤ b := hy₀.2.le
  have hy₀Icc : y₀ ∈ Set.Icc a b := ⟨hy₀a, hy₀b⟩
  have hφy₀c : φ y₀ ≤ c := hφc y₀ hy₀Icc
  have hFc1 : ContinuousAt F ((c : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((c : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using hφy₀c) (by simp)).continuousAt
  have hFc2 : ContinuousAt F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using (le_rfl : φ y₀ ≤ φ y₀)) (by simpa using hφy₀c)).continuousAt
  have hφcAt : ContinuousAt φ y₀ := (hderiv y₀ hy₀).continuousAt
  set W : ℝ → ℝ → ℂ := fun y s =>
    F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
      - F ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) with hW
  have hWlim : Tendsto (fun y : ℝ => ∫ s in (0:ℝ)..1, W y s) (𝓝[>] y₀)
      (𝓝 (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
    apply tendsto_integral_unit
    · filter_upwards [Ioo_mem_nhdsGT hy₀.2] with y hy
      have hyIcc : y ∈ Set.Icc a b := ⟨hy₀a.trans hy.1.le, hy.2.le⟩
      have hφyb : φ y ≤ c := hφc y hyIcc
      apply ContinuousOn.sub
      · refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
        intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        have hima : a ≤ y₀ + (y - y₀) * s := by nlinarith [hy₀a, hy.1.le, hs1]
        have himb : y₀ + (y - y₀) * s ≤ b := by nlinarith [hy₀b, hy.2.le, hs1, hs2]
        have hre : φ (y₀ + (y - y₀) * s) ≤ c := hφc _ ⟨hima, himb⟩
        refine (mem_graphRegion).mpr ⟨by simpa using hima, by simpa using himb, ?_, ?_⟩
        · simpa using hre
        · simp
      · refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
        intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        have hima : a ≤ y₀ + (y - y₀) * s := by nlinarith [hy₀a, hy.1.le, hs1]
        have himb : y₀ + (y - y₀) * s ≤ b := by nlinarith [hy₀b, hy.2.le, hs1, hs2]
        have himy : y₀ + (y - y₀) * s ≤ y := by
          have h1 : (y - y₀) * s ≤ (y - y₀) * 1 := mul_le_mul_of_nonneg_left hs2 (by linarith [hy.1.le])
          linarith
        refine (mem_graphRegion).mpr ⟨by simpa using hima, by simpa using himb, ?_, ?_⟩
        · have hmm := hmono (⟨hima, himb⟩ : _ ∈ Set.Icc a b) hyIcc himy
          simpa using hmm
        · simpa using hφyb
    · intro ε hε
      obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc1) (ε/2) (by linarith))
      obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc2) (ε/2) (by linarith))
      have hδ₂h : 0 < δ₂/2 := by linarith
      have hmin : 0 < min δ₁ (δ₂/2) := lt_min hδ₁ hδ₂h
      have hφev : ∀ᶠ y in 𝓝 y₀, dist (φ y) (φ y₀) < δ₂/2 :=
        (Metric.tendsto_nhds.mp hφcAt) (δ₂/2) hδ₂h
      filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds y₀ hmin),
        Eventually.filter_mono nhdsWithin_le_nhds hφev] with y hyb hyφ
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hyy : |y - y₀| < min δ₁ (δ₂/2) := by
        have hmem : y ∈ Metric.ball y₀ (min δ₁ (δ₂/2)) := hyb
        rwa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hmem
      have hφφ : |φ y - φ y₀| < δ₂/2 := by simpa [dist_eq_norm, Real.norm_eq_abs] using hyφ
      have him : |(y₀ + (y - y₀) * s) - y₀| ≤ |y - y₀| := by
        rw [show y₀ + (y - y₀) * s - y₀ = (y - y₀) * s by ring, abs_mul, abs_of_nonneg hs1]
        exact mul_le_of_le_one_right (abs_nonneg _) hs2
      have hd1 : dist ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
          ((c : ℂ) + (y₀ : ℂ) * Complex.I) < δ₁ := by
        rw [dist_eq_norm]
        have he : (c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I - ((c : ℂ) + (y₀ : ℂ) * Complex.I)
            = (((y₀ + (y - y₀) * s) - y₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
        exact lt_of_le_of_lt him (lt_of_lt_of_le hyy (min_le_left _ _))
      have hd2 : dist ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
          ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) < δ₂ := by
        rw [dist_eq_norm]
        have he : (φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I - ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)
            = ((φ y - φ y₀ : ℝ) : ℂ) + (((y₀ + (y - y₀) * s) - y₀ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf
        rw [he]
        have hna : ‖((φ y - φ y₀ : ℝ) : ℂ)‖ = |φ y - φ y₀| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hnb : ‖((((y₀ + (y - y₀) * s) - y₀ : ℝ)) : ℂ) * Complex.I‖ = |(y₀ + (y - y₀) * s) - y₀| := by
          rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
        calc ‖((φ y - φ y₀ : ℝ) : ℂ) + (((y₀ + (y - y₀) * s) - y₀ : ℝ) : ℂ) * Complex.I‖
            ≤ |φ y - φ y₀| + |(y₀ + (y - y₀) * s) - y₀| := by
              rw [← hna, ← hnb]; exact norm_add_le _ _
          _ < δ₂ := by
              have h2 : |y₀ + (y - y₀) * s - y₀| < δ₂/2 :=
                lt_of_le_of_lt him (lt_of_lt_of_le hyy (min_le_right δ₁ (δ₂/2)))
              linarith
      show dist (W y s) (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≤ ε
      rw [hW]
      calc dist (F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I))
            (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))
          = ‖(F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((c : ℂ) + (y₀ : ℂ) * Complex.I))
            - (F ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))‖ := by rw [dist_eq_norm]; ring_nf
        _ ≤ ‖F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) - F ((c : ℂ) + (y₀ : ℂ) * Complex.I)‖
            + ‖F ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)‖ :=
              norm_sub_le _ _
        _ = dist (F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)) (F ((c : ℂ) + (y₀ : ℂ) * Complex.I))
            + dist (F ((φ y : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)) (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) := by
              rw [dist_eq_norm, dist_eq_norm]
        _ ≤ ε/2 + ε/2 := by
              gcongr
              · exact le_of_lt (hδ₁b (Metric.mem_ball.mpr hd1))
              · exact le_of_lt (hδ₂b (Metric.mem_ball.mpr hd2))
        _ = ε := by ring
  have hsub : ∀ y : ℝ, (∫ y' in y₀..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I)))
      = (y - y₀) • ∫ s in (0:ℝ)..1, W y s := by
    intro y
    rw [hW]
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := (1:ℝ))
      (c := y - y₀) (d := y₀)
      (f := fun x : ℝ => F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ y : ℂ) + (x : ℂ) * Complex.I))
    simp only [mul_zero, mul_one, add_zero] at h
    rw [show y₀ + (y - y₀) = y from by ring] at h
    rw [h]
  refine hWlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyne : (y : ℂ) - (y₀ : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hy) : (y : ℂ) ≠ (y₀ : ℂ))
  change (∫ s in (0:ℝ)..1, W y s)
      = (∫ y' in y₀..y, (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I))) / ((y : ℂ) - (y₀ : ℂ))
  rw [hsub, Complex.real_smul]
  push_cast
  field_simp

/-- For `y → y₀⁻`, the vertical-slice difference quotient tends to the slice value at `y₀`. -/
lemma tendsto_param_left
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo a b) :
    Tendsto (fun y : ℝ => (∫ y' in y₀..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I))) / (y - y₀))
      (𝓝[<] y₀)
      (𝓝 (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
  have hy₀a : a ≤ y₀ := hy₀.1.le
  have hy₀b : y₀ ≤ b := hy₀.2.le
  have hy₀Icc : y₀ ∈ Set.Icc a b := ⟨hy₀a, hy₀b⟩
  have hφy₀c : φ y₀ ≤ c := hφc y₀ hy₀Icc
  have hFc1 : ContinuousAt F ((c : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((c : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using hφy₀c) (by simp)).continuousAt
  have hFc2 : ContinuousAt F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (hF ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) (by simpa using hy₀a) (by simpa using hy₀b)
      (by simpa using (le_rfl : φ y₀ ≤ φ y₀)) (by simpa using hφy₀c)).continuousAt
  have hφcAt : ContinuousAt φ y₀ := (hderiv y₀ hy₀).continuousAt
  set W : ℝ → ℝ → ℂ := fun y s =>
    F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
      - F ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) with hW
  have hWlim : Tendsto (fun y : ℝ => ∫ s in (0:ℝ)..1, W y s) (𝓝[<] y₀)
      (𝓝 (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))) := by
    apply tendsto_integral_unit
    · filter_upwards [Ioo_mem_nhdsLT hy₀.1] with y hy
      have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le.trans hy₀b⟩
      have hyy' : y - y₀ ≤ 0 := by linarith [hy.2.le]
      apply ContinuousOn.sub
      · refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
        intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        have hima : a ≤ y₀ + (y - y₀) * s := by
          have := mul_le_mul_of_nonpos_left hs2 hyy'
          linarith [hy.1.le, this]
        have himb : y₀ + (y - y₀) * s ≤ b := by
          have h1 : (y - y₀) * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hyy' hs1
          linarith [hy₀b, h1]
        have hre : φ (y₀ + (y - y₀) * s) ≤ c := hφc _ ⟨hima, himb⟩
        refine (mem_graphRegion).mpr ⟨by simpa using hima, by simpa using himb, ?_, ?_⟩
        · simpa using hre
        · simp
      · refine (continuousOn_F_graphRegion hF).comp (by fun_prop) ?_
        intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        have hima : a ≤ y₀ + (y - y₀) * s := by
          have := mul_le_mul_of_nonpos_left hs2 hyy'
          linarith [hy.1.le, this]
        have himb : y₀ + (y - y₀) * s ≤ b := by
          have h1 : (y - y₀) * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hyy' hs1
          linarith [hy₀b, h1]
        have himle : y₀ + (y - y₀) * s ≤ y₀ := by
          have h1 : (y - y₀) * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hyy' hs1
          linarith
        refine (mem_graphRegion).mpr ⟨by simpa using hima, by simpa using himb, ?_, ?_⟩
        · have hmm := hmono (⟨hima, himb⟩ : _ ∈ Set.Icc a b) hy₀Icc himle
          simpa using hmm
        · simpa using hφy₀c
    · intro ε hε
      obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc1) (ε/2) (by linarith))
      obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFc2) (ε/2) (by linarith))
      have hδ₂h : 0 < δ₂/2 := by linarith
      have hmin : 0 < min δ₁ (δ₂/2) := lt_min hδ₁ hδ₂h
      have hφev : ∀ᶠ y in 𝓝 y₀, dist (φ y) (φ y₀) < δ₂/2 :=
        (Metric.tendsto_nhds.mp hφcAt) (δ₂/2) hδ₂h
      filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds y₀ hmin),
        Eventually.filter_mono nhdsWithin_le_nhds hφev] with y hyb hyφ
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hyy : |y - y₀| < min δ₁ (δ₂/2) := by
        have hmem : y ∈ Metric.ball y₀ (min δ₁ (δ₂/2)) := hyb
        rwa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hmem
      have hφφ : |φ y - φ y₀| < δ₂/2 := by simpa [dist_eq_norm, Real.norm_eq_abs] using hyφ
      have him : |(y₀ + (y - y₀) * s) - y₀| ≤ |y - y₀| := by
        rw [show y₀ + (y - y₀) * s - y₀ = (y - y₀) * s by ring, abs_mul, abs_of_nonneg hs1]
        exact mul_le_of_le_one_right (abs_nonneg _) hs2
      have hd1 : dist ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
          ((c : ℂ) + (y₀ : ℂ) * Complex.I) < δ₁ := by
        rw [dist_eq_norm]
        have he : (c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I - ((c : ℂ) + (y₀ : ℂ) * Complex.I)
            = (((y₀ + (y - y₀) * s) - y₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
        exact lt_of_le_of_lt him (lt_of_lt_of_le hyy (min_le_left _ _))
      have hd2 : dist ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
          ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) < δ₂ := by
        rw [dist_eq_norm]
        have he : (φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I - ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)
            = (((y₀ + (y - y₀) * s) - y₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
        exact lt_of_le_of_lt him (lt_of_lt_of_le hyy (le_trans (min_le_right δ₁ (δ₂/2)) (by linarith)))
      show dist (W y s) (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≤ ε
      rw [hW]
      calc dist (F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I))
            (F ((c : ℂ) + (y₀ : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))
          = ‖(F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((c : ℂ) + (y₀ : ℂ) * Complex.I))
            - (F ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)
              - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I))‖ := by rw [dist_eq_norm]; ring_nf
        _ ≤ ‖F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) - F ((c : ℂ) + (y₀ : ℂ) * Complex.I)‖
            + ‖F ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)‖ :=
              norm_sub_le _ _
        _ = dist (F ((c : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)) (F ((c : ℂ) + (y₀ : ℂ) * Complex.I))
            + dist (F ((φ y₀ : ℂ) + ((y₀ + (y - y₀) * s : ℝ) : ℂ) * Complex.I)) (F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) := by
              rw [dist_eq_norm, dist_eq_norm]
        _ ≤ ε/2 + ε/2 := by
              gcongr
              · exact le_of_lt (hδ₁b (Metric.mem_ball.mpr hd1))
              · exact le_of_lt (hδ₂b (Metric.mem_ball.mpr hd2))
        _ = ε := by ring
  have hsub : ∀ y : ℝ, (∫ y' in y₀..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I)))
      = (y - y₀) • ∫ s in (0:ℝ)..1, W y s := by
    intro y
    rw [hW]
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := (1:ℝ))
      (c := y - y₀) (d := y₀)
      (f := fun x : ℝ => F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (x : ℂ) * Complex.I))
    simp only [mul_zero, mul_one, add_zero] at h
    rw [show y₀ + (y - y₀) = y from by ring] at h
    rw [h]
  refine hWlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyne : (y : ℂ) - (y₀ : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt hy) : (y : ℂ) ≠ (y₀ : ℂ))
  change (∫ s in (0:ℝ)..1, W y s)
      = (∫ y' in y₀..y, (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I))) / ((y : ℂ) - (y₀ : ℂ))
  rw [hsub, Complex.real_smul]
  push_cast
  field_simp

/-- The fundamental theorem identity: `H` has derivative `g` on `(a,b)`, where
`H y = ∫_{φ y}^{c} F(x + y i)` and `g y = i F(c + y i) - F(φ y + y i) (φ' y + i)`. -/
lemma hasDerivAt_graphIntegral
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
      (Complex.I * F ((c : ℂ) + (y₀ : ℂ) * Complex.I)
        - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * ((φ' y₀ : ℂ) + Complex.I)) y₀ := by
  have hy₀a : a ≤ y₀ := hy₀.1.le
  have hy₀b : y₀ ≤ b := hy₀.2.le
  have hy₀Icc : y₀ ∈ Set.Icc a b := ⟨hy₀a, hy₀b⟩
  have hφy₀c : φ y₀ ≤ c := hφc y₀ hy₀Icc
  let Hfun : ℝ → ℂ := fun y => ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I)
  let E1 : ℝ → ℂ := fun y => -(∫ x in φ y₀..φ y, F ((x : ℂ) + (y₀ : ℂ) * Complex.I))
  let E2 : ℝ → ℂ := fun y => Complex.I * ∫ y' in y₀..y,
      (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I))
  let L1 : ℝ → ℂ := fun y => ∫ x in φ y..φ y₀, F ((x : ℂ) + (y : ℂ) * Complex.I)
  let L2 : ℝ → ℂ := fun y => Complex.I * ∫ y' in y₀..y,
      (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y₀ : ℂ) + (y' : ℂ) * Complex.I))
  have hE1 : Tendsto (fun y : ℝ => E1 y / (y - y₀)) (𝓝[>] y₀)
      (𝓝 (-(F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * (φ' y₀ : ℂ)))) := by
    have h := (tendsto_moving_upper hφc hmono hderiv hF hy₀).neg
    refine h.congr' (Eventually.of_forall fun y => ?_)
    simp only [E1]; ring
  have hE2 : Tendsto (fun y : ℝ => E2 y / (y - y₀)) (𝓝[>] y₀)
      (𝓝 (Complex.I * (F ((c : ℂ) + (y₀ : ℂ) * Complex.I)
        - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)))) := by
    have h := (tendsto_param_right hφc hmono hderiv hF hy₀).const_mul Complex.I
    refine h.congr' (Eventually.of_forall fun y => ?_)
    simp only [E2]; ring
  have hL1 : Tendsto (fun y : ℝ => L1 y / (y - y₀)) (𝓝[<] y₀)
      (𝓝 (-(F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)) * (φ' y₀ : ℂ))) := by
    have h := tendsto_moving_lower hφc hmono hderiv hF hy₀
    refine h.congr' (Eventually.of_forall fun y => ?_)
    simp only [L1]
  have hL2 : Tendsto (fun y : ℝ => L2 y / (y - y₀)) (𝓝[<] y₀)
      (𝓝 (Complex.I * (F ((c : ℂ) + (y₀ : ℂ) * Complex.I)
        - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I)))) := by
    have h := (tendsto_param_left hφc hmono hderiv hF hy₀).const_mul Complex.I
    refine h.congr' (Eventually.of_forall fun y => ?_)
    simp only [L2]; ring
  have hsumR : Tendsto (fun y : ℝ => E1 y / (y - y₀) + E2 y / (y - y₀)) (𝓝[>] y₀)
      (𝓝 (Complex.I * F ((c : ℂ) + (y₀ : ℂ) * Complex.I)
        - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * ((φ' y₀ : ℂ) + Complex.I))) := by
    convert hE1.add hE2 using 1; ring
  have hsumL : Tendsto (fun y : ℝ => L1 y / (y - y₀) + L2 y / (y - y₀)) (𝓝[<] y₀)
      (𝓝 (Complex.I * F ((c : ℂ) + (y₀ : ℂ) * Complex.I)
        - F ((φ y₀ : ℂ) + (y₀ : ℂ) * Complex.I) * ((φ' y₀ : ℂ) + Complex.I))) := by
    convert hL1.add hL2 using 1; ring
  have hHsubR : ∀ᶠ y in 𝓝[>] y₀, Hfun y - Hfun y₀ = E1 y + E2 y := by
    filter_upwards [Ioo_mem_nhdsGT hy₀.2] with y hy
    have hyIcc : y ∈ Set.Icc a b := ⟨hy₀a.trans hy.1.le, hy.2.le⟩
    have hφyb : φ y ≤ c := hφc y hyIcc
    have hy₀yb : φ y₀ ≤ φ y := hmono hy₀Icc hyIcc hy.1.le
    have hint_y : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) c := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
      exact continuousOn_F_horiz hF hyIcc
    have hint_y0 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) volume (φ y) c := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
      exact (continuousOn_F_horiz hF hy₀Icc).mono (Set.Icc_subset_Icc hy₀yb le_rfl)
    have hint_y0_split : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) volume (φ y₀) (φ y) := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hy₀yb]
      exact (continuousOn_F_horiz hF hy₀Icc).mono (Set.Icc_subset_Icc le_rfl hφyb)
    have hsplit : (∫ x in φ y₀..c, F ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        = (∫ x in φ y₀..φ y, F ((x : ℂ) + (y₀ : ℂ) * Complex.I))
          + ∫ x in φ y..c, F ((x : ℂ) + (y₀ : ℂ) * Complex.I) :=
      (intervalIntegral.integral_add_adjacent_intervals hint_y0_split hint_y0).symm
    rw [show Hfun y = ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I) from rfl,
      show Hfun y₀ = ∫ x in φ y₀..c, F ((x : ℂ) + (y₀ : ℂ) * Complex.I) from rfl, hsplit]
    simp only [E1, E2]
    have hdecomp : (∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
        = (∫ x in φ y..c, (F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((x : ℂ) + (y₀ : ℂ) * Complex.I)))
          + ∫ x in φ y..c, F ((x : ℂ) + (y₀ : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_sub hint_y hint_y0, sub_add_cancel]
    rw [hdecomp, rect_identity_le hφc hmono hF hy₀a hy.2.le hy.1.le]
    ring
  have hHsubL : ∀ᶠ y in 𝓝[<] y₀, Hfun y - Hfun y₀ = L1 y + L2 y := by
    filter_upwards [Ioo_mem_nhdsLT hy₀.1] with y hy
    have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le.trans hy₀b⟩
    have hφyb : φ y ≤ c := hφc y hyIcc
    have hyy₀ : φ y ≤ φ y₀ := hmono hyIcc hy₀Icc hy.2.le
    have hint_y : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) c := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
      exact continuousOn_F_horiz hF hyIcc
    have hint_y_upto : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) (φ y₀) := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hyy₀]
      exact (continuousOn_F_horiz hF hyIcc).mono (Set.Icc_subset_Icc le_rfl hφy₀c)
    have hint_y0c : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y₀) c := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφy₀c]
      exact (continuousOn_F_horiz hF hyIcc).mono (Set.Icc_subset_Icc hyy₀ le_rfl)
    have hsplit : (∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
        = (∫ x in φ y..φ y₀, F ((x : ℂ) + (y : ℂ) * Complex.I))
          + ∫ x in φ y₀..c, F ((x : ℂ) + (y : ℂ) * Complex.I) :=
      (intervalIntegral.integral_add_adjacent_intervals hint_y_upto hint_y0c).symm
    rw [show Hfun y = ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I) from rfl,
      show Hfun y₀ = ∫ x in φ y₀..c, F ((x : ℂ) + (y₀ : ℂ) * Complex.I) from rfl, hsplit]
    simp only [L1, L2]
    have hint_h0 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y₀ : ℂ) * Complex.I)) volume (φ y₀) c := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφy₀c]
      exact continuousOn_F_horiz hF hy₀Icc
    have hBC := (intervalIntegral.integral_sub hint_y0c hint_h0).symm
    have hrect := rect_identity_ge hφc hmono hF hy.1.le hy₀b hy.2.le
    linear_combination hBC + hrect
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine hsumL.congr' ?_
    filter_upwards [hHsubL, self_mem_nhdsWithin] with y hyH hylt
    have hyne : (y : ℂ) - (y₀ : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt hylt))
    rw [slope_def_module, hyH, Complex.real_smul]
    push_cast
    field_simp
  · refine hsumR.congr' ?_
    filter_upwards [hHsubR, self_mem_nhdsWithin] with y hyH hygt
    have hyne : (y : ℂ) - (y₀ : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hygt))
    rw [slope_def_module, hyH, Complex.real_smul]
    push_cast
    field_simp

/-- The integral over `[L,u]` of a locally bounded function tends to `0` as `u → L`. -/
lemma tendsto_integral_uIcc_zero {f : ℝ → ℂ} {L C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ u in 𝓝 L, ∀ x ∈ Set.uIcc L u, ‖f x‖ ≤ C) :
    Tendsto (fun u => ∫ x in L..u, f x) (𝓝 L) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hden : (0:ℝ) < 2 * (C + 1) := by linarith
  have hεD : (0:ℝ) < ε / (2 * (C + 1)) := by positivity
  filter_upwards [h, Metric.ball_mem_nhds L hεD] with u hbnd hub
  have hul : |u - L| < ε / (2 * (C + 1)) := by
    have hmem : u ∈ Metric.ball L (ε / (2 * (C + 1))) := hub
    rwa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hmem
  rw [dist_eq_norm, sub_zero]
  calc ‖∫ x in L..u, f x‖ ≤ C * |u - L| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        exact hbnd x (uIoc_subset_uIcc hx)
    _ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hul.le hC
    _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
        nlinarith [hε.le, hC]
    _ < ε := by linarith

/-- The integral over `[L,u]` of a parameterised locally bounded family tends to `0`. -/
lemma tendsto_integral_Icc_param_zero {f : ℝ → ℝ → ℂ} {L C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ u in 𝓝[>] L, ∀ x ∈ Set.Icc L u, ‖f u x‖ ≤ C) :
    Tendsto (fun u => ∫ x in L..u, f u x) (𝓝[>] L) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hden : (0:ℝ) < 2 * (C + 1) := by linarith
  have hεD : (0:ℝ) < ε / (2 * (C + 1)) := by positivity
  filter_upwards [h, self_mem_nhdsWithin,
    Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds L hεD)] with u hbnd hult hub
  have huL : L ≤ u := hult.le
  have hul : |u - L| < ε / (2 * (C + 1)) := by
    have hmem : u ∈ Metric.ball L (ε / (2 * (C + 1))) := hub
    rwa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hmem
  rw [dist_eq_norm, sub_zero]
  calc ‖∫ x in L..u, f u x‖ ≤ C * |u - L| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        exact hbnd x (by rw [uIoc_of_le huL] at hx; exact Ioc_subset_Icc_self hx)
    _ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hul.le hC
    _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
        nlinarith [hε.le, hC]
    _ < ε := by linarith

/-- Shrinking integral with a moving upper limit `g y → L`. -/
lemma tendsto_integral_Icc_param_zero' {l : Filter ℝ} {f : ℝ → ℝ → ℂ} {g : ℝ → ℝ} {L C : ℝ}
    (hC : 0 ≤ C) (hg : Tendsto g l (𝓝 L))
    (h : ∀ᶠ y in l, ∀ x ∈ Set.uIcc L (g y), ‖f y x‖ ≤ C) :
    Tendsto (fun y => ∫ x in L..g y, f y x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hden : (0:ℝ) < 2 * (C + 1) := by linarith
  have hεD : (0:ℝ) < ε / (2 * (C + 1)) := by positivity
  filter_upwards [h, (Metric.tendsto_nhds.mp hg) (ε / (2 * (C + 1))) hεD] with y hbnd hgy
  have hgl : |g y - L| < ε / (2 * (C + 1)) := by
    rw [dist_eq_norm, Real.norm_eq_abs] at hgy; exact hgy
  rw [dist_eq_norm, sub_zero]
  calc ‖∫ x in L..g y, f y x‖ ≤ C * |g y - L| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx; exact hbnd x (uIoc_subset_uIcc hx)
    _ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hgl.le hC
    _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
        nlinarith [hε.le, hC]
    _ < ε := by linarith

/-- Shrinking integral from a fixed limit. -/
lemma tendsto_integral_Icc_param_zero'' {l : Filter ℝ} {f : ℝ → ℝ → ℂ} {L C : ℝ}
    (hC : 0 ≤ C) (hl : l ≤ 𝓝 L)
    (h : ∀ᶠ y in l, ∀ x ∈ Set.uIcc L y, ‖f y x‖ ≤ C) :
    Tendsto (fun y => ∫ x in L..y, f y x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hden : (0:ℝ) < 2 * (C + 1) := by linarith
  have hεD : (0:ℝ) < ε / (2 * (C + 1)) := by positivity
  have hid : Tendsto (fun y : ℝ => y) l (𝓝 L) := tendsto_id.mono_left hl
  filter_upwards [h, (Metric.tendsto_nhds.mp hid) (ε / (2 * (C + 1))) hεD] with y hbnd hgy
  have hgl : |y - L| < ε / (2 * (C + 1)) := by
    rw [dist_eq_norm, Real.norm_eq_abs] at hgy; exact hgy
  rw [dist_eq_norm, sub_zero]
  calc ‖∫ x in L..y, f y x‖ ≤ C * |y - L| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx; exact hbnd x (uIoc_subset_uIcc hx)
    _ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hgl.le hC
    _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
        nlinarith [hε.le, hC]
    _ < ε := by linarith

/-- Cauchy's theorem for a region of the form `{a ≤ im ≤ b, φ im ≤ re ≤ c}`. -/
theorem graph_region_cauchy_mono
    (F : ℂ → ℂ) (φ φ' : ℝ → ℝ) (c a b : ℝ) (hab : a ≤ b)
    (hφc : ∀ y ∈ Set.Icc a b, φ y ≤ c)
    (hφcont : ContinuousOn φ (Set.Icc a b))
    (hφ'cont : ContinuousOn φ' (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt φ (φ' y) y)
    (hmono : MonotoneOn φ (Set.Icc a b))
    (hF : ∀ z : ℂ, a ≤ z.im → z.im ≤ b → φ z.im ≤ z.re → z.re ≤ c → DifferentiableAt ℂ F z) :
    Complex.I * (∫ y in a..b, F ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y in a..b, F ((φ y : ℂ) + (y : ℂ) * Complex.I) * ((φ' y : ℂ) + Complex.I))
      - (∫ x in (φ b)..c, F ((x : ℂ) + (b : ℂ) * Complex.I))
      + (∫ x in (φ a)..c, F ((x : ℂ) + (a : ℂ) * Complex.I)) = 0 := by
  rcases lt_or_eq_of_le hab with hab' | hab_eq
  swap
  · subst hab_eq; simp
  let Hfun : ℝ → ℂ := fun y => ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I)
  let gfun : ℝ → ℂ := fun y => Complex.I * F ((c : ℂ) + (y : ℂ) * Complex.I)
      - F ((φ y : ℂ) + (y : ℂ) * Complex.I) * ((φ' y : ℂ) + Complex.I)
  have hφa : Tendsto φ (𝓝[>] a) (𝓝 (φ a)) :=
    (hφcont.continuousWithinAt (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b)).mono_left
      (nhdsWithin_le_iff.mpr (by
        filter_upwards [Ioo_mem_nhdsGT hab'] with y hy; exact ⟨hy.1.le, hy.2.le⟩))
  have hφb : Tendsto φ (𝓝[<] b) (𝓝 (φ b)) :=
    (hφcont.continuousWithinAt (⟨hab, le_rfl⟩ : b ∈ Set.Icc a b)).mono_left
      (nhdsWithin_le_iff.mpr (by
        filter_upwards [Ioo_mem_nhdsLT hab'] with y hy; exact ⟨hy.1.le, hy.2.le⟩))
  have hFca : ContinuousAt F ((c : ℂ) + (a : ℂ) * Complex.I) :=
    (hF _ (by simpa using (le_rfl : a ≤ a)) (by simpa using hab)
      (by simpa using hφc a ⟨le_rfl, hab⟩) (by simp)).continuousAt
  have hFpa : ContinuousAt F ((φ a : ℂ) + (a : ℂ) * Complex.I) :=
    (hF _ (by simpa using (le_rfl : a ≤ a)) (by simpa using hab)
      (by simpa using (le_rfl : φ a ≤ φ a)) (by simpa using hφc a ⟨le_rfl, hab⟩)).continuousAt
  have hFcb : ContinuousAt F ((c : ℂ) + (b : ℂ) * Complex.I) :=
    (hF _ (by simpa using hab) (by simpa using (le_rfl : b ≤ b))
      (by simpa using hφc b ⟨hab, le_rfl⟩) (by simp)).continuousAt
  have hFpb : ContinuousAt F ((φ b : ℂ) + (b : ℂ) * Complex.I) :=
    (hF _ (by simpa using hab) (by simpa using (le_rfl : b ≤ b))
      (by simpa using (le_rfl : φ b ≤ φ b)) (by simpa using hφc b ⟨hab, le_rfl⟩)).continuousAt
  -- ============ limit at a, from the right ============
  have h0a : Tendsto (fun y : ℝ => Hfun y - Hfun a) (𝓝[>] a) (𝓝 0) := by
    have hdec : ∀ᶠ y in (𝓝[>] a : Filter ℝ), Hfun y - Hfun a
        = Complex.I * (∫ y' in a..y, (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I)))
          - (∫ x in φ a..φ y, F ((x : ℂ) + (a : ℂ) * Complex.I)) := by
      filter_upwards [Ioo_mem_nhdsGT hab'] with y hy
      have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le⟩
      have hφyb : φ y ≤ c := hφc y hyIcc
      have i_y : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) c := by
        apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
        exact continuousOn_F_horiz hF hyIcc
      have i_a : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (a : ℂ) * Complex.I)) volume (φ y) c := by
        apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
        exact (continuousOn_F_horiz hF (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b)).mono
          (Set.Icc_subset_Icc (hmono (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b) hyIcc hy.1.le) le_rfl)
      have i_asplit : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (a : ℂ) * Complex.I)) volume (φ a) (φ y) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (hmono (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b) hyIcc hy.1.le)]
        exact (continuousOn_F_horiz hF (⟨le_rfl, hab⟩ : a ∈ Set.Icc a b)).mono (Set.Icc_subset_Icc le_rfl hφyb)
      have hsplit : (∫ x in φ a..c, F ((x : ℂ) + (a : ℂ) * Complex.I))
          = (∫ x in φ a..φ y, F ((x : ℂ) + (a : ℂ) * Complex.I))
            + ∫ x in φ y..c, F ((x : ℂ) + (a : ℂ) * Complex.I) :=
        (intervalIntegral.integral_add_adjacent_intervals i_asplit i_a).symm
      rw [show Hfun y = ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I) from rfl,
        show Hfun a = ∫ x in φ a..c, F ((x : ℂ) + (a : ℂ) * Complex.I) from rfl, hsplit]
      have hdecomp : (∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
          = (∫ x in φ y..c, (F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((x : ℂ) + (a : ℂ) * Complex.I)))
            + ∫ x in φ y..c, F ((x : ℂ) + (a : ℂ) * Complex.I) := by
        rw [intervalIntegral.integral_sub i_y i_a, sub_add_cancel]
      rw [hdecomp, rect_identity_le hφc hmono hF (le_refl a) hy.2.le hy.1.le]
      ring
    have hL : Tendsto (fun y : ℝ => Complex.I * (∫ y' in a..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I)))) (𝓝[>] a) (𝓝 0) := by
      obtain ⟨δ1, hδ1, hb1⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFca) 1 one_pos)
      obtain ⟨δ2, hδ2, hb2⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFpa) 1 one_pos)
      have hδ2h : (0:ℝ) < δ2/2 := by linarith
      have hmin : (0:ℝ) < min δ1 (δ2/2) := lt_min hδ1 hδ2h
      have hbound : ∀ᶠ y in (𝓝[>] a : Filter ℝ), ∀ x ∈ Set.uIcc a y,
          ‖F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ y : ℂ) + (x : ℂ) * Complex.I)‖
            ≤ ‖F ((c : ℂ) + (a : ℂ) * Complex.I)‖ + ‖F ((φ a : ℂ) + (a : ℂ) * Complex.I)‖ + 2 := by
        filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds a hmin),
          hφa.eventually (Metric.ball_mem_nhds (φ a) hδ2h)] with y hyb hyφ
        intro x hx
        have hyl : |y - a| < min δ1 (δ2/2) := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyb
        have hφl : |φ y - φ a| < δ2/2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyφ
        have hxl : |x - a| ≤ |y - a| := abs_sub_le_of_mem_uIcc hx
        have hd1 : dist ((c : ℂ) + (x : ℂ) * Complex.I) ((c : ℂ) + (a : ℂ) * Complex.I) < δ1 := by
          rw [dist_eq_norm]
          have he : (c : ℂ) + (x : ℂ) * Complex.I - ((c : ℂ) + (a : ℂ) * Complex.I)
              = ((x - a : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
          exact lt_of_le_of_lt hxl (lt_of_lt_of_le hyl (min_le_left _ _))
        have hd2 : dist ((φ y : ℂ) + (x : ℂ) * Complex.I) ((φ a : ℂ) + (a : ℂ) * Complex.I) < δ2 := by
          rw [dist_eq_norm]
          have he : (φ y : ℂ) + (x : ℂ) * Complex.I - ((φ a : ℂ) + (a : ℂ) * Complex.I)
              = ((φ y - φ a : ℝ) : ℂ) + ((x - a : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [he]
          have hna : ‖((φ y - φ a : ℝ) : ℂ)‖ = |φ y - φ a| := by rw [Complex.norm_real, Real.norm_eq_abs]
          have hnb : ‖((x - a : ℝ) : ℂ) * Complex.I‖ = |x - a| := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
          have h2 : |x - a| < δ2/2 := lt_of_le_of_lt hxl (lt_of_lt_of_le hyl (min_le_right _ _))
          calc ‖((φ y - φ a : ℝ) : ℂ) + ((x - a : ℝ) : ℂ) * Complex.I‖
              ≤ |φ y - φ a| + |x - a| := by rw [← hna, ← hnb]; exact norm_add_le _ _
            _ < δ2 := by linarith
        have h1 := hb1 (Metric.mem_ball.mpr hd1)
        have h2 := hb2 (Metric.mem_ball.mpr hd2)
        simp only [Set.mem_ofPred_eq, dist_eq_norm] at h1 h2
        have h3 : ‖F ((φ y : ℂ) + (x : ℂ) * Complex.I)‖ ≤ ‖F ((φ a : ℂ) + (a : ℂ) * Complex.I)‖ + 1 := by
          linarith [norm_le_norm_add_norm_sub' (F ((φ y : ℂ) + (x : ℂ) * Complex.I)) (F ((φ a : ℂ) + (a : ℂ) * Complex.I)), h2]
        have h4 : ‖F ((c : ℂ) + (x : ℂ) * Complex.I)‖ ≤ ‖F ((c : ℂ) + (a : ℂ) * Complex.I)‖ + 1 := by
          linarith [norm_le_norm_add_norm_sub' (F ((c : ℂ) + (x : ℂ) * Complex.I)) (F ((c : ℂ) + (a : ℂ) * Complex.I)), h1]
        calc ‖F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ y : ℂ) + (x : ℂ) * Complex.I)‖
            ≤ ‖F ((c : ℂ) + (x : ℂ) * Complex.I)‖ + ‖F ((φ y : ℂ) + (x : ℂ) * Complex.I)‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      have := (tendsto_integral_Icc_param_zero'' (l := 𝓝[>] a) (L := a)
        (C := ‖F ((c : ℂ) + (a : ℂ) * Complex.I)‖ + ‖F ((φ a : ℂ) + (a : ℂ) * Complex.I)‖ + 2)
        (by positivity) nhdsWithin_le_nhds hbound).const_mul Complex.I
      simpa using this
    have hR : Tendsto (fun y : ℝ => ∫ x in φ a..φ y, F ((x : ℂ) + (a : ℂ) * Complex.I)) (𝓝[>] a) (𝓝 0) := by
      obtain ⟨δ2, hδ2, hb2⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFpa) 1 one_pos)
      have hboundR : ∀ᶠ y in 𝓝[>] a, ∀ x ∈ Set.uIcc (φ a) (φ y),
          ‖F ((x : ℂ) + (a : ℂ) * Complex.I)‖ ≤ ‖F ((φ a : ℂ) + (a : ℂ) * Complex.I)‖ + 1 := by
        filter_upwards [hφa.eventually (Metric.ball_mem_nhds (φ a) hδ2)] with y hyφ
        intro x hx
        have hφl : |φ y - φ a| < δ2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyφ
        have hxl : |x - φ a| ≤ |φ y - φ a| := abs_sub_le_of_mem_uIcc hx
        have hd : dist ((x : ℂ) + (a : ℂ) * Complex.I) ((φ a : ℂ) + (a : ℂ) * Complex.I) < δ2 := by
          rw [dist_eq_norm]
          have he : (x : ℂ) + (a : ℂ) * Complex.I - ((φ a : ℂ) + (a : ℂ) * Complex.I)
              = ((x - φ a : ℝ) : ℂ) := by push_cast; ring
          rw [he, Complex.norm_real, Real.norm_eq_abs]
          exact lt_of_le_of_lt hxl hφl
        have := hb2 (Metric.mem_ball.mpr hd)
        simp only [Set.mem_ofPred_eq, dist_eq_norm] at this
        linarith [norm_le_norm_add_norm_sub' (F ((x : ℂ) + (a : ℂ) * Complex.I)) (F ((φ a : ℂ) + (a : ℂ) * Complex.I)), this]
      exact tendsto_integral_Icc_param_zero' (l := 𝓝[>] a) (g := φ) (L := φ a)
        (C := ‖F ((φ a : ℂ) + (a : ℂ) * Complex.I)‖ + 1) (by positivity) hφa hboundR
    have hsum : Tendsto (fun y : ℝ => Complex.I * (∫ y' in a..y,
          (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ y : ℂ) + (y' : ℂ) * Complex.I)))
          - (∫ x in φ a..φ y, F ((x : ℂ) + (a : ℂ) * Complex.I))) (𝓝[>] a) (𝓝 0) := by
      simpa using hL.sub hR
    refine hsum.congr' ?_
    filter_upwards [hdec] with y hy
    exact hy.symm
  have hlow : Tendsto Hfun (𝓝[>] a) (𝓝 (Hfun a)) := by
    have := h0a.add_const (Hfun a)
    simpa using this
  -- ============ limit at b, from the left ============
  have h0b : Tendsto (fun y : ℝ => Hfun y - Hfun b) (𝓝[<] b) (𝓝 0) := by
    have hdec : ∀ᶠ y in (𝓝[<] b : Filter ℝ), Hfun y - Hfun b
        = (∫ x in φ y..φ b, F ((x : ℂ) + (y : ℂ) * Complex.I))
          + Complex.I * (∫ y' in b..y, (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ b : ℂ) + (y' : ℂ) * Complex.I))) := by
      filter_upwards [Ioo_mem_nhdsLT hab'] with y hy
      have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le⟩
      have hφyb : φ y ≤ c := hφc y hyIcc
      have i_y : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) c := by
        apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hφyb]
        exact continuousOn_F_horiz hF hyIcc
      have i_ysplit : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ y) (φ b) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (hmono hyIcc (⟨hab, le_rfl⟩ : b ∈ Set.Icc a b) hy.2.le)]
        exact (continuousOn_F_horiz hF hyIcc).mono (Set.Icc_subset_Icc le_rfl (hφc b ⟨hab, le_rfl⟩))
      have i_bc : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) volume (φ b) c := by
        apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le (hφc b ⟨hab, le_rfl⟩)]
        exact (continuousOn_F_horiz hF hyIcc).mono
          (Set.Icc_subset_Icc (hmono hyIcc (⟨hab, le_rfl⟩ : b ∈ Set.Icc a b) hy.2.le) le_rfl)
      have hsplit : (∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
          = (∫ x in φ y..φ b, F ((x : ℂ) + (y : ℂ) * Complex.I))
            + ∫ x in φ b..c, F ((x : ℂ) + (y : ℂ) * Complex.I) :=
        (intervalIntegral.integral_add_adjacent_intervals i_ysplit i_bc).symm
      rw [show Hfun y = ∫ x in φ y..c, F ((x : ℂ) + (y : ℂ) * Complex.I) from rfl,
        show Hfun b = ∫ x in φ b..c, F ((x : ℂ) + (b : ℂ) * Complex.I) from rfl, hsplit]
      have hrect := rect_identity_ge hφc hmono hF hy.1.le (le_refl b) hy.2.le
      have i_bcomp : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (b : ℂ) * Complex.I)) volume (φ b) c := by
        apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le (hφc b ⟨hab, le_rfl⟩)]
        exact continuousOn_F_horiz hF (⟨hab, le_rfl⟩ : b ∈ Set.Icc a b)
      have hdecomp : (∫ x in φ b..c, F ((x : ℂ) + (y : ℂ) * Complex.I))
          = (∫ x in φ b..c, (F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((x : ℂ) + (b : ℂ) * Complex.I)))
            + ∫ x in φ b..c, F ((x : ℂ) + (b : ℂ) * Complex.I) := by
        rw [intervalIntegral.integral_sub i_bc i_bcomp, sub_add_cancel]
      rw [hdecomp, hrect]
      ring
    have hL1 : Tendsto (fun y : ℝ => ∫ x in φ y..φ b, F ((x : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] b) (𝓝 0) := by
      obtain ⟨δ2, hδ2, hb2⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFpb) 1 one_pos)
      have hδ2h : (0:ℝ) < δ2/2 := by linarith
      have hbound : ∀ᶠ y in (𝓝[<] b : Filter ℝ), ∀ x ∈ Set.uIcc (φ b) (φ y),
          ‖F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ‖F ((φ b : ℂ) + (b : ℂ) * Complex.I)‖ + 1 := by
        filter_upwards [hφb.eventually (Metric.ball_mem_nhds (φ b) hδ2h),
          Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds b hδ2h)] with y hyφ hyb
        intro x hx
        have hφl : |φ y - φ b| < δ2/2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyφ
        have hβ : |y - b| < δ2/2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyb
        have hxl : |x - φ b| ≤ |φ y - φ b| := abs_sub_le_of_mem_uIcc hx
        have hd : dist ((x : ℂ) + (y : ℂ) * Complex.I) ((φ b : ℂ) + (b : ℂ) * Complex.I) < δ2 := by
          rw [dist_eq_norm]
          have he : (x : ℂ) + (y : ℂ) * Complex.I - ((φ b : ℂ) + (b : ℂ) * Complex.I)
              = ((x - φ b : ℝ) : ℂ) + ((y - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [he]
          have hna : ‖((x - φ b : ℝ) : ℂ)‖ = |x - φ b| := by rw [Complex.norm_real, Real.norm_eq_abs]
          have hnb : ‖((y - b : ℝ) : ℂ) * Complex.I‖ = |y - b| := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
          calc ‖((x - φ b : ℝ) : ℂ) + ((y - b : ℝ) : ℂ) * Complex.I‖
              ≤ |x - φ b| + |y - b| := by rw [← hna, ← hnb]; exact norm_add_le _ _
            _ < δ2 := by linarith
        have := hb2 (Metric.mem_ball.mpr hd)
        simp only [Set.mem_ofPred_eq, dist_eq_norm] at this
        linarith [norm_le_norm_add_norm_sub' (F ((x : ℂ) + (y : ℂ) * Complex.I)) (F ((φ b : ℂ) + (b : ℂ) * Complex.I)), this]
      have hbase := tendsto_integral_Icc_param_zero' (l := 𝓝[<] b) (g := φ) (L := φ b)
        (C := ‖F ((φ b : ℂ) + (b : ℂ) * Complex.I)‖ + 1) (by positivity) hφb hbound
      have hneg : Tendsto (fun y : ℝ => -(∫ x in φ b..φ y, F ((x : ℂ) + (y : ℂ) * Complex.I))) (𝓝[<] b) (𝓝 0) := by
        simpa using hbase.neg
      refine hneg.congr' (Eventually.of_forall fun y => ?_)
      rw [integral_symm, neg_neg]
    have hL2 : Tendsto (fun y : ℝ => Complex.I * (∫ y' in b..y,
        (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ b : ℂ) + (y' : ℂ) * Complex.I)))) (𝓝[<] b) (𝓝 0) := by
      obtain ⟨δ1, hδ1, hb1⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFcb) 1 one_pos)
      obtain ⟨δ2, hδ2, hb2⟩ := Metric.mem_nhds_iff.mp ((Metric.tendsto_nhds.mp hFpb) 1 one_pos)
      have hδ2h : (0:ℝ) < δ2/2 := by linarith
      have hmin : (0:ℝ) < min δ1 (δ2/2) := lt_min hδ1 hδ2h
      have hbound : ∀ᶠ y in (𝓝[<] b : Filter ℝ), ∀ x ∈ Set.uIcc b y,
          ‖F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ b : ℂ) + (x : ℂ) * Complex.I)‖
            ≤ ‖F ((c : ℂ) + (b : ℂ) * Complex.I)‖ + ‖F ((φ b : ℂ) + (b : ℂ) * Complex.I)‖ + 2 := by
        filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds b hmin),
          hφb.eventually (Metric.ball_mem_nhds (φ b) hδ2h)] with y hyb hyφ
        intro x hx
        have hyl : |y - b| < min δ1 (δ2/2) := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hyb
        have hφl : |φ b - φ y| < δ2/2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hyφ
        have hxl : |x - b| ≤ |y - b| := abs_sub_le_of_mem_uIcc hx
        have hd1 : dist ((c : ℂ) + (x : ℂ) * Complex.I) ((c : ℂ) + (b : ℂ) * Complex.I) < δ1 := by
          rw [dist_eq_norm]
          have he : (c : ℂ) + (x : ℂ) * Complex.I - ((c : ℂ) + (b : ℂ) * Complex.I)
              = ((x - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
          exact lt_of_le_of_lt hxl (lt_of_lt_of_le hyl (min_le_left _ _))
        have hd2 : dist ((φ b : ℂ) + (x : ℂ) * Complex.I) ((φ b : ℂ) + (b : ℂ) * Complex.I) < δ2 := by
          rw [dist_eq_norm]
          have he : (φ b : ℂ) + (x : ℂ) * Complex.I - ((φ b : ℂ) + (b : ℂ) * Complex.I)
              = ((x - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [he, Complex.norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
          have h2 : |x - b| < δ2/2 := lt_of_le_of_lt hxl (lt_of_lt_of_le hyl (min_le_right _ _))
          linarith
        have h1 := hb1 (Metric.mem_ball.mpr hd1)
        have h2 := hb2 (Metric.mem_ball.mpr hd2)
        simp only [Set.mem_ofPred_eq, dist_eq_norm] at h1 h2
        have h3 : ‖F ((φ b : ℂ) + (x : ℂ) * Complex.I)‖ ≤ ‖F ((φ b : ℂ) + (b : ℂ) * Complex.I)‖ + 1 := by
          linarith [norm_le_norm_add_norm_sub' (F ((φ b : ℂ) + (x : ℂ) * Complex.I)) (F ((φ b : ℂ) + (b : ℂ) * Complex.I)), h2]
        have h4 : ‖F ((c : ℂ) + (x : ℂ) * Complex.I)‖ ≤ ‖F ((c : ℂ) + (b : ℂ) * Complex.I)‖ + 1 := by
          linarith [norm_le_norm_add_norm_sub' (F ((c : ℂ) + (x : ℂ) * Complex.I)) (F ((c : ℂ) + (b : ℂ) * Complex.I)), h1]
        calc ‖F ((c : ℂ) + (x : ℂ) * Complex.I) - F ((φ b : ℂ) + (x : ℂ) * Complex.I)‖
            ≤ ‖F ((c : ℂ) + (x : ℂ) * Complex.I)‖ + ‖F ((φ b : ℂ) + (x : ℂ) * Complex.I)‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      have := (tendsto_integral_Icc_param_zero'' (l := 𝓝[<] b) (L := b)
        (C := ‖F ((c : ℂ) + (b : ℂ) * Complex.I)‖ + ‖F ((φ b : ℂ) + (b : ℂ) * Complex.I)‖ + 2)
        (by positivity) nhdsWithin_le_nhds hbound).const_mul Complex.I
      simpa using this
    have hsum : Tendsto (fun y : ℝ => (∫ x in φ y..φ b, F ((x : ℂ) + (y : ℂ) * Complex.I))
          + Complex.I * (∫ y' in b..y, (F ((c : ℂ) + (y' : ℂ) * Complex.I) - F ((φ b : ℂ) + (y' : ℂ) * Complex.I)))) (𝓝[<] b) (𝓝 0) := by
      simpa using hL1.add hL2
    refine hsum.congr' ?_
    filter_upwards [hdec] with y hy
    exact hy.symm
  have hhigh : Tendsto Hfun (𝓝[<] b) (𝓝 (Hfun b)) := by
    have := h0b.add_const (Hfun b)
    simpa using this
  -- ============ derivative, integrability, FTC ============
  have hderivH : ∀ y ∈ Set.Ioo a b, HasDerivAt Hfun (gfun y) y :=
    fun y hy => hasDerivAt_graphIntegral hφc hmono hderiv hF hy
  have hintg : IntervalIntegrable gfun volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have h1 : ContinuousOn (fun y : ℝ => Complex.I * F ((c : ℂ) + (y : ℂ) * Complex.I)) (Set.Icc a b) :=
      continuousOn_const.mul (continuousOn_F_vert hF (x := c) (s := Set.Icc a b)
        (fun t ht => ⟨ht.1, ht.2, hφc t ht, le_rfl⟩))
    have h2 : ContinuousOn (fun y : ℝ => F ((φ y : ℂ) + (y : ℂ) * Complex.I)) (Set.Icc a b) :=
      continuousOn_F_curve hF hφc hφcont
    have h3 : ContinuousOn (fun y : ℝ => (φ' y : ℂ) + Complex.I) (Set.Icc a b) :=
      (Complex.continuous_ofReal.comp_continuousOn hφ'cont).add continuousOn_const
    exact h1.sub (h2.mul h3)
  have hFTC : ∫ y in a..b, gfun y = Hfun b - Hfun a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab' hderivH hintg hlow hhigh
  have hg : (∫ y in a..b, gfun y) = Complex.I * (∫ y in a..b, F ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y in a..b, F ((φ y : ℂ) + (y : ℂ) * Complex.I) * ((φ' y : ℂ) + Complex.I)) := by
    simp only [gfun]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
    · refine ((continuousOn_const.mul (continuousOn_F_vert hF (x := c) (s := Set.Icc a b)
        (fun t ht => ⟨ht.1, ht.2, hφc t ht, le_rfl⟩))).mono (by rw [uIcc_of_le hab])).intervalIntegrable
    · refine (((continuousOn_F_curve hF hφc hφcont).mul
        ((Complex.continuous_ofReal.comp_continuousOn hφ'cont).add continuousOn_const)).mono
          (by rw [uIcc_of_le hab])).intervalIntegrable
  rw [← hg, hFTC]
  simp only [Hfun]
  ring

end Commons.Analysis.Complex