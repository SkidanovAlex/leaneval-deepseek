import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-! ## Auxiliary estimates

We prove the continuity of a function `u` whose increments are the integral of `v r / r`,
where `v` obeys the weighted square-root bound of the paper (with the radial weight
`w r = (1+r)²/r²`).  The only point that requires care is that no measurability of `v` is
assumed; the estimate is therefore formulated with `intervalIntegral.norm_integral_le_of_norm_le`,
which is valid for arbitrary integrands.
-/

/-- For every real `x`, `√x ≤ |x| + 1`. -/
private lemma sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg x]
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le]
    positivity

/-- If `|f|` is dominated pointwise on `(s,z]` by an interval-integrable function `Θ`, then the
integral of `f` over `[s,z]` is dominated by the integral of `Θ`.  No measurability of `f` is
required: if `f` fails to be interval integrable its integral is `0` by definition. -/
private lemma abs_intervalIntegral_le_integral_of_abs_le {f Θ : ℝ → ℝ} {s z : ℝ}
    (hsz : s ≤ z) (hΘ : IntervalIntegrable Θ volume s z)
    (hbd : ∀ t ∈ Set.Ioc s z, |f t| ≤ Θ t) :
    |∫ t in s..z, f t| ≤ ∫ t in s..z, Θ t := by
  have h1 : ‖∫ t in s..z, f t‖ ≤ ∫ t in s..z, Θ t :=
    intervalIntegral.norm_integral_le_of_norm_le hsz
      (Filter.Eventually.of_forall fun t ht => by
        simpa only [Real.norm_eq_abs] using hbd t ht) hΘ
  rwa [Real.norm_eq_abs] at h1

/-- **Continuity from the weighted square-root bound.**  If `u` has `v r / r` as its derivative
in the sense of the integral identity `u z - u s = ∫ r in s..z, v r / r` for `0 < s ≤ z`, and
`|v r| ≤ √(π/2) √(A r) / w r` with `A` integrable on `(0,∞)` and `w r = (1+r)²/r²`, then `u` is
continuous on `(0,∞)`.

The proof only uses the local `L¹` bound `√(A r) ≤ 1 + |A r|`; it is a genuine primitive
continuity argument, no differentiability of `u` is needed. -/
theorem continuousOn_of_primitive_of_sqrt_bound {u v A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0))
    (hbd : ∀ r ∈ Set.Ioi (0 : ℝ),
      |v r| ≤ Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r)
    (hchain : ∀ s z : ℝ, 0 < s → s ≤ z → u z - u s = ∫ r in s..z, v r / r) :
    ContinuousOn u (Set.Ioi 0) := by
  -- The majorant `Θ r = √(π/2) (1 + |A r|)`.
  let Θ : ℝ → ℝ := fun r => Real.sqrt (π / 2) * (|A r| + 1)
  have hΘnonneg : ∀ r, 0 ≤ Θ r := fun r =>
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  -- Pointwise bound `|v r / r| ≤ Θ r` for `r > 0`.
  have hmajor : ∀ r ∈ Set.Ioi (0 : ℝ), |v r / r| ≤ Θ r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hwpos : 0 < Work.Spaces.w r := by rw [Work.Spaces.w]; positivity
    have key : (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r
        = Real.sqrt (π / 2) * Real.sqrt (A r) * (r / (1 + r) ^ 2) := by
      rw [Work.Spaces.w]; field_simp
    have hratio : r / (1 + r) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hrpos.le]
    have hstep : (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r
        ≤ Real.sqrt (π / 2) * Real.sqrt (A r) := by
      rw [key]
      have h := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (Real.sqrt_nonneg (π / 2)) (Real.sqrt_nonneg (A r)))
      simpa using h
    calc |v r / r| = |v r| / r := by rw [abs_div, abs_of_pos hrpos]
      _ ≤ (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r :=
            div_le_div_of_nonneg_right (hbd r hr) hrpos.le
      _ ≤ Real.sqrt (π / 2) * Real.sqrt (A r) := hstep
      _ ≤ Θ r := mul_le_mul_of_nonneg_left (sqrt_le_abs_add_one (A r)) (Real.sqrt_nonneg _)
  -- Reduce to continuity at a single point `x₀ > 0`.
  intro x₀ hx₀
  have hx₀pos : 0 < x₀ := hx₀
  set lo : ℝ := x₀ / 2 with hlo_def
  set hi : ℝ := 2 * x₀ with hhi_def
  have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
  have hlo_lt : lo < x₀ := by rw [hlo_def]; linarith
  have hlt_hi : x₀ < hi := by rw [hhi_def]; linarith
  have hlo_hi : lo ≤ hi := le_of_lt (lt_trans hlo_lt hlt_hi)
  -- Integrability of the majorant on `[lo,hi]`.
  have hΘIcc : MeasureTheory.IntegrableOn Θ (Set.Icc lo hi) := by
    have hsub : Set.Icc lo hi ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hlo_pos hx.1
    have hA' : MeasureTheory.IntegrableOn A (Set.Icc lo hi) := hA.mono_set hsub
    have habs : MeasureTheory.IntegrableOn (fun r => |A r|) (Set.Icc lo hi) := hA'.abs
    have h1 : MeasureTheory.IntegrableOn (fun r => |A r| + 1) (Set.Icc lo hi) :=
      habs.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp))
    exact h1.const_mul (Real.sqrt (π / 2))
  have hminorInt : ∀ {s z : ℝ}, lo ≤ s → s ≤ z → z ≤ hi → IntervalIntegrable Θ volume s z := by
    intro s z hs hsz hz
    have hm : MeasureTheory.IntegrableOn Θ (Set.Icc s z) :=
      hΘIcc.mono_set (Set.Icc_subset_Icc hs hz)
    have hm' : MeasureTheory.IntegrableOn Θ (Set.uIcc s z) := by
      rw [Set.uIcc_of_le hsz]; exact hm
    exact hm'.intervalIntegrable
  -- The primitive `z ↦ ∫ t in x₀..z, Θ t` of the majorant is continuous at `x₀`.
  have hGcont : ContinuousOn (fun z => ∫ t in x₀..z, Θ t) (Set.uIcc lo hi) :=
    intervalIntegral.continuousOn_primitive_interval' (hminorInt le_rfl hlo_hi le_rfl)
      (by rw [Set.uIcc_of_le hlo_hi]; exact ⟨hlo_lt.le, hlt_hi.le⟩)
  have hGmem : Set.uIcc lo hi ∈ 𝓝 x₀ := by
    rw [Set.uIcc_of_le hlo_hi]; exact Icc_mem_nhds hlo_lt hlt_hi
  have hGat : ContinuousAt (fun z => ∫ t in x₀..z, Θ t) x₀ := hGcont.continuousAt hGmem
  have hGtend : Filter.Tendsto (fun z => ‖∫ t in x₀..z, Θ t‖) (𝓝 x₀) (𝓝 0) := by
    have h := hGat.norm
    simpa [ContinuousAt] using h
  -- On a neighbourhood of `x₀`, `u · - u x₀` is squeezed by that primitive.
  have hev : ∀ᶠ z in 𝓝 x₀, ‖u z - u x₀‖ ≤ ‖∫ t in x₀..z, Θ t‖ := by
    filter_upwards [Icc_mem_nhds hlo_lt hlt_hi] with z hz
    have hzpos : 0 < z := lt_of_lt_of_le hlo_pos hz.1
    rcases le_total x₀ z with hxz | hzx
    · -- `x₀ ≤ z`
      have hrepr : u z - u x₀ = ∫ r in x₀..z, v r / r := hchain x₀ z hx₀pos hxz
      have hmaj : |∫ r in x₀..z, v r / r| ≤ ∫ r in x₀..z, Θ r :=
        abs_intervalIntegral_le_integral_of_abs_le (f := fun r => v r / r) (Θ := Θ) hxz
          (hminorInt hlo_lt.le hxz hz.2)
          (fun t ht => hmajor t (Set.mem_Ioi.mpr (lt_trans hx₀pos ht.1)))
      have hGz : ‖∫ t in x₀..z, Θ t‖ = ∫ r in x₀..z, Θ r := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (intervalIntegral.integral_nonneg hxz (fun t _ => hΘnonneg t))]
      calc ‖u z - u x₀‖ = |∫ r in x₀..z, v r / r| := by rw [hrepr, Real.norm_eq_abs]
        _ ≤ ∫ r in x₀..z, Θ r := hmaj
        _ = ‖∫ t in x₀..z, Θ t‖ := hGz.symm
    · -- `z ≤ x₀`
      have hrepr : u z - u x₀ = -(∫ r in z..x₀, v r / r) := by
        have h := hchain z x₀ hzpos hzx
        linarith
      have hmaj : |∫ r in z..x₀, v r / r| ≤ ∫ r in z..x₀, Θ r :=
        abs_intervalIntegral_le_integral_of_abs_le (f := fun r => v r / r) (Θ := Θ) hzx
          (hminorInt hz.1 hzx hlt_hi.le)
          (fun t ht => hmajor t (Set.mem_Ioi.mpr (lt_trans hzpos ht.1)))
      have hGz : ‖∫ t in x₀..z, Θ t‖ = ∫ r in z..x₀, Θ r := by
        rw [intervalIntegral.integral_symm z x₀, norm_neg, Real.norm_eq_abs,
          abs_of_nonneg (intervalIntegral.integral_nonneg hzx (fun t _ => hΘnonneg t))]
      calc ‖u z - u x₀‖ = ‖-(∫ r in z..x₀, v r / r)‖ := by rw [hrepr]
        _ = |∫ r in z..x₀, v r / r| := by rw [norm_neg, Real.norm_eq_abs]
        _ ≤ ∫ r in z..x₀, Θ r := hmaj
        _ = ‖∫ t in x₀..z, Θ t‖ := hGz.symm
  -- Squeeze.
  have hnorm : Filter.Tendsto (fun z => ‖u z - u x₀‖) (𝓝 x₀) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg _) hev hGtend
  have hdiff : Filter.Tendsto (fun z => u z - u x₀) (𝓝 x₀) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcont : ContinuousAt u x₀ := by
    have h2 := hdiff.add_const (u x₀)
    have h3 : (fun z => (u z - u x₀) + u x₀) = u := by funext z; ring
    rw [h3] at h2
    simpa [ContinuousAt] using h2
  exact hcont.continuousWithinAt

end Work.FTS.EllipticEst
