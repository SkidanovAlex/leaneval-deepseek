import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval

/-! ### A composition lemma for differentiability when the outer derivative is zero -/

lemma hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
    {P q : ℝ → ℝ} {s b : ℝ}
    (hP : HasDerivAt P 0 b)
    (hq : ContinuousAt q s) (hqs : q s = b)
    (hqO : (fun r : ℝ => q r - b) =O[𝓝 s] (fun r : ℝ => r - s)) :
    HasDerivAt (fun r : ℝ => P (q r)) 0 s := by
  have hP_o : (fun y : ℝ => P y - P b) =o[𝓝 b] (fun y : ℝ => y - b) := by
    simpa using hP.isLittleO
  have hq_tend : Tendsto q (𝓝 s) (𝓝 b) := by
    simpa [hqs] using hq.tendsto
  have hcomp_o : (fun r : ℝ => P (q r) - P b) =o[𝓝 s] (fun r : ℝ => q r - b) := by
    simpa [Function.comp_def] using hP_o.comp_tendsto hq_tend
  have hfinal_o : (fun r : ℝ => P (q r) - P b) =o[𝓝 s] (fun r : ℝ => r - s) := by
    exact hcomp_o.trans_isBigO hqO
  apply HasDerivAt.of_isLittleO
  simpa [hqs] using hfinal_o

lemma isBigO_clamp_sub {a b : ℝ} {x : ℝ → ℝ} {s : ℝ}
    (hxO : (fun r : ℝ => x r - x s) =O[𝓝 s] (fun r : ℝ => r - s)) :
    (fun r : ℝ => max a (min b (x r)) - max a (min b (x s))) =O[𝓝 s] (fun r : ℝ => r - s) := by
  have hle : ∀ r : ℝ,
      ‖max a (min b (x r)) - max a (min b (x s))‖ ≤ ‖x r - x s‖ := by
    intro r
    calc
      ‖max a (min b (x r)) - max a (min b (x s))‖
          = |max a (min b (x r)) - max a (min b (x s))| := by rfl
      _ ≤ |min b (x r) - min b (x s)| := by
        simpa [max_comm] using (abs_max_sub_max_le_abs (min b (x r)) (min b (x s)) a)
      _ ≤ |x r - x s| := by
        have := abs_min_sub_min_le_max b (x r) b (x s)
        simpa [sub_self, abs_zero, max_eq_left (abs_nonneg (x r - x s))] using this
      _ = ‖x r - x s‖ := by rfl
  refine (Asymptotics.isBigO_of_le (𝓝 s) hle).trans ?_
  simpa using hxO

lemma cap_slice_hasDerivAt {n : ℕ} {F s t dh : ℝ} {h : ℝ → ℝ}
    (hn : 2 ≤ n) (hF : 0 ≤ F) (hh : HasDerivAt h dh s) :
    HasDerivAt
      (fun r : ℝ =>
        ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (F ^ 2 - z ^ 2) ^ (n - 1))
      (if -F < s * t + h s ∧ s * t + h s < F then
          (F ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + dh)
        else 0)
      s := by
  let a : ℝ := -F
  let b : ℝ := F
  let g : ℝ → ℝ := fun z => (F ^ 2 - z ^ 2) ^ (n - 1)
  let x : ℝ → ℝ := fun r => r * t + h r
  let u : ℝ → ℝ := fun r => max a (min b (x r))
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hx : HasDerivAt x (t + dh) s := by
    have h1 : HasDerivAt (fun r : ℝ => r * t) t s := by
      simpa using (hasDerivAt_id s).mul_const t
    exact h1.add hh
  have hx_cont : ContinuousAt x s := hx.continuousAt
  have hxO : (fun r : ℝ => x r - x s) =O[𝓝 s] (fun r : ℝ => r - s) :=
    hx.isBigO_sub
  have hu_cont : ContinuousAt u s := by
    dsimp [u, a, b]
    have hmin : ContinuousAt (fun r : ℝ => min F (x r)) s :=
      continuous_min.continuousAt.comp₂ continuousAt_const hx_cont
    have hmax : ContinuousAt (fun r : ℝ => max (-F) (min F (x r))) s :=
      continuous_max.continuousAt.comp₂ continuousAt_const hmin
    simpa using hmax
  have huO : (fun r : ℝ => u r - u s) =O[𝓝 s] (fun r : ℝ => r - s) := by
    dsimp [u, a, b]
    exact isBigO_clamp_sub hxO
  have hg_cont : Continuous g := by
    dsimp [g]
    continuity
  have hnz : n - 1 ≠ 0 := by omega
  have hg_zero_left : g a = 0 := by
    dsimp [g, a]
    simp [zero_pow hnz]
  have hg_zero_right : g b = 0 := by
    dsimp [g, b]
    simp [zero_pow hnz]
  have hP_left : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 a := by
    have h := (hg_cont.integral_hasStrictDerivAt a a).hasDerivAt
    simpa [g, hg_zero_left] using h
  have hP_right : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) 0 b := by
    have h := (hg_cont.integral_hasStrictDerivAt a b).hasDerivAt
    simpa [g, hg_zero_right] using h
  by_cases hcond : -F < s * t + h s ∧ s * t + h s < F
  · have hxs_lower : a < x s := by
      dsimp [x, a]
      simpa using hcond.1
    have hxs_upper : x s < b := by
      dsimp [x, b]
      simpa using hcond.2
    have h_event_lower : ∀ᶠ r in 𝓝 s, a < x r := by
      have hmem : {r : ℝ | a < x r} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxs_lower)
      exact Filter.eventually_iff.mpr hmem
    have h_event_upper : ∀ᶠ r in 𝓝 s, x r < b := by
      have hmem : {r : ℝ | x r < b} ∈ 𝓝 s :=
        hx_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hxs_upper)
      exact Filter.eventually_iff.mpr hmem
    have h_event_u : ∀ᶠ r in 𝓝 s, u r = x r := by
      filter_upwards [h_event_lower, h_event_upper] with r hr_lower hr_upper
      dsimp [u, a, b]
      rw [min_eq_right hr_upper.le, max_eq_right hr_lower.le]
    have hP_deriv : HasDerivAt (fun y : ℝ => ∫ z in a..y, g z) (g (x s)) (x s) :=
      (hg_cont.integral_hasStrictDerivAt a (x s)).hasDerivAt
    have hcomp : HasDerivAt ((fun y : ℝ => ∫ z in a..y, g z) ∘ x)
        (g (x s) * (t + dh)) s := by
      simpa [Function.comp_def] using hP_deriv.comp s hx
    have h_event : (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (F ^ 2 - z ^ 2) ^ (n - 1)) =ᶠ[𝓝 s]
        ((fun y : ℝ => ∫ z in a..y, g z) ∘ x) := by
      filter_upwards [h_event_u] with r hr
      have hr' : max (-F) (min F (r * t + h r)) = r * t + h r := by
        simpa [u, x, a, b] using hr
      simp [a, g, x, hr']
    have hmain : HasDerivAt
        (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
          (F ^ 2 - z ^ 2) ^ (n - 1))
        (g (x s) * (t + dh)) s :=
      HasDerivAt.congr_of_eventuallyEq hcomp h_event
    simpa [x, g, hcond] using hmain
  · have hcond_false : ¬ (-F < s * t + h s ∧ s * t + h s < F) := hcond
    by_cases hle_lower : s * t + h s ≤ -F
    · have hxs_lower : x s ≤ a := by
        dsimp [x, a]
        simpa using hle_lower
      have hqs : u s = a := by
        dsimp [u, a, b]
        rw [min_eq_right (le_trans hxs_lower hab)]
        rw [max_eq_left hxs_lower]
      have hqO : (fun r : ℝ => u r - a) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := a)
          hP_left hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
            (F ^ 2 - z ^ 2) ^ (n - 1)) 0 s := by
        simpa [u, a, b, g] using hderiv0
      simpa [hcond_false] using hmain
    · have h_upper : F ≤ s * t + h s := by
        have h_not_lower : -F < s * t + h s := lt_of_not_ge hle_lower
        have h_not_upper : ¬ s * t + h s < F := by
          intro hup
          exact hcond_false ⟨h_not_lower, hup⟩
        exact le_of_not_gt h_not_upper
      have hxs_upper : b ≤ x s := by
        dsimp [x, b]
        simpa using h_upper
      have hqs : u s = b := by
        dsimp [u, a, b]
        rw [min_eq_left hxs_upper]
        rw [max_eq_right hab]
      have hqO : (fun r : ℝ => u r - b) =O[𝓝 s] (fun r : ℝ => r - s) := by
        simpa [hqs] using huO
      have hderiv0 : HasDerivAt (fun r : ℝ => ∫ z in a..(u r), g z) 0 s := by
        simpa using hasDerivAt_comp_of_deriv_zero_of_isBigO_sub
          (P := fun y : ℝ => ∫ z in a..y, g z) (q := u) (s := s) (b := b)
          hP_right hu_cont hqs hqO
      have hmain : HasDerivAt
          (fun r : ℝ => ∫ z in (-F)..(max (-F) (min F (r * t + h r))),
            (F ^ 2 - z ^ 2) ^ (n - 1)) 0 s := by
        simpa [u, a, b, g] using hderiv0
      simpa [hcond_false] using hmain

end Commons.Geometry.Ulam