import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open MeasureTheory Filter Set
open scoped Topology

/-- The two end-shrinking integrals of an integrable function on `Iθ = [0, π/2]` tend to `0`.

Writing `a n = 1 / (n + 4)`, the first integral is `∫_{(0, a n]} h = F (a n)`, the primitive `F`
of `h`; the second is `∫_{(π/2 - a n, π/2]} h = F (π/2) - F (π/2 - a n)`.  Since `h` is integrable
on `[0, π/2]`, `F` is continuous there, and `a n → 0`, both terms vanish in the limit. -/
theorem ShrinkInt {h : ℝ → ℝ} (hh : MeasureTheory.IntegrableOn h Work.Spaces.Iθ) :
    Filter.Tendsto (fun n : ℕ => (∫ θ in Set.Ioc (0 : ℝ) (1 / ((n : ℝ) + 4)), h θ)
      + ∫ θ in Set.Ioc (Real.pi / 2 - 1 / ((n : ℝ) + 4)) (Real.pi / 2), h θ)
      Filter.atTop (nhds 0) := by
  classical
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hq4 : (1 : ℝ) / 4 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hint : IntegrableOn h (Set.uIcc (0 : ℝ) (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le hpi2]; exact hh
  have hcont : ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..t, h x)
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    intervalIntegral.continuousOn_primitive_interval hint
  have hA : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop := by
      have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 4)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h2
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 4)⁻¹) atTop (nhds 0) := hshift.inv_tendsto_atTop
    simpa [one_div] using h1
  have hle_half : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 4) ≤ Real.pi / 2 := by
    intro n
    have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have h1 : (1 : ℝ) / ((n : ℝ) + 4) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hn
    linarith
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ (1 : ℝ) / ((n : ℝ) + 4) := by
    intro n; positivity
  have hmemA : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 4) ∈ Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    intro n; rw [Set.uIcc_of_le hpi2]; exact ⟨hnn n, hle_half n⟩
  have hmemB : ∀ n : ℕ, Real.pi / 2 - 1 / ((n : ℝ) + 4) ∈ Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    intro n; rw [Set.uIcc_of_le hpi2]; exact ⟨by linarith [hle_half n], by linarith [hnn n]⟩
  have hFA : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(1 / ((n : ℝ) + 4)), h x) atTop (nhds 0) := by
    have h0 : (0:ℝ) ∈ Set.uIcc (0:ℝ) (Real.pi/2) := Set.left_mem_uIcc
    have hwit : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop
        (nhdsWithin (0:ℝ) (Set.uIcc (0:ℝ) (Real.pi/2))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hA, Filter.Eventually.of_forall hmemA⟩
    have h' := Filter.Tendsto.comp (hcont.continuousWithinAt h0) hwit
    simpa only [Function.comp_def, intervalIntegral.integral_same] using h'
  have hFB : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2 - 1 / ((n : ℝ) + 4)), h x)
      atTop (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), h x)) := by
    have hp : (Real.pi/2) ∈ Set.uIcc (0:ℝ) (Real.pi/2) := Set.right_mem_uIcc
    have hB : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 4)) atTop (nhds (Real.pi/2)) := by
      have hh2 := hA.const_sub (Real.pi / 2)
      simpa using hh2
    have hwit : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 4)) atTop
        (nhdsWithin (Real.pi/2) (Set.uIcc (0:ℝ) (Real.pi/2))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hB, Filter.Eventually.of_forall hmemB⟩
    have h' := Filter.Tendsto.comp (hcont.continuousWithinAt hp) hwit
    simpa only [Function.comp_def] using h'
  have hmain : Tendsto (fun n : ℕ =>
      (∫ x in (0:ℝ)..(1 / ((n : ℝ) + 4)), h x)
      + ((∫ x in (0:ℝ)..(Real.pi / 2), h x) - ∫ x in (0:ℝ)..(Real.pi / 2 - 1 / ((n : ℝ) + 4)), h x))
      atTop (nhds 0) := by
    have h' := hFA.add (hFB.const_sub (∫ x in (0:ℝ)..(Real.pi / 2), h x))
    simpa using h'
  refine hmain.congr' ?_
  filter_upwards with n
  have hn0 := hnn n
  have hsub : Set.uIcc (0:ℝ) (Real.pi/2 - 1/((n:ℝ)+4)) ⊆ Set.uIcc (0:ℝ) (Real.pi/2) := by
    rw [Set.uIcc_of_le (by linarith [hle_half n] : (0:ℝ) ≤ Real.pi/2 - 1/((n:ℝ)+4)),
      Set.uIcc_of_le hpi2]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hii1 : IntervalIntegrable h volume (0:ℝ) (Real.pi/2) := hint.intervalIntegrable
  have hii2 : IntervalIntegrable h volume (0:ℝ) (Real.pi / 2 - 1/((n:ℝ)+4)) :=
    (hint.mono_set hsub).intervalIntegrable
  have e1 : (∫ x in (0:ℝ)..(1 / ((n : ℝ) + 4)), h x)
      = ∫ θ in Set.Ioc (0:ℝ) (1/((n:ℝ)+4)), h θ := intervalIntegral.integral_of_le hn0
  have e2 : (∫ x in (0:ℝ)..(Real.pi/2), h x) - (∫ x in (0:ℝ)..(Real.pi/2 - 1/((n:ℝ)+4)), h x)
      = ∫ θ in Set.Ioc (Real.pi/2 - 1/((n:ℝ)+4)) (Real.pi/2), h θ := by
    rw [intervalIntegral.integral_interval_sub_left hii1 hii2]
    exact intervalIntegral.integral_of_le (by linarith)
  rw [e1, e2]

end Work.H2.T1Q
