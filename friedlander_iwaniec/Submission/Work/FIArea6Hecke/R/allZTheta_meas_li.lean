import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Work.FIArea5.S16Hecke
open Work.FIPlan

noncomputable section

/-- Each summand of the all-`z` theta series is continuous in the variable `u`. -/
lemma continuous_allZSummand (chi₀ : GaussianInt → ℂ) (m : ℕ) (z : GaussianInt) :
    Continuous (fun u : ℝ => allZSummand chi₀ m u z) := by
  simp only [allZSummand]
  fun_prop

/-- The all-`z` theta series is continuous on every half-line `[a,∞)`, `a > 0`: the Gaussian
weight is uniformly dominated by its value at `a`, which is summable. -/
lemma continuousOn_allZTheta_Ici {chi₀ : GaussianInt → ℂ} {m : ℕ}
    (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => allZTheta chi₀ m u) (Set.Ici a) := by
  have hmain : ContinuousOn
      (fun x : ℝ => ∑' z : GaussianInt, allZSummand chi₀ m x z) (Set.Ici a) := by
    refine continuousOn_tsum
      (u := fun z : GaussianInt => Real.exp (-(Real.pi * a * (gnorm z : ℝ))) *
        (1 + (gnorm z : ℝ)) ^ m) (fun z => (continuous_allZSummand chi₀ m z).continuousOn)
      (summable_gnorm_weight ha m) ?_
    intro z x hx
    rw [Set.mem_Ici] at hx
    have h1 := allZSummand_norm_le (m := m) (u := x) hb z
    have hg : (0 : ℝ) ≤ (gnorm z : ℝ) := Nat.cast_nonneg _
    have hle : -(Real.pi * x * (gnorm z : ℝ)) ≤ -(Real.pi * a * (gnorm z : ℝ)) := by
      have hpa : Real.pi * a ≤ Real.pi * x := by nlinarith [Real.pi_pos, hx]
      have := mul_le_mul_of_nonneg_right hpa hg
      linarith
    calc ‖allZSummand chi₀ m x z‖
        ≤ Real.exp (-(Real.pi * x * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m := h1
      _ ≤ Real.exp (-(Real.pi * a * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (by positivity)
  refine hmain.congr (fun x _ => ?_)
  exact allZTheta_eq_tsum_summand chi₀ m x

/-- The all-`z` theta series is continuous on the positive half-line. -/
lemma continuousOn_allZTheta_Ioi {chi₀ : GaussianInt → ℂ} {m : ℕ}
    (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) :
    ContinuousOn (fun u : ℝ => allZTheta chi₀ m u) (Set.Ioi 0) := by
  intro x hx
  have hpos : 0 < x := hx
  have hcont := continuousOn_allZTheta_Ici (chi₀ := chi₀) (m := m) hb (half_pos hpos)
  have hxmem : x ∈ Set.Ici (x / 2) := by
    rw [Set.mem_Ici]; linarith
  have hcw : ContinuousWithinAt (fun u : ℝ => allZTheta chi₀ m u) (Set.Ici (x / 2)) x :=
    hcont.continuousWithinAt hxmem
  have hmem : Set.Ici (x / 2) ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (show x / 2 < x by linarith))
      (fun y hy => le_of_lt (show x / 2 < y from hy))
  exact (hcw.continuousAt hmem).continuousWithinAt

theorem allZTheta_meas_li (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) :
    AEMeasurable (Work.FIArea6Hecke.R.allZTheta chi₀ m)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) ∧
      MeasureTheory.LocallyIntegrableOn (Work.FIArea6Hecke.R.allZTheta chi₀ m) (Set.Ioi (0:ℝ)) := by
  have hcont := continuousOn_allZTheta_Ioi (chi₀ := chi₀) (m := m) hchi
  exact ⟨hcont.aemeasurable measurableSet_Ioi,
    hcont.locallyIntegrableOn measurableSet_Ioi⟩

end

end Work.FIArea6Hecke.R
