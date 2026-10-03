import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Work.FIArea5.S16Hecke
open Work.FIPlan

noncomputable section

/-- Each summand of the holomorphic theta series is continuous in the variable `u`. -/
lemma continuous_thetaSummand (chi : GaussianInt → ℂ) (m : ℕ) (z : GaussianInt) :
    Continuous (fun u : ℝ => thetaSummand chi m u z) := by
  simp only [thetaSummand]
  split_ifs with hz
  · fun_prop
  · fun_prop

/-- The holomorphic theta series is continuous on every half-line `[a,∞)`, `a > 0`: the Gaussian
weight is uniformly dominated by its value at `a`, which is summable. -/
lemma continuousOn_thetaHol_Ici {chi : GaussianInt → ℂ} {m : ℕ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => thetaHol chi m u) (Set.Ici a) := by
  have hmain : ContinuousOn
      (fun x : ℝ => ∑' z : GaussianInt, thetaSummand chi m x z) (Set.Ici a) := by
    refine continuousOn_tsum
      (u := fun z : GaussianInt => Real.exp (-(Real.pi * a * (gnorm z : ℝ))) *
        (1 + (gnorm z : ℝ)) ^ m) (fun z => (continuous_thetaSummand chi m z).continuousOn)
      (summable_gnorm_weight ha m) ?_
    intro z x hx
    rw [Set.mem_Ici] at hx
    have h1 := thetaSummand_norm_le (m := m) (u := x) hb z
    have hg : (0 : ℝ) ≤ (gnorm z : ℝ) := Nat.cast_nonneg _
    have hle : -(Real.pi * x * (gnorm z : ℝ)) ≤ -(Real.pi * a * (gnorm z : ℝ)) := by
      have hpa : Real.pi * a ≤ Real.pi * x := by nlinarith [Real.pi_pos, hx]
      have := mul_le_mul_of_nonneg_right hpa hg
      linarith
    calc ‖thetaSummand chi m x z‖
        ≤ Real.exp (-(Real.pi * x * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m := h1
      _ ≤ Real.exp (-(Real.pi * a * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (by positivity)
  refine hmain.congr (fun x _ => ?_)
  exact thetaHol_eq_tsum chi m x

/-- The holomorphic theta series is continuous on the positive half-line. -/
lemma continuousOn_thetaHol_Ioi {chi : GaussianInt → ℂ} {m : ℕ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ContinuousOn (fun u : ℝ => thetaHol chi m u) (Set.Ioi 0) := by
  intro x hx
  have hpos : 0 < x := hx
  have hcont := continuousOn_thetaHol_Ici (chi := chi) (m := m) hb (half_pos hpos)
  have hxmem : x ∈ Set.Ici (x / 2) := by
    rw [Set.mem_Ici]; linarith
  have hcw : ContinuousWithinAt (fun u : ℝ => thetaHol chi m u) (Set.Ici (x / 2)) x :=
    hcont.continuousWithinAt hxmem
  have hmem : Set.Ici (x / 2) ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (show x / 2 < x by linarith))
      (fun y hy => le_of_lt (show x / 2 < y from hy))
  exact (hcw.continuousAt hmem).continuousWithinAt

theorem thetaHol_meas_li {chi : GaussianInt → ℂ} {m : ℕ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    AEMeasurable (Work.FIArea5.S16Hecke.thetaHol chi m)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) ∧
      MeasureTheory.LocallyIntegrableOn (Work.FIArea5.S16Hecke.thetaHol chi m) (Set.Ioi (0:ℝ)) := by
  have hcont := continuousOn_thetaHol_Ioi (chi := chi) (m := m) hb
  exact ⟨hcont.aemeasurable measurableSet_Ioi,
    hcont.locallyIntegrableOn measurableSet_Ioi⟩

end

end Work.FIArea6Hecke.R
