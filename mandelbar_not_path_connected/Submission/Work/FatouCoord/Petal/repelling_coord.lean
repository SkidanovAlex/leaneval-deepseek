import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Repelling.exists_conjugacy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Existence of a repelling coordinate at a parabolic germ

Given `ParabolicBounds f h a r A A'` (so `f z = z + z ^ 2 * h z` with `h 0 = 1` and a simple
parabolic fixed point at `0`), we produce a *repelling coordinate*: a holomorphic function `Ψ` on
a far left half-plane `{Re w < -R}` of the parabolic chart `w = -1/z` which conjugates the shift
`w ↦ w + 1` to `f`, is injective, avoids `0`, and converges to `0` at the far end.

The construction is through the chart-conjugate dynamics `wMap f w = -1/f(-1/w)` (a translation by
`1` up to `O(1/‖w‖)`): we solve the conjugacy equation `V (w + 1) = wMap f (V w)` with
`V w = w + O(log ‖w‖)` by a contraction argument (see `Repelling/exists_conjugacy`), and set
`Ψ w = -1 / V w`.
-/

open scoped Topology
open Set Filter Metric

namespace Work.FatouCoord.Petal

noncomputable section

/-- The repelling coordinate built from a conjugacy `V` (in the chart `w = -1/z`): `-1/V w` on
the half-plane `{Re w < -R}`, and propagated one step to the right by the functional equation
(the values off the half-plane are only there to make `Ψ (w+1)` available in the equivariance
statement for `w` in the half-plane). -/
def repPsi (f V : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  if w.re < -R then -1 / V w else if w.re < -R + 1 then f (-1 / V (w - 1)) else 0

theorem repPsi_of_mem {f V : ℂ → ℂ} {R : ℝ} {w : ℂ} (hw : w.re < -R) :
    repPsi f V R w = -1 / V w := by
  simp only [repPsi]
  rw [if_pos hw]

theorem repPsi_of_not_mem {f V : ℂ → ℂ} {R : ℝ} {w : ℂ} (hw : ¬ w.re < -R)
    (hw' : w.re < -R + 1) :
    repPsi f V R w = f (-1 / V (w - 1)) := by
  simp only [repPsi]
  rw [if_neg hw, if_pos hw']

theorem repelling_coord {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ (R : ℝ) (Ψ : ℂ → ℂ), IsRepellingCoord f 0 R Ψ := by
  obtain ⟨R, hRpos, hRr, V, hVdiff, hVshift, hVclose, hVne, hVinj⟩ :=
    Work.FatouCoord.Repelling.exists_conjugacy hb
  refine ⟨R, repPsi f V R, hRpos, ?_, ?_, ?_, ?_, ?_⟩
  · -- holomorphy on the half-plane
    have h1 : DifferentiableOn ℂ (fun w : ℂ => -1 / V w) (LeftHalfPlane R) :=
      (differentiableOn_const (c := (-1 : ℂ))).div hVdiff fun w hw => hVne w hw
    refine h1.congr fun w hw => ?_
    exact repPsi_of_mem hw
  · -- equivariance: `Ψ (w+1) = f (Ψ w)`
    intro w hw
    by_cases h2 : (w + 1).re < -R
    · rw [repPsi_of_mem h2, repPsi_of_mem hw]
      have h := hVshift w hw
      simp only [wMap, chart] at h
      rw [h]
      field_simp
    · have h3 : (w + 1).re < -R + 1 := by
        have : (w + 1).re = w.re + 1 := by simp
        linarith
      rw [repPsi_of_not_mem h2 h3, repPsi_of_mem hw]
      congr 1
      ring_nf
  · -- injectivity on the half-plane
    intro x hx y hy hxy
    rw [repPsi_of_mem hx, repPsi_of_mem hy] at hxy
    have h1 : V x = V y := by
      have h2 := congrArg (fun z : ℂ => -1 / z) hxy
      simpa using h2
    exact hVinj hx hy h1
  · -- non-vanishing
    intro w hw
    rw [repPsi_of_mem hw]
    exact div_ne_zero (by norm_num) (hVne w hw)
  · -- small at the far end
    intro ε hε
    refine ⟨max R (2 / ε + 1), fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_left _ _))
    rw [repPsi_of_mem hwR]
    have hmax : (2 / ε + 1 : ℝ) ≤ max R (2 / ε + 1) := le_max_right _ _
    have h1 : (2 / ε + 1 : ℝ) ≤ ‖w‖ := by
      calc (2 / ε + 1 : ℝ) ≤ max R (2 / ε + 1) := hmax
        _ ≤ -w.re := by linarith
        _ ≤ ‖w‖ := le_trans (neg_le_abs w.re) (Complex.abs_re_le_norm w)
    have hnorm : 2 / ε < ‖w‖ := by linarith
    have hVw := hVclose w hwR
    have h2 : ‖w‖ / 2 ≤ ‖V w‖ := by
      have h3 : |‖V w‖ - ‖w‖| ≤ ‖V w - w‖ := abs_norm_sub_norm_le (V w) w
      have h3' : ‖w‖ - ‖V w - w‖ ≤ ‖V w‖ := by
        have h := (abs_le.mp h3).1
        linarith
      linarith
    have hwpos : (0 : ℝ) < ‖w‖ := by
      have : (0 : ℝ) < 2 / ε := by positivity
      linarith
    have hVpos : 0 < ‖V w‖ := by linarith
    rw [sub_zero, norm_div, norm_neg, norm_one, div_lt_iff₀ hVpos]
    have h4 : 1 < ε * (‖w‖ / 2) := by
      have h5 : ε * (2 / ε) = 2 := by field_simp
      nlinarith [hε, hnorm]
    have h5 : ε * (‖w‖ / 2) ≤ ε * ‖V w‖ := mul_le_mul_of_nonneg_left h2 hε.le
    linarith

end

end Work.FatouCoord.Petal
