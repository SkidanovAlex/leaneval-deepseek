/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FatouCoordFix.Repelling.ZDecay
import Submission.Work.FatouCoord.Repelling.defect_bound
import Submission.Work.FatouCoord.Flower.defect_zero_bound
import Submission.Work.FlowerGlue2.sum_log_div_sq_le
import Submission.Work.FlowerGlue2.log_ratio_norm_bound
import Submission.Work.FlowerGlue2.log_ratio_antitone

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The **fine decay of the correction `Z`** of the repelling coordinate

`Submission/Work/FatouCoordFix/Repelling/ZDecay.lean` exports the repelling coordinate
`V w = w + (1 - a) Λ w + Z w` of the parabolic germ `f z = z + z² h z` on a far left half-plane
`{Re w < -R}`, together with the *coarse* decay `‖Z w‖ ≤ K / √(1 - Re w)` of its correction.
That bound is uniform in `Im w` and is therefore useless when `Re w` is bounded but `|Im w|` is
large: it does not tend to `0` there.

The present lemma refines it to the bound actually needed by the implosion comparison
(`Submission/Work/NOTES_LEAD_mandelbar_implosion.md`, the exit comparison (B.4)):

  `‖Z w‖ ≤ K (1 + log ‖w‖) / ‖w‖`   on `{Re w < -R}`,

which is decay of the *sharp* order: the correction of the Fatou coordinate has an asymptotic
expansion `Z w = c/w + O(log ‖w‖/‖w‖²)`, so `(log ‖w‖)/‖w‖` is exactly the right size, and the
bound is uniform in the direction (it holds for `|Im w| → ∞` at fixed `Re w` as well).

## Proof

Write `w = -S + i Y` with `S = -Re w > 0`, `Y = |Im w|`.  Let `v := S + Y + 1`.

The correction is a fixed point of `Omega`: on the half-plane

  `Z w = ∑' n, defect f a (w - n - 1) (Z (w - n - 1))`,

and `‖defect f a x ζ‖ ≤ K (1 + log ‖x‖)/‖x‖²` for `x ∈ LeftHalfPlane R` and `‖ζ‖ ≤ 1`
(`Work.FatouCoord.Repelling.defect_bound`), while `‖Z‖ ≤ 1/2`.  The `n`-th point
`xₙ = w - n - 1` has `|Re xₙ| = S + n + 1`, `|Im xₙ| = Y`, so `‖xₙ‖ ≤ v + n` and
`(v + n)² ≤ 2 ‖xₙ‖²`; hence (`Work.FlowerGlue2.log_ratio_norm_bound`)

  `(1 + log ‖xₙ‖)/‖xₙ‖² ≤ 2 (1 + log (v+n))/(v+n)²`.

The series `∑ₙ (1 + log (v+n))/(v+n)²` is bounded by `8 (1 + log v)/v`
(`Work.FlowerGlue2.sum_log_div_sq_le`), and finally `(1 + log t)/t` is antitone on `[1,∞)`
(`Work.FlowerGlue2.log_ratio_antitone`) with `1 ≤ ‖w‖ ≤ v`, so
`(1 + log v)/v ≤ (1 + log ‖w‖)/‖w‖`.  This gives the claim with `K = 16 K₀ + 1`.
-/

namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

theorem fine_Z_decay_fatou {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ ∃ Z V : ℂ → ℂ,
      (∀ w : ℂ, w.re < -R → V w = w + (1 - a) * Work.FatouCoord.Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w.re < -R → V (w + 1) = Work.FatouCoord.wMap f (V w)) ∧
      Set.InjOn V {w : ℂ | w.re < -R} ∧
      ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, w.re < -R →
        ‖Z w‖ ≤ K * (1 + Real.log ‖w‖) / ‖w‖ := by
  obtain ⟨R₁, hR₁pos, -, Z, V, hZdiff, hZbd, hZeq, hZfix, hVdiff, hVdef, hVconj, hVnorm, hVne,
    hVinj, -, -, -⟩ := Work.FatouCoordFix.Repelling.exists_conjugacy_Z hb
  obtain ⟨R₂, K₂, hR₂pos, hrR₂, hK₂nn, hK₂⟩ := Work.FatouCoord.Repelling.defect_bound hb
  set R : ℝ := max (max R₁ R₂) 4 with hRdef
  have hR₁le : R₁ ≤ R := by rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₂le : R₂ ≤ R := by rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h4le : (4 : ℝ) ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hRpos : 0 < R := by linarith
  refine ⟨R, hRpos, Z, V, ?_, ?_, ?_, ⟨16 * K₂ + 1, by linarith, ?_⟩⟩
  · -- the corrected ansatz for `V`
    intro w hw
    exact hVdef w (by rw [Work.FatouCoord.Petal.mem_LeftHalfPlane]; linarith)
  · -- the conjugacy `V (w+1) = wMap f (V w)`
    intro w hw
    exact hVconj w (by rw [Work.FatouCoord.Petal.mem_LeftHalfPlane]; linarith)
  · -- injectivity, restricted to the smaller half-plane
    refine hVinj.mono ?_
    intro w hw
    rw [Work.FatouCoord.Petal.mem_LeftHalfPlane]
    have hw' : w.re < -R := hw
    linarith
  · -- the fine decay of `Z`
    intro w hw
    have hw1 : w ∈ Work.FatouCoord.Petal.LeftHalfPlane R₁ := by
      rw [Work.FatouCoord.Petal.mem_LeftHalfPlane]; linarith
    set S : ℝ := -w.re with hSdef
    have hS4 : 4 < S := by rw [hSdef]; linarith
    set Y : ℝ := |w.im| with hYdef
    have hYnn : 0 ≤ Y := by rw [hYdef]; exact abs_nonneg _
    have hv1 : 1 ≤ S + Y + 1 := by linarith
    have hw1le : 1 ≤ ‖w‖ := by
      have h := Complex.abs_re_le_norm w
      rw [abs_of_neg (by linarith : w.re < 0)] at h
      have hS4' : (4 : ℝ) < -w.re := by linarith
      linarith
    have hwlev : ‖w‖ ≤ S + Y + 1 := by
      rw [hSdef, hYdef]
      have h := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_neg (by linarith : w.re < 0)] at h
      linarith
    -- the fixed point form of `Z`
    have hfixw : Z w = ∑' n : ℕ, Work.FatouCoord.Petal.defect f a (w - ((n : ℕ) + 1))
        (Z (w - ((n : ℕ) + 1))) := by
      rw [hZfix w hw1, Work.FatouCoord.Petal.Omega_apply]
    -- the termwise estimate
    have hterm : ∀ n : ℕ,
        ‖Work.FatouCoord.Petal.defect f a (w - ((n : ℕ) + 1)) (Z (w - ((n : ℕ) + 1)))‖
          ≤ 2 * K₂ * ((1 + Real.log ((S + Y + 1) + (n : ℝ))) / ((S + Y + 1) + (n : ℝ)) ^ 2) := by
      intro n
      set x : ℂ := w - ((n : ℕ) + 1) with hxdef
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxre : x.re = -S - ((n : ℝ) + 1) := by
        rw [hxdef, hSdef]
        simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
        ring
      have hxim : x.im = w.im := by
        rw [hxdef]
        simp only [Complex.sub_im, Complex.add_im, Complex.natCast_im, Complex.one_im]
        ring
      have hxneg : x.re < 0 := by rw [hxre]; linarith
      have hxmem : x ∈ Work.FatouCoord.Petal.LeftHalfPlane R₂ := by
        rw [Work.FatouCoord.Petal.mem_LeftHalfPlane, hxre]
        linarith
      have hxmem₁ : x ∈ Work.FatouCoord.Petal.LeftHalfPlane R₁ := by
        rw [Work.FatouCoord.Petal.mem_LeftHalfPlane, hxre]
        linarith
      have hZx : ‖Z x‖ ≤ 1 := le_trans (hZbd x hxmem₁) (by norm_num)
      have hbd := hK₂ x (Z x) hxmem hZx
      have hx1 : 1 ≤ ‖x‖ := by
        have h := Complex.abs_re_le_norm x
        rw [abs_of_neg hxneg, hxre] at h
        linarith
      have hnorm := log_ratio_norm_bound x hx1
      have harg : |x.re| + |x.im| = (S + Y + 1) + (n : ℝ) := by
        rw [abs_of_neg hxneg, hxre, hxim]
        ring
      rw [harg] at hnorm
      calc ‖Work.FatouCoord.Petal.defect f a x (Z x)‖
          ≤ K₂ * (1 + Real.log ‖x‖) / ‖x‖ ^ 2 := hbd
        _ = K₂ * ((1 + Real.log ‖x‖) / ‖x‖ ^ 2) := by ring
        _ ≤ K₂ * (2 * (1 + Real.log ((S + Y + 1) + (n : ℝ))) / ((S + Y + 1) + (n : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hnorm hK₂nn
        _ = 2 * K₂ * ((1 + Real.log ((S + Y + 1) + (n : ℝ))) / ((S + Y + 1) + (n : ℝ)) ^ 2) := by
            ring
    have hsumm : Summable (fun n : ℕ =>
        2 * K₂ * ((1 + Real.log ((S + Y + 1) + (n : ℝ))) / ((S + Y + 1) + (n : ℝ)) ^ 2)) :=
      (sum_log_div_sq_le (S + Y + 1) hv1).1.mul_left (2 * K₂)
    have hnormsumm : Summable (fun n : ℕ =>
        ‖Work.FatouCoord.Petal.defect f a (w - ((n : ℕ) + 1)) (Z (w - ((n : ℕ) + 1)))‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsumm
    have hratio : (1 + Real.log (S + Y + 1)) / (S + Y + 1) ≤ (1 + Real.log ‖w‖) / ‖w‖ :=
      log_ratio_antitone hw1le hwlev
    have hnonneg : 0 ≤ (1 + Real.log ‖w‖) / ‖w‖ := by
      refine div_nonneg ?_ (by linarith)
      have := Real.log_nonneg hw1le
      linarith
    calc ‖Z w‖
        = ‖∑' n : ℕ, Work.FatouCoord.Petal.defect f a (w - ((n : ℕ) + 1))
            (Z (w - ((n : ℕ) + 1)))‖ := by rw [hfixw]
      _ ≤ ∑' n : ℕ, ‖Work.FatouCoord.Petal.defect f a (w - ((n : ℕ) + 1))
            (Z (w - ((n : ℕ) + 1)))‖ := norm_tsum_le_tsum_norm hnormsumm
      _ ≤ ∑' n : ℕ,
            2 * K₂ * ((1 + Real.log ((S + Y + 1) + (n : ℝ))) / ((S + Y + 1) + (n : ℝ)) ^ 2) :=
          Summable.tsum_le_tsum hterm hnormsumm hsumm
      _ = 2 * K₂ * (∑' n : ℕ, (1 + Real.log ((S + Y + 1) + (n : ℝ))) /
            ((S + Y + 1) + (n : ℝ)) ^ 2) := by
          rw [tsum_mul_left]
      _ ≤ 2 * K₂ * (8 * (1 + Real.log (S + Y + 1)) / (S + Y + 1)) :=
          mul_le_mul_of_nonneg_left (sum_log_div_sq_le (S + Y + 1) hv1).2 (by positivity)
      _ = 16 * K₂ * ((1 + Real.log (S + Y + 1)) / (S + Y + 1)) := by ring
      _ ≤ 16 * K₂ * ((1 + Real.log ‖w‖) / ‖w‖) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ (16 * K₂ + 1) * ((1 + Real.log ‖w‖) / ‖w‖) := by nlinarith
      _ = (16 * K₂ + 1) * (1 + Real.log ‖w‖) / ‖w‖ := by ring

end Work.FlowerGlue2
