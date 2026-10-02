import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp
import Submission.Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_ball
import Submission.Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le
import Submission.Work.MRMT.Cauchy.exists_lintegral_enorm_rpow_lt_top_of_memLp
import Submission.Work.MRMT.Cauchy.holder_bound_cauchyIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the Cauchy transform of a compactly supported `L^p` function, `p > 2`

The Cauchy transform `Cν(z) = -(1/π) ∫ w, ν w / (w - z)` of a compactly supported function
`ν ∈ L^p(ℂ)`, `2 < p`, is continuous.  The proof reduces to a Hölder estimate of order
`1 - 2/t` with `t` a finite exponent `2 < t ≤ p`, whose kernel input is the two-point bound

`∫⁻ w, ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q) ≤ K ‖z - z'‖ ^ (2 - 2q)`,  `q = t/(t-1) ∈ (1,2)`,

proved here by splitting the plane into `ball z (d/2)`, `ball z (2d) \ ball z (d/2)` and the
exterior `{2d ≤ ‖w - z‖}`, `d = ‖z - z'‖`, and using the explicit planar integrals
`Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_ball` and
`Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le`.
-/

namespace Work.MRMT.Found

open MeasureTheory Metric

set_option maxHeartbeats 1000000

/-- Pulling a constant out of an `ℝ≥0∞`-valued set integral. -/
private lemma setLIntegral_const_mul_ennreal {s : Set ℂ} (hs : MeasurableSet s) (c : ENNReal)
    (g : ℂ → ENNReal) (hg : Measurable g) :
    (∫⁻ w in s, c * g w) = c * ∫⁻ w in s, g w := by
  have h1 : (∫⁻ w in s, c * g w) = ∫⁻ w, s.indicator (fun w => c * g w) w :=
    (MeasureTheory.lintegral_indicator hs (fun w => c * g w)).symm
  have h2 : (∫⁻ w in s, g w) = ∫⁻ w, s.indicator g w :=
    (MeasureTheory.lintegral_indicator hs g).symm
  have hpt : s.indicator (fun w => c * g w) = fun w => c * s.indicator g w := by
    funext w
    by_cases hw : w ∈ s
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
  rw [h1, h2, hpt, MeasureTheory.lintegral_const_mul c (hg.indicator hs)]

/-- **Two-point bound for the plane Cauchy kernel.**  For `1 < q < 2` there is a constant `K`,
depending only on `q`, such that for all distinct `z z' : ℂ`
`∫⁻ w, ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q) ≤ ofReal (K * ‖z - z'‖ ^ (2 - 2q))`.

This is the kernel estimate behind the Hölder continuity of order `(2-q)/q` of the Cauchy
transform on `L^t`, `t = q/(q-1) > 2`. -/
theorem two_point_kernel_bound {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z z' : ℂ, z ≠ z' →
      (∫⁻ w : ℂ, ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q)) ≤
        ENNReal.ofReal (K * ‖z - z'‖ ^ (2 - 2 * q)) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have h2q : 0 < 2 - q := by linarith
  have hq2' : 0 < 2 * q - 2 := by linarith
  have hnegq : -q ≤ 0 := by linarith
  set c1 : ℝ := 2 * Real.pi * 2 ^ (2 * q - 2) / (2 - q) with hc1def
  set c2 : ℝ := 2 ^ q * (2 * Real.pi * 3 ^ (2 - q) / (2 - q)) with hc2def
  set c3 : ℝ := 2 ^ q * (2 * Real.pi * 2 ^ (2 - 2 * q) / (2 * q - 2)) with hc3def
  have hc1nn : 0 ≤ c1 := by
    rw [hc1def]
    exact div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)) h2q.le
  have hc2nn : 0 ≤ c2 := by
    rw [hc2def]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)) h2q.le)
  have hc3nn : 0 ≤ c3 := by
    rw [hc3def]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)) hq2'.le)
  refine ⟨c1 + c2 + c3, by linarith, ?_⟩
  intro z z' hzz
  set F : ℂ → ENNReal := fun w => ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q) with hFdef
  set d : ℝ := ‖z - z'‖ with hdd
  have hdpos : 0 < d := by rw [hdd]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  set r : ℝ := d / 2 with hrd
  have hrpos : 0 < r := by rw [hrd]; linarith
  set A1 : Set ℂ := Metric.ball z r with hA1
  set A2 : Set ℂ := Metric.ball z (2 * d) \ Metric.ball z r with hA2
  set A3 : Set ℂ := {w : ℂ | 2 * d ≤ ‖w - z‖} with hA3
  have hA1m : MeasurableSet A1 := by rw [hA1]; exact Metric.isOpen_ball.measurableSet
  have hA3m : MeasurableSet A3 := by
    rw [hA3]
    exact (isClosed_le continuous_const
      (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  have hA2m : MeasurableSet A2 := by
    rw [hA2]; exact Metric.isOpen_ball.measurableSet.diff (by rw [← hA1]; exact hA1m)
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    intro a b c
    have := dist_triangle a b c
    simpa only [dist_eq_norm] using this
  have hcompl : A1ᶜ = A2 ∪ A3 := by
    rw [hA1, hA2, hA3]
    ext w
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, Metric.mem_ball,
      Set.mem_setOf_eq, dist_eq_norm]
    constructor
    · intro h
      by_cases h2 : ‖w - z‖ < 2 * d
      · exact Or.inl ⟨h2, h⟩
      · exact Or.inr (not_lt.mp h2)
    · rintro (⟨h1, h2⟩ | h3)
      · exact h2
      · intro hc
        rw [hrd] at hc; linarith
  have hdisj : Disjoint A2 A3 := by
    rw [Set.disjoint_left]
    intro w hw2 hw3
    rw [hA2, Set.mem_sdiff, Metric.mem_ball, dist_eq_norm, hrd] at hw2
    rw [hA3, Set.mem_setOf_eq] at hw3
    linarith [hw2.1, hw2.2]
  have hfac1 : ∀ w : ℂ, w ∈ A1 → ‖w - z'‖ₑ ^ (-q) ≤ ENNReal.ofReal (r ^ (-q)) := by
    intro w hw
    rw [hA1, Metric.mem_ball, dist_eq_norm] at hw
    rw [hrd] at hw
    have hwr : r ≤ ‖w - z'‖ := by
      rw [hrd]
      have h := htri z w z'
      rw [← hdd, norm_sub_rev z w] at h
      linarith
    have hpos : 0 < ‖w - z'‖ := lt_of_lt_of_le hrpos hwr
    rw [show ‖w - z'‖ₑ = ENNReal.ofReal ‖w - z'‖ from by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_pos hpos]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hrpos hwr hnegq)
  have hfac2 : ∀ w : ℂ, w ∈ A2 → ‖w - z‖ₑ ^ (-q) ≤ ENNReal.ofReal (r ^ (-q)) := by
    intro w hw
    rw [hA2, Set.mem_sdiff, Metric.mem_ball, dist_eq_norm] at hw
    obtain ⟨_, hw2⟩ := hw
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hw2
    have hpos : 0 < ‖w - z‖ := lt_of_lt_of_le hrpos hw2
    rw [show ‖w - z‖ₑ = ENNReal.ofReal ‖w - z‖ from by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_pos hpos]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hrpos hw2 hnegq)
  have hfac3 : ∀ w : ℂ, w ∈ A3 →
      ‖w - z'‖ₑ ^ (-q) ≤ ENNReal.ofReal (2 ^ q) * ‖w - z‖ₑ ^ (-q) := by
    intro w hw
    rw [hA3, Set.mem_setOf_eq] at hw
    have hwz : 0 < ‖w - z‖ := by linarith [hdpos]
    have hwr : ‖w - z‖ / 2 ≤ ‖w - z'‖ := by
      have h := htri w z' z
      rw [norm_sub_rev z' z, ← hdd] at h
      linarith
    have hpos : 0 < ‖w - z'‖ := lt_of_lt_of_le (by linarith) hwr
    have h3 : (‖w - z‖ / 2) ^ (-q) = 2 ^ q * ‖w - z‖ ^ (-q) := by
      rw [show ‖w - z‖ / 2 = ‖w - z‖ * (1 / 2) by ring,
        Real.mul_rpow hwz.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2) (-q),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (-q),
        show -(-q) = q by ring]
      ring
    have h2 : ‖w - z'‖ ^ (-q) ≤ 2 ^ q * ‖w - z‖ ^ (-q) := by
      have h4 := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < ‖w - z‖ / 2) hwr hnegq
      rwa [h3] at h4
    rw [show ‖w - z'‖ₑ = ENNReal.ofReal ‖w - z'‖ from by simp [enorm_eq_nnnorm],
      show ‖w - z‖ₑ = ENNReal.ofReal ‖w - z‖ from by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_rpow_of_pos hwz]
    calc ENNReal.ofReal (‖w - z'‖ ^ (-q))
        ≤ ENNReal.ofReal (2 ^ q * ‖w - z‖ ^ (-q)) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (‖w - z‖ ^ (-q)) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) q)
  have hpow1 : r ^ (-q) * r ^ (2 - q) = d ^ (2 - 2 * q) * 2 ^ (2 * q - 2) := by
    rw [← Real.rpow_add hrpos (-q) (2 - q), show -q + (2 - q) = 2 - 2 * q by ring]
    rw [hrd, show d / 2 = d * (1 / 2) by ring,
      Real.mul_rpow hdpos.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2) (2 - 2 * q),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (2 - 2 * q),
      show -(2 - 2 * q) = 2 * q - 2 by ring]
  have hid1 : r ^ (-q) * (2 * Real.pi * r ^ (2 - q) / (2 - q)) = c1 * d ^ (2 - 2 * q) := by
    rw [hc1def]
    calc r ^ (-q) * (2 * Real.pi * r ^ (2 - q) / (2 - q))
        = (2 * Real.pi / (2 - q)) * (r ^ (-q) * r ^ (2 - q)) := by ring
      _ = (2 * Real.pi / (2 - q)) * (d ^ (2 - 2 * q) * 2 ^ (2 * q - 2)) := by rw [hpow1]
      _ = 2 * Real.pi * 2 ^ (2 * q - 2) / (2 - q) * d ^ (2 - 2 * q) := by ring
  have hpow2 : r ^ (-q) * (3 * d) ^ (2 - q) = d ^ (2 - 2 * q) * (2 ^ q * 3 ^ (2 - q)) := by
    have hr2 : r ^ (-q) = d ^ (-q) * 2 ^ q := by
      rw [hrd, show d / 2 = d * (1 / 2) by ring,
        Real.mul_rpow hdpos.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2) (-q),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (-q),
        show -(-q) = q by ring]
    have h3d : (3 * d) ^ (2 - q) = 3 ^ (2 - q) * d ^ (2 - q) :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hdpos.le
    have hkey : d ^ (-q) * d ^ (2 - q) = d ^ (2 - 2 * q) := by
      rw [← Real.rpow_add hdpos (-q) (2 - q), show -q + (2 - q) = 2 - 2 * q by ring]
    calc r ^ (-q) * (3 * d) ^ (2 - q)
        = (d ^ (-q) * 2 ^ q) * (3 ^ (2 - q) * d ^ (2 - q)) := by rw [hr2, h3d]
      _ = (2 ^ q * 3 ^ (2 - q)) * (d ^ (-q) * d ^ (2 - q)) := by ring
      _ = (2 ^ q * 3 ^ (2 - q)) * d ^ (2 - 2 * q) := by rw [hkey]
      _ = d ^ (2 - 2 * q) * (2 ^ q * 3 ^ (2 - q)) := by ring
  have hid2 : r ^ (-q) * (2 * Real.pi * (3 * d) ^ (2 - q) / (2 - q)) = c2 * d ^ (2 - 2 * q) := by
    rw [hc2def]
    calc r ^ (-q) * (2 * Real.pi * (3 * d) ^ (2 - q) / (2 - q))
        = (2 * Real.pi / (2 - q)) * (r ^ (-q) * (3 * d) ^ (2 - q)) := by ring
      _ = (2 * Real.pi / (2 - q)) * (d ^ (2 - 2 * q) * (2 ^ q * 3 ^ (2 - q))) := by rw [hpow2]
      _ = 2 ^ q * (2 * Real.pi * 3 ^ (2 - q) / (2 - q)) * d ^ (2 - 2 * q) := by ring
  have hid3 : 2 ^ q * (2 * Real.pi * (2 * d) ^ (2 - 2 * q) / (2 * q - 2)) = c3 * d ^ (2 - 2 * q) := by
    rw [hc3def]
    have h2d : (2 * d) ^ (2 - 2 * q) = 2 ^ (2 - 2 * q) * d ^ (2 - 2 * q) :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hdpos.le
    calc 2 ^ q * (2 * Real.pi * (2 * d) ^ (2 - 2 * q) / (2 * q - 2))
        = (2 * Real.pi / (2 * q - 2)) * (2 ^ q * (2 * d) ^ (2 - 2 * q)) := by ring
      _ = (2 * Real.pi / (2 * q - 2)) * (2 ^ q * (2 ^ (2 - 2 * q) * d ^ (2 - 2 * q))) := by
            rw [h2d]
      _ = 2 ^ q * (2 * Real.pi * 2 ^ (2 - 2 * q) / (2 * q - 2)) * d ^ (2 - 2 * q) := by ring
  have hR1 : (∫⁻ w in A1, F w) ≤ ENNReal.ofReal (c1 * d ^ (2 - 2 * q)) := by
    have hpt : ∀ w : ℂ, w ∈ A1 →
        F w ≤ ENNReal.ofReal (r ^ (-q)) * ‖w - z‖ₑ ^ (-q) := by
      intro w hw
      rw [hFdef]
      calc ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q)
          ≤ ‖w - z‖ₑ ^ (-q) * ENNReal.ofReal (r ^ (-q)) :=
            mul_le_mul_right (hfac1 w hw) _
        _ = ENNReal.ofReal (r ^ (-q)) * ‖w - z‖ₑ ^ (-q) := mul_comm _ _
    calc (∫⁻ w in A1, F w)
        ≤ ∫⁻ w in A1, ENNReal.ofReal (r ^ (-q)) * ‖w - z‖ₑ ^ (-q) :=
          MeasureTheory.setLIntegral_mono (by measurability) hpt
      _ = ENNReal.ofReal (r ^ (-q)) * ∫⁻ w in A1, ‖w - z‖ₑ ^ (-q) :=
          setLIntegral_const_mul_ennreal hA1m _ _ (by measurability)
      _ = ENNReal.ofReal (r ^ (-q)) * ENNReal.ofReal (2 * Real.pi * r ^ (2 - q) / (2 - q)) := by
          rw [hA1, Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_ball z hq1 hq2 hrpos]
      _ = ENNReal.ofReal (c1 * d ^ (2 - 2 * q)) := by
          rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos hrpos (-q))), hid1]
  have hA2sub : A2 ⊆ Metric.ball z' (3 * d) := by
    intro w hw
    rw [hA2, Set.mem_sdiff, Metric.mem_ball, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖w - z'‖ ≤ ‖w - z‖ + ‖z - z'‖ := htri w z z'
    rw [← hdd] at h1
    linarith [hw.1]
  have hR2 : (∫⁻ w in A2, F w) ≤ ENNReal.ofReal (c2 * d ^ (2 - 2 * q)) := by
    have hpt : ∀ w : ℂ, w ∈ A2 →
        F w ≤ ENNReal.ofReal (r ^ (-q)) * ‖w - z'‖ₑ ^ (-q) := by
      intro w hw
      rw [hFdef]
      exact mul_le_mul_left (hfac2 w hw) _
    calc (∫⁻ w in A2, F w)
        ≤ ∫⁻ w in A2, ENNReal.ofReal (r ^ (-q)) * ‖w - z'‖ₑ ^ (-q) :=
          MeasureTheory.setLIntegral_mono (by measurability) hpt
      _ = ENNReal.ofReal (r ^ (-q)) * ∫⁻ w in A2, ‖w - z'‖ₑ ^ (-q) :=
          setLIntegral_const_mul_ennreal hA2m _ _ (by measurability)
      _ ≤ ENNReal.ofReal (r ^ (-q)) *
            ENNReal.ofReal (2 * Real.pi * (3 * d) ^ (2 - q) / (2 - q)) := by
          apply mul_le_mul_of_nonneg_left _ bot_le
          calc (∫⁻ w in A2, ‖w - z'‖ₑ ^ (-q))
              ≤ ∫⁻ w in Metric.ball z' (3 * d), ‖w - z'‖ₑ ^ (-q) :=
                MeasureTheory.lintegral_mono_set hA2sub
            _ = ENNReal.ofReal (2 * Real.pi * (3 * d) ^ (2 - q) / (2 - q)) :=
                Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_ball z' hq1 hq2 (by linarith)
      _ = ENNReal.ofReal (c2 * d ^ (2 - 2 * q)) := by
          rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos hrpos (-q))), hid2]
  have hR3 : (∫⁻ w in A3, F w) ≤ ENNReal.ofReal (c3 * d ^ (2 - 2 * q)) := by
    have hpt : ∀ w : ℂ, w ∈ A3 →
        F w ≤ ENNReal.ofReal (2 ^ q) * ‖w - z‖ₑ ^ (-(2 * q)) := by
      intro w hw
      rw [hFdef]
      have hwz : 0 < ‖w - z‖ := by
        rw [hA3, Set.mem_setOf_eq] at hw
        linarith [hdpos]
      have hne0 : ‖w - z‖ₑ ≠ 0 := by
        rw [show ‖w - z‖ₑ = ENNReal.ofReal ‖w - z‖ from by simp [enorm_eq_nnnorm]]
        exact (ENNReal.ofReal_pos.mpr hwz).ne'
      have hnetop : ‖w - z‖ₑ ≠ ⊤ := by
        rw [show ‖w - z‖ₑ = ENNReal.ofReal ‖w - z‖ from by simp [enorm_eq_nnnorm]]
        exact ENNReal.ofReal_ne_top
      calc ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q)
          ≤ ‖w - z‖ₑ ^ (-q) * (ENNReal.ofReal (2 ^ q) * ‖w - z‖ₑ ^ (-q)) :=
            mul_le_mul_right (hfac3 w hw) _
        _ = ENNReal.ofReal (2 ^ q) * (‖w - z‖ₑ ^ (-q) * ‖w - z‖ₑ ^ (-q)) := by ring
        _ = ENNReal.ofReal (2 ^ q) * ‖w - z‖ₑ ^ (-(2 * q)) := by
            rw [← ENNReal.rpow_add (-q) (-q) hne0 hnetop, show -q + -q = -(2 * q) by ring]
    calc (∫⁻ w in A3, F w)
        ≤ ∫⁻ w in A3, ENNReal.ofReal (2 ^ q) * ‖w - z‖ₑ ^ (-(2 * q)) :=
          MeasureTheory.setLIntegral_mono (by measurability) hpt
      _ = ENNReal.ofReal (2 ^ q) * ∫⁻ w in A3, ‖w - z‖ₑ ^ (-(2 * q)) :=
          setLIntegral_const_mul_ennreal hA3m _ _ (by measurability)
      _ = ENNReal.ofReal (2 ^ q) *
            ENNReal.ofReal (2 * Real.pi * (2 * d) ^ (2 - 2 * q) / (2 * q - 2)) := by
          rw [hA3,
            Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_of_le z hq1 hq2
              (by linarith : (0:ℝ) < 2 * d)]
      _ = ENNReal.ofReal (c3 * d ^ (2 - 2 * q)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) q), hid3]
  have hdecomp : (∫⁻ w : ℂ, F w)
      = (∫⁻ w in A1, F w) + ((∫⁻ w in A2, F w) + (∫⁻ w in A3, F w)) := by
    rw [← MeasureTheory.lintegral_add_compl F hA1m]
    rw [hcompl, MeasureTheory.lintegral_union hA3m hdisj]
  have hsum : ENNReal.ofReal (c1 * d ^ (2 - 2 * q))
        + (ENNReal.ofReal (c2 * d ^ (2 - 2 * q)) + ENNReal.ofReal (c3 * d ^ (2 - 2 * q)))
      = ENNReal.ofReal ((c1 + c2 + c3) * d ^ (2 - 2 * q)) := by
    have hs : 0 ≤ d ^ (2 - 2 * q) := Real.rpow_nonneg hdpos.le _
    have hA : 0 ≤ c2 * d ^ (2 - 2 * q) := mul_nonneg hc2nn hs
    have hB : 0 ≤ c3 * d ^ (2 - 2 * q) := mul_nonneg hc3nn hs
    have hC : 0 ≤ c1 * d ^ (2 - 2 * q) := mul_nonneg hc1nn hs
    have e1 : ENNReal.ofReal (c2 * d ^ (2 - 2 * q)) + ENNReal.ofReal (c3 * d ^ (2 - 2 * q))
        = ENNReal.ofReal ((c2 + c3) * d ^ (2 - 2 * q)) := by
      rw [← ENNReal.ofReal_add hA hB]
      congr 1
      ring
    have e2 : ENNReal.ofReal (c1 * d ^ (2 - 2 * q)) + ENNReal.ofReal ((c2 + c3) * d ^ (2 - 2 * q))
        = ENNReal.ofReal ((c1 + (c2 + c3)) * d ^ (2 - 2 * q)) := by
      rw [← ENNReal.ofReal_add hC (mul_nonneg (add_nonneg hc2nn hc3nn) hs)]
      congr 1
      ring
    rw [e1, e2]
    congr 1
    ring
  calc (∫⁻ w : ℂ, F w)
      = (∫⁻ w in A1, F w) + ((∫⁻ w in A2, F w) + (∫⁻ w in A3, F w)) := hdecomp
    _ ≤ ENNReal.ofReal (c1 * d ^ (2 - 2 * q))
          + (ENNReal.ofReal (c2 * d ^ (2 - 2 * q)) + ENNReal.ofReal (c3 * d ^ (2 - 2 * q))) :=
        add_le_add hR1 (add_le_add hR2 hR3)
    _ = ENNReal.ofReal ((c1 + c2 + c3) * d ^ (2 - 2 * q)) := hsum

/-- A map whose increments are bounded by `C * ‖z - z'‖ ^ σ` with `σ > 0` is continuous. -/
theorem continuous_of_norm_sub_le_rpow {F : ℂ → ℂ} {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (h : ∀ z z' : ℂ, ‖F z - F z'‖ ≤ C * ‖z - z'‖ ^ σ) : Continuous F := by
  rw [Metric.continuous_iff]
  intro z0 ε hε
  refine ⟨(ε / (C + 1)) ^ (1 / σ), Real.rpow_pos_of_pos (div_pos hε (by linarith)) _, ?_⟩
  intro z' hz'
  rw [dist_eq_norm] at hz' ⊢
  have h2 : ‖z' - z0‖ ^ σ < ε / (C + 1) := by
    have h3 := Real.rpow_lt_rpow (norm_nonneg _) hz' hσ
    have h4 : ((ε / (C + 1)) ^ (1 / σ)) ^ σ = ε / (C + 1) := by
      rw [← Real.rpow_mul (le_of_lt (div_pos hε (by linarith))), one_div_mul_cancel hσ.ne',
        Real.rpow_one]
    rwa [h4] at h3
  calc ‖F z' - F z0‖ ≤ C * ‖z' - z0‖ ^ σ := h z' z0
    _ ≤ (C + 1) * ‖z' - z0‖ ^ σ :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left h2 (by linarith)
    _ = ε := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)]

/-- **Continuity of the Cauchy transform of a compactly supported `L^p` function, `p > 2`.**

The Cauchy transform of `ν` is `C ν (z) = -(1/π) ∫ w, ν w / (w - z)`; the integral converges
absolutely because `ν ∈ L^p` with `p > 2` and `ν` has compact support (so the kernel
`1/|w - z|` may be localised, where it lies in `L^q` for `q < 2`).  Writing `t` for a finite
exponent with `2 < t ≤ p` and `∫⁻ ‖ν‖ₑ ^ t < ⊤`, and `q = t/(t-1) ∈ (1,2)`, the Hölder estimate
`‖C ν z - C ν z'‖ ≤ K ‖ν‖_t ‖z - z'‖ ^ (1 - 2/t)` holds, the kernel bound
`∫⁻ w, ‖w - z‖ₑ ^ (-q) ‖w - z'‖ₑ ^ (-q) ≤ K ‖z - z'‖ ^ (2 - 2q)` supplying the exponent
`(2 - 2q)/q + 1 = 1 - 2/t > 0`. -/
theorem continuous_cauchyTransform_of_memLp {ν : ℂ → ℂ} {p : ENNReal} (hp : 2 < p)
    (hν : MeasureTheory.MemLp ν p (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport ν) : Continuous (Work.MRMT.cauchyTransform ν) := by
  -- a finite exponent `t > 2` with `∫⁻ ‖ν‖ₑ ^ t < ⊤`
  obtain ⟨s, hs2, _hsp, hsfin, hsinteg⟩ :=
    Work.MRMT.Cauchy.exists_lintegral_enorm_rpow_lt_top_of_memLp hp hν hs
  have hsne : s ≠ ⊤ := hsfin.ne
  have ht2 : 2 < s.toReal :=
    (ENNReal.toReal_lt_toReal (ENNReal.ofNat_ne_top (n := 2)) hsne).mpr hs2
  -- the conjugate exponent `q = t/(t-1)` lies in `(1,2)`
  have hq1 : 1 < s.toReal / (s.toReal - 1) :=
    (one_lt_div (by linarith : (0 : ℝ) < s.toReal - 1)).mpr (by linarith)
  have hq2 : s.toReal / (s.toReal - 1) < 2 :=
    (div_lt_iff₀ (by linarith : (0 : ℝ) < s.toReal - 1)).mpr (by linarith)
  -- the two analytic inputs
  obtain ⟨K, hK0, hK⟩ := two_point_kernel_bound hq1 hq2
  obtain ⟨C, hC0, hC⟩ := Work.MRMT.Cauchy.holder_bound_cauchyIntegral (K := K) ht2 hK0
    hν.aestronglyMeasurable hsinteg hs hK
  -- a Hölder estimate is a continuity statement
  have hσ : 0 < (s.toReal - 2) / s.toReal := div_pos (by linarith) (by linarith)
  have hcont : Continuous (fun z : ℂ => ∫ w : ℂ, ν w / (w - z)) :=
    continuous_of_norm_sub_le_rpow hσ hC0 hC
  have hEq : Work.MRMT.cauchyTransform ν
      = fun z : ℂ => Work.MRMT.cauchyConst * ∫ w : ℂ, ν w / (w - z) := rfl
  rw [hEq]
  exact Continuous.const_mul hcont Work.MRMT.cauchyConst

end Work.MRMT.Found
