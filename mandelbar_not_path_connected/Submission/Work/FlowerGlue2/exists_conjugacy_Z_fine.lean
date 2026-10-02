import Mathlib
import Submission.Work.FatouCoordFix.Repelling.ZDecay
import Submission.Work.FlowerGlue2.fine_Z_decay_fatou
import Submission.Work.FatouCoord.Repelling.defect_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The repelling conjugacy with the **fine** decay of the correction `Z`

This is `Work.FlowerGlue2.exists_conjugacy_Z_fine`: the conjunction of

* the full repelling-coordinate package of `Work.FatouCoordFix.Repelling.exists_conjugacy_Z`
  (`R > 1/r`, holomorphic `Z` with `‖Z‖ ≤ 1/2` and `Z = Ω Z`, holomorphic `V` with
  `V = w + (1-a) Λ w + Z`, the conjugacy `V (w+1) = wMap f (V w)`, `‖V w - w‖ ≤ ‖w‖/2`,
  `V w ≠ 0`, injectivity of `V` on the left half-plane), and
* the *fine* decay `‖Z w‖ ≤ K (1 + log ‖w‖)/‖w‖` of the correction
  (the sharp order, uniform in the direction; compare `Work.FlowerGlue2.fine_Z_decay_fatou`).

Both halves concern the same `Z` and `V`: the fine decay is a property of the correction alone,
so we may take `Z`, `V` from the construction and restrict everything to the larger half-plane
`{Re w < -R}` on which the fine decay holds.
-/

namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

theorem exists_conjugacy_Z_fine {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ 1 / r < R ∧ ∃ Z V : ℂ → ℂ,
      DifferentiableOn ℂ Z (Work.FatouCoord.Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R →
        Z w = Work.FatouCoord.Petal.Omega f a Z w) ∧
      DifferentiableOn ℂ V (Work.FatouCoord.Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R →
        V w = w + (1 - a) * Work.FatouCoord.Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R →
        V (w + 1) = Work.FatouCoord.wMap f (V w)) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖) ∧
      (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → V w ≠ 0) ∧
      Set.InjOn V (Work.FatouCoord.Petal.LeftHalfPlane R) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R →
        ‖Z w‖ ≤ K * (1 + Real.log ‖w‖) / ‖w‖ := by
  -- The repelling-coordinate package, with the coarse decay of the correction.
  obtain ⟨R₁, hR₁pos, hrR₁, Z, V, hZdiff, hZbd, hZeq, hZfix, hVdiff, hVdef, hVconj, hVnorm,
    hVne, hVinj, -, -, -⟩ := Work.FatouCoordFix.Repelling.exists_conjugacy_Z hb
  -- The defect bound feeding the fine decay.
  obtain ⟨R₂, K₂, hR₂pos, hrR₂, hK₂nn, hK₂⟩ := Work.FatouCoord.Repelling.defect_bound hb
  set R : ℝ := max (max R₁ R₂) 4 with hRdef
  have hR₁le : R₁ ≤ R := by
    rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₂le : R₂ ≤ R := by
    rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h4le : (4 : ℝ) ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hrR : 1 / r < R := lt_of_lt_of_le hrR₁ hR₁le
  have hsub₁ : Work.FatouCoord.Petal.LeftHalfPlane R ⊆
      Work.FatouCoord.Petal.LeftHalfPlane R₁ := by
    intro w hw
    rw [Work.FatouCoord.Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  refine ⟨R, hRpos, hrR, Z, V, hZdiff.mono hsub₁, ?_, ?_, hVdiff.mono hsub₁, ?_, ?_, ?_, ?_,
    hVinj.mono hsub₁, ⟨16 * K₂ + 1, by linarith, ?_⟩⟩
  · intro w hw; exact hZbd w (hsub₁ hw)
  · intro w hw; exact hZfix w (hsub₁ hw)
  · intro w hw; exact hVdef w (hsub₁ hw)
  · intro w hw; exact hVconj w (hsub₁ hw)
  · intro w hw; exact hVnorm w (hsub₁ hw)
  · intro w hw; exact hVne w (hsub₁ hw)
  · -- the fine decay of `Z`
    intro w hw
    have hwre : w.re < -R := hw
    have hw1 : w ∈ Work.FatouCoord.Petal.LeftHalfPlane R₁ := hsub₁ hw
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
