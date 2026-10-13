import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.RadialWAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Real

namespace Work.FTS.PhiStar.FlatWAux.Kernels

/-- Comparison of a set integral over `Ioi 1` of a function dominated by an integrable one. -/
private lemma abs_integral_Ioi_le {F G : ℝ → ℝ} (hG : IntegrableOn G (Set.Ioi 1))
    (h : ∀ u ∈ Set.Ioi 1, |F u| ≤ G u) :
    |∫ u in Set.Ioi 1, F u| ≤ ∫ u in Set.Ioi 1, G u := by
  refine (abs_integral_le_integral_abs (f := F)).trans ?_
  exact setIntegral_mono_of_nonneg (fun u _ => abs_nonneg _) h hG

/-- `∫_1^∞ u^a du = 1/(-(a+1))` for `a < -1`. -/
private lemma integral_Ioi_rpow (a : ℝ) (ha : a < -1) :
    ∫ u in Set.Ioi 1, u ^ a = 1 / (-(a + 1)) := by
  rw [integral_Ioi_rpow_of_lt (a := a) ha (c := 1) (by norm_num)]
  rw [Real.one_rpow, div_eq_mul_inv, div_eq_mul_inv, inv_neg]
  ring

/-- `u ↦ c u^a` is integrable on `(1,∞)` for `a < -1`. -/
private lemma integrableOn_Ioi_const_mul_rpow (c a : ℝ) (ha : a < -1) :
    IntegrableOn (fun u : ℝ => c * u ^ a) (Set.Ioi 1) := by
  have h : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (t := 1) (by norm_num)).mpr ha
  exact h.const_mul c

theorem psiKernelWeightedLe {P B : ℝ} (hP : 9 ≤ P) (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ 10 → ∀ t : ℝ, 0 < t → |iteratedDeriv j h t| ≤ B / (1 + t ^ (j + 2))) :
    ∀ j : ℕ, j ≤ 10 → (j : ℝ) < P → ∀ z : ℝ, 0 < z →
      (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) := by
  intro j hj hjP z hz
  have _ := hh
  have hqpos : 0 < P - (j : ℝ) := by linarith
  have hElt : (j : ℝ) - P - 1 < -1 := by linarith
  have hP3lt : -P - 3 < -1 := by linarith
  have hP2pos : 0 < P + 2 := by linarith
  -- ### pointwise bound, first (crude) form
  have key1 : ∀ u ∈ Set.Ioi 1,
      |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)| ≤ B * u ^ ((j : ℝ) - P - 1) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hzu : (0 : ℝ) < z * u := mul_pos hz hu0
    have h1 : |iteratedDeriv j h (z * u)| ≤ B / (1 + (z * u) ^ (j + 2)) := hb j hj (z * u) hzu
    have h2 : B / (1 + (z * u) ^ (j + 2)) ≤ B := by
      rw [div_le_iff₀ (by positivity)]
      refine le_mul_of_one_le_right hB ?_
      have hnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := pow_nonneg hzu.le _
      linarith
    calc |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        = |iteratedDeriv j h (z * u)| * u ^ ((j : ℝ) - P - 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      _ ≤ B * u ^ ((j : ℝ) - P - 1) :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (Real.rpow_nonneg hu0.le _)
  -- ### pointwise bound, sharp form with the `j+2` decay
  have key2 : ∀ u ∈ Set.Ioi 1,
      |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hzu : (0 : ℝ) < z * u := mul_pos hz hu0
    have h1 : |iteratedDeriv j h (z * u)| ≤ B / (1 + (z * u) ^ (j + 2)) := hb j hj (z * u) hzu
    have hpow : (z * u) ^ (j + 2) = (z * u) ^ ((j : ℝ) + 2) := by
      have hc : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
      rw [← Real.rpow_natCast (z * u) (j + 2), hc]
    have hp : (0 : ℝ) < (z * u) ^ (j + 2) := pow_pos hzu _
    have h2 : B / (1 + (z * u) ^ (j + 2)) ≤ B / ((z * u) ^ (j + 2)) := by
      refine div_le_div_of_nonneg_left hB hp ?_
      have hnn : (0 : ℝ) ≤ (z * u) ^ (j + 2) := hp.le
      linarith
    have h3 : B / ((z * u) ^ (j + 2)) = B * (z * u) ^ (-((j : ℝ) + 2)) := by
      rw [hpow, div_eq_mul_inv, ← Real.rpow_neg hzu.le]
    have h4 : B * (z * u) ^ (-((j : ℝ) + 2))
        = B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2)) := by
      rw [Real.mul_rpow hz.le hu0.le]; ring
    have h5 : |iteratedDeriv j h (z * u)| ≤ B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2)) :=
      h1.trans (h2.trans (le_of_eq (h3.trans h4)))
    calc |iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        = |iteratedDeriv j h (z * u)| * u ^ ((j : ℝ) - P - 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      _ ≤ (B * z ^ (-((j : ℝ) + 2)) * u ^ (-((j : ℝ) + 2))) * u ^ ((j : ℝ) - P - 1) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hu0.le _)
      _ = B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3) := by
          have hcomb : u ^ (-((j : ℝ) + 2)) * u ^ ((j : ℝ) - P - 1) = u ^ (-P - 3) := by
            rw [← Real.rpow_add hu0]
            congr 1
            ring
          rw [mul_assoc, hcomb]
  -- ### the two integral values
  have hInt1 : ∫ u in Set.Ioi 1, u ^ ((j : ℝ) - P - 1) = 1 / (P - (j : ℝ)) := by
    rw [integral_Ioi_rpow ((j : ℝ) - P - 1) hElt]
    rw [show -(((j : ℝ) - P - 1) + 1) = P - (j : ℝ) by ring]
  have hInt2 : ∫ u in Set.Ioi 1, u ^ (-P - 3) = 1 / (P + 2) := by
    rw [integral_Ioi_rpow (-P - 3) hP3lt]
    rw [show -(-P - 3 + 1) = P + 2 by ring]
  -- ### integrability of the dominants
  have hintG1 : IntegrableOn (fun u : ℝ => B * u ^ ((j : ℝ) - P - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_const_mul_rpow B ((j : ℝ) - P - 1) hElt
  have hintG2 : IntegrableOn (fun u : ℝ => B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3))
      (Set.Ioi 1) :=
    integrableOn_Ioi_const_mul_rpow (B * z ^ (-((j : ℝ) + 2))) (-P - 3) hP3lt
  rcases lt_or_ge z 1 with hz1 | hz1
  · -- ### case `z < 1`
    have hA : |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * (1 / (P - (j : ℝ))) := by
      have hmain := abs_integral_Ioi_le
        (F := fun u => iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))
        (G := fun u => B * u ^ ((j : ℝ) - P - 1)) hintG1 key1
      have hG : ∫ u in Set.Ioi 1, B * u ^ ((j : ℝ) - P - 1) = B * (1 / (P - (j : ℝ))) := by
        rw [MeasureTheory.integral_const_mul, hInt1]
      rwa [hG] at hmain
    have hW : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (j + 1)
    have hstep1 : (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ)))) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have hstep2 : (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ))))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ))) := by
      calc (z + 1) ^ (j + 1) * (B * (1 / (P - (j : ℝ))))
          = ((z + 1) ^ (j + 1) * B) * (1 / (P - (j : ℝ))) := by ring
        _ ≤ ((2 : ℝ) ^ (j + 1) * B) * (1 / (P - (j : ℝ))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW hB) (by positivity)
        _ = (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ))) := by ring
    have hstep3 : (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (mul_nonneg (pow_nonneg (by norm_num) _) hB)
    linarith
  · -- ### case `1 ≤ z`
    have hA : |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)) := by
      have hmain := abs_integral_Ioi_le
        (F := fun u => iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1))
        (G := fun u => B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3)) hintG2 key2
      have hG : ∫ u in Set.Ioi 1, B * z ^ (-((j : ℝ) + 2)) * u ^ (-P - 3)
          = B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)) := by
        rw [MeasureTheory.integral_const_mul, hInt2]
      rwa [hG] at hmain
    have hW : (z + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * z ^ (j + 1) := by
      have h1 : (z + 1) ^ (j + 1) ≤ (2 * z) ^ (j + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (j + 1)
      rwa [mul_pow] at h1
    have hzpow : z ^ (j + 1) * z ^ (-((j : ℝ) + 2)) = z ^ (-1 : ℝ) := by
      have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [← Real.rpow_natCast z (j + 1), hc, ← Real.rpow_add hz]
      congr 1
      ring
    have hzle : z ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hz1
    have hnonneg : 0 ≤ B * (1 / (P + 2)) := mul_nonneg hB (by positivity)
    have hstep1 : (z + 1) ^ (j + 1) *
          |∫ u in Set.Ioi 1, iteratedDeriv j h (z * u) * u ^ ((j : ℝ) - P - 1)|
        ≤ (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2))) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have hstep2 : (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2)) := by
      calc (z + 1) ^ (j + 1) * (B * z ^ (-((j : ℝ) + 2)) * (1 / (P + 2)))
          = ((z + 1) ^ (j + 1) * z ^ (-((j : ℝ) + 2))) * (B * (1 / (P + 2))) := by ring
        _ ≤ ((2 : ℝ) ^ (j + 1) * z ^ (j + 1) * z ^ (-((j : ℝ) + 2)))
              * (B * (1 / (P + 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            exact mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg hz.le _)
        _ = (2 : ℝ) ^ (j + 1) * (z ^ (j + 1) * z ^ (-((j : ℝ) + 2)))
              * (B * (1 / (P + 2))) := by ring
        _ = (2 : ℝ) ^ (j + 1) * z ^ (-1 : ℝ) * (B * (1 / (P + 2))) := by rw [hzpow]
        _ ≤ (2 : ℝ) ^ (j + 1) * 1 * (B * (1 / (P + 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            exact mul_le_mul_of_nonneg_left hzle (pow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2)) := by ring
    have hstep3 : (2 : ℝ) ^ (j + 1) * B * (1 / (P + 2))
        ≤ (2 : ℝ) ^ (j + 1) * B * (1 / (P - (j : ℝ)) + 1 / (P + 2)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (mul_nonneg (pow_nonneg (by norm_num) _) hB)
    linarith

end Work.FTS.PhiStar.FlatWAux.Kernels
