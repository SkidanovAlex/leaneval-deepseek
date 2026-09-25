import Mathlib
import Submission.Work.BourgainPlan.Maximal.tsum_min_geometric

namespace Work.BourgainPlan.Maximal

/-- The dyadic annulus moment `∑_{m∈ℤ} 2^{-4m} (1 + 2^{-m}|z|)^{-6}` is summable and bounded by a
universal constant times `|z|^{-4}`.  The point is the `min` estimate: the `m`-th term is at most
both `2^{-4m}` (the `(1+·)^{-6}` factor being `≤ 1`) and `2^{2m}|z|^{-6}` (using
`(1+u)^{-6} ≤ u^{-6}`), so the whole sum is bounded by `∑_m min(2^{-4m}, 2^{2m}|z|^{-6})`, which is
the crossing-point sum `tsum_min_geometric` with `A = 4`, `B = 2`, `P = 1`, `Q = |z|^{-6}`. -/
theorem tsum_annulus_moment : ∃ K : ℝ, 0 < K ∧ ∀ z : ℝ, z ≠ 0 →
    Summable (fun m : ℤ => ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ))) ∧
    (∑' m : ℤ, ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ)))
      ≤ K * |z| ^ (-(4:ℝ)) := by
  obtain ⟨C, hCnn, hmain⟩ :=
    tsum_min_geometric 4 2 (by norm_num) (by norm_num)
  refine ⟨C + 1, by linarith, ?_⟩
  intro z hz
  have hr : 0 < |z| := abs_pos.mpr hz
  obtain ⟨hsumG, hGle⟩ := hmain 1 (|z| ^ (-(6:ℝ))) (by norm_num) (Real.rpow_nonneg hr.le _)
  have hFnn : ∀ m : ℤ, 0 ≤ ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ)) := by
    intro m; positivity
  -- termwise domination by the `min` of the two geometric bounds
  have hFG : ∀ m : ℤ,
      ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ))
        ≤ min (1 * (2:ℝ)^(-((4:ℤ))*m)) ((|z|^(-(6:ℝ))) * (2:ℝ)^((2:ℤ)*m)) := by
    intro m
    rw [one_mul]
    refine le_min ?_ ?_
    · -- `(1+u)^{-6} ≤ 1`, hence the term is at most `2^{-4m}`
      calc ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ))
          ≤ ((2:ℝ)^(-m))^4 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
            have : 0 ≤ (2:ℝ)^(-m) * |z| := by positivity
            linarith
        _ = ((2:ℝ)^(-m))^4 := by ring
        _ = (2:ℝ)^(-(4:ℤ)*m) := by
            rw [← zpow_natCast, ← zpow_mul]
            congr 1
            ring
    · -- `(1+u)^{-6} ≤ u^{-6}`, hence the term is at most `2^{2m}|z|^{-6}`
      have hb : 0 < (2:ℝ)^(-m) := zpow_pos (show (0:ℝ) < 2 by norm_num) (-m)
      have hu : 0 < (2:ℝ)^(-m) * |z| := by positivity
      have h2 : (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ)) ≤ ((2:ℝ)^(-m) * |z|)^(-(6:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hu (by linarith) (by norm_num)
      have hmul : ((2:ℝ)^(-m) * |z|)^(-(6:ℝ)) = ((2:ℝ)^(-m))^(-(6:ℝ)) * |z|^(-(6:ℝ)) := by
        rw [Real.mul_rpow (by positivity) hr.le]
      calc ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ))
          ≤ ((2:ℝ)^(-m))^4 * ((2:ℝ)^(-m) * |z|)^(-(6:ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ((2:ℝ)^(-m))^4 * (((2:ℝ)^(-m))^(-(6:ℝ)) * |z|^(-(6:ℝ))) := by rw [hmul]
        _ = (((2:ℝ)^(-m))^4 * ((2:ℝ)^(-m))^(-(6:ℝ))) * |z|^(-(6:ℝ)) := by ring
        _ = ((2:ℝ)^(-m))^(-(2:ℝ)) * |z|^(-(6:ℝ)) := by
            congr 1
            rw [← Real.rpow_natCast ((2:ℝ)^(-m)) 4, ← Real.rpow_add hb]
            norm_num
        _ = (2:ℝ)^((2:ℤ)*m) * |z|^(-(6:ℝ)) := by
            congr 1
            rw [show (-(2:ℝ)) = ((-2:ℤ):ℝ) by norm_num, Real.rpow_intCast, ← zpow_mul]
            congr 1
            ring
        _ = |z|^(-(6:ℝ)) * (2:ℝ)^((2:ℤ)*m) := by ring
  have hFsum : Summable (fun m : ℤ => ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ))) :=
    Summable.of_nonneg_of_le hFnn hFG hsumG
  refine ⟨hFsum, ?_⟩
  have hle1 := Summable.tsum_le_tsum hFG hFsum hsumG
  have hle2 : (∑' m : ℤ,
        min (1 * (2:ℝ)^(-((4:ℤ))*m)) ((|z|^(-(6:ℝ))) * (2:ℝ)^((2:ℤ)*m)))
      ≤ C * |z| ^ (-(4:ℝ)) := by
    refine le_trans hGle ?_
    rw [Real.one_rpow, mul_one]
    rw [← Real.rpow_mul hr.le]
    norm_num
  calc (∑' m : ℤ, ((2:ℝ)^(-m))^4 * (1 + (2:ℝ)^(-m) * |z|)^(-(6:ℝ)))
      ≤ ∑' m : ℤ, min (1 * (2:ℝ)^(-((4:ℤ))*m)) ((|z|^(-(6:ℝ))) * (2:ℝ)^((2:ℤ)*m)) := hle1
    _ ≤ C * |z| ^ (-(4:ℝ)) := hle2
    _ ≤ (C + 1) * |z| ^ (-(4:ℝ)) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.le _)

end Work.BourgainPlan.Maximal
