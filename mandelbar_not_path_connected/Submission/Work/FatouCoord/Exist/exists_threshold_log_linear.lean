import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Exist

/-- Elementary fact: a linear function eventually dominates a nonnegative multiple of the
logarithm.  Concretely, for any `a ≥ 0` and any real constants `d`, `B`, there is a
threshold beyond which `a * log (x + B) + d < x`. -/
lemma exists_threshold_log_linear_aux {a d B : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ x : ℝ, C < x → a * Real.log (x + B) + d < x := by
  let u : ℝ := 2 * a + |B + d| + 2
  have hu1 : 1 ≤ u := by
    simp only [u]
    have h2a : 0 ≤ 2 * a := by linarith
    have h2 : 0 ≤ |B + d| := abs_nonneg _
    linarith
  have hu2 : 2 * a + 1 ≤ u := by
    simp only [u]; have := abs_nonneg (B + d); linarith
  have hu3 : B + d < u := by
    simp only [u]; have h2 : 0 ≤ 2 * a := by linarith
    have := le_abs_self (B + d); linarith
  refine ⟨u ^ 2 - B, ?_⟩
  intro x hx
  have h1 : u ^ 2 < x + B := by linarith
  have hupos : 0 < u := by linarith
  have hxpos : 0 < x + B := by nlinarith [sq_nonneg u]
  set s : ℝ := Real.sqrt (x + B) with hs_def
  have hs2 : s ^ 2 = x + B := Real.sq_sqrt (le_of_lt hxpos)
  have hspos : 0 < s := by
    rw [hs_def]; exact Real.sqrt_pos_of_pos hxpos
  have hs_gt_u : u < s := by
    have h : Real.sqrt (u ^ 2) < Real.sqrt (x + B) := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq (le_of_lt hupos), ← hs_def] at h
  have hbig : B + d < s * (s - 2 * a) := by
    have hsa : 1 < s - 2 * a := by linarith [lt_of_le_of_lt hu2 hs_gt_u]
    have hmul : s * 1 < s * (s - 2 * a) := mul_lt_mul_of_pos_left hsa hspos
    nlinarith [hmul, lt_trans hu3 hs_gt_u]
  have hlog : Real.log (x + B) ≤ 2 * s := by
    have hst : s ^ 2 = x + B := hs2
    have hlogt : Real.log (x + B) = 2 * Real.log s := by
      rw [← hst, Real.log_pow]; norm_num
    rw [hlogt]
    have := Real.log_le_sub_one_of_pos hspos
    linarith
  have hbound : a * Real.log (x + B) ≤ 2 * a * s := by
    have := mul_le_mul_of_nonneg_left hlog ha
    linarith
  have hsx : s ^ 2 - B = x := by linarith [hs2]
  nlinarith [hbound, hbig, hsx]

/-- For a nonnegative coefficient `c`: a linear expression eventually dominates
`(2c+4) log (x+B) + (2cπ + 4K + 100) + M`. -/
theorem exists_threshold_log_linear {B M c K : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ x : ℝ, C < x →
      (2 * c + 4) * Real.log (x + B) + (2 * c * Real.pi + 4 * K + 100) + M < x := by
  have ha : (0 : ℝ) ≤ 2 * c + 4 := by linarith
  simpa only [add_assoc] using exists_threshold_log_linear_aux (a := 2 * c + 4)
    (d := 2 * c * Real.pi + 4 * K + 100 + M) (B := B) ha

end Work.FatouCoord.Exist
