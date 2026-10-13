import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STHardSlot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-! ## Elementary `rpow` bookkeeping on `sin (2θ)`

The three pointwise bounds of `HardSlotBCRBounds` are all of the shape
`|sin(2θ)^e · (stuff)| ≤ const · sin(2θ)^{2p-q}`, and the exponent algebra needs the two
identities below (valid on the open interval, where `sin (2θ) > 0`).  At the endpoints of
`Iθ` both sides are handled separately, since `Real.rpow_add` requires a positive base. -/

private lemma sq_rpow_nat (s p : ℝ) (hs : 0 ≤ s) : (s ^ p) ^ 2 = s ^ (2 * p) := by
  have h : (s ^ p) ^ (2 : ℝ) = s ^ (2 * p) := by
    rw [← Real.rpow_mul hs p 2]
    congr 1
    ring
  simpa [Real.rpow_natCast] using h

private lemma rpow_shift (s : ℝ) (hs : 0 < s) (q p : ℝ) :
    s ^ (-q - 1) * s * s ^ (2 * p) = s ^ (2 * p - q) := by
  rw [rpow_neg_sub_one_mul q hs, ← Real.rpow_add hs]
  ring_nf

private lemma rpow_shift2 (s : ℝ) (hs : 0 < s) (q p : ℝ) :
    s ^ (-q) * s ^ (2 * p) = s ^ (2 * p - q) := by
  rw [← Real.rpow_add hs]
  ring_nf

theorem HardSlotBCRBounds {q K C p : ℝ} (hq0 : 0 < q) (hp0 : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hf2 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.pth f z θ| ≤ 3 * K)
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    (∀ θ ∈ Work.Spaces.Iθ,
        |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2|
          ≤ q * K * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q)) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
        |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ * (v z θ) ^ 2|
          ≤ (3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q)) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
        |(Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2| ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q)) := by
  -- (1) the `D_θ`-slot: `|f| ≤ K sin(2θ)` supplies one power of `sin(2θ)`,
  --     `|cos(2θ)| ≤ 1` and `|v|² ≤ C² sin(2θ)^{2p}` finish the exponent count.
  have key1 : ∀ θ ∈ Work.Spaces.Iθ,
      |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2|
        ≤ q * K * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    rcases eq_or_lt_of_le hs0 with hs | hs
    · -- endpoint: `sin(2θ) = 0`, the negative power vanishes
      rw [← hs, Real.zero_rpow (x := -q - 1) (by linarith)]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hq0.le hK) (sq_nonneg C))
        (Real.rpow_nonneg le_rfl _)
    · have hsa : 0 ≤ (Real.sin (2 * θ)) ^ (-q - 1) := Real.rpow_nonneg hs0 _
      have hV2 : (v z θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
        rw [← sq_abs (v z θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv1 θ hθ) 2
      have hL : |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          * (v z θ) ^ 2|
          = q * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q - 1) * |f z θ|
              * (v z θ) ^ 2 := by
        simp only [abs_mul, abs_of_pos hq0, abs_of_nonneg hsa,
          abs_of_nonneg (sq_nonneg (v z θ))]
      calc |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2|
          = q * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q - 1) * |f z θ|
              * (v z θ) ^ 2 := hL
        _ ≤ q * 1 * (Real.sin (2 * θ)) ^ (-q - 1) * (K * Real.sin (2 * θ))
              * (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
            gcongr
            · exact Real.abs_cos_le_one (2 * θ)
            · exact hf1 θ hθ
        _ = q * K * C ^ 2 * (Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ)
              * (Real.sin (2 * θ)) ^ (2 * p) := by
            rw [mul_pow, sq_rpow_nat _ _ hs0]; ring
        _ = q * K * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
            rw [show q * K * C ^ 2 * (Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ)
                * (Real.sin (2 * θ)) ^ (2 * p)
              = q * K * C ^ 2 * ((Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ)
                * (Real.sin (2 * θ)) ^ (2 * p)) by ring]
            rw [rpow_shift _ hs q p]
  -- (2) the mixed slot: `|∂_θf| ≤ 3K` and `|v|² ≤ C² sin(2θ)^{2p}`.
  have key2 : ∀ θ ∈ Work.Spaces.Iθ,
      |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ * (v z θ) ^ 2|
        ≤ (3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, Real.zero_rpow (x := -q) (by linarith)]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * K / 2) (sq_nonneg C))
        (Real.rpow_nonneg le_rfl _)
    · have hsa : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hs0 _
      have hV2 : (v z θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
        rw [← sq_abs (v z θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv1 θ hθ) 2
      have hL : |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ
          * (v z θ) ^ 2|
          = (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * |Work.Spaces.pth f z θ|
              * (v z θ) ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hsa,
          abs_of_nonneg (sq_nonneg (v z θ))]
      calc |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ * (v z θ) ^ 2|
          = (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * |Work.Spaces.pth f z θ|
              * (v z θ) ^ 2 := hL
        _ ≤ (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * (3 * K)
              * (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
            gcongr
            exact hf2 θ hθ
        _ = (3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * (Real.sin (2 * θ)) ^ (2 * p) := by
            rw [mul_pow, sq_rpow_nat _ _ hs0]; ring
        _ = (3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
            rw [show (3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (-q)
                * (Real.sin (2 * θ)) ^ (2 * p)
              = (3 * K / 2) * C ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
                * (Real.sin (2 * θ)) ^ (2 * p)) by ring]
            rw [rpow_shift2 _ hs q p]
  -- (3) the `D_z`-slot: no `f` at all, just `|v|² ≤ C² sin(2θ)^{2p}`.
  have key3 : ∀ θ ∈ Work.Spaces.Iθ,
      |(Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2| ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, Real.zero_rpow (x := -q) (by linarith)]
      simp only [mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (sq_nonneg C) (Real.rpow_nonneg le_rfl _)
    · have hsa : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hs0 _
      have hV2 : (v z θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
        rw [← sq_abs (v z θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv1 θ hθ) 2
      have hL : |(Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2|
          = (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2 :=
        abs_of_nonneg (mul_nonneg hsa (sq_nonneg (v z θ)))
      calc |(Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2|
          = (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2 := hL
        _ ≤ (Real.sin (2 * θ)) ^ (-q) * (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
            gcongr
        _ = C ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (2 * p) := by
            rw [mul_pow, sq_rpow_nat _ _ hs0]; ring
        _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
            rw [show C ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (2 * p)
              = C ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (2 * p)) by ring]
            rw [rpow_shift2 _ hs q p]
  exact ⟨key1, key2, key3⟩

end Work.FTS.H2
