import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

set_option maxHeartbeats 800000

/-- **The `p`-decay of the windowed pair amplitude.**

Pointwise product bound: the slot-amplitudes `tBamp χ p W j x`, `tBamp χ p V j x`
decay like `(1+‖p‖)^{-3}` on the box (hypotheses `hW`, `hV`), the radial symbol
`F` grows at most like `K(1+‖p‖)²` (`hF`), and the box indicator `indU ℓ 0 (x j)`
has modulus `≤ 1`. Hence the pair term decays like `(1+‖p‖)^{-4}`:
`|indU·F(‖p‖)·Re(ā·b)| ≤ 1 · K(1+‖p‖)² · (CW(1+‖p‖)⁻³)(CV(1+‖p‖)⁻³)
= K·CW·CV·(1+‖p‖)⁻⁴`. -/
theorem tBamp_pair_decay_bound {n : ℕ} {ℓ K CW CV : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {W V : Submission.BoseGases.X n → ℝ} {F : ℝ → ℝ} (j : Fin n)
    (hK : 0 ≤ K) (hCW : 0 ≤ CW) (hCV : 0 ≤ CV)
    (hF : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2)
    (hW : ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ p : EuclideanSpace ℝ (Fin 3),
        ‖Work.SmallBoxTBWord.tBamp χ p W j x‖ ≤ CW / (1 + ‖p‖) ^ 3)
    (hV : ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ p : EuclideanSpace ℝ (Fin 3),
        ‖Work.SmallBoxTBWord.tBamp χ p V j x‖ ≤ CV / (1 + ‖p‖) ^ 3) :
    ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseKinLoc.indU ℓ 0 (x j) *
        (F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
          Work.SmallBoxTBWord.tBamp χ p V j x).re)‖
        ≤ K * CW * CV / (1 + ‖p‖) ^ 4 := by
  intro x hx p
  have hp3 : (0 : ℝ) < (1 + ‖p‖) ^ 3 := by positivity
  have hW' := hW x hx p
  have hV' := hV x hx p
  -- the box indicator has modulus `≤ 1`
  have h1 : ‖Work.BoseKinLoc.indU ℓ 0 (x j)‖ ≤ 1 := by
    rw [Work.BoseKinLoc.indU]
    by_cases h : x j ∈ Work.BoseKinLoc.lamBox ℓ 0
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  -- the pair term `Re(ā b)` decays like `(1+‖p‖)^{-6}`
  have h2 : |(star (Work.SmallBoxTBWord.tBamp χ p W j x) *
        Work.SmallBoxTBWord.tBamp χ p V j x).re| ≤ CW * CV / (1 + ‖p‖) ^ 6 := by
    calc |(star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re|
        ≤ ‖star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x‖ := Complex.abs_re_le_norm _
      _ = ‖Work.SmallBoxTBWord.tBamp χ p W j x‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p V j x‖ := by rw [norm_mul, norm_star]
      _ ≤ (CW / (1 + ‖p‖) ^ 3) * (CV / (1 + ‖p‖) ^ 3) :=
            mul_le_mul hW' hV' (norm_nonneg _) (div_nonneg hCW (le_of_lt hp3))
      _ = CW * CV / (1 + ‖p‖) ^ 6 := by field_simp
  have h3 : |F ‖p‖| ≤ K * (1 + ‖p‖) ^ 2 := hF ‖p‖ (norm_nonneg p)
  have hz : ‖F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
        Work.SmallBoxTBWord.tBamp χ p V j x).re‖
      ≤ K * (1 + ‖p‖) ^ 2 * (CW * CV / (1 + ‖p‖) ^ 6) := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h3 h2 (abs_nonneg _) (mul_nonneg hK (by positivity))
  calc ‖Work.BoseKinLoc.indU ℓ 0 (x j) *
        (F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
          Work.SmallBoxTBWord.tBamp χ p V j x).re)‖
      = ‖Work.BoseKinLoc.indU ℓ 0 (x j)‖ *
        ‖F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
          Work.SmallBoxTBWord.tBamp χ p V j x).re‖ := norm_mul _ _
    _ ≤ 1 * (K * (1 + ‖p‖) ^ 2 * (CW * CV / (1 + ‖p‖) ^ 6)) :=
        mul_le_mul h1 hz (norm_nonneg _) zero_le_one
    _ = K * CW * CV / (1 + ‖p‖) ^ 4 := by field_simp

end Work.BoseFixB2.DvApriori
