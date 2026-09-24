import Mathlib
import Submission.Work.GM.S3.prop101_defs

namespace Work.GM.S3

/-- Pointwise domination of the `m₂ > 0` part of `Bsum` by `affineSum`: since `ψ' = 1` on the
support of `RtildeSq` (by `hψ'one` and `hRsupp`) we have `Rtilde x ^ 2 = RtildeSq x ≤ testfun x` for
every `x`, and the index set of `BsumPos` (`idx1 M₁ × idxMpos M × idxM M`) is contained in the index
set of `affineSum 2 M₁ M M` (whose `m₃`-range is the larger `Icc (-⌊2M⌋) ⌊2M⌋`); every summand of
`affineSum` is a value of `testfun` and hence non-negative.  `hB : 0 ≤ (N:ℝ)*B` gives `0 ≤ RtildeSq`
(if `N = 0` then `RtildeSq ≡ 0` because the integrand vanishes; otherwise `0 ≤ B` follows from `hB`),
which is what makes `Rtilde x ^ 2 = RtildeSq x` and the non-negativity of `testfun` available. -/
theorem bsumPos_le_affineSum (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 16) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16)
    (hψ' : Work.GM.S3.IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8))
    (v : ℝ) :
    Work.GM.S3.BsumPos N W B M₁ M ψ₁ ψ₂ v ≤
      Submission.GM.affineSum 2 M₁ M M (Work.GM.S3.testfun N W B ψ₁ ψ₂ ψ') v := by
  -- `0 ≤ RtildeSq` for every point, from `hB = 0 ≤ N * B` (the integrand is a product of
  -- non-negative factors).
  have hRnn : ∀ x, 0 ≤ Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x := fun x =>
    MeasureTheory.integral_nonneg fun u' =>
      mul_nonneg (mul_nonneg (mul_nonneg hB (hψ₁.2.1 _)) (hψ₂.2.1 u')) (sq_nonneg _)
  -- Pointwise: `Rtilde x ^ 2 = testfun x` for every `x` (if `RtildeSq x = 0` both sides vanish,
  -- otherwise `x` lies in `[1/8, 33/8]` where `ψ' = 1`).
  have hpt : ∀ x, Work.GM.S3.Rtilde W N B ψ₁ ψ₂ x ^ 2 =
      Work.GM.S3.testfun N W B ψ₁ ψ₂ ψ' x := by
    intro x
    rw [Work.GM.S3.Rtilde_sq W N B ψ₁ ψ₂ x (hRnn x)]
    simp only [Work.GM.S3.testfun]
    by_cases hx : Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x = 0
    · simp [hx]
    · simp [hψ'one x (hRsupp x hx)]
  -- Every summand of `affineSum` is a value of `testfun`, hence non-negative.
  have htestfun_nn : ∀ x, 0 ≤ Work.GM.S3.testfun N W B ψ₁ ψ₂ ψ' x :=
    fun x => mul_nonneg (hψ'.2.1 x) (hRnn x)
  simp only [Work.GM.S3.BsumPos, Submission.GM.affineSum, Work.GM.S3.idx1,
    Work.GM.S3.idxMpos, Work.GM.S3.idxM, Work.GM.S3.arg2, hpt]
  refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m₃ _ _ => htestfun_nn _)

end Work.GM.S3
