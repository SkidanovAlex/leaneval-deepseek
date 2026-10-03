import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert

/-- Elementary real arithmetic behind `cone_subset_Qm`: if `y` is large compared with
`p, q, r` and `|x| ≤ |y|/2`, then `-|y - q| < x - p` and `x + r < |y|`. -/
private lemma cone_arith {x y p q r : ℝ} (hy : 2 * (|p| + |q| + |r|) + 4 ≤ |y|)
    (hx : |x| ≤ |y| / 2) : -|y - q| < x - p ∧ x + r < |y| := by
  have hk : |p| + |q| < |y| / 2 := by have := abs_nonneg r; linarith
  have hy3 : |y| / 2 + (|p| + |q| + |r|) ≤ |y| - 2 := by linarith
  constructor
  · have h1 : |y| - |q| ≤ |y - q| := abs_sub_abs_le_abs_sub y q
    have h2 : -|y| / 2 ≤ x := by have h := neg_abs_le x; linarith
    have h3 : -|p| ≤ -p := by have h := le_abs_self p; linarith
    linarith
  · have h1 : x ≤ |y| / 2 := le_trans (le_abs_self x) hx
    have h2 : r ≤ |r| := le_abs_self r
    have h4 : |r| ≤ |p| + |q| + |r| := by
      have := abs_nonneg p; have := abs_nonneg q; linarith
    linarith

/-- The deep cone `|Re z| ≤ |Im z|/2` above a large height lies in the gate
`Qm ξ₁ α = MandelDim.Qreg (some (ξ₁ - 1/α)) (some (-ξ₁))`.  Elementary arithmetic: for such `z`,
`(z - b₁).re + |(z - b₁).im| > 0` and `|(z - b₂).im| - (z - b₂).re > 0` with `b₁ = ξ₁ - 1/α`,
`b₂ = -ξ₁`, once `|Im z|` is large compared with `ξ₁`, `Re (1/α)`, `Im (1/α)`. -/
theorem cone_subset_Qm {ξ₁ : ℝ} {α : ℂ} :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T ≤ |z.im| → |z.re| ≤ |z.im| / 2 → z ∈ Qm ξ₁ α := by
  refine ⟨2 * (|(((ξ₁ : ℂ) - 1 / α)).re| + |(((ξ₁ : ℂ) - 1 / α)).im| + |ξ₁|) + 4, ?_, ?_⟩
  · have h1 := abs_nonneg (((ξ₁ : ℂ) - 1 / α)).re
    have h2 := abs_nonneg (((ξ₁ : ℂ) - 1 / α)).im
    have h3 := abs_nonneg ξ₁
    linarith
  · intro z hz hx
    rw [Qm, MandelDim.Qreg]
    simp only [Set.mem_ofPred_eq, Option.mem_some_iff, forall_eq']
    have hca := cone_arith (x := z.re) (y := z.im) (p := ((ξ₁ : ℂ) - 1 / α).re)
      (q := ((ξ₁ : ℂ) - 1 / α).im) (r := ξ₁) hz hx
    refine ⟨?_, ?_⟩
    · simpa only [Complex.sub_re, Complex.sub_im] using hca.1
    · have h5 : (z - (-(ξ₁ : ℂ))).re = z.re + ξ₁ := by
        rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
      have h6 : (z - (-(ξ₁ : ℂ))).im = z.im := by
        rw [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; simp
      rw [h5, h6]
      linarith [hca.2]

end Work.Pert
