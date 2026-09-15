import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Commons.Analysis.Calculus.contDiff_of_contDiffOn_compl_zero

/-!
# A smooth function equal to `t ↦ (t ^ 2)⁻¹` on a compact interval `[a, b]` with `0 < a`

We build a `C^∞` (in particular `C^2`) function `K : ℝ → ℝ` which agrees with
`t ↦ (t ^ 2)⁻¹` on any interval `[a, b]` with `0 < a ≤ b`.

The construction multiplies `t ↦ (t ^ 2)⁻¹` by a smooth bump function `φ` centred at
`(a + b) / 2`, equal to `1` on `[a, b]` and supported away from the origin (inside the ball of
radius `b / 2` around `(a + b) / 2`, which lies in `(a / 2, ∞)`).  Since `φ` vanishes near `0`,
the product is the zero function near `0` and the product of two smooth functions elsewhere;
smoothness is deduced from Mathlib's `ContDiffOn` calculus via the auxiliary lemma
`Commons.Analysis.Calculus.contDiff_of_contDiffOn_compl_zero`.
-/

namespace Commons.Analysis.Calculus

open Set Metric Filter
open scoped ContDiff Topology

theorem exists_contDiff_eq_inv_sq_on_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ → ℝ, ContDiff ℝ 2 K ∧ ∀ t ∈ Set.Icc a b, K t = (t ^ 2)⁻¹ := by
  have hrIn_pos : 0 < (2 * b - a) / 4 := by linarith
  have hrIn_lt_rOut : (2 * b - a) / 4 < b / 2 := by linarith
  let φ : ContDiffBump ((a + b) / 2 : ℝ) := ⟨(2 * b - a) / 4, b / 2, hrIn_pos, hrIn_lt_rOut⟩
  have hφrOut : φ.rOut = b / 2 := rfl
  have hφrIn : φ.rIn = (2 * b - a) / 4 := rfl
  refine ⟨fun t => (t ^ 2)⁻¹ * φ t, ?_, ?_⟩
  · apply contDiff_of_contDiffOn_compl_zero (n := (2 : ℕ∞ω))
    · have hφc : ContDiff ℝ (2 : ℕ∞ω) (fun t : ℝ => φ t) := by
        simpa using (φ.contDiff (n := (2 : ℕ∞)))
      have hφ : ContDiffOn ℝ (2 : ℕ∞ω) (fun t : ℝ => φ t) {x : ℝ | x ≠ 0} := hφc.contDiffOn
      have hpow : ContDiffOn ℝ (2 : ℕ∞ω) (fun t : ℝ => t ^ 2) {x : ℝ | x ≠ 0} := by
        have h : ContDiff ℝ (2 : ℕ∞ω) (id : ℝ → ℝ) := contDiff_id
        simpa using (h.pow 2).contDiffOn
      have hsq : ContDiffOn ℝ (2 : ℕ∞ω) (fun t : ℝ => (t ^ 2)⁻¹) {x : ℝ | x ≠ 0} :=
        hpow.inv (fun x hx => pow_ne_zero 2 hx)
      exact hsq.mul hφ
    · have hmem : Set.Iio (a / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by linarith)
      refine Filter.eventually_of_mem hmem ?_
      intro t ht
      have ht' : t < a / 2 := ht
      have hφ0 : φ t = 0 := by
        apply ContDiffBump.zero_of_le_dist
        rw [Real.dist_eq]
        have hneg : t - (a + b) / 2 < 0 := by linarith
        rw [abs_of_neg hneg]
        rw [hφrOut]
        linarith
      show (t ^ 2)⁻¹ * φ t = (0 : ℝ)
      rw [hφ0, mul_zero]
  · intro t ht
    have hφ1 : φ t = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, hφrIn, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    show (t ^ 2)⁻¹ * φ t = (t ^ 2)⁻¹
    rw [hφ1, mul_one]

end Commons.Analysis.Calculus