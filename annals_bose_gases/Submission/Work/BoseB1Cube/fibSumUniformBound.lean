import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

/-- **Uniform boundedness of the one-body fibre sum in the sliding parameter `u`.**

For fixed data `v, h, M, ℓ, d` in the diluteness regime `R ≤ ℓ·d/16`, `R ≤ ℓ·chiR0` and any
continuous state `Φ : X n → ℝ`, the quantity

    fibSum h M ℓ d u Φ = ∫_{abox n ℓ} Φ(x)² · Σ_i ∫_{acube ℓ} w_{1,B(u)}(x_i,y) dy

is bounded by a constant independent of the sliding parameter `u`, namely the product of the crude
per-fibre constant `Kav = 16π·chiSupAbs·chiSmallDecay M/smallConvLower M`, the scattering length
`a v` and the linear-count bound `n·(chiSupAbs·chiSmallDecay M)·∫Φ²` of `chiSum_le`.

The proof uses (i) the pointwise nonnegativity of the fibre
(`wSmall1Pair_fibre_nonneg`, so `|fibSum| = fibSum`), (ii) the crude fibre bound `fibSum_le` and
(iii) the linear cutoff count bound `chiSum_le`; both (ii) and (iii) are already uniform in `u`.
The sign of `a v` is `av_bounds_weak`. -/
theorem fibSumUniformBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixB1.fibSum h M ℓ d u Φ| ≤ B := by
  -- `0 ≤ a v` (maximum principle for the scattering solution).
  obtain ⟨ha0, -⟩ := Submission.BoseGases.av_bounds_weak (v := v) (R := R) hR hv hvrad hv_supp h
  -- the two nonnegative constants of the fibre and cutoff estimates
  have hKav0 : 0 ≤ 16 * Real.pi * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M := by
    have h1 : (0 : ℝ) ≤ 16 * Real.pi * Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay M := by
      have := Submission.BoseGases.chiSupAbs_nonneg
      have := Submission.BoseGases.chiSmallDecay_nonneg M
      positivity
    exact div_nonneg h1 (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  refine ⟨(16 * Real.pi * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
        * ((n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg hKav0 ha0) ?_
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hCs0) ?_
    exact integral_nonneg fun x => sq_nonneg _
  · intro u
    -- (1) the crude fibre bound, uniform in `u`
    have hfib := Work.BoseFixB1.fibSum_le (v := v) (h := h) (R0 := R) hv hvrad hR hv_supp
      (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hRd hRχ u hΦ
    -- (2) the linear cutoff count bound, uniform in `u`
    have hchi := Work.BoseFixB1.chiSum_le (M := M) hM (ℓ := ℓ) (d := d) u hΦ
    -- the fibre sum is nonnegative, so its absolute value is itself
    have hnonneg : 0 ≤ Work.BoseFixB1.fibSum h M ℓ d u Φ := by
      rw [Work.BoseFixB1.fibSum]
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ =>
          Work.BoseFixB1.wSmall1Pair_fibre_nonneg (v := v) (R0 := R) hR hv hvrad hv_supp h
            u (x i))
    rw [abs_of_nonneg hnonneg]
    exact le_trans hfib (mul_le_mul_of_nonneg_left hchi (mul_nonneg hKav0 ha0))

end Work.BoseB1Cube
