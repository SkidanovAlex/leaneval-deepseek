import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.mom2Summable
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sharpRowSummable` — summability of the sharp (cut-off) lattice kinetic row

The target is the finiteness of the lattice row

`Σ_n ℓ⁻³·[‖k_n‖ − λ]₊²·‖kinFT g(k_n)‖²`,  `k_n = kmomInt ℓ n = ℓ⁻¹•(2π n)`,  `λ ≥ 0`,

for `g` smooth, compactly supported in the inscribed ball `B(0,ℓ/2)` of the box `Λ(ℓ)`.

There is no spectral subtlety: since `λ ≥ 0` one has the pointwise domination
`[r − λ]₊² ≤ r²` (`r = ‖k_n‖ ≥ 0`), so the sharp row is dominated *termwise* by the second lattice
moment `Σ_n ℓ⁻³‖k_n‖²‖kinFT g(k_n)‖²`, whose summability is exactly the already-established
`Work.BoseBoxFock.summable_lattice_kinFT_weight` (weight exponent `2`, from polynomial decay of
`kinFT g` for smooth compactly supported `g`).  No frame/Poisson identity and no support
hypothesis beyond compactness is needed.
-/

namespace Work.BoseBoxFock

/-- The pointwise comparison of the FS cut-off symbol with the free square: for `λ ≥ 0` and
`r ≥ 0` one has `[r − λ]₊² ≤ r²`.  (Both `r − λ ≤ r` and `0 ≤ r`, and the square is monotone on
`[0,∞)`.) -/
lemma sharpRow_fsKinCoeff_le_sq {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff lam r ≤ r ^ 2 :=
  pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) hr) 2

theorem sharpRowSummable {ℓ lam : ℝ} (hℓ : 0 < ℓ) (hlam : 0 ≤ lam)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    Summable (fun n : Fin 3 → ℤ =>
        (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖Work.BoseBoxFock.kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_lattice_kinFT_weight hℓ hg hgc 2)
  · -- nonnegativity of the sharp summand
    have h1 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ Submission.BoseGases.fsKinCoeff lam ‖Work.BoseBoxFock.kmomInt ℓ n‖ :=
      sq_nonneg _
    have h3 : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 :=
      sq_nonneg _
    exact mul_nonneg (mul_nonneg h1 h2) h3
  · -- termwise domination by the second lattice moment
    have hfs : Submission.BoseGases.fsKinCoeff lam ‖Work.BoseBoxFock.kmomInt ℓ n‖
        ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 :=
      sharpRow_fsKinCoeff_le_sq hlam (norm_nonneg _)
    have hc : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hnorm : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 :=
      sq_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfs hc) hnorm

end Work.BoseBoxFock
