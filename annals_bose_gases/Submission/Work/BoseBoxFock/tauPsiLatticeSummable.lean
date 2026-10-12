import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.tauGapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPsiLatticeSummable`

The convexity defect `tauPsi c r = tauRho c r - c²·tauPhi (r/c)` of the smoothed kinetic
weight is dominated by its quadratic tail `tauRho c r = (r - 3c/2)² + c₀c²`, and `tauRho`
itself is `O(1 + r²)`.  Since `kinFT g` decays faster than any power of `‖p‖` for smooth
compactly supported `g` (`SqrtKin.kinFT_decay_gen`, used through
`lattice_heatSubordination.summable_lattice_kinFT_weight`), the `ℓ⁻³`-weighted lattice sum of
`tauPsi c ‖k_n‖·‖kinFT g k_n‖²` is absolutely convergent, with **no support hypothesis** on `g`.

The bound is exactly the sixth conjunct of the delegated `deficit_inputs` (there under the
additional hypothesis `tsupport g ⊆ closedBall 0 (ℓ/2)`, which the decay argument does not
need).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- `tauPsi` lies below its quadratic tail `tauRho` (`c²·tauPhi ≥ 0`). -/
lemma tauPsi_le_tauRho {c r : ℝ} (_hc : 0 < c) : tauPsi c r ≤ tauRho c r := by
  have h : 0 ≤ c ^ 2 * tauPhi (r / c) := mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
  rw [tauPsi, tauRho]
  linarith

/-- **The quantitative upper bound for the convexity defect**: `tauPsi c r ≲ 1 + r²`,
uniformly in `r`.  (Only the quadratic tail matters: `tauPsi ≤ tauRho ≤ 2r² + 9c²/2 + c₀c²`.) -/
lemma tauPsi_le_quad {c : ℝ} (_hc : 0 < c) (r : ℝ) :
    tauPsi c r ≤ (9 / 2 * c ^ 2 + tauC0phi * c ^ 2 + 2) * (1 + r ^ 2) := by
  refine le_trans (tauPsi_le_tauRho _hc) ?_
  have hsq : (r - 3 * c / 2) ^ 2 ≤ 2 * r ^ 2 + 9 * c ^ 2 / 2 := by
    nlinarith [sq_nonneg (r + 3 * c / 2)]
  have hprod : 0 ≤ (9 / 2 * c ^ 2 + tauC0phi * c ^ 2) * r ^ 2 :=
    mul_nonneg (by nlinarith [sq_nonneg c, tauC0phi_nonneg]) (sq_nonneg r)
  have hc0 : 0 ≤ tauC0phi := tauC0phi_nonneg
  rw [tauRho]
  nlinarith [hsq, hprod, hc0]

/-- **Summability of the `tauPsi`-weighted lattice samples of `‖kinFT g‖².**

The weight `tauPsi c ‖k_n‖` is bounded by `K(1 + ‖k_n‖²)` with the fixed constant
`K = 9c²/2 + c₀c² + 2`, so the summand is dominated by `K` times the sum of the two summable
lattice families of weight exponent `0` and `2`, and summability passes down by comparison. -/
theorem tauPsiLatticeSummable {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauPsi c ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  set K : ℝ := 9 / 2 * c ^ 2 + tauC0phi * c ^ 2 + 2 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; nlinarith [sq_nonneg c, tauC0phi_nonneg]
  -- the two summable lattice moment families (weight exponents `0` and `2`)
  have h0 := summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 0
  have h2 := summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 2
  have hmaj : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * (1 + ‖kmomInt ℓ n‖ ^ 2)
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    refine (h0.add h2).congr (fun n => ?_)
    rw [pow_zero]
    ring
  -- comparison: `ℓ⁻³ τ_c(‖k_n‖)‖kinFT‖² ≤ K · ℓ⁻³(1+‖k_n‖²)‖kinFT‖²`
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Summable.mul_left K hmaj)
  · refine mul_nonneg (mul_nonneg ?_ (tauPsi_nonneg hc)) (sq_nonneg _)
    exact inv_nonneg.mpr (pow_nonneg hℓ.le 3)
  · have hpsi : tauPsi c ‖kmomInt ℓ n‖ ≤ K * (1 + ‖kmomInt ℓ n‖ ^ 2) := by
      rw [hK]; exact tauPsi_le_quad hc _
    have hF : 0 ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    have hinv : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hℓ.le 3)
    calc (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * (K * (1 + ‖kmomInt ℓ n‖ ^ 2))
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi hinv) hF
      _ = K * ((ℓ ^ 3)⁻¹ * (1 + ‖kmomInt ℓ n‖ ^ 2)
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by ring

end Work.BoseBoxFock
