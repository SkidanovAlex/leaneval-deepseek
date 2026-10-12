import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lattice_heatSubordination
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.summable_of_quad_growth`

Summability of the lattice kinetic row against a symbol `F` of **quadratic growth**:

    `Σ_n ℓ⁻³ · F(‖k_n‖) · ‖kinFT g (k_n)‖² < ∞`,   `k_n = kmomInt ℓ n = (2π/ℓ) n`,

for `g` smooth with compact support, `F ≥ 0` and `F(r) ≤ A r² + B` for `r ≥ 0`.

The point is that `kinFT g` decays faster than any polynomial
(`SqrtKin.kinFT_decay_gen`, polynomial decay for smooth compactly supported `g`), so the
quadratic growth of `F` is absorbed: the general term is dominated by
`C·(1 + ‖k_n‖)⁻⁶`, which is summable over the lattice by the polynomial-decay summability
`summable_lattice_kinFT_weight` at the weights `j = 0` and `j = 2`.
-/

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **Summability of the lattice kinetic row against a quadratically growing symbol.**

If `g` is smooth with compact support and `F ≥ 0` grows at most quadratically, then the
`ℓ⁻³`-weighted lattice samples of `F(‖k_n‖)·‖kinFT g (k_n)‖²` are summable: the polynomial growth
of `F` is beaten by the super-polynomial decay of the Fourier transform of the `C^∞` compactly
supported `g`. -/
theorem summable_of_quad_growth {ℓ A B : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {F : ℝ → ℝ} (hF0 : ∀ r, 0 ≤ F r)
    (hF : ∀ r, 0 ≤ r → F r ≤ A * r ^ 2 + B) :
    Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * F ‖Work.BoseBoxFock.kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  -- The two polynomial weights `j = 0` and `j = 2` of the lattice kinetic row are summable.
  have h0 := summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 0
  have h2 := summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 2
  -- Hence so is the majorant `ℓ⁻³ (A ‖k_n‖² + B) ‖kinFT g (k_n)‖²`, being the sum of the two
  -- multiples `A·(j = 2)` and `B·(j = 0)`.
  have hbnd : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * (A * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 + B)
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
    have hA : Summable (fun n : Fin 3 → ℤ => A * ((ℓ ^ 3)⁻¹
        * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)) :=
      (h2.mul_left A).congr (fun n => by rfl)
    have hB : Summable (fun n : Fin 3 → ℤ => B * ((ℓ ^ 3)⁻¹
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)) :=
      (h0.mul_left B).congr (fun n => by ring)
    exact (hA.add hB).congr (fun n => by ring)
  -- Compare the target termwise against the majorant, using `F ≥ 0` and the quadratic bound.
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbnd
  · exact mul_nonneg (mul_nonneg (by positivity) (hF0 _)) (sq_nonneg _)
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (hF _ (norm_nonneg _)) (by positivity)

end Work.BoseBoxFock
