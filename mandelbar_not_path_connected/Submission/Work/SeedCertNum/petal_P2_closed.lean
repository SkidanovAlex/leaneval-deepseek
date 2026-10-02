/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# P2 of the petal model on the **closed** ball

`Work.SeedCertNum.petal_P2` states the backward invariance of the petal for `z` in the *open* ball
`Metric.ball z₁ ρ₁`.  The ray area `SeedCertRay` needs it for `‖z − z₁‖ ≤ ρ₁`: the ray pieces are
covered by boxes that only satisfy `Petal ⊆ closedBall z₁ ρ₁` (via `hRQ`), so the boundary
`‖z − z₁‖ = ρ₁` is not excluded a priori.

On the sphere the hypothesis is *vacuous*: `Work.SeedCertNum.petal_P1` says that the sphere
`‖z − z₁‖ = ρ₁` is mapped by `F` out of the petal, so `F z ∈ petal` is already false there.  Hence
the closed-ball form follows from `petal_P2` plus `petal_P1` by a two-line case split.
-/
import Mathlib
import Submission.Work.SeedCertNum.Petal
import Submission.Work.SeedCertNum.petal_P1
import Submission.Work.SeedCertNum.petal_P2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- **P2 of the petal model, closed-ball form.**  Same hypotheses as `petal_P2`, but the conclusion
holds for every `z` with `‖z − z₁‖ ≤ ρ₁`. -/
theorem petal_P2_closed {F E : ℂ → ℂ} {z₁ A : ℂ} {M ρ₁ ρ₂ δ R : ℝ}
    (hA : A ≠ 0) (hM : 0 ≤ M) (hρ₁ : 0 < ρ₁) (hρρ : ρ₁ < ρ₂) (hδ : 0 < δ)
    (hsmall : (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) < 1)
    (hmodel : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → F (z₁ + u) = z₁ + u + A * u ^ 2 + E u)
    (hE : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → ‖E u‖ ≤ M * ‖u‖ ^ 3)
    (hC1 : M * ρ₁ / ‖A‖ + (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ^ 2
              / (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) ≤ 1 - δ)
    (hC2 : 1 / (‖A‖ * ρ₁) ≤ R) :
    ∀ z : ℂ, ‖z - z₁‖ ≤ ρ₁ → F z ∈ Work.SeedCert.petal z₁ A R →
      z ∈ Work.SeedCert.petal z₁ A R ∧
        (Work.SeedCert.fatouW z₁ A z).re ≤ (Work.SeedCert.fatouW z₁ A (F z)).re - δ := by
  intro z hz hFz
  rcases lt_or_eq_of_le hz with hlt | heq
  · refine petal_P2 hA hM hρ₁ hρρ hδ hsmall hmodel hE hC1 hC2 z ?_ hFz
    rwa [Metric.mem_ball, dist_eq_norm]
  · exfalso
    have h := petal_P1 hA hM hρ₁ hρρ hδ hsmall hmodel hE hC1 hC2 (z - z₁) heq
    rw [show z₁ + (z - z₁) = z from by ring] at h
    exact h hFz

end Work.SeedCertNum
