import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.KernelFibreBound
import Submission.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.AprioriCount.wScaledChiScaleIntegral`

The **window/fibre domination** used by the `AprioriCount` chapter: for an integrable numerator
`g` supported in `ball 0 R`, in the dilute regime `R ≤ ℓ·r₀` (where `(χ⋆χ) ≥ 1/2` on `ball 0 r₀`),

    |∫_y wScaled ℓ g (a − y) · χ_ℓ(y)| ≤ 2·chiSup·∫|g|          (`chiSup = (∫χ_base²)^{-1/2}`).

Proof: pointwise, `|wScaled ℓ g z| = |kRat g ℓ z| ≤ 2|g z|` (`Submission.BoseGases.abs_kRat_le`;
whenever `g z ≠ 0` one has `‖z‖ < R ≤ ℓ r₀`, so the denominator `(χ⋆χ)_ℓ(z) ≥ 1/2`), and
`|χ_ℓ(y)| ≤ chiSup` (`Submission.BoseGases.abs_chiScale_le_chiSup`).  Integrating the resulting
domination `2·chiSup·|g(a−y)|` and using translation invariance of Lebesgue measure gives the
claim.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.AprioriCount

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem wScaledChiScaleIntegral {g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ R r₀ : ℝ}
    (hℓ : 0 < ℓ) (hi : MeasureTheory.Integrable g)
    (hgsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → g z = 0)
    (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z)
    (a : EuclideanSpace ℝ (Fin 3)) :
    |∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y|
      ≤ 2 * Submission.BoseGases.chiSup * (∫ z : EuclideanSpace ℝ (Fin 3), |g z|) := by
  classical
  -- Pointwise domination of the integrand by `2·chiSup·|g (a − y)|`.
  have hpt : ∀ y : E3,
      ‖Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y‖
        ≤ 2 * Submission.BoseGases.chiSup * |g (a - y)| := by
    intro y
    have h1 : |Submission.BoseGases.wScaled ℓ g (a - y)| ≤ 2 * |g (a - y)| := by
      have hk := Submission.BoseGases.abs_kRat_le (h := g) (ℓ := ℓ) (R := R) (r₀ := r₀)
        hℓ hgsupp hRℓ hC (a - y)
      simpa [Submission.BoseGases.wScaled, Submission.BoseGases.kRat] using hk
    have h2 : |Submission.BoseGases.chiScale ℓ y| ≤ Submission.BoseGases.chiSup :=
      Submission.BoseGases.abs_chiScale_le_chiSup ℓ y
    rw [Real.norm_eq_abs, abs_mul]
    calc |Submission.BoseGases.wScaled ℓ g (a - y)| * |Submission.BoseGases.chiScale ℓ y|
        ≤ (2 * |g (a - y)|) * Submission.BoseGases.chiSup :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = 2 * Submission.BoseGases.chiSup * |g (a - y)| := by ring
  -- Integrability of the dominating function.
  have hgi : MeasureTheory.Integrable (fun y : E3 => g (a - y)) :=
    Submission.BoseGases.km_integrable_comp_sub_left hi a
  have hdom : MeasureTheory.Integrable
      (fun y : E3 => 2 * Submission.BoseGases.chiSup * |g (a - y)|) :=
    hgi.abs.const_mul _
  calc
    |∫ y : E3, Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y|
        = ‖∫ y : E3,
            Submission.BoseGases.wScaled ℓ g (a - y) * Submission.BoseGases.chiScale ℓ y‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ y : E3, 2 * Submission.BoseGases.chiSup * |g (a - y)| :=
          MeasureTheory.norm_integral_le_of_norm_le hdom (ae_of_all _ hpt)
    _ = 2 * Submission.BoseGases.chiSup * ∫ y : E3, |g (a - y)| := by
          rw [MeasureTheory.integral_const_mul]
    _ = 2 * Submission.BoseGases.chiSup * ∫ z : E3, |g z| := by
          congr 1
          exact Submission.BoseGases.integral_comp_sub_left (fun z : E3 => |g z|) a

end Work.AprioriCount
