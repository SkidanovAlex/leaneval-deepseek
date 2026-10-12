import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotAppPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `aP_abs_le_of_bound`

The centred-box condensate mean

    aP ℓ i Ξ x = (1/ℓ³) ∫_{y ∈ acube ℓ} Ξ (update x i y)

cannot increase the sup-norm: if `|Ξ| ≤ B` on the N-particle centred box
`abox N ℓ`, then `|aP ℓ i Ξ x| ≤ B` for every `x ∈ abox N ℓ`.

This is the measurable (rather than continuous) version of
`Submission.BoseGases.aP_abs_le`: the only integrability input needed is the
a.e. bound, which is fed to `MeasureTheory.norm_integral_le_of_norm_le_const`.

The key point is that `x ∈ abox N ℓ` and `y ∈ acube ℓ` give
`update x i y ∈ abox N ℓ` (`update_mem_abox`), so the integrand is bounded
pointwise on the whole cube; the mean of a function bounded by `B` over a set
of measure `ℓ³` is again bounded by `B`.
-/

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem aP_abs_le_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ξ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΞm : Measurable Ξ)
    (hΞb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ξ x| ≤ B) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ, |Submission.BoseGases.aP ℓ i Ξ x| ≤ B := by
  intro x hx
  have hℓnn : 0 ≤ ℓ := le_of_lt hℓ
  -- Work with the restricted measure `μ = volume ↾ acube ℓ`.
  set μ : Measure ℝ³ := (volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ) with hμ
  have hμfin : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓnn⟩
  -- The integrand is bounded a.e. by `B`: every `update x i y` with `x ∈ abox`,
  -- `y ∈ acube` lies in `abox`.
  have hb : ∀ᵐ y ∂μ, ‖Ξ (Function.update x i y)‖ ≤ B := by
    rw [hμ, ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)]
    exact ae_of_all volume (fun y hy => by
      rw [Real.norm_eq_abs]
      exact hΞb _ (Submission.BoseGases.update_mem_abox i hx hy))
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun y : ℝ³ => Ξ (Function.update x i y)) (C := B) hb
  have hvol : μ.real Set.univ = ℓ ^ 3 := by
    rw [hμ]; exact Submission.BoseGases.real_volume_acube ℓ hℓnn
  rw [hvol] at h
  have hnorm : |∫ y, Ξ (Function.update x i y) ∂μ| ≤ B * ℓ ^ 3 := by
    rw [← Real.norm_eq_abs]; exact h
  -- Unfold the mean and pull out the (nonnegative) prefactor `1/ℓ³`.
  unfold Submission.BoseGases.aP
  rw [← hμ]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3)
        * |∫ y, Ξ (Function.update x i y) ∂volume.restrict (Submission.BoseGases.acube ℓ)|
      ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = B := by field_simp

end Work.BoseFixB3.CS.Pieces
