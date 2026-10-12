import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

theorem slotNormReduction {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχnn : ∀ z, 0 ≤ χ z)
    {F : EuclideanSpace ℝ (Fin 3) → ℂ} {M : ℝ} (hM : ∀ z, χ z * ‖F z‖ ≤ M)
    {Θ Γ : Submission.BoseGases.X n → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hΓm : Measurable Γ) (hΓb : ∀ x, |Γ x| ≤ D) :
    ‖∫ x : Submission.BoseGases.X n,
        (Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖
      ≤ M * (∫ x in Submission.BoseGases.abox n ℓ, |Θ x| * |Γ x|) := by
  -- `M` is non-negative, since `χ ≥ 0`.
  have hMnn : 0 ≤ M := le_trans (mul_nonneg (hχnn 0) (norm_nonneg (F 0))) (hM 0)
  -- `Θ` vanishes off the box.
  have hzero : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → Θ x = 0 := by
    intro x hx
    by_contra h
    exact hx (hΘs (Function.mem_support.mpr h))
  -- The pointwise bound `‖Θ·χ·F·Γ‖ ≤ M·|Θ|·|Γ|`.
  have hpt : ∀ x : Submission.BoseGases.X n,
      ‖(Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖ ≤ M * (|Θ x| * |Γ x|) := by
    intro x
    have hχj : (0 : ℝ) ≤ χ (x j) := hχnn _
    have hkey : χ (x j) * ‖F (x j)‖ ≤ M := hM _
    have hnorm : ‖(Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖
        = |Θ x| * (χ (x j) * ‖F (x j)‖) * |Γ x| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχj]
      ring
    rw [hnorm]
    calc |Θ x| * (χ (x j) * ‖F (x j)‖) * |Γ x|
        ≤ |Θ x| * M * |Γ x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
      _ = M * (|Θ x| * |Γ x|) := by ring
  -- Integrability of the majorant on the (finite-measure) box.
  have hμfin : (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  have hgmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => M * (|Θ x| * |Γ x|))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ((hΘm.abs.mul hΓm.abs).const_mul M).aestronglyMeasurable
  have hgbd : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      ‖M * (|Θ x| * |Γ x|)‖ ≤ M * (C * D) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hMnn (mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hΘb x) (hΓb x) (abs_nonneg _) hC) hMnn
  have hgint : IntegrableOn (fun x : Submission.BoseGases.X n => M * (|Θ x| * |Γ x|))
      (Submission.BoseGases.abox n ℓ) volume :=
    IntegrableOn.of_bound hμfin hgmeas (M * (C * D)) hgbd
  have hle : ‖∫ x in Submission.BoseGases.abox n ℓ,
        (Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, M * (|Θ x| * |Γ x|) :=
    MeasureTheory.norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  -- Move the integral onto the box (using `hzero`), then pull out the constant `M`.
  calc ‖∫ x : Submission.BoseGases.X n,
          (Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖
      = ‖∫ x in Submission.BoseGases.abox n ℓ,
          (Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ)‖ := by
        rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Submission.BoseGases.abox n ℓ)
          (f := fun x : Submission.BoseGases.X n =>
            (Θ x : ℂ) * (χ (x j) : ℂ) * F (x j) * (Γ x : ℂ))
          (fun x hx => by simp [hzero x hx])]
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, M * (|Θ x| * |Γ x|) := hle
    _ = M * (∫ x in Submission.BoseGases.abox n ℓ, |Θ x| * |Γ x|) :=
        MeasureTheory.integral_const_mul M (fun x => |Θ x| * |Γ x|)

end Work.BoseBoxFock.PCFU
