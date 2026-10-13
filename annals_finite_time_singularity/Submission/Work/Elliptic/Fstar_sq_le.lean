/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular `L²`-bound for the moment `F_*`

`F_*(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` is the angular moment of the solvability
condition of Proposition `prop:L2`.  Cauchy--Schwarz gives

`F_*(z)² ≤ (∫_0^{π/2} sin²θ cos⁴θ dθ) · ∫_0^{π/2} F(z,θ)² dθ`,

and since `sin θ cos²θ ∈ [0,1]` on `[0,π/2]` the first factor is at most the length
`π/2` of the interval.  This is the estimate used to control the singular part
`G_* = -(1/(4α)) L₁₂(F)` in `L²`.

The proof avoids any measurability hypothesis on `θ ↦ F(z,θ)`: the hypothesis is only
that `θ ↦ F(z,θ)²` be integrable.  If the product `θ ↦ F(z,θ) sin θ cos²θ` is not
integrable then its integral vanishes, and otherwise one argues with the
discriminant of the nonnegative quadratic `t ↦ ∫_0^{π/2} (F(z,θ) - t sin θ cos²θ)² dθ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- Cauchy--Schwarz in discriminant form: if the real quadratic `A - 2tB + t²C` is
nonnegative for every `t`, then `B² ≤ A·C`. -/
lemma sq_le_mul_of_quadratic_nonneg {A B C : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  have hq : ∀ x : ℝ, 0 ≤ C * (x * x) + (-2 * B) * x + A := by
    intro x
    have := h x
    nlinarith [this]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

theorem Fstar_sq_le (F : ℝ → ℝ → ℝ) (z : ℝ)
    (h : MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ) :
    (Work.Elliptic.Fstar F z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The angular weight is continuous.
  have hw_cont : Continuous (fun θ : ℝ => sinCos2 θ) := by
    unfold sinCos2
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  -- Its square is integrable on the compact interval `Iθ`.
  have hw2_int : IntegrableOn (fun θ : ℝ => (sinCos2 θ) ^ 2) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (hw_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  -- Pointwise, `sinCos2 θ ^ 2 ≤ 1` on `Iθ`.
  have hpt_le : ∀ θ ∈ Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ (1 : ℝ) := by
    intro θ hθ
    obtain ⟨hθ0, hθ2⟩ := hθ
    have hpi : 0 < π := Real.pi_pos
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith⟩
    have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hcos_nn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ2⟩
    have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcos2_nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    have hcos2_le : Real.cos θ ^ 2 ≤ 1 := by nlinarith
    have hw_nn : 0 ≤ sinCos2 θ := by
      rw [sinCos2]
      exact mul_nonneg hsin_nn hcos2_nn
    have hw_le : sinCos2 θ ≤ 1 := by
      rw [sinCos2]
      calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
            mul_le_mul hsin_le hcos2_le hcos2_nn zero_le_one
        _ = 1 := by ring
    nlinarith
  -- Consequently `∫_{Iθ} sinCos2² ≤ vol(Iθ) = π/2`.
  have hw2_le : ∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ π / 2 := by
    have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hle : ∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hInt1
        (by filter_upwards [ae_restrict_mem hIθ] with θ hθ; exact hpt_le θ hθ)
    have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hconst : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = π / 2 := by
      have h1 : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = volume.real Work.Spaces.Iθ := by
        rw [MeasureTheory.setIntegral_const]
        simp
      rw [h1, hvol]
    linarith
  -- Main argument: unfold `F_*` and argue with the discriminant of
  -- `t ↦ ∫_{Iθ} (F(z,θ) - t sin θ cos²θ)²`.
  rw [Fstar]
  have hA0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 : ℝ) :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hkey : (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
    by_cases huw : IntegrableOn (fun θ => F z θ * sinCos2 θ) Work.Spaces.Iθ
    · -- `F sinθcos²θ` is integrable: use the nonnegative quadratic in `t`.
      have hexpand : ∀ t : ℝ, ∫ θ in Work.Spaces.Iθ, (F z θ - t * sinCos2 θ) ^ 2
          = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
            - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
            + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
        intro t
        have h1 : IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ := h
        have h2 : IntegrableOn (fun θ => F z θ * sinCos2 θ) Work.Spaces.Iθ := huw
        have h3 : IntegrableOn (fun θ => (sinCos2 θ) ^ 2) Work.Spaces.Iθ := hw2_int
        have h12 : IntegrableOn
            (fun θ => (F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)) Work.Spaces.Iθ :=
          h1.sub (h2.const_mul (2 * t))
        have hstep2 : (∫ θ in Work.Spaces.Iθ,
              ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)))
            = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
              - ∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ) :=
          integral_sub h1 (h2.const_mul (2 * t))
        have hstep3 : (∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ))
            = (2 * t) * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) :=
          integral_const_mul (2 * t) (fun θ => F z θ * sinCos2 θ)
        have hstep4 : (∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2)
            = t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) :=
          integral_const_mul (t ^ 2) (fun θ => (sinCos2 θ) ^ 2)
        calc ∫ θ in Work.Spaces.Iθ, (F z θ - t * sinCos2 θ) ^ 2
            = ∫ θ in Work.Spaces.Iθ, ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)
                + t ^ 2 * (sinCos2 θ) ^ 2) := by
              exact setIntegral_congr_fun hIθ (fun θ _ => by ring)
          _ = (∫ θ in Work.Spaces.Iθ, ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)))
                + ∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2 :=
              integral_add h12 (h3.const_mul (t ^ 2))
          _ = ((∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - ∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ))
                + ∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2 := by
              rw [hstep2]
          _ = ((∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - (2 * t) * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ))
                + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
              rw [hstep3, hstep4]
          _ = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
                + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
              ring
      have hq : ∀ t : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
          - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
          + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
        intro t
        rw [← hexpand t]
        exact integral_nonneg (fun θ => sq_nonneg _)
      exact sq_le_mul_of_quadratic_nonneg hq
    · -- Otherwise the integral of the product vanishes.
      have hB0 : (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) = 0 := integral_undef huw
      rw [hB0]
      have hC0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 : ℝ) :=
        integral_nonneg (fun θ => sq_nonneg _)
      simpa using mul_nonneg hA0 hC0
  calc (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := hkey
    _ ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) * (π / 2) :=
        mul_le_mul_of_nonneg_left hw2_le hA0
    _ = (π / 2) * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) := by ring

end Work.Elliptic
