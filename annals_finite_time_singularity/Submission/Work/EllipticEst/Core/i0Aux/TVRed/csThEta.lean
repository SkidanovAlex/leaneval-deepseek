import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

/-!
# Cauchy–Schwarz for the angular weight `thEta`

The angular weight `thEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ = [0, π/2]`, so the
elementary Cauchy–Schwarz inequality holds for it:

  `(∫_{Iθ} g h thEta)² ≤ (∫_{Iθ} g² thEta) · (∫_{Iθ} h² thEta)`.

The point of the present formulation (and the reason it is not just an instance of
`Work.Spaces.cs_integral`) is that **no measurability of `g` or `h` is assumed**: only that
the two weighted squares `g² thEta`, `h² thEta` are integrable.  The proof therefore uses
the discriminant argument rather than `L²`-Cauchy–Schwarz: for every real `t` the function
`(g + t h)² thEta` is nonnegative, hence (when it is integrable, which it is exactly when
`g h thEta` is) has nonnegative integral `A + 2 t B + t² C`, which forces `B² ≤ A C`.  If
`g h thEta` is *not* integrable then the Bochner integral on the left vanishes by definition
and the right-hand side is a product of two nonnegative integrals.
-/

/-- Weighted Cauchy–Schwarz for an a.e. nonnegative weight `w` and **arbitrary** (not
necessarily measurable) functions `g`, `h` whose weighted squares are integrable:
`(∫_s g h w)² ≤ (∫_s g² w) · (∫_s h² w)`. -/
private lemma weighted_cs {w g h : ℝ → ℝ} {s : Set ℝ}
    (hw : ∀ᵐ θ ∂(MeasureTheory.volume.restrict s), 0 ≤ w θ)
    (hg : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 * w θ)
      (MeasureTheory.volume.restrict s))
    (hh : MeasureTheory.Integrable (fun θ : ℝ => (h θ) ^ 2 * w θ)
      (MeasureTheory.volume.restrict s)) :
    (∫ θ in s, g θ * h θ * w θ) ^ 2
      ≤ (∫ θ in s, (g θ) ^ 2 * w θ) * (∫ θ in s, (h θ) ^ 2 * w θ) := by
  by_cases hI : MeasureTheory.Integrable (fun θ : ℝ => g θ * h θ * w θ)
      (MeasureTheory.volume.restrict s)
  · -- Main case: `g h w` is integrable, so every quadratic `(g + t h)² w` is integrable
    -- and the discriminant of `t ↦ ∫ (g + t h)² w` is nonpositive.
    have key : ∀ t : ℝ, 0 ≤ (∫ θ in s, (g θ) ^ 2 * w θ)
        + 2 * t * (∫ θ in s, g θ * h θ * w θ) + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
      intro t
      have hpt : ∀ θ : ℝ, (g θ + t * h θ) ^ 2 * w θ
          = (g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)
            + (t ^ 2) * ((h θ) ^ 2 * w θ) := fun θ => by ring
      have hnn : 0 ≤ ∫ θ in s, (g θ + t * h θ) ^ 2 * w θ :=
        MeasureTheory.integral_nonneg_of_ae
          (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
      have heq : (∫ θ in s, (g θ + t * h θ) ^ 2 * w θ)
          = (∫ θ in s, (g θ) ^ 2 * w θ) + 2 * t * (∫ θ in s, g θ * h θ * w θ)
            + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
        have h1 : MeasureTheory.Integrable
            (fun θ : ℝ => (g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ))
            (MeasureTheory.volume.restrict s) :=
          hg.add (hI.const_mul (2 * t))
        have h2 : MeasureTheory.Integrable (fun θ : ℝ => t ^ 2 * ((h θ) ^ 2 * w θ))
            (MeasureTheory.volume.restrict s) := hh.const_mul (t ^ 2)
        calc (∫ θ in s, (g θ + t * h θ) ^ 2 * w θ)
            = ∫ θ in s,
                ((g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)) + t ^ 2 * ((h θ) ^ 2 * w θ) := by
              rw [funext hpt]
          _ = (∫ θ in s, ((g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)))
                + ∫ θ in s, t ^ 2 * ((h θ) ^ 2 * w θ) :=
              MeasureTheory.integral_add h1 h2
          _ = ((∫ θ in s, (g θ) ^ 2 * w θ) + ∫ θ in s, 2 * t * (g θ * h θ * w θ))
                + ∫ θ in s, t ^ 2 * ((h θ) ^ 2 * w θ) := by
              rw [MeasureTheory.integral_add hg (hI.const_mul (2 * t))]
          _ = ((∫ θ in s, (g θ) ^ 2 * w θ) + 2 * t * (∫ θ in s, g θ * h θ * w θ))
                + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      linarith [hnn, heq.le, heq.ge]
    have hA : 0 ≤ ∫ θ in s, (g θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    have hC : 0 ≤ ∫ θ in s, (h θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · -- `∫ h² w = 0`: then `∫ g h w = 0` as well.
      have hB0 : (∫ θ in s, g θ * h θ * w θ) = 0 := by
        by_contra hBne
        have hk := key (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
          / (2 * (∫ θ in s, g θ * h θ * w θ)))
        have hval : (∫ θ in s, (g θ) ^ 2 * w θ)
              + 2 * (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
                  / (2 * (∫ θ in s, g θ * h θ * w θ))) * (∫ θ in s, g θ * h θ * w θ)
              + (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
                  / (2 * (∫ θ in s, g θ * h θ * w θ))) ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ)
            = -1 := by
          rw [← hC0]; field_simp; ring
        rw [hval] at hk
        linarith [hk]
      rw [hB0, ← hC0]
      norm_num
    · -- `∫ h² w > 0`: instantiate the quadratic at `t = -(∫ g h w)/(∫ h² w)`.
      have hk := key (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ))
      have hval : (∫ θ in s, (g θ) ^ 2 * w θ)
            + 2 * (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ))
              * (∫ θ in s, g θ * h θ * w θ)
            + (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ)) ^ 2
              * (∫ θ in s, (h θ) ^ 2 * w θ)
          = (∫ θ in s, (g θ) ^ 2 * w θ)
            - (∫ θ in s, g θ * h θ * w θ) ^ 2 / (∫ θ in s, (h θ) ^ 2 * w θ) := by
        field_simp; ring
      rw [hval] at hk
      have h2 : (∫ θ in s, g θ * h θ * w θ) ^ 2 / (∫ θ in s, (h θ) ^ 2 * w θ)
          ≤ (∫ θ in s, (g θ) ^ 2 * w θ) := by linarith
      rwa [div_le_iff₀ hCpos] at h2
  · -- Otherwise the left-hand integral is `0` by definition and the right-hand side is a
    -- product of two nonnegative integrals.
    rw [MeasureTheory.integral_undef hI]
    have hA : 0 ≤ ∫ θ in s, (g θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    have hC : 0 ≤ ∫ θ in s, (h θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    norm_num
    exact mul_nonneg hA hC

theorem csThEta {g h : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hh : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (h θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ : ℝ => g θ * h θ * Work.FTS.EllipticEst.thEta θ)) ^ 2
      ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        * (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (h θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  have hw : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.FTS.EllipticEst.thEta θ :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_Icc :
      MeasurableSet Work.Spaces.Iθ)).mpr
      (Filter.Eventually.of_forall
        (fun θ (hθ : θ ∈ Work.Spaces.Iθ) => Work.FTS.EllipticEst.thEta_nonneg hθ))
  exact weighted_cs hw hg hh

end Work.EllipticEst.Core.i0Aux.TVRed
