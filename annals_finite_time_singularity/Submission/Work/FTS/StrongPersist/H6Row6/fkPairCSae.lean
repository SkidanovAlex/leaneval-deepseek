import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPairCS
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open MeasureTheory

/-- AM–GM in the form used to dominate a product of square roots: for `a, b ≥ 0`,
`2 √a √b ≤ a + b`. -/
private lemma fkPairCSae_sqrt_amgm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem fkPairCSae {ρ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {V₁ V₂ : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hr : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), |r z| ≤ K)
    (hρ : ∀ z, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 ≤ ρ z θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ) ^ 2) Work.Spaces.Iz)
    (hI2 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ) ^ 2) Work.Spaces.Iz)
    (hs1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (V₁ z θ) ^ 2) Work.Spaces.Iθ)
    (hs2 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (V₂ z θ) ^ 2) Work.Spaces.Iθ) :
    |∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
      ≤ K * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ) ^ 2) := by
  -- nonnegativity of the angular slice densities, pointwise in `z`: the hypothesis is only
  -- a.e. in `θ`, which is exactly what an integral can see.
  have hPnn : ∀ z, 0 ≤ (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2) := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
  have hQnn : ∀ z, 0 ≤ (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
  -- Cauchy–Schwarz in the angular variable, for each fixed `z ∈ Iz`
  have hθcs : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
    intro z hz
    have h1i : MeasureTheory.Integrable (fun θ => ρ z θ * (V₁ z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hs1 z hz
    have h2i : MeasureTheory.Integrable (fun θ => ρ z θ * (V₂ z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hs2 z hz
    have hpnn : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun θ => ρ z θ * (V₁ z θ)^2) :=
      (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
    have hqnn : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iθ)]
        (fun θ => ρ z θ * (V₂ z θ)^2) :=
      (hρ z).mono fun θ hθ => mul_nonneg hθ (sq_nonneg _)
    have hcs := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) hpnn hqnn h1i h2i
    have hpt : ∀ a x y : ℝ, 0 ≤ a → |a * x * y| = Real.sqrt (a * x^2) * Real.sqrt (a * y^2) := by
      intro a x y ha
      have h1 : Real.sqrt (a * x^2) = Real.sqrt a * |x| := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]
      have h2 : Real.sqrt (a * y^2) = Real.sqrt a * |y| := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]
      have h3 : Real.sqrt a * Real.sqrt a = a := by rw [← sq, Real.sq_sqrt ha]
      calc |a * x * y| = a * |x| * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha]
        _ = (Real.sqrt a * Real.sqrt a) * (|x| * |y|) := by rw [h3]; ring
        _ = Real.sqrt (a * x^2) * Real.sqrt (a * y^2) := by rw [h1, h2]; ring
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * V₁ z θ * V₂ z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ θ in Work.Spaces.Iθ,
            Real.sqrt (ρ z θ * (V₁ z θ)^2) * Real.sqrt (ρ z θ * (V₂ z θ)^2) :=
          MeasureTheory.integral_congr_ae ((hρ z).mono fun θ hθ =>
            hpt (ρ z θ) (V₁ z θ) (V₂ z θ) hθ)
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := hcs
  -- the pointwise-in-`z` bound, a.e. on `Iz`
  have hmain : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
        ≤ K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) := by
    filter_upwards [hr, MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0:ℝ)))]
      with z hrz hz
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hrz (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hθcs z hz) hK)
  -- the dominating profile is integrable, being bounded by `(P + Q)/2`
  have hInt_sqrt : MeasureTheory.Integrable
      (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun z => (1/2) * ((∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        + (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2))) ?_ ?_ ?_
    · exact (hI1.add hI2).const_mul (1/2)
    · exact ((hI1.aemeasurable.sqrt).aestronglyMeasurable).mul
        ((hI2.aemeasurable.sqrt).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ici (a := (0:ℝ)))] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      have h2 := fkPairCSae_sqrt_amgm (hPnn z) (hQnn z)
      linarith
  have hIntK : MeasureTheory.Integrable
      (fun z => K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hInt_sqrt.const_mul K
  have hpae : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz)]
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2) :=
    Filter.Eventually.of_forall hPnn
  have hqae : 0 ≤ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz)]
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) :=
    Filter.Eventually.of_forall hQnn
  -- the radial Cauchy–Schwarz
  calc |∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)|
      ≤ ∫ z in Work.Spaces.Iz, |r z * (∫ θ in Work.Spaces.Iθ, ρ z θ * V₁ z θ * V₂ z θ)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, K * (Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          hIntK hmain
    _ = K * ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) :=
        MeasureTheory.integral_const_mul K _
    _ ≤ K * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2)) :=
        mul_le_mul_of_nonneg_left
          (Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
            (MeasureTheory.volume.restrict Work.Spaces.Iz) hpae hqae hI1 hI2) hK
    _ = K * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₁ z θ)^2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (V₂ z θ)^2) := by
        ring

end Work.FTS.StrongPersist.H6Row6
