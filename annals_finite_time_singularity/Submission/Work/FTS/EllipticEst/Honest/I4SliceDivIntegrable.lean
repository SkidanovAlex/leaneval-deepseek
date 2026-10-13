import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.I4SliceAlgebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.Honest

/-- **The integrability hypothesis of the boundary lemma.**

Let `Φ` be of class `C²` on `(0, π/2)` with `∫_θ (Φ/cos θ)²σ` and `∫_θ (Φ'')²σ` integrable over
`[0, π/2]` (`σ = sin(2θ)^{-η}`, `η = 99/100`).  Then the quantity `(P'/cos θ)²σ`, where
`P = cos²θ·(Φ/cos θ)'`, is integrable on `(0, π/2)` — this is the third hypothesis of
`Work.FTS.EllipticEst.Honest.I4BoundaryVanish` when it is applied with `ψ := Φ/cos θ`.

Route: by the pointwise calculus identity `P' = cos θ·(Φ'' + Φ)`
(`Work.FTS.EllipticEst.I4SliceAlgebra`), the integrand equals `(Φ'' + Φ)²σ` on `(0, π/2)`, which
is dominated by `2(Φ'')²σ + 2(Φ/cos θ)²σ` (since `Φ = cos θ·(Φ/cos θ)` and `σ ≥ 0`).  Both terms
are integrable by the hypotheses, so the domination `MeasureTheory.Integrable.mono'` applies,
with `AEStronglyMeasurable (fun θ => (Φ'' θ + Φ θ)²σ)` (a.e. strong measurability of the second
derivative is `aestronglyMeasurable_deriv`, of `Φ` from continuity, of `σ` from
`ContinuousOn.rpow_const` on `(0, π/2)` where `sin 2θ ≠ 0`).  Finally transfer the integrability
to the `P'`-form by a.e. equality on `(0, π/2)`. -/
theorem I4SliceDivIntegrable (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => (Real.cos θ') ^ 2
            * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2)) := by
  have hUmeas : MeasurableSet (Set.Ioo (0:ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hcospos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.cos θ := by
    intro θ hθ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsin2pos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- the pointwise calculus identity `P' = cos θ · (Φ'' + Φ)` on `(0, π/2)`
  have hid := (Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm).2.2.1
  -- the two summands, restricted from `[0, π/2]` to `(0, π/2)`
  have hA' : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set Set.Ioo_subset_Icc_self
  have hB' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hB.mono_set Set.Ioo_subset_Icc_self
  -- the dominating function
  have hbounds : MeasureTheory.IntegrableOn
      (fun θ => 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hB'.const_mul 2).add (hA'.const_mul 2)
  -- a.e. strong measurability of `(Φ'' + Φ)²σ`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (deriv (deriv Φ))
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      aestronglyMeasurable_deriv (deriv Φ) _
    have h2 : MeasureTheory.AEStronglyMeasurable Φ
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      hsm.continuousOn.aestronglyMeasurable hUmeas
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
      apply ContinuousOn.aestronglyMeasurable _ hUmeas
      exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hsin2pos x hx)))
    exact ((h1.add h2).pow 2).mul h3
  -- the pointwise domination `(Φ'' + Φ)²σ ≤ 2(Φ'')²σ + 2(Φ/cos θ)²σ`
  have hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ‖(deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))‖
      ≤ 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
    rw [MeasureTheory.ae_restrict_iff' hUmeas]
    filter_upwards with θ hθ
    have hsinn := hsin2pos θ hθ
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := Real.rpow_nonneg (le_of_lt hsinn) _
    have hcos2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
    have hcos2pos : 0 < Real.cos θ ^ 2 := pow_pos (hcospos θ hθ) 2
    have hb : Φ θ ^ 2 ≤ (Φ θ / Real.cos θ) ^ 2 := by
      have h1 : 1 ≤ 1 / Real.cos θ ^ 2 := by
        rw [le_div_iff₀ hcos2pos]; simpa using hcos2
      calc Φ θ ^ 2 = Φ θ ^ 2 * 1 := by ring
        _ ≤ Φ θ ^ 2 * (1 / Real.cos θ ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (Φ θ / Real.cos θ) ^ 2 := by rw [div_pow]; ring
    have hkey : (deriv (deriv Φ) θ + Φ θ) ^ 2
        ≤ 2 * (deriv (deriv Φ) θ) ^ 2 + 2 * (Φ θ / Real.cos θ) ^ 2 := by
      have h1 := add_sq_le (a := deriv (deriv Φ) θ) (b := Φ θ)
      nlinarith [hb]
    have hmain : (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        ≤ 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
      nlinarith [mul_le_mul_of_nonneg_right hkey hσnn]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
    exact hmain
  -- integrability of `(Φ'' + Φ)²σ` on `(0, π/2)`
  have hgint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' hbounds haesm hdom
  -- transfer to the `P'`-form by a.e. equality on `(0, π/2)`
  refine hgint.congr ?_
  rw [Filter.EventuallyEq]
  rw [MeasureTheory.ae_restrict_iff' hUmeas]
  filter_upwards with θ hθ
  have hne : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
  rw [hid θ hθ, mul_div_cancel_left₀ _ hne]

end Work.FTS.EllipticEst.Honest
