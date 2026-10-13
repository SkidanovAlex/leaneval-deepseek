import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Cauchy–Schwarz cut-off estimate `cs_cutoff`

This file proves the angular Cauchy–Schwarz inequality used in the `λ`-cut-off estimates of
`Submission/Work/FTS/PhiStar/Honesty/CptApp`.  With

* `f θ = X θ · (w z / sin(2θ)^{η/2})` (the "square-integrable" factor, hypothesis `hA2`), and
* `h θ = γ θ · sin(2θ)^{η/2} · sinCos2 θ` (the second factor, controlled by `|γ| ≤ 1`),

one has, **on `Iθ = [0, π/2]`**,

* `f θ * h θ = w z * (γ θ * X θ * sinCos2 θ)`
  (the `sin(2θ)^{η/2}` factors cancel where `sin 2θ ≠ 0`; where `sin 2θ = 0` both sides
  vanish because then `sinCos2 θ = sin θ cos²θ = 0`), and
* `(h θ)² = (γ θ)² · sin(2θ)^{η} · sinCos2 θ²`
  (using `(sin 2θ)^{η/2} · (sin 2θ)^{η/2} = (sin 2θ)^{η}`, valid since `sin 2θ ≥ 0` on `Iθ`).

Applying the Cauchy–Schwarz inequality `Work.RPFresh.integral_mul_sq_le_sq_mul_sq` to `f`
and `h` over `volume.restrict Iθ` and rewriting the two sides gives the claim.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory

private lemma eta_half_ne : Work.Spaces.eta / 2 ≠ 0 := by unfold Work.Spaces.eta; norm_num

private lemma eta_half_pos : (0 : ℝ) < Work.Spaces.eta / 2 := by
  unfold Work.Spaces.eta; norm_num

/-- `sin θ cos²θ = sin(2θ) · cos θ / 2`. -/
private lemma sc_eq (θ : ℝ) : Work.Elliptic.sinCos2 θ = Real.sin (2 * θ) * Real.cos θ / 2 := by
  rw [Real.sin_two_mul, Work.Elliptic.sinCos2]; ring

/-- On `Iθ = [0, π/2]` one has `sin(2θ) ≥ 0`. -/
private lemma sin0 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- `|sin θ cos²θ| ≤ 1` everywhere. -/
private lemma sc_abs_le (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  unfold Work.Elliptic.sinCos2
  rw [abs_mul, abs_pow]
  nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ, abs_nonneg (Real.sin θ),
    abs_nonneg (Real.cos θ)]

/-- The pointwise cancellation of the `sin(2θ)^{η/2}` weights **on `Iθ`**. -/
private lemma mul_eq_cutoff (X γ : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
        (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ))
      = Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ) := by
  have hs0 := sin0 hθ
  rcases eq_or_ne (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) 0 with ha0 | ha0
  · -- `sin(2θ)^{η/2} = 0`, hence `sin 2θ = 0` and `sinCos2 θ = 0`: both sides vanish.
    have hs : Real.sin (2 * θ) = 0 := (Real.rpow_eq_zero hs0 eta_half_ne).mp ha0
    rw [ha0, sc_eq, hs]
    ring
  · -- `sin(2θ)^{η/2} ≠ 0`: cancel the weight.
    rw [sc_eq]
    have hcancel : Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = Work.Spaces.w z :=
      div_mul_cancel₀ _ ha0
    rw [show X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) *
          (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * θ) * Real.cos θ / 2)))
        = (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
            * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
          * (X θ * γ θ * (Real.sin (2 * θ) * Real.cos θ / 2)) by ring, hcancel]
    ring

/-- The pointwise identification of the square of the second factor, **on `Iθ`**. -/
private lemma sq_eq_cutoff (γ : ℝ → ℝ) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)) ^ 2
      = (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2 := by
  have hs0 := sin0 hθ
  have ha2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [show (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) from
            (Real.rpow_natCast _ 2).symm,
        (Real.rpow_mul hs0 (Work.Spaces.eta / 2) 2).symm]
    congr 1
    ring
  rw [mul_pow, mul_pow, ha2]
  ring

theorem cs_cutoff {X γ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hγm : MeasureTheory.AEStronglyMeasurable γ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hγb : ∀ θ : ℝ, |γ θ| ≤ 1)
    (hAm : MeasureTheory.AEStronglyMeasurable
      (fun θ => X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hA2 : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
            (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2) := by
  -- the second factor `h θ = γ θ · sin(2θ)^{η/2} · sinCos2 θ` is measurable and its square is
  -- bounded by `1` on the finite-measure set `Iθ`
  have hGcont : Continuous (fun θ : ℝ =>
      Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ) := by
    apply Continuous.mul
    · exact (Real.continuous_rpow_const (le_of_lt eta_half_pos)).comp (by continuity)
    · unfold Work.Elliptic.sinCos2; fun_prop
  have hHm : AEStronglyMeasurable
      (fun θ => γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hγm.mul hGcont.aestronglyMeasurable
  have hH2 : Integrable
      (fun θ => (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      Real.isFiniteMeasure_restrict_Icc 0 (Real.pi / 2)
    refine Integrable.of_bound (hHm.pow 2) 1
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_))
    have hs0 := sin0 hθ
    have ha1 : |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      exact Real.rpow_le_one hs0 (Real.sin_le_one _) (le_of_lt eta_half_pos)
    have hH1 : |γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)| ≤ 1 := by
      rw [abs_mul, abs_mul]
      have h1 : |γ θ| * |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
        nlinarith [hγb θ, ha1, abs_nonneg (γ θ),
          abs_nonneg (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))]
      nlinarith [h1, sc_abs_le θ, abs_nonneg (Work.Elliptic.sinCos2 θ),
        abs_nonneg (|γ θ| * |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)|)]
    rw [Real.norm_eq_abs, abs_sq]
    nlinarith [hH1,
      abs_nonneg (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)),
      sq_abs (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ))]
  -- Cauchy–Schwarz for `f` and `h`
  have hkey := Work.RPFresh.integral_mul_sq_le_sq_mul_sq (volume.restrict Work.Spaces.Iθ)
      (f := fun θ => X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (h := fun θ => γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ))
      hAm hHm hA2 hH2
  -- identify the three integrals
  have hprod : (∫ θ in Work.Spaces.Iθ,
        (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
          (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)))
      = Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) :=
    calc (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
              (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
                * Work.Elliptic.sinCos2 θ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ)) :=
          integral_congr_ae (by
            filter_upwards [ae_restrict_of_forall_mem (s := Set.Icc 0 (Real.pi / 2))
              (p := fun θ => (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
                  (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
                    * Work.Elliptic.sinCos2 θ))
                  = Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ))
              measurableSet_Icc (fun θ hθ => mul_eq_cutoff X γ z θ hθ)] with θ hθ
            exact hθ)
      _ = Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) :=
          integral_const_mul _ _
  have hsq : (∫ θ in Work.Spaces.Iθ,
        (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2 :=
    integral_congr_ae (by
      filter_upwards [ae_restrict_of_forall_mem (s := Set.Icc 0 (Real.pi / 2))
        (p := fun θ => (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
              * Work.Elliptic.sinCos2 θ)) ^ 2
            = (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2)
        measurableSet_Icc (fun θ hθ => sq_eq_cutoff γ θ hθ)] with θ hθ
      exact hθ)
  rw [hprod, hsq] at hkey
  calc (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) ^ 2
        * (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ)) ^ 2 :=
        by ring
    _ ≤ (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
            (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2) := hkey

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
