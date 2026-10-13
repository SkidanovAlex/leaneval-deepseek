import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Step4

open MeasureTheory

/-- Cauchy–Schwarz integrability for a `κ`-weighted product on a set: if `κ ≥ 0` on `s` and both
`f ^ 2 * κ` and `g ^ 2 * κ` are integrable on `s`, then so is `f * g * κ`.  This is the
integrability input needed to split products against the relation `v = -α + β - 6δ`. -/
theorem integrableOn_mul_mul_of_sq {s : Set ℝ} {p q κ : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hmp : AEStronglyMeasurable p (volume.restrict s))
    (hmq : AEStronglyMeasurable q (volume.restrict s))
    (hmκ : AEStronglyMeasurable κ (volume.restrict s))
    (hκ0 : ∀ θ ∈ s, 0 ≤ κ θ)
    (hp : IntegrableOn (fun θ => (p θ) ^ 2 * κ θ) s)
    (hq : IntegrableOn (fun θ => (q θ) ^ 2 * κ θ) s) :
    IntegrableOn (fun θ => p θ * q θ * κ θ) s := by
  have hmeas : AEStronglyMeasurable (fun θ => p θ * q θ * κ θ) (volume.restrict s) :=
    (hmp.mul hmq).mul hmκ
  have hdom : Integrable (fun θ => ((p θ) ^ 2 * κ θ + (q θ) ^ 2 * κ θ) / 2)
      (volume.restrict s) :=
    (hp.add hq).div_const 2
  refine Integrable.mono' hdom hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' hs]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  have hk := hκ0 θ hθ
  have h2 : |p θ * q θ| ≤ ((p θ) ^ 2 + (q θ) ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|p θ| - |q θ|), abs_nonneg (p θ), abs_nonneg (q θ),
      sq_abs (p θ), sq_abs (q θ)]
  have h3 : |p θ * q θ| * κ θ ≤ ((p θ) ^ 2 * κ θ + (q θ) ^ 2 * κ θ) / 2 := by
    have h4 := mul_le_mul_of_nonneg_right h2 hk
    nlinarith [h4]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  exact h3

theorem integral_sq_eq_of_rel {s : Set ℝ} {α β δ v κ : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hκ0 : ∀ θ ∈ s, 0 ≤ κ θ) (hκ1 : ∀ θ ∈ s, κ θ ≤ 1)
    (hrel : ∀ θ ∈ s, v θ = -α θ + β θ - 6 * δ θ)
    (hmα : MeasureTheory.AEStronglyMeasurable α (MeasureTheory.volume.restrict s))
    (hmv : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume.restrict s))
    (hmδ : MeasureTheory.AEStronglyMeasurable δ (MeasureTheory.volume.restrict s))
    (hmκ : MeasureTheory.AEStronglyMeasurable κ (MeasureTheory.volume.restrict s))
    (hIα : MeasureTheory.IntegrableOn (fun θ => (α θ) ^ 2 * κ θ) s)
    (hIv : MeasureTheory.IntegrableOn (fun θ => (v θ) ^ 2 * κ θ) s)
    (hIδ : MeasureTheory.IntegrableOn (fun θ => (δ θ) ^ 2 * κ θ) s) :
    (∫ θ in s, (v θ) ^ 2 * κ θ)
      = - (∫ θ in s, α θ * v θ * κ θ) + (∫ θ in s, β θ * v θ * κ θ)
        - 6 * (∫ θ in s, δ θ * v θ * κ θ) := by
  -- The products `α v κ` and `δ v κ` are integrable on `s` by Cauchy–Schwarz.
  have hA : IntegrableOn (fun θ => α θ * v θ * κ θ) s :=
    integrableOn_mul_mul_of_sq hs hmα hmv hmκ hκ0 hIα hIv
  have hD : IntegrableOn (fun θ => δ θ * v θ * κ θ) s :=
    integrableOn_mul_mul_of_sq hs hmδ hmv hmκ hκ0 hIδ hIv
  -- The relation rewrites `β` in terms of `v`, `α`, `δ`.
  have hβeq : ∀ θ ∈ s, β θ = v θ + α θ + 6 * δ θ := by
    intro θ hθ
    have h := hrel θ hθ
    linarith
  -- Hence `β v κ` is a sum of integrable terms.
  have hB : IntegrableOn (fun θ => β θ * v θ * κ θ) s := by
    have hcomb : IntegrableOn
        (fun θ => (v θ) ^ 2 * κ θ + (α θ * v θ * κ θ) + 6 * (δ θ * v θ * κ θ)) s :=
      (hIv.add hA).add (hD.const_mul 6)
    refine hcomb.congr_fun ?_ hs
    intro θ hθ
    dsimp only
    rw [hβeq θ hθ]
    ring
  -- Pointwise the integrand is the linear combination `-αvκ + βvκ - 6δvκ`.
  have hcongr : (∫ θ in s, (v θ) ^ 2 * κ θ)
      = ∫ θ in s, (-(α θ * v θ * κ θ) + (β θ * v θ * κ θ) - 6 * (δ θ * v θ * κ θ)) :=
    setIntegral_congr_fun hs (fun θ hθ => by rw [hrel θ hθ]; ring)
  have e1 : (∫ θ in s, (-(α θ * v θ * κ θ) + (β θ * v θ * κ θ) - 6 * (δ θ * v θ * κ θ)))
      = (∫ θ in s, (-(α θ * v θ * κ θ) + (β θ * v θ * κ θ)))
        - (∫ θ in s, 6 * (δ θ * v θ * κ θ)) :=
    integral_sub (f := fun θ => -(α θ * v θ * κ θ) + (β θ * v θ * κ θ))
      (g := fun θ => 6 * (δ θ * v θ * κ θ)) ((hA.neg).add hB) (hD.const_mul 6)
  have e2a : (∫ θ in s, (-(α θ * v θ * κ θ) + (β θ * v θ * κ θ)))
      = (∫ θ in s, -(α θ * v θ * κ θ)) + (∫ θ in s, β θ * v θ * κ θ) :=
    integral_add (f := fun θ => -(α θ * v θ * κ θ)) (g := fun θ => β θ * v θ * κ θ) hA.neg hB
  have e2b : (∫ θ in s, -(α θ * v θ * κ θ)) = - (∫ θ in s, α θ * v θ * κ θ) :=
    integral_neg (fun θ => α θ * v θ * κ θ)
  have e2 : (∫ θ in s, (-(α θ * v θ * κ θ) + (β θ * v θ * κ θ)))
      = - (∫ θ in s, α θ * v θ * κ θ) + (∫ θ in s, β θ * v θ * κ θ) := by rw [e2a, e2b]
  have e3 : (∫ θ in s, 6 * (δ θ * v θ * κ θ)) = 6 * (∫ θ in s, δ θ * v θ * κ θ) :=
    integral_const_mul 6 (fun θ => δ θ * v θ * κ θ)
  rw [hcongr, e1, e2, e3]

end Work.FTS.EllipticEst.remov.Step4
