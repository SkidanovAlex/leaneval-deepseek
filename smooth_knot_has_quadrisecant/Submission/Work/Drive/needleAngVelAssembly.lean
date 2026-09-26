import Mathlib
import Submission.Work.Drive.blurAngularVelocity

/-!
# The angular velocity of the doubly blurred needle: the assembly

`Work.Drive.meanProd_bound₂` (`blurAngularVelocity.lean`) compares the *product* of the two iterated
weighted averages of two two-variable functions with the iterated weighted average of their product,
up to the product of the two oscillations.  This module turns that estimate into the statement the
low end of the chord sweep consumes: **the angular-velocity numerator of the doubly blurred needle
is positive** as soon as

* the *diagonal* — the weighted average of the individual (raw) numerators — is bounded below by
  some `κ > 0` (this is the geometric input, produced from the concave profile of the loop's lens by
  `Work.Drive.arcProf_angVel_margin`), and
* the two mismatch products `2 * (osc α) * (osc β')` and `2 * (osc β) * (osc α')` sum to less than
  `κ` (the analytic input, produced from the Lipschitz moduli of the loop in its two parameters).

The point of stating this assembly *abstractly* (in terms of four functions of the two window
parameters and the weight) is that all of the work of this module is pure integral calculus: the
instantiation to the chord sweep
(`α (u,v) = ⟪sweepLoopChamfer r D lam (ε - δ₂ v) (t - δ₁ u) - c', u⟫` and its three siblings) then
only has to supply the interface identities of `Work.Drive.needleNumerator` and the estimates.

* `Work.Drive.DoubleAverageData` — the integrability data needed to compare the two sides;
* `Work.Drive.doubleAverage_mul_sub_le` — `meanProd_bound₂` in the packaged form;
* `Work.Drive.diag_integral_eq` — the two ways of writing the diagonal term agree;
* `Work.Drive.needle_num_pos_of_diag_osc` — **the assembly**.
-/

noncomputable section
namespace Work.Drive

open scoped Real Topology intervalIntegral

/-- The integrability data needed by `Work.Drive.meanProd_bound₂` to compare the product of the
iterated weighted averages of `f` and `g` with the iterated weighted average of `f * g`.  All of it
is automatic when `f` and `g` are bounded on the window (`MeasureTheory.IntegrableOn.of_bound`), and
in the instantiation to the chord sweep it is the boundedness of the loop and of its velocity. -/
structure DoubleAverageData (b : ℝ → ℝ) (f g : ℝ → ℝ → ℝ) : Prop where
  slice_f : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ => b v * f u v) MeasureTheory.volume (-1) 1
  slice_g : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ => b v * g u v) MeasureTheory.volume (-1) 1
  slice_fg : ∀ u : ℝ,
    IntervalIntegrable (fun v : ℝ => b v * (f u v * g u v)) MeasureTheory.volume (-1) 1
  outer_f : IntervalIntegrable (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1, b v * f u v))
    MeasureTheory.volume (-1) 1
  outer_g : IntervalIntegrable (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1, b v * g u v))
    MeasureTheory.volume (-1) 1
  outer_fg : IntervalIntegrable (fun u : ℝ =>
      b u * ((∫ v in (-1 : ℝ)..1, b v * f u v) * (∫ v in (-1 : ℝ)..1, b v * g u v)))
    MeasureTheory.volume (-1) 1
  outer_slice_fg : IntervalIntegrable (fun u : ℝ =>
      b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v))) MeasureTheory.volume (-1) 1

/-- **`Work.Drive.meanProd_bound₂` in packaged form.**  If the integrability data of
`Work.Drive.DoubleAverageData` holds and the joint oscillations of `f` and `g` over the window are at
most `A` and `J`, then the product of the two iterated weighted averages differs from the iterated
weighted average of the product by at most `2 * (A * J)`. -/
theorem doubleAverage_mul_sub_le {b : ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {A J : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hd : DoubleAverageData b f g)
    (hA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |f u v - f u' v'| ≤ A)
    (hJ : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |g u v - g u' v'| ≤ J) :
    |(∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * f u v))
      * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * g u v))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v)))|
      ≤ 2 * (A * J) :=
  meanProd_bound₂ hb hb0 hb1 hd.slice_f hd.slice_g hd.slice_fg hd.outer_f hd.outer_g
    hd.outer_fg hd.outer_slice_fg hA hJ

/-- **The two ways of writing the diagonal term agree.**  The iterated weighted average
`∫ u, b u * (∫ v, b v * (f u v * g u v))` of a product of two two-variable functions is the double
integral of the product weight.  (No integrability is needed: both sides are integrals of pointwise
equal integrands, and the outer `b u` is a constant for the inner integral.) -/
theorem diag_integral_eq (b : ℝ → ℝ) (f g : ℝ → ℝ → ℝ) :
    (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v)))
      = ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, b u * b v * (f u v * g u v) := by
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun v _ => by ring)

/-- **The diagonal, in the form of a double integral with `b u * b v`, is the difference of the two
iterated averages.**  This is the passage from the geometric statement "every individual numerator
is at least `κ`" (whose weighted average is the double integral of the difference of the two
products) to the form consumed by the assembly. -/
theorem diag_integral_sub_eq {b : ℝ → ℝ} {f g h k : ℝ → ℝ → ℝ}
    (hd1 : DoubleAverageData b f g) (hd2 : DoubleAverageData b h k) :
    (∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, b u * b v * (f u v * g u v - h u v * k u v))
      = (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v)))
        - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (h u v * k u v))) := by
  -- pull the difference out of the inner integral
  have hinner : ∀ u : ℝ,
      (∫ v in (-1 : ℝ)..1, b u * b v * (f u v * g u v - h u v * k u v))
        = b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v))
          - b u * (∫ v in (-1 : ℝ)..1, b v * (h u v * k u v)) := by
    intro u
    rw [show (fun v : ℝ => b u * b v * (f u v * g u v - h u v * k u v))
        = (fun v : ℝ => b u * (b v * (f u v * g u v)) - b u * (b v * (h u v * k u v))) from by
      funext v; ring]
    rw [intervalIntegral.integral_sub ((hd1.slice_fg u).const_mul (b u))
      ((hd2.slice_fg u).const_mul (b u)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr (fun u _ => hinner u)]
  rw [intervalIntegral.integral_sub hd1.outer_slice_fg hd2.outer_slice_fg]

/-- **The angular-velocity numerator of a doubly blurred curve is positive**, from the diagonal
lower bound and the oscillation bounds.

Let `b` be a nonnegative weight of total mass `1` on `[-1,1]` (the blur bump), and let `α`, `β`
(resp. `α'`, `β'`) be the two coordinates of a family of curves (resp. of their velocities) over the
window `[-1,1]²`.  Write `P := ∫ u, b u * ∫ v, b v * α u v` and similarly `Q'`, `Q`, `P'` for `β'`,
`β`, `α'` — these are the two coordinates of the blurred curve and of its derivative.  If

* every individual numerator is at least `κ`: `κ ≤ ∫∫ b u b v (α β' - β α')`, and
* the oscillations satisfy `2 * (osc α) * (osc β') + 2 * (osc β) * (osc α') < κ`,

then the numerator `P * Q' - Q * P'` of the blurred curve is positive.

The proof is the three-term telescoping
`P Q' - Q P' = (P Q' - ∫∫ b b α β') + (∫∫ b b (α β' - β α')) + (∫∫ b b (β α') - Q P')`,
whose first and third terms are bounded by `Work.Drive.doubleAverage_mul_sub_le`. -/
theorem needle_num_pos_of_diag_osc {b : ℝ → ℝ} {α β α' β' : ℝ → ℝ → ℝ} {A B A' B' κ : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hd1 : DoubleAverageData b α β') (hd2 : DoubleAverageData b β α')
    (hA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |α u v - α u' v'| ≤ A)
    (hB : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |β u v - β u' v'| ≤ B)
    (hA' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |α' u v - α' u' v'| ≤ A')
    (hB' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |β' u v - β' u' v'| ≤ B')
    (hdiag : κ ≤ ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1,
      b u * b v * (α u v * β' u v - β u v * α' u v))
    (hlt : 2 * (A * B') + 2 * (B * A') < κ) :
    0 < (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
        * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β' u v))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
        * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α' u v)) := by
  have h12 := doubleAverage_mul_sub_le hb hb0 hb1 hd1 hA hB'
  have h21 := doubleAverage_mul_sub_le hb hb0 hb1 hd2 hB hA'
  have h12' := abs_le.mp h12
  have h21' := abs_le.mp h21
  have hdiag' : κ ≤ (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β' u v)))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (β u v * α' u v))) := by
    rw [← diag_integral_sub_eq hd1 hd2]
    exact hdiag
  have key : (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
        * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β' u v))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
        * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α' u v))
      = ((∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
            * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β' u v))
          - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β' u v))))
        + (((∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β' u v)))
            - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (β u v * α' u v))))
          + ((∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (β u v * α' u v)))
            - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
              * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α' u v)))) := by
    ring
  rw [key]
  linarith [h12'.1, h12'.2, h21'.1, h21'.2, hdiag', hlt]

end Work.Drive
