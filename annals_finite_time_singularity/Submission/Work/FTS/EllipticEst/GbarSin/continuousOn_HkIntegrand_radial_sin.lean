/-
Copyright: work module for the Elgindi finite-time singularity project.

# Continuity of the `ℋ^k`-integrand of `R(z)·sin 2θ`

The `ℋ^k`-integrand (`Work.Spaces.HkIntegrand`) of a separated function
`(z,θ) ↦ R(z)·sin 2θ` is a finite sum of squares of the iterated derivatives
`D_z^i (R·sin 2θ)` and `D_z^j D_θ^i (R·sin 2θ)`, multiplied by the weights
`w(z)/sin(2θ)^{η/2}` resp. `Wt α z θ`.  Since both operators respect the product
structure of the function, those derivatives factor as

* `D_z^i (R·sin 2θ) = (rDzIter i R)(z)·sin 2θ` (`DzIter_mul_of_radial`), and
* `D_z^j D_θ^i (R·sin 2θ) = (rDzIter j R)(z)·sinIter i θ` (`mixed_radial_sin` below),

so on the open quadrant `Q0 = (0,∞) × (0,π/2)` the integrand is a sum of products of a
function of `z` alone — the radial iterate `rDzIter i R`, assumed continuous on `(0,∞)`
for `i ≤ k` — and a continuous function of `θ` (the angular profile `sinIter i`, or
`sin 2θ`).  This makes the continuity immediate; besides the stated continuity of the
radial iterates no regularity of `R` is used.

The file also records the two continuity facts for the angular profile `sinIter i` and
for the weight `Wt α` that the argument needs.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Polynomial
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllipticEst.DthIter_mul_of_angular
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular profile `sinIter i` is continuous -/

/-- `sinIter i = D_θ^i (sin 2θ)` is a continuous (indeed smooth) function of the angle:
it equals `sin(2θ)·pᵢ(cos 2θ)` for the polynomial `pᵢ = sinPoly i` (`sinIter_eq_sinPoly`). -/
theorem continuous_sinIter (i : ℕ) : Continuous (sinIter i) := by
  have hpoly : Continuous (fun t : ℝ => (sinPoly i).eval t) := Polynomial.continuous _
  have hfun : sinIter i
      = fun θ : ℝ => Real.sin (2 * θ) * (sinPoly i).eval (Real.cos (2 * θ)) := by
    funext θ
    exact sinIter_eq_sinPoly i θ
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
    (hpoly.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))

/-- The uncurried angular profile is continuous on the open quadrant. -/
theorem continuousOn_sinIter_Q0 (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => sinIter i p.2) Q0 :=
  (continuous_sinIter i).continuousOn.comp continuousOn_snd (fun _ _ => Set.mem_univ _)

/-! ## The mixed derivative of a radial profile times `sin 2θ` -/

/-- **`D_θ` and `D_z` respect the product `R(z)·sin 2θ`**:
`D_z^j D_θ^i (R(z)·sin 2θ) = (rDzIter j R)(z) · sinIter i θ`.  The statement is
unconditional in the differentiability of `R`: Lean's `deriv` is junk-tolerant, and both
sides carry the same junk where `R` fails to be differentiable. -/
theorem mixed_radial_sin (R : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => R z * Real.sin (2 * θ)) z θ
      = rDzIter j R z * sinIter i θ := by
  rw [Work.Spaces.mixed]
  have h1 : Work.Spaces.DthIter i (fun z θ => R z * Real.sin (2 * θ))
      = fun z θ => R z * sinIter i θ := by
    funext z θ
    rw [DthIter_mul_of_angular]
    rfl
  rw [h1]
  exact DzIter_mul_of_radial j R (sinIter i) z θ

/-! ## The weight `Wt` is continuous on the open quadrant -/

/-- `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant, where
`z ≠ 0` and `sin(2θ) > 0`. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-! ## The main lemma -/

/-- **Continuity of the `ℋ^k`-integrand of `R(z)·sin 2θ` on the open quadrant.**

The integrand factors, on `Q0`, as the explicit finite sum
`∑_{i≤k} ((rDzIter i R)(z)·sin 2θ · w(z)/sin(2θ)^{η/2})²
 + ∑_{i,j≤k} [(1 ≤ i ∧ i+j ≤ k)] ((rDzIter j R)(z)·sinIter i θ·Wt α z θ)²`,
which is manifestly continuous there because the `rDzIter i R` are continuous on `(0,∞)`
for `i ≤ k` (hypothesis), `sinIter i` is continuous in `θ`, and the weights `w`,
`sin(2θ)^{η/2}`, `Wt α` are continuous on `Q0`. -/
theorem continuousOn_HkIntegrand_radial_sin (α : ℝ) (k : ℕ) (R : ℝ → ℝ)
    (hR : ∀ i ≤ k, ContinuousOn (Work.FTS.EllipticEst.rDzIter i R) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  change ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) p.1 p.2) Q0
  have hRc : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => rDzIter i R p.1) Q0 := fun i hi =>
    (hR i hi).comp continuousOn_fst (fun p hp => hp.1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 := by fun_prop
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (rDzIter i R p.1 * Real.sin (2 * p.2)
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (rDzIter j R p.1 * sinIter i p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0)) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ fun i hi => ?_
      exact (((hRc i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul hsin).mul
        continuousOn_wdivsin_Q0).pow 2
    · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact (((hRc j (by omega)).mul (continuousOn_sinIter_Q0 i)).mul
          (continuousOn_Wt_Q0 α)).pow 2
      · simp only [if_neg hc]
        exact continuousOn_const
  · intro p hp
    simp only [Work.Spaces.HkIntegrand]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [DzIter_mul_of_radial i R (fun θ => Real.sin (2 * θ)) p.1 p.2]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc, mixed_radial_sin R j i p.1 p.2]
      · simp only [if_neg hc]

end Work.FTS.EllipticEst.GbarSin
