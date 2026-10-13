/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/psiDSecondDeriv` — the second derivative of the angular bump `psiD δ`

The angular cut-off of the collar chain is
`psiD δ θ = ψ((θ - δ/4)/(δ/4)) · ψ(((π/2 - δ/4) - θ)/(δ/4))` with `ψ = Real.smoothTransition`,
a product of two bumps of width `δ/4`.  Its first two derivatives are computed explicitly by the
chain and product rules, and the second one is bounded by `Cψ / δ²` with a constant `Cψ`
independent of `δ` and `θ` (the two `δ⁻¹` factors of each chain rule give the `δ⁻²`).

The bounds on `deriv ψ` and `deriv (deriv ψ)` themselves come from
`Work.FTS.EllipticEst.PropL2CutKids.exists_bound_of_continuous_zero_off` (a continuous function
vanishing off `[0,1]` is bounded) together with the vanishing lemmas of
`Work.FTS.EllipticEst.PropL2CutKids.Wc_deriv_bdd`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.PropL2CutKids.Wc_deriv_bdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-! ### The second derivative of the angular bump `psiD δ`

`psiD δ θ = ψ((θ - δ/4)/(δ/4)) · ψ(((π/2 - δ/4) - θ)/(δ/4))` with `ψ = Real.smoothTransition`
is a product of two bumps of width `δ/4`, so its second derivative is `O(δ⁻²)`. -/

section PsiDSecondDeriv

private lemma differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 2)).differentiable (by norm_num)

/-- Chain rule for `y ↦ F ((y - a)/k)`. -/
private lemma hasDerivAt_div_sub_comp (F : ℝ → ℝ) (k a x : ℝ)
    (hF : DifferentiableAt ℝ F ((x - a) / k)) :
    HasDerivAt (fun y : ℝ => F ((y - a) / k)) (deriv F ((x - a) / k) * (1 / k)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - a) / k) (1 / k) x := by
    simpa using ((hasDerivAt_id' (x := x)).sub_const a).div_const k
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  rfl

/-- Chain rule for `y ↦ F ((c - y)/k)`. -/
private lemma hasDerivAt_sub_div_comp (F : ℝ → ℝ) (k c x : ℝ)
    (hF : DifferentiableAt ℝ F ((c - x) / k)) :
    HasDerivAt (fun y : ℝ => F ((c - y) / k)) (deriv F ((c - x) / k) * (-(1 / k))) x := by
  have h1 : HasDerivAt (fun y : ℝ => (c - y) / k) (-(1 / k)) x := by
    have h := ((hasDerivAt_const (x := x) c).sub (hasDerivAt_id' (x := x))).div_const k
    have hval : (0 - 1) / k = -(1 / k) := by ring
    rwa [hval] at h
  have h := (hF.hasDerivAt).comp x h1
  convert h using 1
  funext y
  rfl

/-- **The second derivative of the angular bump is `O(δ⁻²)`.** -/
theorem psiD_deriv2_bound_alt : ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ (δ : ℝ), 0 < δ → ∀ θ : ℝ,
    |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ Cψ / δ ^ 2 := by
  have hcont1 : Continuous (deriv Real.smoothTransition) := by
    have h : deriv Real.smoothTransition = iteratedDeriv 1 Real.smoothTransition := by
      rw [iteratedDeriv_one]
    rw [h]
    exact (Real.smoothTransition.contDiff (n := 2)).continuous_iteratedDeriv 1 (by norm_num)
  have hcont2 : Continuous (deriv (deriv Real.smoothTransition)) := by
    have h := (Real.smoothTransition.contDiff (n := 3)).continuous_iteratedDeriv 2 (by norm_num)
    have e : deriv (deriv Real.smoothTransition) = iteratedDeriv 2 Real.smoothTransition := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [e]
    exact h
  obtain ⟨S1, hS1nn, hS1⟩ :=
    Work.FTS.EllipticEst.PropL2CutKids.exists_bound_of_continuous_zero_off
      (deriv Real.smoothTransition) hcont1 (a := 0) (b := 1) (fun x hx => by
        rcases hx with h | h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv_smoothTransition_eq_zero_of_lt h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv_smoothTransition_eq_zero_of_gt h)
  obtain ⟨S2, hS2nn, hS2⟩ :=
    Work.FTS.EllipticEst.PropL2CutKids.exists_bound_of_continuous_zero_off
      (deriv (deriv Real.smoothTransition)) hcont2 (a := 0) (b := 1) (fun x hx => by
        rcases hx with h | h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv2_smoothTransition_eq_zero_of_lt h
        · exact Work.FTS.EllipticEst.PropL2CutKids.deriv2_smoothTransition_eq_zero_of_gt h)
  have hd2diff : Differentiable ℝ (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two
  refine ⟨16 * (2 * S2 + 2 * S1 ^ 2) + 1, by nlinarith [hS1nn, hS2nn], ?_⟩
  intro δ hδ θ
  have hk : (0 : ℝ) < δ / 4 := by linarith
  have hpsi_fun : Work.FTS.EllipticEst.AeColl.psiD δ
      = fun y : ℝ => Real.smoothTransition ((y - δ / 4) / (δ / 4))
          * Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4)) := by
    funext y
    exact Work.FTS.EllipticEst.AeColl.psiD_apply δ y
  -- the first derivative, as a function
  have hderiv_eq : deriv (Work.FTS.EllipticEst.AeColl.psiD δ)
      = fun y : ℝ => deriv Real.smoothTransition ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4))
            * Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
          + Real.smoothTransition ((y - δ / 4) / (δ / 4))
              * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
                  * (-(1 / (δ / 4)))) := by
    rw [hpsi_fun]
    funext y
    exact ((hasDerivAt_div_sub_comp Real.smoothTransition (δ / 4) (δ / 4) y
        (differentiable_smoothTransition.differentiableAt)).mul
      (hasDerivAt_sub_div_comp Real.smoothTransition (δ / 4) (Real.pi / 2 - δ / 4) y
        (differentiable_smoothTransition.differentiableAt))).deriv
  -- the derivatives of the four pieces of the first derivative
  have hP : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => deriv Real.smoothTransition ((z - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
      ((deriv (deriv Real.smoothTransition) ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
        * (1 / (δ / 4))) y := by
    intro y
    exact (hasDerivAt_div_sub_comp (deriv Real.smoothTransition) (δ / 4) (δ / 4) y
      (hd2diff.differentiableAt)).mul_const (1 / (δ / 4))
  have hQ : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => Real.smoothTransition (((Real.pi / 2 - δ / 4) - z) / (δ / 4)))
      (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
        * (-(1 / (δ / 4)))) y := fun y =>
    hasDerivAt_sub_div_comp Real.smoothTransition (δ / 4) (Real.pi / 2 - δ / 4) y
      (differentiable_smoothTransition.differentiableAt)
  have hR : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => Real.smoothTransition ((z - δ / 4) / (δ / 4)))
      (deriv Real.smoothTransition ((y - δ / 4) / (δ / 4)) * (1 / (δ / 4))) y := fun y =>
    hasDerivAt_div_sub_comp Real.smoothTransition (δ / 4) (δ / 4) y
      (differentiable_smoothTransition.differentiableAt)
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - z) / (δ / 4))
        * (-(1 / (δ / 4))))
      ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - y) / (δ / 4))
          * (-(1 / (δ / 4))))
        * (-(1 / (δ / 4)))) y := by
    intro y
    exact (hasDerivAt_sub_div_comp (deriv Real.smoothTransition) (δ / 4) (Real.pi / 2 - δ / 4) y
      (hd2diff.differentiableAt)).mul_const (-(1 / (δ / 4)))
  -- the second derivative
  have hsec : deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = ((deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
            * (1 / (δ / 4)))
          * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
        + (deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
          * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
        + ((deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * (1 / (δ / 4)))
          * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
        + Real.smoothTransition ((θ - δ / 4) / (δ / 4))
          * ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))
              * (-(1 / (δ / 4))))
            * (-(1 / (δ / 4))))) := by
    rw [hderiv_eq]
    exact (((hP θ).mul (hQ θ)).add ((hR θ).mul (hS θ))).deriv
  rw [hsec]
  -- the four summands of the second derivative
  set K : ℝ := 1 / (δ / 4) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKnn : 0 ≤ K := le_of_lt hKpos
  have hKsq : K ^ 2 = 16 / δ ^ 2 := by
    rw [hKdef, one_div, inv_div]
    ring
  set t1 : ℝ := ((deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4)) * K) * K)
      * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) with ht1def
  set t2 : ℝ := (deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4)) * K)
      * (deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) * (-K)) with ht2def
  set t4 : ℝ := Real.smoothTransition ((θ - δ / 4) / (δ / 4))
      * ((deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4)) * (-K))
        * (-K)) with ht4def
  have hb1 : |deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4))| ≤ S1 := hS1 _
  have hb2 : |deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ S1 := hS1 _
  have hb3 : |deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4))| ≤ S2 := hS2 _
  have hb4 : |deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ S2 :=
    hS2 _
  have hP1 : |Real.smoothTransition ((θ - δ / 4) / (δ / 4))| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hP2 : |Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have ht1b : |t1| ≤ S2 * K ^ 2 := by
    rw [ht1def]
    simp only [abs_mul, abs_of_nonneg hKnn]
    calc |deriv (deriv Real.smoothTransition) ((θ - δ / 4) / (δ / 4))| * K * K
          * |Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))|
        ≤ S2 * K * K * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hb3 le_rfl hKnn hS2nn) le_rfl hKnn
            (mul_nonneg hS2nn hKnn)) hP2 (abs_nonneg _) (by positivity)
      _ = S2 * K ^ 2 := by ring
  have ht2b : |t2| ≤ S1 ^ 2 * K ^ 2 := by
    rw [ht2def]
    simp only [abs_mul, abs_neg, abs_of_nonneg hKnn]
    calc |deriv Real.smoothTransition ((θ - δ / 4) / (δ / 4))| * K
          * (|deriv Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
        ≤ S1 * K * (S1 * K) := by
          refine mul_le_mul (mul_le_mul hb1 le_rfl hKnn hS1nn)
            (mul_le_mul hb2 le_rfl hKnn hS1nn) (by positivity) (by positivity)
      _ = S1 ^ 2 * K ^ 2 := by ring
  have ht4b : |t4| ≤ S2 * K ^ 2 := by
    rw [ht4def]
    simp only [abs_mul, abs_neg, abs_of_nonneg hKnn]
    calc |Real.smoothTransition ((θ - δ / 4) / (δ / 4))|
          * ((|deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
            * K)
        ≤ 1 * (S2 * (K * K)) := by
          refine mul_le_mul hP1 ?_ (by positivity) (by norm_num)
          calc ((|deriv (deriv Real.smoothTransition) (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))| * K)
                * K) ≤ (S2 * K) * K :=
                mul_le_mul_of_nonneg_right (mul_le_mul hb4 le_rfl hKnn hS2nn) hKnn
            _ = S2 * (K * K) := by ring
      _ = S2 * K ^ 2 := by ring
  have htri : |(t1 + t2) + (t2 + t4)| ≤ (|t1| + |t2|) + (|t2| + |t4|) :=
    (abs_add_le (t1 + t2) (t2 + t4)).trans
      (add_le_add (abs_add_le t1 t2) (abs_add_le t2 t4))
  calc |(t1 + t2) + (t2 + t4)| ≤ (|t1| + |t2|) + (|t2| + |t4|) := htri
    _ ≤ (S2 * K ^ 2 + S1 ^ 2 * K ^ 2) + (S1 ^ 2 * K ^ 2 + S2 * K ^ 2) :=
        add_le_add (add_le_add ht1b ht2b) (add_le_add ht2b ht4b)
    _ = (2 * S2 + 2 * S1 ^ 2) * K ^ 2 := by ring
    _ = (2 * S2 + 2 * S1 ^ 2) * (16 / δ ^ 2) := by rw [hKsq]
    _ = 16 * (2 * S2 + 2 * S1 ^ 2) / δ ^ 2 := by ring
    _ ≤ (16 * (2 * S2 + 2 * S1 ^ 2) + 1) / δ ^ 2 := by
        have hδ2 : 0 < δ ^ 2 := by positivity
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ2)

end PsiDSecondDeriv

end Work.FTS.EllipticEst.Deleg
