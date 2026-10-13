/-
Work module for the Elgindi finite-time singularity project: the `z`-integration by parts
identity on `Iz = [0, ∞)` for a function `g` supported in `[0, R]` and vanishing at `0`.

If `f` and `g` are differentiable on `(-1, ∞)` with continuous derivatives on `[0, R]`,
`g` vanishes for `x ≥ R`, `g'` vanishes for `x > R`, and `g 0 = 0`, then

  `∫_{Iz} g x * f' x = - ∫_{Iz} g' x * f x`.

# Route

`Iz = [0, R] ∪ (R, ∞)` and both integrands vanish identically on `(R, ∞)`, so the set
integrals over `Iz` are those over `[0, R]` (`setIntegral_Iz_eq_Icc`, proved from
`MeasureTheory.integral_union_eq_left_of_forall`).  On `[0, R]`, `intervalIntegral`'s
integration by parts (`integral_mul_deriv_eq_deriv_mul`) applied to `u = g`, `v = f`
gives

  `∫_0^R g f' = g R * f R - g 0 * f 0 - ∫_0^R g' f`,

and both boundary terms vanish, by `hgR R le_rfl` and `hg0`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
-- The statement's hypotheses `hf_cont` and `hg_cont` are not needed for the identity
-- (only continuity of the derivatives is), but they are part of the requested statement.
set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.Auxiliary

/-- A function vanishing on `(R, ∞)` (with `0 ≤ R`) has the same integral over
`Iz = [0, ∞)` as over `[0, R]`. -/
theorem setIntegral_Iz_eq_Icc {R : ℝ} (hR : 0 ≤ R) (h : ℝ → ℝ)
    (hh : ∀ x, R < x → h x = 0) :
    ∫ x in Work.Spaces.Iz, h x = ∫ x in Set.Icc (0 : ℝ) R, h x := by
  have hI : Work.Spaces.Iz = Set.Icc (0 : ℝ) R ∪ Set.Ioi R := by
    rw [Work.Spaces.Iz, ← Set.Icc_union_Ioi_eq_Ici hR]
  rw [hI]
  exact MeasureTheory.integral_union_eq_left_of_forall measurableSet_Ioi fun x hx => hh x hx

theorem zIBP1_fts (f f' g g' : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) (hf : ∀ x ∈ Set.Ioi (-1), HasDerivAt f (f' x) x) (hg : ∀ x ∈ Set.Ioi (-1), HasDerivAt g (g' x) x) (hf_cont : ContinuousOn f (Set.Icc 0 R)) (hf'_cont : ContinuousOn f' (Set.Icc 0 R)) (hg_cont : ContinuousOn g (Set.Icc 0 R)) (hg'_cont : ContinuousOn g' (Set.Icc 0 R)) (hgR : ∀ x, R ≤ x → g x = 0) (hgR' : ∀ x, R < x → g' x = 0) (hg0 : g 0 = 0) : ∫ x in Work.Spaces.Iz, g x * f' x = - ∫ x in Work.Spaces.Iz, g' x * f x := by
  -- On `uIcc 0 R = Icc 0 R` (as `0 ≤ R`) every point is `> -1`, where `f` and `g` are
  -- differentiable.
  have hmem : ∀ x ∈ Set.uIcc (0 : ℝ) R, x ∈ Set.Ioi (-1) := by
    intro x hx
    rw [Set.uIcc_of_le hR, Set.mem_Icc] at hx
    exact Set.mem_Ioi.mpr (by linarith [hx.1])
  have hg'c : ContinuousOn g' (Set.uIcc (0 : ℝ) R) := by rwa [Set.uIcc_of_le hR]
  have hf'c : ContinuousOn f' (Set.uIcc (0 : ℝ) R) := by rwa [Set.uIcc_of_le hR]
  -- Integration by parts on `[0, R]`.
  have hibp : ∫ x in Set.Icc (0 : ℝ) R, g x * f' x
      = - ∫ x in Set.Icc (0 : ℝ) R, g' x * f x := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := R)
      (u := g) (v := f) (u' := g') (v' := f')
      (fun x hx => hg x (hmem x hx)) (fun x hx => hf x (hmem x hx))
      hg'c.intervalIntegrable hf'c.intervalIntegrable
    rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR] at h
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc] at h
    simp only [hgR R le_rfl, hg0, zero_mul] at h
    simpa using h
  -- Both integrands vanish on `(R, ∞)`, so the integrals over `Iz` are those over `[0, R]`.
  rw [setIntegral_Iz_eq_Icc hR (fun x => g x * f' x)
        (fun x hx => by rw [hgR x (le_of_lt hx), zero_mul]),
      setIntegral_Iz_eq_Icc hR (fun x => g' x * f x)
        (fun x hx => by rw [hgR' x hx, zero_mul])]
  exact hibp

end Work.FTS.EllipticEst.Auxiliary
