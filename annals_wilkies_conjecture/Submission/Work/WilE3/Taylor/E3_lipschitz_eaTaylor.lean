import Mathlib
import Submission.Work.WilE3.API.eaTaylor_remainder

namespace Work.WilE3.Taylor

open Classical Topology
open WilkiesDesign.E

/-!
## Bounds for the truncated Taylor polynomial of an EA function

`eaTaylor c Q N y x` is the value at `x` of a polynomial in `x` (a sum of monomials in the
differences `x i - y i`, of total degree `≤ N`, with coefficients `eaEval c (eaDmulti c m Q) y`
that do not depend on `x`).  Every polynomial is locally Lipschitz, so the target statement is
elementary, but the constant must be produced explicitly.  We obtain it by induction on `N`,
using the mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the closed
ball of radius `R` together with the two facts already recorded in the API layer:

* `Work.WilE3.API.fderiv_eaTaylor` gives the derivative of `eaTaylor c Q (N+1) y` as
  `∑ i, eaTaylor c (eaD c i Q) N y z • proj i`;
* `Work.WilE3.API.norm_sum_smul_proj_le` bounds the norm of such a combination of projections.

The two steps are:

* `eaTaylor_norm_le_on_ball`: for every order `N` and every EA polynomial, `|eaTaylor c Q N y x|` is
  bounded on the closed ball of radius `R` around `y` by a constant depending on `N`, `c`, `Q`, `y`,
  `R` (induction on `N`; the step is the mean value inequality with the derivative bound coming from
  the induction hypothesis);
* `eaTaylor_lipschitz_of_norm_le_on_ball`: the Lipschitz statement at order `N + 1`, obtained the
  same way from the value bound at order `N`.

The target theorem is the second step, with the base case `N = 0` (a constant function) separate.
-/

/-- **Value bound.**  On the closed ball of radius `R` around `y`, the truncated Taylor polynomial
of order `N` of `eaEval c Q` is bounded by an explicit constant: the induction is on `N`, and the
step is the mean value inequality applied to the function `z ↦ eaTaylor c Q (n+1) y z`, whose
derivative is a combination of the order-`n` polynomials of the derivatives `eaD c i Q`. -/
theorem eaTaylor_norm_le_on_ball {k r : ℕ} (N : ℕ) :
    ∀ (c : EAChain k r) (Q : EAPoly k r) (y : Fin k → ℝ) (R : ℝ), 0 ≤ R →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin k → ℝ, dist x y ≤ R → |eaTaylor c Q N y x| ≤ B := by
  induction N with
  | zero =>
    intro c Q y R _hR
    exact ⟨|eaEval c Q y|, abs_nonneg _,
      fun x _ => by rw [Work.WilE3.API.eaTaylor_zero]⟩
  | succ n ih =>
    intro c Q y R hR
    have hbdd : ∀ i : Fin k, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z : Fin k → ℝ, dist z y ≤ R → |eaTaylor c (eaD c i Q) n y z| ≤ B :=
      fun i => ih c (eaD c i Q) y R hR
    choose B hB0 hB using hbdd
    refine ⟨(∑ i, B i) * R + |eaEval c Q y|,
      add_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hB0 i) hR) (abs_nonneg _), ?_⟩
    intro x hx
    have hMVT := (convex_closedBall y R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => eaTaylor c Q (n + 1) y z)
      (f' := fun z : Fin k → ℝ => ∑ i : Fin k, (eaTaylor c (eaD c i Q) n y z) •
          (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
      (s := Metric.closedBall y R) (x := y) (y := x) (C := ∑ i, B i)
      (fun z _ => (Work.WilE3.API.fderiv_eaTaylor c Q n y z).hasFDerivWithinAt)
      (fun z hz => by
        calc ‖∑ i : Fin k, (eaTaylor c (eaD c i Q) n y z) •
              (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)‖
            ≤ ∑ i, |eaTaylor c (eaD c i Q) n y z| := Work.WilE3.API.norm_sum_smul_proj_le _
          _ ≤ ∑ i, B i :=
              Finset.sum_le_sum fun i _ => hB i z (Metric.mem_closedBall.mp hz))
      (Metric.mem_closedBall.mpr (by rw [dist_self]; exact hR))
      (Metric.mem_closedBall.mpr hx)
    have hstep : |eaTaylor c Q (n + 1) y x - eaEval c Q y| ≤ (∑ i, B i) * R := by
      have h1 : ‖(fun z => eaTaylor c Q (n + 1) y z) x - (fun z => eaTaylor c Q (n + 1) y z) y‖
          = |eaTaylor c Q (n + 1) y x - eaEval c Q y| := by
        simp [Real.norm_eq_abs, Work.WilE3.API.eaTaylor_self]
      rw [h1, ← dist_eq_norm x y] at hMVT
      exact le_trans hMVT (mul_le_mul_of_nonneg_left hx (Finset.sum_nonneg fun i _ => hB0 i))
    calc |eaTaylor c Q (n + 1) y x|
        = |(eaTaylor c Q (n + 1) y x - eaEval c Q y) + eaEval c Q y| := by
          congr 1; ring
      _ ≤ |eaTaylor c Q (n + 1) y x - eaEval c Q y| + |eaEval c Q y| := abs_add_le _ _
      _ ≤ (∑ i, B i) * R + |eaEval c Q y| := add_le_add hstep le_rfl

/-! ### The target -/

/-- `eaTaylor c Q N y : (Fin k → ℝ) → ℝ` is the truncation at order `N` of the Taylor expansion of
the EA function `eaEval c Q` at the centre `y` (`WilkiesDesign.E.eaTaylor`).  The claim is that it is
Lipschitz on the ball of radius `R` around `y`, with a constant that may depend on everything.  It is
the "polynomial part" estimate used in the `(⇐)` direction of `E3_taylor_closure`: when `x` is moved
to a nearby point `z ∈ Z` of the zero set of the equations, the Taylor polynomial of a strict
inequality `g > 0` must not decrease by more than `Λ · dist z x`. -/
theorem E3_lipschitz_eaTaylor {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Q : WilkiesDesign.E.EAPoly k r) (N : ℕ) (y : Fin k → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x x' : Fin k → ℝ, dist x y ≤ R → dist x' y ≤ R →
      |WilkiesDesign.E.eaTaylor c Q N y x' - WilkiesDesign.E.eaTaylor c Q N y x|
        ≤ C * dist x' x := by
  cases N with
  | zero =>
    -- the order-`0` Taylor polynomial is the constant `eaEval c Q y`
    refine ⟨0, le_refl 0, fun x x' _ _ => ?_⟩
    rw [Work.WilE3.API.eaTaylor_zero c Q y x', Work.WilE3.API.eaTaylor_zero c Q y x,
      sub_self, abs_zero, zero_mul]
  | succ n =>
    -- the order-`n+1` polynomial has derivative `∑ i, eaTaylor c (eaD c i Q) n y z • proj i`,
    -- whose norm is bounded on the ball by the value bound at order `n`
    have hbdd : ∀ i : Fin k, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z : Fin k → ℝ, dist z y ≤ R → |eaTaylor c (eaD c i Q) n y z| ≤ B :=
      fun i => eaTaylor_norm_le_on_ball n c (eaD c i Q) y R hR
    choose B hB0 hB using hbdd
    refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB0 i, fun x x' hx hx' => ?_⟩
    have hMVT := (convex_closedBall y R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => eaTaylor c Q (n + 1) y z)
      (f' := fun z : Fin k → ℝ => ∑ i : Fin k, (eaTaylor c (eaD c i Q) n y z) •
          (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
      (s := Metric.closedBall y R) (x := x) (y := x') (C := ∑ i, B i)
      (fun z _ => (Work.WilE3.API.fderiv_eaTaylor c Q n y z).hasFDerivWithinAt)
      (fun z hz => by
        calc ‖∑ i : Fin k, (eaTaylor c (eaD c i Q) n y z) •
              (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)‖
            ≤ ∑ i, |eaTaylor c (eaD c i Q) n y z| := Work.WilE3.API.norm_sum_smul_proj_le _
          _ ≤ ∑ i, B i :=
              Finset.sum_le_sum fun i _ => hB i z (Metric.mem_closedBall.mp hz))
      (Metric.mem_closedBall.mpr hx)
      (Metric.mem_closedBall.mpr hx')
    calc |eaTaylor c Q (n + 1) y x' - eaTaylor c Q (n + 1) y x|
        = ‖(fun z => eaTaylor c Q (n + 1) y z) x' - (fun z => eaTaylor c Q (n + 1) y z) x‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ (∑ i, B i) * ‖x' - x‖ := hMVT
      _ = (∑ i, B i) * dist x' x := by rw [dist_eq_norm]

end Work.WilE3.Taylor
