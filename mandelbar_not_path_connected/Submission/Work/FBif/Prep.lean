/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — preparation for the HS estimate at a simple parabolic parameter

This module fixes the auxiliary vocabulary of `Submission/Work/FBif/exists_HSExpansion.lean`
(the proof of Hubbard–Schleicher's Lemma 3.4 at a root-parabolic parameter, arXiv:1209.1753).

Write `p := Tantibar c`, so that `p(z) = z̄² + c` and `p^[5] = p ∘ Tsq^[2]` with
`Tsq c z = (z² + c̄)² + c` the holomorphic second iterate.  Then

* `star ∘ p^[5] = z ↦ (Tsq^[2] z)² + c̄`

is a *holomorphic polynomial* (`fPoly c`, of degree `32`).  Since `p^[5]` is antiholomorphic
and fixes `z₁`, its local expansion at `z₁` is

  `p^[5](z₁ + w) = z₁ + lam * w̄ + A₂ * w̄² + O(‖w‖³)`

with `lam = star ((fPoly c)'(z₁))` (`lamHS c z₁`) and `A₂ = star ((fPoly c)''(z₁))/2`
(`A2HS c z₁`).

## Contents

* `TsqPoly c`, `TsqPoly2 c`, `fPoly c` — `Tsq c`, `Tsq^[2]`, `star ∘ Tantibar c^[5]` as
  elements of `ℂ[X]`, with their evaluation identities;
* `poly_taylor_remainder` — the Taylor expansion of a polynomial with cubic remainder;
* `lamHS c z₁`, `A2HS c z₁` — the first and second Taylor coefficients of `p^[5]` at `z₁`;
* `fifthExpansion` — the expansion of `p^[5]` at `z₁` up to `O(‖w‖³)`;
* `lamHS_norm` — `‖lamHS‖ = 1` at a parabolic point with multiplier `1`;
* `lam_mul_star_eq`, `div_lam_mul_star`, `div_coeff` — the algebra of the normalised
  coordinate `z = z₁ + s u`;
* `simplicity_algebra`, `nonOrthogonality` — the algebra of the simplicity of the parabolic
  point;
* `perturb_iterate_fifth_at` — the exact value of the perturbed fifth iterate at `z₁`.
-/
import Mathlib
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Cycle
import Submission.Work.FBif.exists_goodPerturbation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open Polynomial

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## `Tsq`, `Tsq^[2]` and `star ∘ Tantibar^[5]` as polynomials -/

/-- The holomorphic second iterate `Tsq c z = (z² + c̄)² + c` as a polynomial. -/
noncomputable def TsqPoly (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)) ^ 2 + C c

theorem TsqPoly_eval (c z : ℂ) : (TsqPoly c).eval z = Work.Landing.Tsq c z := by
  simp [TsqPoly, Work.Landing.Tsq]

/-- `Tantibar c` squared is the holomorphic map `Tsq c`. -/
theorem Tantibar_iterate_two (c : ℂ) : (Tantibar c)^[2] = Work.Landing.Tsq c := by
  funext z
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar,
    Work.Landing.Tsq, starRingEnd_apply, star_add, star_pow, star_star]

/-- `Tsq^[2]` as a polynomial. -/
noncomputable def TsqPoly2 (c : ℂ) : ℂ[X] := (TsqPoly c).comp (TsqPoly c)

theorem TsqPoly2_eval (c z : ℂ) : (TsqPoly2 c).eval z = (Work.Landing.Tsq c)^[2] z := by
  rw [TsqPoly2, Polynomial.eval_comp]
  simp only [TsqPoly_eval]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  rfl

/-- `star ∘ Tantibar c^[5] = z ↦ (Tsq^[2] z)² + c̄`, the holomorphic polynomial whose value
at `z` is the conjugate of `p^[5](z)`. -/
noncomputable def fPoly (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)).comp (TsqPoly2 c)

theorem fPoly_eval (c z : ℂ) : (fPoly c).eval z = star ((Tantibar c)^[5] z) := by
  have h5 : (Tantibar c)^[5] z = Tantibar c (((Work.Landing.Tsq c)^[2]) z) := by
    rw [show (5 : ℕ) = 1 + 4 by norm_num, Function.iterate_add, Function.iterate_one]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, Function.iterate_mul, Tantibar_iterate_two]
    rfl
  rw [h5, fPoly, Polynomial.eval_comp, TsqPoly2_eval]
  rw [LeanEval.ComplexAnalysis.Tantibar, starRingEnd_apply]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    star_add, star_pow, star_star]

/-- The holomorphic polynomial `star ∘ Tantibar c^[5]` is differentiable everywhere. -/
theorem fPoly_differentiableAt (c z : ℂ) :
    DifferentiableAt ℂ (fun z => (fPoly c).eval z) z :=
  (Polynomial.differentiable (fPoly c)).differentiableAt

/-- The first Taylor coefficient of `Tantibar c^[5]` at `z₁` (the conjugate-linear
multiplier `lam` of HS §2). -/
noncomputable def lamHS (c z₁ : ℂ) : ℂ := star ((fPoly c).derivative.eval z₁)

/-- The second Taylor coefficient of `Tantibar c^[5]` at `z₁`. -/
noncomputable def A2HS (c z₁ : ℂ) : ℂ := star ((fPoly c).derivative.derivative.eval z₁) / 2

/-! ## Taylor expansion of a polynomial with cubic remainder -/

/-- `star` commutes with division. -/
private lemma star_div_star (a b : ℂ) : star (a / b) = star a / star b := by
  have h : (star : ℂ → ℂ) = (starRingEnd ℂ) := rfl
  rw [h, map_div₀, starRingEnd_apply, starRingEnd_apply]

/-- `star` commutes with division by `2`. -/
private lemma star_div_two (a : ℂ) : star (a / 2) = star a / 2 := by
  rw [star_div_star]
  norm_num

private lemma coeff_one_eq (p : ℂ[X]) : p.coeff 1 = (Polynomial.derivative p).coeff 0 := by
  rw [Polynomial.coeff_derivative]
  norm_num

private lemma coeff_two_eq (p : ℂ[X]) :
    p.coeff 2 = (Polynomial.derivative (Polynomial.derivative p)).coeff 0 / 2 := by
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
  norm_num

/-- **The Taylor expansion of a polynomial with cubic remainder.**  For `P : ℂ[X]` and
`v : ℂ` there is `C ≥ 0` with

`‖P(v+t) - P(v) - P'(v) t - (P''(v)/2) t²‖ ≤ C ‖t‖³`  for `‖t‖ ≤ 1`. -/
theorem poly_taylor_remainder (P : ℂ[X]) (v : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ ≤ 1 →
      ‖P.eval (v + t) - P.eval v - (P.derivative.eval v) * t
          - ((P.derivative.derivative).eval v / 2) * t ^ 2‖ ≤ C * ‖t‖ ^ 3 := by
  set Q : ℂ[X] := P - (C (P.eval v) + C (P.derivative.eval v) * (X - C v)
    + C ((P.derivative.derivative).eval v / 2) * (X - C v) ^ 2) with hQ
  -- substituting `X ↦ X + v` turns the Taylor part into the truncation of `P(X+v)`
  have hsub : Q.comp (X + C v) = P.comp (X + C v)
      - (C (P.eval v) + C (P.derivative.eval v) * X
          + C ((P.derivative.derivative).eval v / 2) * X ^ 2) := by
    rw [hQ]
    simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, Polynomial.pow_comp]
    ring
  -- the first three coefficients of the expansion of `P` at `v`
  have hW0 : (P.comp (X + C v)).coeff 0 = P.eval v := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add]
  have hd1 : Polynomial.derivative (P.comp (X + C v)) = P.derivative.comp (X + C v) := by
    rw [Polynomial.derivative_comp]
    simp
  have hW1 : (P.comp (X + C v)).coeff 1 = P.derivative.eval v := by
    rw [coeff_one_eq, hd1, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
  have hdd : Polynomial.derivative (Polynomial.derivative (P.comp (X + C v)))
      = (P.derivative.derivative).comp (X + C v) := by
    rw [hd1, Polynomial.derivative_comp]
    simp
  have hW2 : (P.comp (X + C v)).coeff 2 = (P.derivative.derivative).eval v / 2 := by
    rw [coeff_two_eq, hdd, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
  -- hence `X³ ∣ Q.comp (X + C v)`
  have hX3 : X ^ 3 ∣ Q.comp (X + C v) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [hsub]
    interval_cases d
    · simp [Polynomial.coeff_add, hW0]
    · simp [Polynomial.coeff_add, hW1]
    · simp [Polynomial.coeff_add, hW2]
  have hdvd : (X - C v) ^ 3 ∣ Q := by
    rw [Polynomial.X_sub_C_pow_dvd_iff]
    exact hX3
  obtain ⟨R, hR⟩ := hdvd
  refine ⟨∑ i ∈ R.support, ‖R.coeff i‖ * (‖v‖ + 1) ^ i, Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) i), fun t ht => ?_⟩
  have hQeval : Q.eval (v + t) = P.eval (v + t) - P.eval v - (P.derivative.eval v) * t
      - ((P.derivative.derivative).eval v / 2) * t ^ 2 := by
    rw [hQ]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  have hRsplit : Q.eval (v + t) = t ^ 3 * R.eval (v + t) := by
    rw [hR]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  have ht1 : ‖v + t‖ ≤ ‖v‖ + 1 := by
    calc ‖v + t‖ ≤ ‖v‖ + ‖t‖ := norm_add_le _ _
      _ ≤ ‖v‖ + 1 := by linarith
  have hRbound : ‖R.eval (v + t)‖ ≤ ∑ i ∈ R.support, ‖R.coeff i‖ * (‖v‖ + 1) ^ i := by
    rw [Polynomial.eval_eq_sum]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht1 i) (norm_nonneg _)
  rw [← hQeval, hRsplit, norm_mul, norm_pow]
  calc ‖t‖ ^ 3 * ‖R.eval (v + t)‖
      ≤ ‖t‖ ^ 3 * (∑ i ∈ R.support, ‖R.coeff i‖ * (‖v‖ + 1) ^ i) :=
        mul_le_mul_of_nonneg_left hRbound (by positivity)
    _ = (∑ i ∈ R.support, ‖R.coeff i‖ * (‖v‖ + 1) ^ i) * ‖t‖ ^ 3 := by ring

/-! ## The expansion of `Tantibar c^[5]` at the parabolic point -/

/-- **The expansion of `p^[5]` at `z₁`** (Hubbard–Schleicher arXiv:1209.1753 §2):
`p^[5](z₁ + w) = z₁ + lam w̄ + A₂ w̄² + O(‖w‖³)`. -/
theorem fifthExpansion (c z₁ : ℂ) (hper : (Tantibar c)^[5] z₁ = z₁) :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ δ →
      ‖(Tantibar c)^[5] (z₁ + w) - z₁ - lamHS c z₁ * star w
          - A2HS c z₁ * (star w) ^ 2‖ ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := poly_taylor_remainder (fPoly c) z₁
  refine ⟨1, one_pos, C, hC, fun w hw => ?_⟩
  have h := hbound w hw
  have hstar : ‖star (Polynomial.eval (z₁ + w) (fPoly c) - Polynomial.eval z₁ (fPoly c)
      - Polynomial.eval z₁ (Polynomial.derivative (fPoly c)) * w
      - Polynomial.eval z₁ (Polynomial.derivative (Polynomial.derivative (fPoly c))) / 2
        * w ^ 2)‖ ≤ C * ‖w‖ ^ 3 := by
    rw [norm_star]
    exact h
  have hinside : star (Polynomial.eval (z₁ + w) (fPoly c) - Polynomial.eval z₁ (fPoly c)
      - Polynomial.eval z₁ (Polynomial.derivative (fPoly c)) * w
      - Polynomial.eval z₁ (Polynomial.derivative (Polynomial.derivative (fPoly c))) / 2
        * w ^ 2)
      = (Tantibar c)^[5] (z₁ + w) - z₁ - lamHS c z₁ * star w
        - A2HS c z₁ * (star w) ^ 2 := by
    rw [star_sub, star_sub, star_sub, star_mul, star_mul, star_pow]
    rw [fPoly_eval, fPoly_eval]
    simp only [hper, star_star, star_div_two, lamHS, A2HS]
    ring
  rw [hinside] at hstar
  exact hstar

/-! ## The modulus of the conjugate-linear multiplier -/

/-- `Tantibar c^[5]` is `star` followed by the holomorphic polynomial `fPoly c`. -/
theorem star_comp_fPoly (c : ℂ) : star ∘ (fun z => (fPoly c).eval z) = (Tantibar c)^[5] := by
  funext z
  simp only [Function.comp_apply, fPoly_eval, star_star]

/-- `Tantibar c^[10] = Tsq c^[5]`. -/
theorem Tantibar_iterate_ten (c : ℂ) : (Tantibar c)^[10] = (Work.Landing.Tsq c)^[5] := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, Function.iterate_mul, Tantibar_iterate_two]

/-- **The conjugate-linear multiplier of `Tantibar c^[5]` at a parabolic point is a unit:**
`‖lamHS c z₁‖ = 1`, because the holomorphic second return map `Tsq c^[5]` has multiplier `1`. -/
theorem lamHS_norm (c z₁ : ℂ) (hper : (Tantibar c)^[5] z₁ = z₁)
    (hmult : deriv ((Work.Landing.Tsq c)^[5]) z₁ = 1) : ‖lamHS c z₁‖ = 1 := by
  have hf : DifferentiableAt ℂ (fun z => (fPoly c).eval z) z₁ := fPoly_differentiableAt c z₁
  have hx : star ((fun z => (fPoly c).eval z) z₁) = z₁ := by
    simp only
    rw [fPoly_eval, star_star, hper]
  have hkey := Work.Landing.Family.deriv_star_comp_self
    (f := fun z => (fPoly c).eval z) hf hx
  have hcomp : (star ∘ (fun z => (fPoly c).eval z)) ∘ (star ∘ (fun z => (fPoly c).eval z))
      = (Work.Landing.Tsq c)^[5] := by
    rw [star_comp_fPoly, ← Function.iterate_add]
    norm_num
    exact Tantibar_iterate_ten c
  rw [hcomp, hmult] at hkey
  have h1 : Complex.normSq (deriv (fun z => (fPoly c).eval z) z₁) = 1 := by
    exact_mod_cast hkey.symm
  rw [lamHS, norm_star, ← Polynomial.deriv (p := fPoly c) (x := z₁)]
  have h2 : ‖deriv (fun z => (fPoly c).eval z) z₁‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, h1]
  nlinarith [norm_nonneg (deriv (fun z => (fPoly c).eval z) z₁)]

/-! ## Coordinate algebra in the normalised coordinate `z = z₁ + s u` -/

/-- `s² = lam` and `‖s‖ = 1` force `lam * s̄ = s`. -/
theorem lam_mul_star_eq (lam s : ℂ) (hs : s ^ 2 = lam) (h1 : ‖s‖ = 1) :
    lam * star s = s := by
  have hss : s * star s = 1 := by
    have h := Complex.mul_conj s
    rw [Complex.normSq_eq_norm_sq, h1] at h
    norm_num at h
    exact h
  rw [← hs, pow_two, mul_assoc, hss, mul_one]

/-- `s² = lam` and `‖s‖ = 1` force `(lam s̄)/s = 1`: the linear part of the normalised
iterate is `ū`. -/
theorem div_lam_mul_star (lam s : ℂ) (hs : s ^ 2 = lam) (h1 : ‖s‖ = 1) :
    lam * star s / s = 1 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; norm_num at h1
  rw [lam_mul_star_eq lam s hs h1, div_self hs0]

/-- `s² = lam` and `‖s‖ = 1` force `(A (s̄)²)/s = A/(lam s)`: the quadratic coefficient of
the normalised iterate is `A = A₂/(lam s)`. -/
theorem div_coeff (A₂ lam s : ℂ) (hs : s ^ 2 = lam) (h1 : ‖s‖ = 1) :
    A₂ * (star s) ^ 2 / s = A₂ / (lam * s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; norm_num at h1
  have hss : star s * s = 1 := by
    have h := Complex.mul_conj s
    rw [Complex.normSq_eq_norm_sq, h1] at h
    norm_num at h
    rw [mul_comm]
    exact h
  have hstar : star s = s⁻¹ := eq_inv_of_mul_eq_one_left hss
  rw [hstar, ← hs]
  field_simp

/-! ## Simplicity of the parabolic point: the algebra -/

/-- **The algebra of the simplicity.**  If `‖lam‖ = 1` and `s² = lam`, then
`(lam Ā + A lam̄²) * s = 2 * Re(A/(lam s))`. -/
theorem simplicity_algebra (lam A₂ s : ℂ) (hs : s ^ 2 = lam) (h1 : ‖s‖ = 1) :
    (lam * star A₂ + A₂ * (star lam) ^ 2) * s
      = 2 * ((A₂ / (lam * s)).re : ℂ) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; norm_num at h1
  have hss : star s * s = 1 := by
    have h := Complex.mul_conj s
    rw [Complex.normSq_eq_norm_sq, h1] at h
    norm_num at h
    rw [mul_comm]
    exact h
  have hstar : star s = s⁻¹ := eq_inv_of_mul_eq_one_left hss
  rw [show 2 * ((A₂ / (lam * s)).re : ℂ) = A₂ / (lam * s) + star (A₂ / (lam * s)) from by
    have h := Complex.add_conj (A₂ / (lam * s))
    simp only [starRingEnd_apply] at h
    rw [h]; push_cast; ring]
  rw [star_div_star, star_mul, hstar, ← hs]
  rw [star_pow, hstar]
  field_simp
  ring

/-- **The non-orthogonality of `A₂` and `lam`.**  If `‖lam‖ = 1`, `s² = lam` and
`lam Ā₂ + A₂ lam̄² ≠ 0`, then `Re(A₂/(lam s)) ≠ 0`.

This is the form of the simplicity of the parabolic point used below: the second return map
`Tsq c^[5]` has nonvanishing second derivative exactly when `lam Ā₂ + A₂ lam̄² ≠ 0`, and then
the choice of the square root `s` of `lam` (there are two, giving `±A₂/(lam s)`) makes
`Re(A₂/(lam s)) > 0`. -/
theorem nonOrthogonality {lam A₂ s : ℂ} (h1 : ‖lam‖ = 1) (hs : s ^ 2 = lam)
    (hB : lam * star A₂ + A₂ * (star lam) ^ 2 ≠ 0) : (A₂ / (lam * s)).re ≠ 0 := by
  have hs1 : ‖s‖ = 1 := by
    have h : ‖s‖ ^ 2 = 1 := by
      rw [← norm_pow, hs, h1]
    nlinarith [norm_nonneg s]
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hs1; norm_num at hs1
  intro h
  refine hB ?_
  have hkey := simplicity_algebra lam A₂ s hs hs1
  rw [h] at hkey
  norm_num at hkey
  exact hkey.resolve_right hs0

/-! ## The perturbed fifth iterate at the parabolic point -/

/-- **The perturbed fifth iterate at `z₁` is exact.**  If `q = P(z̄)` vanishes at
`z₁, Tz₁, T²z₁, T³z₁`, then for every `ε`

`(T_c + ε q)^[5] z₁ = z₁ + ε q(T⁴ z₁)`.

No error term: the first four iterates coincide with those of `T_c`, because the perturbation
vanishes at the four cycle points `z₀, …, z₃` met on the way. -/
theorem perturb_iterate_fifth_at (c z₁ : ℂ) (P : ℂ[X]) (ε : ℝ)
    (hper : (Tantibar c)^[5] z₁ = z₁)
    (hvan : ∀ j : ℕ, j ≤ 3 → P.eval (star (cyclePt c z₁ j)) = 0) :
    (perturb c (fun z => P.eval (star z)) ε)^[5] z₁
      = z₁ + (ε : ℂ) * P.eval (star (cyclePt c z₁ 4)) := by
  have hk : ∀ k : ℕ, k ≤ 4 →
      (perturb c (fun z => P.eval (star z)) ε)^[k] z₁ = cyclePt c z₁ k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k ≤ 3 := by omega
      rw [Function.iterate_succ_apply', ih (by omega), perturb_apply, ← cyclePt_succ,
        hvan k hk', mul_zero, add_zero]
  rw [show (5 : ℕ) = 4 + 1 by norm_num, Function.iterate_succ_apply']
  simp only [hk 4 le_rfl, perturb_apply,
    show Tantibar c (cyclePt c z₁ 4) = z₁ from hper]

end Work.FBif

end
