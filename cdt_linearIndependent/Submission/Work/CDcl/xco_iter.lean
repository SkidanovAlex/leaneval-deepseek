import Mathlib
import Submission.Work.CDcl.xrel_defs

/-!
# `T k = A^k (T 0)` in `ℚ((x))`

`Submission/Work/CDcl/setup.lean` defines the pullbacks `T k = (G^{(k)})∘y` of the derivatives of
`G = Sym⁺(logP …)` along the symmetrization coordinate `y = x²/(x−1)`, and
`Submission/Work/CDcl/xrel_defs.lean` transfers them to the field `LF = ℚ((x))` of Laurent-ish
series, where the `y`-derivative acts as `Aop f = ρ · f'` with `ρ = dx/dy = (x−1)²/(x(x−2))`.

The content of this file is the chain rule

  `Aop (g∘y) = g'∘y`      (in `LF`, for `g : ℚ⟦X⟧`),

which rests on the single scalar identity `ρ · y' = 1` (the definitions of `ρ` and `y` are
reciprocal), and the resulting iteration

  `Aop^[k] (Φ (g ∘ y)) = Φ ((d/dX)^[k] g ∘ y)`.

Applying this with `g = G0 a b ra rb rab r0` gives `Aop^[k] (Tfun … 0) = Tfun … k`.
-/

noncomputable section

open PowerSeries

namespace Work.CDcl

/-! ## Two scalar identities -/

/-- `(X−1)⁻¹·(X−1) = 1` in `ℚ⟦X⟧`. -/
lemma xco_XsubOne_inv_mul :
    (((X : PowerSeries ℚ) - 1)⁻¹) * ((X : PowerSeries ℚ) - 1) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

/-- The `x`-derivative of the symmetrization coordinate `y = x²/(x−1)`:
`y' = X·(X−2)·(X−1)⁻²`. -/
lemma xco_sympY_deriv : (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY =
    (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
  let W : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹
  have hunit : W * ((X : PowerSeries ℚ) - 1) = 1 := by
    dsimp [W]
    exact xco_XsubOne_inv_mul
  have hW : (PowerSeries.derivative (R := ℚ)) W = -(W ^ 2) := by
    dsimp [W]
    rw [PowerSeries.derivative_inv']
    simp
  have h2m : 2 - (X : PowerSeries ℚ) * W = W * ((X : PowerSeries ℚ) - 2) := by
    have h0 : W * ((X : PowerSeries ℚ) - 2) - (2 - (X : PowerSeries ℚ) * W) = 0 := by
      have h : W * ((X : PowerSeries ℚ) - 2) - (2 - (X : PowerSeries ℚ) * W)
          = 2 * (W * ((X : PowerSeries ℚ) - 1) - 1) := by ring
      rw [h, hunit]
      ring
    exact (sub_eq_zero.mp h0).symm
  have hdefY : Submission.CDT.sympY = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) * W) := by
    dsimp [W]
    rfl
  calc (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY
      = (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) * W)) := by
          rw [hdefY]
    _ = (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) * W)
          + (X : PowerSeries ℚ) * W := by
          rw [Derivation.leibniz]
          simp
    _ = (X : PowerSeries ℚ)
          * ((X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) W + W)
          + (X : PowerSeries ℚ) * W := by
          rw [Derivation.leibniz]
          simp
    _ = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) * (-(W ^ 2)) + W)
          + (X : PowerSeries ℚ) * W := by
          rw [hW]
    _ = (X : PowerSeries ℚ) * W * (2 - (X : PowerSeries ℚ) * W) := by ring
    _ = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2 := by
          rw [h2m]
          ring
    _ = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
          dsimp [W]

/-! ## The image of `ρ` in `LF` and the scalar identity `ρ · y' = 1` -/

/-- `ρ = (x−1)²/(x(x−2))` in `ℚ((x))`, written in terms of the image of `X`. -/
lemma xco_rhoL :
    rhoL = (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1) ^ 2
      / (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ)
          * (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 2)) := by
  simp only [rhoL, rhoK, xK, toL_div, map_pow, map_mul, map_sub, toL_X, map_one, map_ofNat]

/-- `Φ (y') = (Φ X)(Φ X − 2)(Φ X − 1)⁻²`, where `Φ : ℚ⟦X⟧ → ℚ((x))` is the inclusion. -/
lemma xco_algebraMap_deriv_sympY :
    algebraMap (PowerSeries ℚ) LF ((PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY)
      = (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ)
          * (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 2))
        * ((algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
  have hΦne : ∀ f : PowerSeries ℚ, f ≠ 0 → algebraMap (PowerSeries ℚ) LF f ≠ 0 := by
    intro f hf h
    exact hf (IsFractionRing.injective (PowerSeries ℚ) LF (by rw [h, map_zero]))
  have hinv : algebraMap (PowerSeries ℚ) LF (((X : PowerSeries ℚ) - 1)⁻¹)
      = (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1)⁻¹ := by
    have hsub : algebraMap (PowerSeries ℚ) LF ((X : PowerSeries ℚ) - 1)
        = algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1 := by rw [map_sub, map_one]
    have h : algebraMap (PowerSeries ℚ) LF (((X : PowerSeries ℚ) - 1)⁻¹)
        * (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1) = 1 := by
      rw [← hsub, ← map_mul, xco_XsubOne_inv_mul, map_one]
    exact eq_inv_of_mul_eq_one_left h
  rw [xco_sympY_deriv]
  simp only [map_mul, map_pow, map_sub, map_ofNat, hinv]

/-- Field bookkeeping: `A²/B · (B·(A⁻¹)²) = 1`. -/
private lemma xco_field_alg {F : Type*} [Field F] (A B : F) (hA : A ≠ 0) (hB : B ≠ 0) :
    A ^ 2 / B * (B * (A⁻¹) ^ 2) = 1 := by
  rw [div_eq_mul_inv, inv_pow]
  rw [show A ^ 2 * B⁻¹ * (B * (A ^ 2)⁻¹) = A ^ 2 * (A ^ 2)⁻¹ * (B⁻¹ * B) by ring]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hA), inv_mul_cancel₀ hB, mul_one]

/-- **The scalar identity `ρ · y' = 1` in `ℚ((x))`** — the definitions `ρ = (x−1)²/(x(x−2))` and
`y = x²/(x−1)` are reciprocal, so `dy/dx = 1/ρ`. -/
lemma xco_rhoL_mul_deriv_sympY :
    rhoL * algebraMap (PowerSeries ℚ) LF ((PowerSeries.derivative (R := ℚ)) Submission.CDT.sympY) = 1 := by
  have hΦne : ∀ f : PowerSeries ℚ, f ≠ 0 → algebraMap (PowerSeries ℚ) LF f ≠ 0 := by
    intro f hf h
    exact hf (IsFractionRing.injective (PowerSeries ℚ) LF (by rw [h, map_zero]))
  have hX : algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) ≠ 0 := by
    refine hΦne (X : PowerSeries ℚ) ?_
    intro h
    have hh := congrArg (PowerSeries.coeff 1) h
    simp at hh
  have hX1 : algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 1 ≠ 0 := by
    have h := hΦne ((X : PowerSeries ℚ) - 1) (by
      intro h
      have hh := congrArg PowerSeries.constantCoeff h
      simp at hh)
    simpa [map_sub, map_one] using h
  have hX2 : algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) *
      (algebraMap (PowerSeries ℚ) LF (X : PowerSeries ℚ) - 2) ≠ 0 := by
    refine mul_ne_zero hX ?_
    have h := hΦne ((X : PowerSeries ℚ) - 2) (by
      intro h
      have hh := congrArg PowerSeries.constantCoeff h
      simp [map_ofNat] at hh)
    simpa [map_sub, map_ofNat] using h
  rw [xco_rhoL, xco_algebraMap_deriv_sympY]
  exact xco_field_alg _ _ hX1 hX2

/-! ## The chain rule and the iteration -/

/-- **Chain rule**: on the image of `ℚ⟦X⟧`, `Aop` is `d/dX` (with the variable change `y`). -/
lemma xco_chain (g : PowerSeries ℚ) :
    Aop (algebraMap (PowerSeries ℚ) LF (g.subst Submission.CDT.sympY))
      = algebraMap (PowerSeries ℚ) LF
          (((PowerSeries.derivative (R := ℚ)) g).subst Submission.CDT.sympY) := by
  rw [Aop, dL_algebraMap, PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst, map_mul]
  linear_combination (algebraMap (PowerSeries ℚ) LF
    (((PowerSeries.derivative (R := ℚ)) g).subst Submission.CDT.sympY)) * xco_rhoL_mul_deriv_sympY

/-- **Iterated chain rule**: `Aop^[k] (g∘y) = (g^{(k)})∘y`. -/
lemma xco_iter_aux (g : PowerSeries ℚ) (k : ℕ) :
    Aop^[k] (algebraMap (PowerSeries ℚ) LF (g.subst Submission.CDT.sympY))
      = algebraMap (PowerSeries ℚ) LF
          (((PowerSeries.derivative (R := ℚ))^[k] g).subst Submission.CDT.sympY) := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Aop, dL_algebraMap,
        PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst, map_mul]
      linear_combination (algebraMap (PowerSeries ℚ) LF
        (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))^[n] g)).subst
          Submission.CDT.sympY)) * xco_rhoL_mul_deriv_sympY

/-- `T k = A^k (T 0)`: the pullbacks of the iterated derivatives of `G` are the iterates of the
`y`-derivative `Aop` applied to `T 0`. -/
theorem xco_iter (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Aop^[k] (Tfun a b ra rb rab r0 0) = Tfun a b ra rb rab r0 k := by
  simpa only [Tfun, T, Function.iterate_zero_apply] using xco_iter_aux (G0 a b ra rb rab r0) k

end Work.CDcl
