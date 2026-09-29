import Mathlib
import Submission.Work.CDcl.xrel_defs

/-!
# The order-two ODE for `P = logP a b ra rb rab r0` inside `ℚ((x))`

This lifts `Submission.CDT.logP_ode` (the paper's equation (ODE),
`P₂·P'' + P₁·P' + P₀·P = p` for the unlikely `G`-function `logP`) to the fraction
field `LF = ℚ((x)) = Frac ℚ⟦x⟧` of `Submission.Work.CDcl`, where the polynomial
coefficients `P₂, P₁, P₀, p` become invertible by the leading coefficient `P₂`.

The result is exactly the normal form used by the reduction of the pullbacks:
`P'' = α·P' + β·P + γ` with `α = -P₁/P₂`, `β = -P₀/P₂`, `γ = p/P₂`.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

local notation "Φ" => algebraMap (PowerSeries ℚ) LF

/-! ## The polynomial coefficients of `M` are the `logPA*` series -/

lemma coe_p2poly (a b : ℚ) :
    ((p2poly a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP2 a b := by
  simp only [p2poly, Submission.CDT.logPAP2, q4poly, Submission.CDT.logPAQ4,
    Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X]

lemma coe_p0poly (a b : ℚ) :
    ((p0poly a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP0 a b := by
  simp only [p0poly, Submission.CDT.logPAP0, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X]

lemma coe_p1poly (a b : ℚ) :
    ((p1poly a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP1 a b := by
  have h3 : ((3 : Polynomial ℚ) : PowerSeries ℚ) = (3 : PowerSeries ℚ) := by
    rw [show (3 : Polynomial ℚ) = Polynomial.C (3 : ℚ) from rfl, Polynomial.coe_C]
    exact map_ofNat PowerSeries.C 3
  have hm1 : ((-1 : Polynomial ℚ) : PowerSeries ℚ) = (-1 : PowerSeries ℚ) := by
    rw [show (-1 : Polynomial ℚ) = -(1 : Polynomial ℚ) from rfl, Polynomial.coe_neg,
      Polynomial.coe_one]
  simp only [p1poly, Submission.CDT.logPAP1, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X]
  rw [h3, hm1]

lemma coe_ppoly (a b : ℚ) (ra rb rab r0 : ℤ) :
    ((ppoly a b ra rb rab r0 : Polynomial ℚ) : PowerSeries ℚ)
      = PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
        + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
        + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b := by
  simp only [ppoly, Submission.CDT.RaFam, Submission.CDT.RbFam, Submission.CDT.RabFam,
    Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X]
  simp only [map_mul, map_add, map_neg, map_one, map_ofNat]
  ring_nf

lemma p2poly_ne_zero (a b : ℚ) : p2poly a b ≠ 0 := by
  show (Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1) * q4poly a b ≠ 0
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · simpa using (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero
  · exact Polynomial.X_ne_zero
  · simpa using (Polynomial.monic_X_add_C (1 : ℚ)).ne_zero
  · intro h
    have := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    simp [q4poly] at this

/-! ## `p•K = algebraMap ℚ[x] ℚ(x) p•` -/

lemma p2K_eq (a b : ℚ) : p2K a b = algebraMap (Polynomial ℚ) K (p2poly a b) := by
  have h := Polynomial.eval₂_algebraMap_X (p2poly a b)
    ((Algebra.ofId (Polynomial ℚ) K).restrictScalars ℚ)
  simp only [AlgHom.coe_restrictScalars', Algebra.ofId_apply, RatFunc.algebraMap_X] at h
  unfold p2K xK
  exact h

lemma p1K_eq (a b : ℚ) : p1K a b = algebraMap (Polynomial ℚ) K (p1poly a b) := by
  have h := Polynomial.eval₂_algebraMap_X (p1poly a b)
    ((Algebra.ofId (Polynomial ℚ) K).restrictScalars ℚ)
  simp only [AlgHom.coe_restrictScalars', Algebra.ofId_apply, RatFunc.algebraMap_X] at h
  unfold p1K xK
  exact h

lemma p0K_eq (a b : ℚ) : p0K a b = algebraMap (Polynomial ℚ) K (p0poly a b) := by
  have h := Polynomial.eval₂_algebraMap_X (p0poly a b)
    ((Algebra.ofId (Polynomial ℚ) K).restrictScalars ℚ)
  simp only [AlgHom.coe_restrictScalars', Algebra.ofId_apply, RatFunc.algebraMap_X] at h
  unfold p0K xK
  exact h

lemma pK_eq (a b : ℚ) (ra rb rab r0 : ℤ) :
    pK a b ra rb rab r0 = algebraMap (Polynomial ℚ) K (ppoly a b ra rb rab r0) := by
  have h := Polynomial.eval₂_algebraMap_X (ppoly a b ra rb rab r0)
    ((Algebra.ofId (Polynomial ℚ) K).restrictScalars ℚ)
  simp only [AlgHom.coe_restrictScalars', Algebra.ofId_apply, RatFunc.algebraMap_X] at h
  unfold pK xK
  exact h

lemma p2K_ne_zero (a b : ℚ) : p2K a b ≠ 0 := by
  rw [p2K_eq]
  intro h
  refine p2poly_ne_zero a b (IsFractionRing.injective (Polynomial ℚ) K ?_)
  rw [h, map_zero]

lemma toL_injective : Function.Injective toL := by
  intro x y hxy
  have h : toL (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have h2 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h3 : toL (x - y) * toL (x - y)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h2, map_one]
  rw [h, zero_mul] at h3
  exact one_ne_zero h3.symm

/-! ## The lifted ODE and its normal form -/

theorem xco_ode_P (a b : ℚ) (ra rb rab r0 : ℤ) :
    dL (dL (Pfun a b ra rb rab r0))
      = alphaL a b * dL (Pfun a b ra rb rab r0)
        + betaL a b * Pfun a b ra rb rab r0 + gammaL a b ra rb rab r0 := by
  have hd1 : dL (Pfun a b ra rb rab r0)
      = Φ (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)) := by
    unfold Pfun
    rw [dL_algebraMap]
  have hd2 : dL (dL (Pfun a b ra rb rab r0))
      = Φ (PowerSeries.derivative (R := ℚ)
            (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))) := by
    rw [hd1, dL_algebraMap]
  have hode : Φ (Submission.CDT.logPAODE a b (Submission.CDT.logP a b ra rb rab r0))
      = Φ (PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
            + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
            + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b) := by
    rw [Submission.CDT.logP_ode]
  have hode' : Φ (Submission.CDT.logPAODE a b (Submission.CDT.logP a b ra rb rab r0))
      = Φ (Submission.CDT.logPAP2 a b) * dL (dL (Pfun a b ra rb rab r0))
        + Φ (Submission.CDT.logPAP1 a b) * dL (Pfun a b ra rb rab r0)
        + Φ (Submission.CDT.logPAP0 a b) * Pfun a b ra rb rab r0 := by
    simp only [Submission.CDT.logPAODE, map_add, map_mul]
    rw [← hd2, ← hd1]
    rfl
  have hp2 : Φ (Submission.CDT.logPAP2 a b) = toL (p2K a b) := by
    rw [← coe_p2poly a b, ← toL_algebraMap (p2poly a b), ← p2K_eq a b]
  have hp1 : Φ (Submission.CDT.logPAP1 a b) = toL (p1K a b) := by
    rw [← coe_p1poly a b, ← toL_algebraMap (p1poly a b), ← p1K_eq a b]
  have hp0 : Φ (Submission.CDT.logPAP0 a b) = toL (p0K a b) := by
    rw [← coe_p0poly a b, ← toL_algebraMap (p0poly a b), ← p0K_eq a b]
  have hpa : Φ (PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
            + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
            + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b)
      = toL (pK a b ra rb rab r0) := by
    rw [← coe_ppoly a b ra rb rab r0, ← toL_algebraMap (ppoly a b ra rb rab r0),
      ← pK_eq a b ra rb rab r0]
  have hmain : toL (p2K a b) * dL (dL (Pfun a b ra rb rab r0))
        + toL (p1K a b) * dL (Pfun a b ra rb rab r0)
        + toL (p0K a b) * Pfun a b ra rb rab r0 = toL (pK a b ra rb rab r0) := by
    have h := hode'.symm.trans hode
    rw [hp2, hp1, hp0, hpa] at h
    exact h
  have hT : toL (p2K a b) ≠ 0 := by
    intro h
    have h0 : toL (p2K a b) = toL (0 : K) := by rw [h, map_zero]
    exact p2K_ne_zero a b (toL_injective h0)
  have hkey : toL (p2K a b) * dL (dL (Pfun a b ra rb rab r0))
      = - toL (p1K a b) * dL (Pfun a b ra rb rab r0)
        - toL (p0K a b) * Pfun a b ra rb rab r0 + toL (pK a b ra rb rab r0) := by
    linear_combination hmain
  have hTA : toL (p2K a b) * (alphaL a b * dL (Pfun a b ra rb rab r0)
        + betaL a b * Pfun a b ra rb rab r0 + gammaL a b ra rb rab r0)
      = - toL (p1K a b) * dL (Pfun a b ra rb rab r0)
        - toL (p0K a b) * Pfun a b ra rb rab r0 + toL (pK a b ra rb rab r0) := by
    simp only [alphaL, betaL, gammaL, alphaK, betaK, gammaK, toL_neg, toL_div]
    field_simp [hT]
    ring
  exact mul_left_cancel₀ hT (hkey.trans hTA.symm)

end Work.CDcl
