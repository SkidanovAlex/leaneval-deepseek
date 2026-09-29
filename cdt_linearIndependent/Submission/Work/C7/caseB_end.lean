import Mathlib
import Submission.Work.C7.seven_setup
import Submission.Work.C7.caseB_key

/-!
# Area C7 — the `case B` leaf of the `x`-side independence proof of Lemma `seven`

The relation `d·(g 5 + λ·g 6) + Σ C_j·f5_j = 0` (polynomial coefficients, `d ≠ 0`) is reduced
to a contradiction as follows.

* `Work.C7.caseB_key` extracts, by applying `∂ = x(x-1)²·d/dx` to the relation and reading off the
  coefficient of `Lps²` (via the `ℚ[x]`-independence `hind` of `f5`), the polynomial identity
  `dshP d · C 2 - d · dshP (C 2) = d²·α` with `α = C(-½)(x-1)(x-2) + C(λ)C(½)x(x-2)²`.
* Dividing by `d²` this says, for `ρ = C 2/d ∈ ℚ(x)`,
  `dRat ρ = -α / (X(X-1)²)`; since `α(0) = -1 ≠ 0`, the right-hand side has a **simple pole at 0**.
* But no derivative of a rational function has a simple pole (`Submission.CDT.ordAt_dRat_ne_neg_one`).

-/

noncomputable section

namespace Work.C7

open Polynomial PowerSeries

/-- No rational function has a derivative with a simple pole at `0`: if
`dRat ρ = G / (X(X-1)²)` with `G(0) ≠ 0` then `ordAt 0 (dRat ρ) = -1`, contradicting
`Submission.CDT.ordAt_dRat_ne_neg_one`. -/
theorem dRat_zero_simplepole {G : Polynomial ℚ} (hG : G.coeff 0 ≠ 0) (ρ : RatFunc ℚ)
    (h : Submission.CDT.dRat ρ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) G
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X * (Polynomial.X - 1)^2)) :
    False := by
  have hG0 : G ≠ 0 := fun h0 => hG (by rw [h0]; simp)
  have hS : (Polynomial.X * (Polynomial.X - 1)^2 : Polynomial ℚ) ≠ 0 := by
    refine mul_ne_zero Polynomial.X_ne_zero ?_
    exact pow_ne_zero 2 (by simpa using Polynomial.X_sub_C_ne_zero (1:ℚ))
  have hrootS : Polynomial.rootMultiplicity (0:ℚ)
      ((Polynomial.X : Polynomial ℚ) * (Polynomial.X - 1)^2) = 1 := by
    rw [Polynomial.rootMultiplicity_mul hS]
    have h1 : Polynomial.rootMultiplicity (0:ℚ) (Polynomial.X : Polynomial ℚ) = 1 := by
      rw [show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C (0:ℚ) by simp,
        Polynomial.rootMultiplicity_X_sub_C_self]
    have h2 : Polynomial.rootMultiplicity (0:ℚ) ((Polynomial.X - 1)^2 : Polynomial ℚ) = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      rw [Polynomial.IsRoot.def]; norm_num
    rw [h1, h2, add_zero]
  have hrootG : Polynomial.rootMultiplicity (0:ℚ) G = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [Polynomial.IsRoot.def]
    intro hh
    exact hG (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hh)
  have hord : Submission.CDT.ordAt (0:ℚ) (Submission.CDT.dRat ρ) = -1 := by
    rw [h]
    rw [Submission.CDT.ordAt_div 0 (RatFunc.algebraMap_ne_zero hG0) (RatFunc.algebraMap_ne_zero hS),
      Submission.CDT.ordAt_algebraMap, Submission.CDT.ordAt_algebraMap, hrootG, hrootS]
    norm_num
  exact Submission.CDT.ordAt_dRat_ne_neg_one (0:ℚ) ρ hord

theorem caseB_end
    (hd5 : Work.C7.dsh (Work.C7.g 5)
      = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
        * Work.C7.Lps ^ 2)
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (hind : Submission.CDTPlan.PolyIndependent Work.C7.f5)
    (hN1 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ
      ≠ 2 * (RatFunc.X - 2) ^ 2 * ((RatFunc.X - 1) ^ 2)⁻¹)
    (hN2 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ
      ≠ (RatFunc.X - 2) * (RatFunc.X * (RatFunc.X - 1))⁻¹)
    (lam : ℚ) (d : Polynomial ℚ) (hd : d ≠ 0) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * (Work.C7.g 5 + PowerSeries.C lam * Work.C7.g 6)
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) : False := by
  have hkey := caseB_key hd5 hd6 hdJ hind lam d hd C h
  set αP : Polynomial ℚ := Polynomial.C (-(1 / 2)) * (Polynomial.X - 1) * (Polynomial.X - 2)
      + Polynomial.C lam * Polynomial.C (1 / 2) * Polynomial.X * (Polynomial.X - 2) ^ 2 with hαPdef
  have hkey' : Work.C7.dshP d * C 2 - d * Work.C7.dshP (C 2) = d ^ 2 * αP := by
    rw [hαPdef]; exact hkey
  have hSne : (Polynomial.X * (Polynomial.X - 1) ^ 2 : Polynomial ℚ) ≠ 0 := by
    refine mul_ne_zero Polynomial.X_ne_zero ?_
    exact pow_ne_zero 2 (by simpa using Polynomial.X_sub_C_ne_zero (1:ℚ))
  have hAS0 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X * (Polynomial.X - 1) ^ 2) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hSne
  have hAd0 : algebraMap (Polynomial ℚ) (RatFunc ℚ) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hAx : ∀ p : Polynomial ℚ,
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C7.dshP p)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X * (Polynomial.X - 1) ^ 2)
          * Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) := by
    intro p
    simp only [Work.C7.dshP, map_mul, Submission.CDT.dRat_algebraMap]
  have h0 := congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) hkey'
  simp only [map_sub, map_mul, map_pow] at h0
  rw [hAx d, hAx (C 2)] at h0
  have hS' : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X * (Polynomial.X - 1) ^ 2)
      * (Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) d)
          * algebraMap (Polynomial ℚ) (RatFunc ℚ) (C 2)
        - algebraMap (Polynomial ℚ) (RatFunc ℚ) d
          * Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) (C 2)))
      = (algebraMap (Polynomial ℚ) (RatFunc ℚ) d) ^ 2
        * algebraMap (Polynomial ℚ) (RatFunc ℚ) αP := by
    linear_combination h0
  have hrel : algebraMap (Polynomial ℚ) (RatFunc ℚ) ((C 2).derivative * d - C 2 * d.derivative)
      = -(Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) d)
          * algebraMap (Polynomial ℚ) (RatFunc ℚ) (C 2)
        - algebraMap (Polynomial ℚ) (RatFunc ℚ) d
          * Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) (C 2))) := by
    simp only [map_sub, map_mul, Submission.CDT.dRat_algebraMap]
    ring
  have hρ : Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) (C 2)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) d)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (-αP)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X * (Polynomial.X - 1) ^ 2) := by
    rw [Submission.CDT.dRat_div, eq_div_iff hAS0, map_neg, hrel, div_mul_eq_mul_div]
    field_simp
    linear_combination -hS'
  have hcoeff : (-αP).coeff 0 ≠ 0 := by
    rw [hαPdef]; rw [Polynomial.coeff_zero_eq_eval_zero]; simp
  exact dRat_zero_simplepole hcoeff _ hρ

end Work.C7
