import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotAS.ZiasGraphData
import Submission.Work.MotV5.AsQDefs
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.ASZQuadDetGen`

The determinant (elimination) identity of the AS residual chart:

```
R² - (β²)⁻¹·Lt·R·D₀ + (β²)⁻¹·At·D₀² ∈ (P)
```

where

* `D₀ = ziasGraphD0 a b g`, `R = ziasGraphR a b g` are the two coefficients of the *graph element*
  `G = D₀·X₀ + R ∈ ZIAS a b g` (`G = (a²+b²)·zcubAS 3 - (a²-ab-b²)·zcubAS 1`);
* `P = ASZElim.P a b g` is the eliminant of the chart;
* `β = aszQuBeta a b`, `Lt = aszQuLt a b g`, `At = aszQuAt a b g` are the coefficients of the
  *monic quadratic* `Q = X₀² + (β²)⁻¹Lt·X₀ + (β²)⁻¹At ∈ ZIAS a b g` (`aszQu_ident`/`aszDpQuad`).

The identity says that the graph `X₀ ↦ -R/D₀` satisfies the quadratic `Q`: clearing denominators
gives `R² - (β²)⁻¹Lt·R·D₀ + (β²)⁻¹At·D₀² = 0` modulo `P`, which is precisely the statement that the
graph of the residual curve is the graph of the quadratic over the plane curve `P = 0`.

## Proof

The whole content is the characteristic-`5` polynomial identity

`β²·R² - Lt·R·D₀ + At·D₀² = P · cq · X₀`,   `cq = -a¹⁵ - a¹⁰b⁵ - 2a⁵b¹⁰ + 2b¹⁵`,

which is verified by `ring` after (i) expanding all the `MvPolynomial.C`-coefficients into the
atoms `C a`, `C b`, `C g` via the `map_*` lemmas, and (ii) reducing all numerals modulo the
characteristic `5` (`Work.MotV5.ofNat_eq_mod_charP_five`, the technique used throughout the
workspace, e.g. in `ASZSplitCerts`).  The statement is then obtained by multiplying with the
scalar `C (β²)⁻¹`; this uses `β = 2(a+2b)⁴ ≠ 0`, which follows from `a² - ab - b² ≠ 0`
(exactly as in `Work.MotC5N3.ASZPrimeness.DpQuadNoHab`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- **The characteristic-`5` polynomial identity underlying `ASZQuadDetGen`.**  With
`P = ASZElim.P a b g`, `D₀ = ziasGraphD0 a b g`, `R = ziasGraphR a b g`, `β = aszQuBeta a b`,
`Lt = aszQuLt a b g`, `At = aszQuAt a b g` and `cq = -a¹⁵ - a¹⁰b⁵ - 2a⁵b¹⁰ + 2b¹⁵`,

`β²·R² - Lt·R·D₀ + At·D₀² = P · (C cq · X₀)`.

No hypothesis on `a b g` is needed: this is a polynomial identity (in characteristic `5`) in the
five variables `a, b, g, X₀, X₁`. -/
theorem aszQuadDet_ident (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2) * (Work.MotAS.ziasGraphR a b g) ^ 2
      - Work.MotAS.aszQuLt a b g * Work.MotAS.ziasGraphR a b g * Work.MotAS.ziasGraphD0 a b g
      + Work.MotAS.aszQuAt a b g * (Work.MotAS.ziasGraphD0 a b g) ^ 2
    = Work.MotAS.ASZElim.P a b g
        * (MvPolynomial.C (-a ^ 15 - a ^ 10 * b ^ 5 - 2 * a ^ 5 * b ^ 10 + 2 * b ^ 15)
            * MvPolynomial.X 0) := by
  rw [← sub_eq_zero]
  simp only [Work.MotAS.ziasGraphD0, Work.MotAS.ziasGraphR, Work.MotAS.aszQuLt,
    Work.MotAS.aszQuAt, Work.MotAS.aszQuL2, Work.MotAS.aszQuA2, Work.MotAS.aszQuL4,
    Work.MotAS.aszQuA4, Work.MotAS.aszQuAlpha, Work.MotAS.aszQuBeta, Work.MotAS.ASZElim.P,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat, map_natCast,
    map_intCast]
  ring_nf
  simp only [Work.MotV5.ofNat_eq_mod_charP_five, Nat.reduceMod, Nat.cast_zero, mul_zero, add_zero]
  refl_ring1

/-- `β = aszQuBeta a b` does not vanish when `a² - ab - b² ≠ 0`: in characteristic `5`,
`β = 2(a+2b)⁴`, and `a + 2b = 0` forces `a² - ab - b² = 5b² = 0`. -/
theorem aszQuBeta_sq_ne_zero (K : Type) [Field K] [CharP K 5] (a b : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) : ((Work.MotAS.aszQuBeta a b) ^ 2) ≠ 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have hfac : a ^ 2 - a * b - b ^ 2 = (a + 2 * b) * (a - 3 * b) + 5 * b ^ 2 := by ring
    rw [h, zero_mul, zero_add] at hfac
    rw [hfac, h5, zero_mul]
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h32 : (3 : K) * 2 = 1 := by
      have h : (3 : K) * 2 - 1 = (5 : K) * 1 := by ring
      rwa [h5, mul_one, sub_eq_zero] at h
    rw [h2, mul_zero] at h32
    exact one_ne_zero h32.symm
  have hβ : Work.MotAS.aszQuBeta a b ≠ 0 := by
    rw [Work.MotAS.aszQuBeta_eq a b]
    exact mul_ne_zero h2ne (pow_ne_zero 4 h2b)
  exact pow_ne_zero 2 hβ

theorem ASZQuadDetGen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (Work.MotAS.ziasGraphR a b g) ^ 2
      - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
          * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
      + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
          * (Work.MotAS.ziasGraphD0 a b g) ^ 2
    ∈ Ideal.span {Work.MotAS.ASZElim.P a b g} := by
  have hβ2 : ((Work.MotAS.aszQuBeta a b) ^ 2) ≠ 0 := aszQuBeta_sq_ne_zero K a b ha
  have hkey := aszQuadDet_ident K a b g
  -- the two "multiply by `C (β²)`" cancellations
  have h1 : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
      * (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuLt a b g)
      = Work.MotAS.aszQuLt a b g := by
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hβ2, MvPolynomial.C_1, one_mul]
  have h2 : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
      * (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuAt a b g)
      = Work.MotAS.aszQuAt a b g := by
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hβ2, MvPolynomial.C_1, one_mul]
  -- `C (β²) * W` is the inverse-free combination of `aszQuadDet_ident`
  have eX : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
      * (((MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuLt a b g)
            * (Work.MotAS.ziasGraphR a b g)) * (Work.MotAS.ziasGraphD0 a b g))
      = Work.MotAS.aszQuLt a b g * (Work.MotAS.ziasGraphR a b g)
          * (Work.MotAS.ziasGraphD0 a b g) := by
    rw [← mul_assoc, ← mul_assoc, h1]
  have eY : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
      * ((MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuAt a b g)
            * (Work.MotAS.ziasGraphD0 a b g) ^ 2)
      = Work.MotAS.aszQuAt a b g * (Work.MotAS.ziasGraphD0 a b g) ^ 2 := by
    rw [← mul_assoc, h2]
  have hCβW : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
      * ((Work.MotAS.ziasGraphR a b g) ^ 2
          - (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuLt a b g)
              * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
          + (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuAt a b g)
              * (Work.MotAS.ziasGraphD0 a b g) ^ 2)
      = MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2) * (Work.MotAS.ziasGraphR a b g) ^ 2
          - Work.MotAS.aszQuLt a b g * (Work.MotAS.ziasGraphR a b g)
              * (Work.MotAS.ziasGraphD0 a b g)
          + Work.MotAS.aszQuAt a b g * (Work.MotAS.ziasGraphD0 a b g) ^ 2 := by
    rw [mul_add, mul_sub]
    rw [eX, eY]
  -- the two scalar manipulations at the end
  have hinv : MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹)
      * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)
          * ((Work.MotAS.ziasGraphR a b g) ^ 2
              - (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuLt a b g)
                  * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
              + (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuAt a b g)
                  * (Work.MotAS.ziasGraphD0 a b g) ^ 2))
      = ((Work.MotAS.ziasGraphR a b g) ^ 2
          - (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuLt a b g)
              * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
          + (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹) * Work.MotAS.aszQuAt a b g)
              * (Work.MotAS.ziasGraphD0 a b g) ^ 2) := by
    rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hβ2, MvPolynomial.C_1, one_mul]
  have hstep2 : MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹)
      * (Work.MotAS.ASZElim.P a b g
          * (MvPolynomial.C (-a ^ 15 - a ^ 10 * b ^ 5 - 2 * a ^ 5 * b ^ 10 + 2 * b ^ 15)
              * MvPolynomial.X 0))
      = Work.MotAS.ASZElim.P a b g
          * (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
              * (-a ^ 15 - a ^ 10 * b ^ 5 - 2 * a ^ 5 * b ^ 10 + 2 * b ^ 15))
              * MvPolynomial.X 0) := by
    rw [MvPolynomial.C_mul]
    refl_ring1
  have hW : (Work.MotAS.ziasGraphR a b g) ^ 2
      - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
          * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
      + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
          * (Work.MotAS.ziasGraphD0 a b g) ^ 2
      = Work.MotAS.ASZElim.P a b g
          * (MvPolynomial.C (((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
              * (-a ^ 15 - a ^ 10 * b ^ 5 - 2 * a ^ 5 * b ^ 10 + 2 * b ^ 15))
              * MvPolynomial.X 0) :=
    (hinv.symm.trans (by rw [hCβW, hkey])).trans hstep2
  rw [Ideal.mem_span_singleton]
  exact ⟨_, hW⟩

end Work.MotAS.ASRulV2M
