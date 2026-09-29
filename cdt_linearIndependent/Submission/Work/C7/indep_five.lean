import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.c7base

set_option linter.unusedVariables false

/-!
# Area C7 — `1, L, L², Li₂, J` are `ℚ[x]`-linearly independent (the `x`-side Lemma `seven`)

With `L = log(1-x)`, `Li₂ = Li₂(x)` and `J = x·₃F₂(1/2,1,1;3/2,3/2; y/4)` (`y = x²/(x-1)`), we
prove that `1, L, L², Li₂, J` are `ℚ[x]`-linearly independent, given

* `h4`: `1, L, L², Li₂` are independent;
* `hJ`: the order-one relation `2x(x-1)J' - xJ = 2(1-x)L` satisfied by `J`;
* `hsq`, `hsq'`, `hb`: the `ℚ(x)`-side "no rational solution" facts: `ε' = ±ε/(2(x-1))` has only
  the trivial solution and `b' = b/(2(x-1)) + 1/x` has none.

**Argument.** Suppose `∑ Pᵢ fᵢ = 0` with `Pᵢ ∈ ℚ[x]` and `P₄ ≠ 0` (if `P₄ = 0` then `h4` kills the
relation).  Applying `θ = 2x(x-1)·d/dx` to the relation gives a second polynomial-coefficient
relation `∑ (thetaP P)ᵢ fᵢ = 0` (`theta_rel`): the factor `2x(x-1)` clears the denominators
`1/(x-1)`, `1/x` coming from `L'`, `Li₂'` and `J'`.  Eliminating `J` between the two relations
(`A := P₄·θP - (θP)₄·P`, whose last coefficient is `0`, hence `A = 0` by `h4`) gives the three
polynomial identities

* `2x(x-1)(P₄·P₂' - P₂·P₄') = x·P₄·P₂`            (coefficient of `L²`)
* `2x(x-1)(P₄·P₃' - P₃·P₄') = x·P₄·P₃`            (coefficient of `Li₂`)
* `2x(x-1)(P₄·P₁' - P₁·P₄') = 2(x-1)P₄² + x·P₄·P₁`  (coefficient of `L`, after `P₂ = P₃ = 0`).

The first two read `(Pᵢ/P₄)' = (Pᵢ/P₄)/(2(x-1))`, so `hsq` gives `P₂ = P₃ = 0`; the third reads
`(P₁/P₄)' = (P₁/P₄)/(2(x-1)) + 1/x`, contradicting `hb`.
-/

noncomputable section

namespace Work.C7

open PowerSeries

/-! ## The derivation step -/

/-- Applying `θ = 2x(x-1)·d/dx` to a polynomial-coefficient relation gives a relation whose
coefficients are again polynomials, given the ODE of `J`. -/
theorem theta_rel_aux
    (hJ : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Jps
      - PowerSeries.X * Jps = 2 * (1 - PowerSeries.X) * Lps)
    (P : Fin 5 → Polynomial ℚ)
    (hP : ∑ i, (P i : PowerSeries ℚ) * F5 i = 0) :
    ∑ i, (thetaP P i : PowerSeries ℚ) * F5 i = 0 := by
  have f1 : (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Lps = 1 := by
    have h2 := deriv_Lps
    linear_combination -h2
  have f2 : PowerSeries.derivative (R := ℚ) (Lps ^ 2) = 2 * Lps * PowerSeries.derivative (R := ℚ) Lps := by
    rw [PowerSeries.derivative_pow]
    norm_num
  have f3 : PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Li2ps
      = -(PowerSeries.X - 1) * Lps := by
    linear_combination (PowerSeries.X - 1) * deriv_Li2ps
  have f4 : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Jps
      = PowerSeries.X * Jps - 2 * (PowerSeries.X - 1) * Lps := by
    linear_combination hJ
  have hkey : 2 * PowerSeries.X * (PowerSeries.X - 1)
      * PowerSeries.derivative (R := ℚ) (∑ i, (P i : PowerSeries ℚ) * F5 i)
      = ∑ i, (thetaP P i : PowerSeries ℚ) * F5 i := by
    rw [Fin.sum_univ_five, Fin.sum_univ_five, F5_zero, F5_one, F5_two, F5_three, F5_four,
      th_zero, th_one, th_two, th_three, th_four]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_one,
      PowerSeries.derivative_coe]
    simp only [th0, th1, th2, th3, th4, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one, poly_coe_two, poly_coe_four]
    linear_combination (2 * PowerSeries.X * ↑(P 1) + 4 * PowerSeries.X * ↑(P 2) * Lps) * f1
      + (2 * PowerSeries.X * (PowerSeries.X - 1) * ↑(P 2)) * f2 + (2 * ↑(P 3)) * f3
      + (↑(P 4)) * f4
  have h0 : PowerSeries.derivative (R := ℚ) (∑ i, (P i : PowerSeries ℚ) * F5 i) = 0 := by
    rw [hP, map_zero]
  rw [← hkey, h0, mul_zero]

/-! ## The `h4`-elimination step -/

/-- A five-term relation with vanishing `J`-coefficient is trivial: it is a four-term relation
among `1, L, L², Li₂`, to which `h4` applies. -/
theorem five_rel_last_zero_aux
    (h4 : Submission.CDTPlan.PolyIndependent (fun i : Fin 4 => ![1, Lps, Lps ^ 2, Li2ps] i))
    (P : Fin 5 → Polynomial ℚ)
    (h : ∑ i, (P i : PowerSeries ℚ) * F5 i = 0) (hP4 : P 4 = 0) :
    P = 0 := by
  have hrel : ∑ i : Fin 4, ((P i.castSucc) : PowerSeries ℚ) * (![1, Lps, Lps ^ 2, Li2ps] i) = 0 := by
    rw [Fin.sum_univ_castSucc] at h
    have hlast : P (Fin.last 4) = 0 := hP4
    rw [hlast] at h
    simp only [Polynomial.coe_zero, zero_mul, add_zero] at h
    exact h
  have hzero := h4 (fun i : Fin 4 => P i.castSucc) hrel
  funext i
  fin_cases i
  · exact hzero 0
  · exact hzero 1
  · exact hzero 2
  · exact hzero 3
  · exact hP4

/-! ## The two "ratio" lemmas: polynomial identity ⟹ the `ℚ(x)` ODE -/

/-- `2x(x-1)(q p' - p q') = x·p·q` is the clearing of `(p/q)' = (p/q)/(2(x-1))`. -/
theorem dRat_ratio_eq_aux {p q : Polynomial ℚ} (hq : q ≠ 0)
    (h : 2 * Polynomial.X * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative)
      = Polynomial.X * p * q) :
    Submission.CDT.dRat ((p : RatFunc ℚ) / (q : RatFunc ℚ)) =
      ((p : RatFunc ℚ) / (q : RatFunc ℚ)) / (2 * (RatFunc.X - 1)) := by
  have hqR : algebraMap (Polynomial ℚ) (RatFunc ℚ) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hXm1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by
    have h1 : ((RatFunc.X : RatFunc ℚ) - 1)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 1) := by
      simp only [map_sub, map_one, RatFunc.algebraMap_X]
    rw [h1]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)
  have hden : 2 * (RatFunc.X - 1) ≠ 0 := mul_ne_zero two_ne_zero hXm1
  have h' : 2 * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative) = p * q := by
    have h2 : Polynomial.X * (2 * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative)
        - p * q) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left Polynomial.X_ne_zero)
  have hc : ((2 * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative) : Polynomial ℚ)
        : RatFunc ℚ) = ((p * q : Polynomial ℚ) : RatFunc ℚ) := by
    rw [h']
  simp only [RatFunc.coePolynomial, map_mul, map_sub, map_ofNat, map_one,
    RatFunc.algebraMap_X] at hc
  simp only [RatFunc.coePolynomial]
  rw [eq_div_iff hden]
  rw [Submission.CDT.dRat_div, div_mul_eq_mul_div]
  field_simp
  simp only [map_mul, map_sub]
  linear_combination hc

/-- Clearing of `(p/q)' = (p/q)/(2(x-1)) + 1/x`. -/
theorem dRat_ratio_eq_plus_aux {p q : Polynomial ℚ} (hq : q ≠ 0)
    (h : 2 * Polynomial.X * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative)
      = 2 * (Polynomial.X - 1) * q ^ 2 + Polynomial.X * p * q) :
    Submission.CDT.dRat ((p : RatFunc ℚ) / (q : RatFunc ℚ)) =
      ((p : RatFunc ℚ) / (q : RatFunc ℚ)) / (2 * (RatFunc.X - 1)) + 1 / RatFunc.X := by
  have hqR : algebraMap (Polynomial ℚ) (RatFunc ℚ) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hXne : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hXm1 : (RatFunc.X : RatFunc ℚ) - 1 ≠ 0 := by
    have h1 : ((RatFunc.X : RatFunc ℚ) - 1)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 1) := by
      simp only [map_sub, map_one, RatFunc.algebraMap_X]
    rw [h1]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)
  have hden : 2 * (RatFunc.X - 1) ≠ 0 := mul_ne_zero two_ne_zero hXm1
  have hc : ((2 * Polynomial.X * (Polynomial.X - 1) * (q * p.derivative - p * q.derivative)
        : Polynomial ℚ) : RatFunc ℚ)
      = ((2 * (Polynomial.X - 1) * q ^ 2 + Polynomial.X * p * q : Polynomial ℚ) : RatFunc ℚ) := by
    rw [h]
  simp only [RatFunc.coePolynomial, map_mul, map_sub, map_add, map_pow, map_ofNat, map_one,
    RatFunc.algebraMap_X] at hc
  simp only [RatFunc.coePolynomial]
  rw [Submission.CDT.dRat_div]
  field_simp
  simp only [map_mul, map_sub]
  linear_combination hc

/-- **Area C7, the `x`-side.** If `1, L, L², Li₂` are `ℚ[x]`-linearly independent (`h4`), `J`
satisfies `2x(x-1)J' - xJ = 2(1-x)L` (`hJ`), and the two homogeneous and the inhomogeneous
first-order ODEs with the coefficient `1/(2(x-1))` have only trivial solutions (`hsq`, `hsq'`,
`hb`), then `1, L, L², Li₂, J` are `ℚ[x]`-linearly independent. -/
theorem indep_five
    (h4 : Submission.CDTPlan.PolyIndependent (fun i : Fin 4 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2, Work.C7.Li2ps] i))
    (hJ : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps)
    (hsq : ∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = ε / (2 * (RatFunc.X - 1)) → ε = 0)
    (hsq' : ∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = -ε / (2 * (RatFunc.X - 1)) → ε = 0)
    (hb : ∀ b : RatFunc ℚ, Submission.CDT.dRat b = b / (2 * (RatFunc.X - 1)) + 1 / RatFunc.X → False) :
    Submission.CDTPlan.PolyIndependent (fun i : Fin 5 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2, Work.C7.Li2ps, Work.C7.Jps] i) := by
  intro P hP
  by_cases hPz : P = 0
  · intro i
    rw [hPz]
    rfl
  · exfalso
    have hP4 : P 4 ≠ 0 := fun h40 => hPz (five_rel_last_zero_aux h4 P hP h40)
    have hQ : ∑ i, (thetaP P i : PowerSeries ℚ) * F5 i = 0 := theta_rel_aux hJ P hP
    set A : Fin 5 → Polynomial ℚ := fun i => P 4 * thetaP P i - thetaP P 4 * P i with hAdef
    have hArel : ∑ i, (A i : PowerSeries ℚ) * F5 i = 0 := by
      have key : ∑ i, ((P 4 * thetaP P i - thetaP P 4 * P i : Polynomial ℚ) : PowerSeries ℚ)
          * F5 i = 0 := by
        have hP' : ∑ i, (P i : PowerSeries ℚ) * F5 i = 0 := hP
        rw [Fin.sum_univ_five] at hQ hP' ⊢
        simp only [F5_zero, F5_one, F5_two, F5_three, F5_four] at hQ hP' ⊢
        push_cast
        linear_combination (↑(P 4)) * hQ - (↑(thetaP P 4)) * hP'
      simpa [hAdef] using key
    have hA4 : A 4 = 0 := by
      simp only [hAdef]
      ring
    have hAll : ∀ i, A i = 0 := fun i => congrFun (five_rel_last_zero_aux h4 A hArel hA4) i
    have hP2 : P 2 = 0 := by
      have h2 : P 4 * th2 P - th4 P * P 2 = 0 := by
        simpa [hAdef, th_two, th_four] using hAll 2
      simp only [th2, th4] at h2
      have hE2 : 2 * Polynomial.X * (Polynomial.X - 1)
            * (P 4 * (P 2).derivative - P 2 * (P 4).derivative) = Polynomial.X * P 2 * P 4 := by
        linear_combination h2
      have heps := dRat_ratio_eq_aux (p := P 2) (q := P 4) hP4 hE2
      have hz := hsq ((P 2 : RatFunc ℚ) / (P 4 : RatFunc ℚ)) heps
      have hP4R : (P 4 : RatFunc ℚ) ≠ 0 :=
        fun hh => hP4 (RatFunc.algebraMap_injective ℚ (by simpa using hh))
      have h1 : (P 2 : RatFunc ℚ) = 0 := by
        calc (P 2 : RatFunc ℚ)
            = ((P 2 : RatFunc ℚ) / (P 4 : RatFunc ℚ)) * (P 4 : RatFunc ℚ) :=
              (div_mul_cancel₀ _ hP4R).symm
          _ = 0 := by rw [hz, zero_mul]
      exact RatFunc.algebraMap_injective ℚ (by simpa using h1)
    have hP3 : P 3 = 0 := by
      have h3 : P 4 * th3 P - th4 P * P 3 = 0 := by
        simpa [hAdef, th_three, th_four] using hAll 3
      simp only [th3, th4] at h3
      have hE3 : 2 * Polynomial.X * (Polynomial.X - 1)
            * (P 4 * (P 3).derivative - P 3 * (P 4).derivative) = Polynomial.X * P 3 * P 4 := by
        linear_combination h3
      have heps := dRat_ratio_eq_aux (p := P 3) (q := P 4) hP4 hE3
      have hz := hsq ((P 3 : RatFunc ℚ) / (P 4 : RatFunc ℚ)) heps
      have hP4R : (P 4 : RatFunc ℚ) ≠ 0 :=
        fun hh => hP4 (RatFunc.algebraMap_injective ℚ (by simpa using hh))
      have h1 : (P 3 : RatFunc ℚ) = 0 := by
        calc (P 3 : RatFunc ℚ)
            = ((P 3 : RatFunc ℚ) / (P 4 : RatFunc ℚ)) * (P 4 : RatFunc ℚ) :=
              (div_mul_cancel₀ _ hP4R).symm
          _ = 0 := by rw [hz, zero_mul]
      exact RatFunc.algebraMap_injective ℚ (by simpa using h1)
    have h1 : P 4 * th1 P - th4 P * P 1 = 0 := by
      simpa [hAdef, th_one, th_four] using hAll 1
    simp only [th1, th4, hP2, hP3] at h1
    have hE1 : 2 * Polynomial.X * (Polynomial.X - 1)
          * (P 4 * (P 1).derivative - P 1 * (P 4).derivative)
        = 2 * (Polynomial.X - 1) * (P 4) ^ 2 + Polynomial.X * P 1 * P 4 := by
      linear_combination h1
    exact hb ((P 1 : RatFunc ℚ) / (P 4 : RatFunc ℚ)) (dRat_ratio_eq_plus_aux hP4 hE1)

end Work.C7
