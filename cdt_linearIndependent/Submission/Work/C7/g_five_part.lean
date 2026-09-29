import Mathlib
import Submission.Work.C7.seven_setup

/-!
# Area C7 — the "five-function" part of the `x`-side independence

If a `ℚ[x]`-relation `∑ᵢ Pᵢ · gᵢ = 0` among the seven pullbacks `gᵢ = Bᵢ ∘ y`
involves only `g 0, …, g 4` (i.e. `P 5 = P 6 = 0`), then all `Pᵢ` vanish.

After multiplying by `x - 1` the relation becomes a relation among the five
`ℚ(x)`-independent functions `1, L, L², Li₂, J` with polynomial coefficients

  `(x-1)P₀ + 2x²P₁`, `-x(x-2)P₁`, `-½(x-1)P₂ + ½x(x-2)P₃`, `2x(x-2)P₃`, `xP₄`,

so `hind` forces each of them to be zero, and each `Pᵢ` is recovered by
dividing by the (nonzero) rational functions `x-1`, `x`, `x-2`, `2`, `½`.
-/

noncomputable section

open PowerSeries
open scoped BigOperators

namespace Work.C7

/-- The coercion `ℚ[X] → ℚ⟦X⟧` of the rational number `2`, in the `ℕ`-numeral
shape in which it occurs after `push_cast`. -/
lemma coe_two_PS : ((2 : Polynomial ℚ) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from rfl, Polynomial.coe_C,
    PowerSeries.C_eq_algebraMap, map_ofNat]

theorem g_five_part
    (h0 : Work.C7.g 0 = 1)
    (h1 : Work.C7.g 1 = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
    (h2 : Work.C7.g 2 = -(PowerSeries.C (1 / 2 : ℚ)) * Work.C7.Lps ^ 2)
    (h3 : Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (h4 : Work.C7.g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Work.C7.Jps)
    (hind : Submission.CDTPlan.PolyIndependent
      (fun i : Fin 5 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2, Work.C7.Li2ps, Work.C7.Jps] i))
    (P : Fin 7 → Polynomial ℚ)
    (hP : ∑ i, (P i : PowerSeries ℚ) * Work.C7.g i = 0)
    (h5 : P 5 = 0) (h6 : P 6 = 0) : ∀ i, P i = 0 := by
  -- Reduction of the relation to the five functions `g 0, …, g 4`.
  have hsum : (P 0 : PowerSeries ℚ) * Work.C7.g 0 + (P 1 : PowerSeries ℚ) * Work.C7.g 1
      + (P 2 : PowerSeries ℚ) * Work.C7.g 2 + (P 3 : PowerSeries ℚ) * Work.C7.g 3
      + (P 4 : PowerSeries ℚ) * Work.C7.g 4 = 0 := by
    rw [Fin.sum_univ_seven] at hP
    simp only [h5, h6, Polynomial.coe_zero, zero_mul, add_zero] at hP
    exact hP
  -- The polynomial coefficients of `1, L, L², Li₂, J` in `(x-1)·(∑ Pᵢ gᵢ)`.
  set B : Fin 5 → Polynomial ℚ :=
    ![(Polynomial.X - 1) * P 0 + 2 * Polynomial.X ^ 2 * P 1,
      -(Polynomial.X * (Polynomial.X - 2)) * P 1,
      -(Polynomial.C (1 / 2 : ℚ)) * (Polynomial.X - 1) * P 2
        + Polynomial.C (1 / 2 : ℚ) * (Polynomial.X * (Polynomial.X - 2)) * P 3,
      2 * (Polynomial.X * (Polynomial.X - 2)) * P 3,
      Polynomial.X * P 4] with hBdef
  have hy : Work.C7.yps * ((PowerSeries.X : PowerSeries ℚ) - 1) = PowerSeries.X ^ 2 :=
    Work.C7.yps_mul_sub_one_seven_setup
  have hc : Work.C7.cfun * ((PowerSeries.X : PowerSeries ℚ) - 1)
      = PowerSeries.X * (PowerSeries.X - 2) := by
    rw [Work.C7.cfun_eq']
    linear_combination (PowerSeries.X * (PowerSeries.X - 2)) * Work.C7.gU_mul
  have hj : ((PowerSeries.X : PowerSeries ℚ) * (PowerSeries.X - 1)⁻¹) * (PowerSeries.X - 1)
      = PowerSeries.X := by
    linear_combination (PowerSeries.X) * Work.C7.gU_mul
  -- `(x-1)·gᵢ` for `i = 0, …, 4`.
  have e0 : ((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 0
      = ((PowerSeries.X : PowerSeries ℚ) - 1) * 1 := by rw [h0]
  have e1 : ((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 1
      = 2 * PowerSeries.X ^ 2 - PowerSeries.X * (PowerSeries.X - 2) * Work.C7.Lps := by
    rw [h1]
    linear_combination (2 : PowerSeries ℚ) * hy - (Work.C7.Lps) * hc
  have e2 : ((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 2
      = -(PowerSeries.C (1 / 2 : ℚ)) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.Lps ^ 2) := by
    rw [h2]; ring
  have e3 : ((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 3
      = PowerSeries.X * (PowerSeries.X - 2)
          * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) := by
    rw [h3, Work.C7.cfun_sub_phi]
    linear_combination (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) * hc
  have e4 : ((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 4 = PowerSeries.X * Work.C7.Jps := by
    rw [h4]
    linear_combination (Work.C7.Jps) * hj
  -- The cleared relation.
  have hE : (P 0 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 0)
      + (P 1 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 1)
      + (P 2 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 2)
      + (P 3 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 3)
      + (P 4 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * Work.C7.g 4) = 0 := by
    linear_combination ((PowerSeries.X : PowerSeries ℚ) - 1) * hsum
  rw [e0, e1, e2, e3, e4] at hE
  -- Regroup `hE` as a `ℚ[x]`-relation among `1, L, L², Li₂, J`.
  have hBrel : ∑ i : Fin 5, (B i : PowerSeries ℚ) * Work.C7.f5 i = 0 := by
    rw [Fin.sum_univ_five, hBdef]
    show (((Polynomial.X - 1) * P 0 + 2 * Polynomial.X ^ 2 * P 1 : Polynomial ℚ) : PowerSeries ℚ)
          * (1 : PowerSeries ℚ)
      + ((-(Polynomial.X * (Polynomial.X - 2)) * P 1 : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Lps
      + (((-(Polynomial.C (1/2 : ℚ)) * (Polynomial.X - 1) * P 2
          + Polynomial.C (1/2 : ℚ) * (Polynomial.X * (Polynomial.X - 2)) * P 3) : Polynomial ℚ) : PowerSeries ℚ)
          * Work.C7.Lps ^ 2
      + ((2 * (Polynomial.X * (Polynomial.X - 2)) * P 3 : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Li2ps
      + ((Polynomial.X * P 4 : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Jps = 0
    push_cast
    simp only [coe_two_PS]
    linear_combination hE
  have hzero := hind B hBrel
  -- Read off the `Pᵢ`, from the highest index down.
  have hp4 : P 4 = 0 := by
    have h := hzero 4
    rw [hBdef] at h
    exact (mul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero
  have hp3 : P 3 = 0 := by
    have h := hzero 3
    rw [hBdef] at h
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0))
        (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (2 : ℚ))))
  have hp2 : P 2 = 0 := by
    have h := hzero 2
    rw [hBdef, hp3] at h
    simp only [mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr (Polynomial.C_ne_zero.mpr (by norm_num : (1/2 : ℚ) ≠ 0)))
        (Polynomial.X_sub_C_ne_zero (1 : ℚ)))
  have hp1 : P 1 = 0 := by
    have h := hzero 1
    rw [hBdef] at h
    exact (mul_eq_zero.mp h).resolve_left
      (neg_ne_zero.mpr (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero (2 : ℚ))))
  have hp0 : P 0 = 0 := by
    have h := hzero 0
    rw [hBdef, hp1] at h
    simp only [mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (Polynomial.X_sub_C_ne_zero (1 : ℚ))
  intro i
  fin_cases i
  · exact hp0
  · exact hp1
  · exact hp2
  · exact hp3
  · exact hp4
  · exact h5
  · exact h6

end Work.C7
