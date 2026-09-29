import Mathlib
import Submission.Work.ADcl.yode14_defs
import Submission.Work.ADcl.d14_brows
import Submission.Work.ADcl.d14_int_rows

namespace Work.ADcl

open PowerSeries Polynomial

noncomputable section

/-! ## The `G`-rows (`i = 5,6,7`): the derivative is the next function -/

/-- Row `k` (`k = 5,6,7`, i.e. `G, G', G''`): `d/dy G^{(k-5)} = G^{(k-4)}`. -/
lemma d14_G_row (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ) (a b c : ℤ) (i : Fin 14)
    (hi : i.val = 5 ∨ i.val = 6 ∨ i.val = 7) :
    (QF q0 q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c i)
      = ∑ j, (A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c) i j : PowerSeries ℚ) *
          Submission.CDTPlan.fourteen a b c j := by
  rcases hi with h | h | h
  · rw [show i = 5 from Fin.ext h,
        show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (5 : Fin 14))
          = Submission.CDTPlan.fourteen a b c (6 : Fin 14) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [A14]
  · rw [show i = 6 from Fin.ext h,
        show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (6 : Fin 14))
          = Submission.CDTPlan.fourteen a b c (7 : Fin 14) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [A14]
  · rw [show i = 7 from Fin.ext h,
        show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (7 : Fin 14))
          = Submission.CDTPlan.fourteen a b c (8 : Fin 14) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [A14]

/-! ## Row `8`: `G'''`, whose derivative `G''''` is given by the order-four `y`-ODE -/

/-- Row `8`: the ODE `q · G⁗ = Σ_{k<4} A k · G^{(k)} + cc` turns the derivative of `G'''`
(entry `8`) into a polynomial combination of the entries `5,6,7,8` and the constant term
`cc · B₁` (entry `0`), with the common denominator `QF q0 q = X⁴ q₀ q`. -/
lemma d14_ode_row (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ) (a b c : ℤ)
    (hode : (q : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[4] (Submission.CDTPlan.GZ a b c)
        = (∑ k : Fin 4, (A k : PowerSeries ℚ) *
            (PowerSeries.derivative (R := ℚ))^[k] (Submission.CDTPlan.GZ a b c)) + (cc : PowerSeries ℚ)) :
    (QF q0 q : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (8 : Fin 14))
      = ∑ j, (A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c) (8 : Fin 14) j : PowerSeries ℚ) *
          Submission.CDTPlan.fourteen a b c j := by
  have hQF : (QF q0 q : PowerSeries ℚ) =
      (Work.CDcl.qOf q0 : PowerSeries ℚ) * (q : PowerSeries ℚ) := by
    simp [QF, Work.CDcl.qOf, Polynomial.coe_mul]
  rw [hQF,
    show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (8 : Fin 14))
      = (PowerSeries.derivative (R := ℚ))^[4] (Submission.CDTPlan.GZ a b c) from rfl,
    mul_assoc, hode, mul_add, Finset.mul_sum]
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hf0 : Submission.CDTPlan.fourteen a b c (0 : Fin 14) = 1 := rfl
  have hf5 : Submission.CDTPlan.fourteen a b c (5 : Fin 14) = Submission.CDTPlan.GZ a b c := rfl
  have hf6 : Submission.CDTPlan.fourteen a b c (6 : Fin 14)
      = PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.GZ a b c) := rfl
  have hf7 : Submission.CDTPlan.fourteen a b c (7 : Fin 14)
      = PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.GZ a b c)) := rfl
  have hf8 : Submission.CDTPlan.fourteen a b c (8 : Fin 14)
      = PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ)
          (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.GZ a b c))) := rfl
  simp [A14, Work.CDcl.qOf, Polynomial.coe_mul, Polynomial.coe_pow]
  simp only [hf0, hf5, hf6, hf7, hf8]
  ring

/-! ## Assembly -/

/-- **The `D`-closure of the fourteen functions of Theorem A**, from an inhomogeneous order-four
`y`-ODE for `G = GZ a b c` with polynomial coefficients and polynomial inhomogeneity, plus the
`D`-closure data of the seven pure functions `pureB`. -/
theorem dclosed_of_yode (a b c : ℤ)
    (hode : ∃ (q : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ), q ≠ 0 ∧
      (q : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[4] (Submission.CDTPlan.GZ a b c)
        = (∑ k : Fin 4, (A k : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Submission.CDTPlan.GZ a b c))
          + (cc : PowerSeries ℚ))
    (hP : Submission.CDTPlan.PureFacts) :
    Submission.CDTPlan.DClosed (Submission.CDTPlan.fourteen a b c) := by
  obtain ⟨q, A, cc, hq, hode⟩ := hode
  obtain ⟨q0, hq0, A0, hA0⟩ := hP.2.2.2.2.2.2.2
  refine ⟨QF q0 q, QF_ne_zero hq0 hq, A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c), ?_⟩
  intro i
  fin_cases i
  · exact d14_brows q0 q A0 A cc a b c hA0 0
  · exact d14_brows q0 q A0 A cc a b c hA0 1
  · exact d14_brows q0 q A0 A cc a b c hA0 2
  · exact d14_brows q0 q A0 A cc a b c hA0 3
  · exact d14_brows q0 q A0 A cc a b c hA0 4
  · exact d14_G_row q0 q A0 A cc a b c 5 (Or.inl rfl)
  · exact d14_G_row q0 q A0 A cc a b c 6 (Or.inr (Or.inl rfl))
  · exact d14_G_row q0 q A0 A cc a b c 7 (Or.inr (Or.inr rfl))
  · exact d14_ode_row q0 q A0 A cc a b c hode
  · exact d14_brows q0 q A0 A cc a b c hA0 5
  · exact d14_brows q0 q A0 A cc a b c hA0 6
  · exact d14_int_rows q0 q A0 A cc a b c 11 (Or.inl rfl)
  · exact d14_int_rows q0 q A0 A cc a b c 12 (Or.inr (Or.inl rfl))
  · exact d14_int_rows q0 q A0 A cc a b c 13 (Or.inr (Or.inr rfl))

end

end Work.ADcl
