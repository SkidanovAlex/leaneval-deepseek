import Mathlib
import Submission.Work.LinnikBurgess.ddLog_pow_eq
import Submission.Work.LinnikBurgess.ddLog_one_isUnit

namespace Work.LinnikBurgess

/-!
# The shape of `L ∘ (a X + b X² + c X³ + p G)`

`ddLogPoly p K` is the truncated `p`-adic logarithm `∑_{j=1}^{K} c_j X^j` with
`c_1 = 1` and `p ∣ c_j` for every `j ≥ 2` (`ddLogCoeff_one`, `dvd_ddLogCoeff`).
Consequently `ddLogPoly p K = X + p · R` for a polynomial `R`, and composing with
`a X + b X² + c X³ + p G = A + p G` keeps the top part `A` unchanged:

`L(A + p G) = (A + p G) + p · R(A + p G) = A + p · (G + R(A + p G))`.

This is the structural fact behind the "Weyl-differencing" normal form: the linear part
`A` survives composition verbatim and everything else stays inside the ideal `(p)`.
-/

open Polynomial Finset

/-- A formal quotient of the `j`-th coefficient of the truncated logarithm by `p`
(defined for all `j`, and equal to `0` when `j < 2`, where divisibility need not hold). -/
noncomputable def ddLogCoeffDiv (p K : ℕ) [Fact p.Prime] (j : ℕ) : ZMod (p ^ K) :=
  if h : 2 ≤ j then Classical.choose (dvd_ddLogCoeff p K j h) else 0

/-- `p · ddLogCoeffDiv p K j = ddLogCoeff p K j` for `2 ≤ j`. -/
lemma ddLogCoeffDiv_spec {p K j : ℕ} [Fact p.Prime] (hj : 2 ≤ j) :
    (p : ZMod (p ^ K)) * ddLogCoeffDiv p K j = ddLogCoeff p K j := by
  rw [ddLogCoeffDiv, dif_pos hj]
  exact (Classical.choose_spec (dvd_ddLogCoeff p K j hj)).symm

/-- The "tail" `∑_{j=2}^{K} (c_j / p) X^j` of the truncated logarithm: `ddLogPoly p K` equals
`X + p · ddLogTail p K`. -/
noncomputable def ddLogTail (p K : ℕ) [Fact p.Prime] : Polynomial (ZMod (p ^ K)) :=
  ∑ j ∈ Finset.Icc 2 K, Polynomial.C (ddLogCoeffDiv p K j) * Polynomial.X ^ j

/-- `ddLogPoly p K = X + p · ddLogTail p K`. -/
lemma ddLogPoly_eq {p K : ℕ} [Fact p.Prime] (hK : 1 ≤ K) :
    ddLogPoly p K = Polynomial.X + Polynomial.C (p : ZMod (p ^ K)) * ddLogTail p K := by
  have hsplit : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 K := by simp
  have htail : (∑ j ∈ Finset.Icc 2 K, Polynomial.C (ddLogCoeff p K j) * Polynomial.X ^ j)
      = Polynomial.C (p : ZMod (p ^ K)) * ddLogTail p K := by
    rw [ddLogTail, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [← mul_assoc, ← Polynomial.C_mul, ddLogCoeffDiv_spec hj2]
  rw [ddLogPoly, hsplit, Finset.sum_insert h1, htail]
  simp [ddLogCoeff_one]

theorem ddLogPolyCompShape {p K : ℕ} [Fact p.Prime] (hK : 1 ≤ K)
    (a b c : ZMod (p ^ K)) (G : Polynomial (ZMod (p ^ K))) :
    ∃ W' : Polynomial (ZMod (p ^ K)),
      (Work.LinnikBurgess.ddLogPoly p K).comp
        (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2
          + Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C (p : ZMod (p ^ K)) * G)
      = Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2
        + Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C (p : ZMod (p ^ K)) * W' := by
  set F := Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2
        + Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C (p : ZMod (p ^ K)) * G with hF
  set A := Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2
        + Polynomial.C c * Polynomial.X ^ 3 with hA
  have hFA : F = A + Polynomial.C (p : ZMod (p ^ K)) * G := by rw [hF, hA]
  refine ⟨G + (ddLogTail p K).comp F, ?_⟩
  rw [ddLogPoly_eq hK, Polynomial.add_comp, Polynomial.X_comp, Polynomial.mul_comp,
    Polynomial.C_comp, hFA]
  ring

end Work.LinnikBurgess
