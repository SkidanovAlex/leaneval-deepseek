import Mathlib
import Submission.Work.OddCurveB.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddBridge.dvi_reduce

/-!
# The Volterra data at the diagonal

The two rows of the Volterra system `(hah44)` that involve the perturbation are `-G₂(s,s,z)`, and
on the diagonal `G₂(s,s,z) = (∫₀¹ (√(τ(1-τ)))⁻¹) • Kvec(s,s,z)` (`Work.OddBridge.G2_self_eq_smul`).
At `σ = s` the kernel is *explicit*: the Abel numerators are given by the case split in
`Work.OddVolterra.J1` / `J2`,

`J₁(s,s,t) = (2n+1)!! (-(L ∂_sL))^{n+1}`,  `J₂(s,s,t) = (2n-1)!! (-(L ∂_sL))^n ∂_sL`,

with `L = s t + h s`, `∂_sL = t + h' s`, and `Kden(s,s,t) = √((t + h'(s)) · 2 L)`.

So every estimate about `Godd` at the diagonal reduces to elementary estimates on the explicit
expression in `(s, t, h s, h' s)`.  This file records that reduction.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Existence

open Work.OddVolterra

noncomputable section

/-- The Abel weight mass `∫₀¹ (√(τ(1-τ)))⁻¹ dτ = π`. -/
noncomputable def abelMass : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹

/-- **The perturbed rows of the system, at the diagonal.** -/
lemma Godd_eq_abelMass_smul (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) :
    Godd n h s z =
      ![z 0, z 1, -(abelMass * (Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 0),
        -(abelMass * (Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 1)] := by
  have hG2 := Work.OddBridge.G2_self_eq_smul (n := n) h s (z 0) (z 1) (z 2) (z 3)
  funext i
  fin_cases i <;>
    simp only [Godd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
  · rfl
  · rfl
  · show - (G2 n h s s (z 0) (z 1) (z 2) (z 3)) 0 = -(abelMass * (Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 0)
    rw [hG2]; simp [abelMass, Pi.smul_apply, smul_eq_mul]
  · show - (G2 n h s s (z 0) (z 1) (z 2) (z 3)) 1 = -(abelMass * (Kvec n h s s (z 0) (z 1) (z 2) (z 3)) 1)
    rw [hG2]; simp [abelMass, Pi.smul_apply, smul_eq_mul]

/-- The explicit diagonal value of the first Abel numerator. -/
lemma J1_diag_eq (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    J1 n h s s t = (Nat.doubleFactorial (2 * n + 1) : ℝ) *
      (- (line h s t * lineSlope h s t)) ^ (n + 1) := by
  unfold J1; simp

/-- The explicit diagonal value of the second Abel numerator. -/
lemma J2_diag_eq (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    J2 n h s s t = (Nat.doubleFactorial (2 * n - 1) : ℝ) *
      (- (line h s t * lineSlope h s t)) ^ n * lineSlope h s t := by
  unfold J2; simp

/-- The diagonal value of the kernel denominator: `√((t + h'(s)) · 2 (s t + h s))`. -/
lemma Kden_diag_eq (h : ℝ → ℝ) (s t : ℝ) :
    Kden h s s t = Real.sqrt ((t + deriv h s) * (2 * line h s t)) := by
  unfold Kden
  rw [hquot_self]
  congr 1
  ring

end

end Work.OddCurveB.Existence
