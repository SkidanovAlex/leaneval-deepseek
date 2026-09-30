import Mathlib
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford's (5.2): shared vocabulary for the single-term comparison

The file `Submission/Work/BMF/Ssum/norm_ab_sum_sub_Usum_le.lean` compares the double sum
`∑_{a ≤ M₁} ∑_{b ≤ M₂} (n + ab + u)^{-it}` with Ford's smoothed exponential sum `Usum`, at one
value `z = n + u` (K. Ford, *Vinogradov's integral and bounds for the Riemann zeta function*,
Proc. LMS 85 (2002), (5.2)).  This file collects the definitions and the elementary facts about
the additive character `eZ` that the comparison uses.

* `taylog k x = ∑_{i<k} (-1)^i x^{i+1}/(i+1)` is the degree-`k` Taylor polynomial of
  `log (1+x)`, in the index range `i < k` that matches the `Fin k` sums of `Usum`;
* `Uphase k t z c = ∑_{j≤k} γ_j c^j` is the phase of the `Usum` summand, with
  `γ_j = gam j t z = (-1)^j t/(2π j z^j)`;
* `logphase t z = -(t/(2π)) log z` is the phase of `z^{-it}`.
-/

namespace Work.BMF.Ssum

open Finset
open scoped BigOperators

noncomputable section

/-- The degree-`k` Taylor polynomial of `log (1 + x)`: `∑_{i<k} (-1)^i x^{i+1}/(i+1)`. -/
def taylog (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * x ^ (i + 1) / ((i : ℝ) + 1)

/-- Ford's phase `∑_{j=1}^{k} γ_j c^j = ∑_{j : Fin k} gam (j+1) t z * c^{j+1}`. -/
def Uphase (k : ℕ) (t z c : ℝ) : ℝ :=
  ∑ j : Fin k, gam ((j : ℕ) + 1) t z * c ^ ((j : ℕ) + 1)

/-- The phase `-(t/(2π)) log z` of `z^{-it}`; `z^{-it} = eZ (logphase t z)` for `z > 0`. -/
def logphase (t z : ℝ) : ℝ := -(t / (2 * Real.pi)) * Real.log z

lemma eZ_norm (x : ℝ) : ‖eZ x‖ = 1 := by
  unfold eZ
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
      = Complex.I * (((2 * Real.pi * x : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

lemma eZ_norm_le (x : ℝ) : ‖eZ x‖ ≤ 1 := le_of_eq (eZ_norm x)

lemma eZ_add (x y : ℝ) : eZ (x + y) = eZ x * eZ y := by
  unfold eZ
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eZ_zero : eZ 0 = 1 := by
  unfold eZ
  simp

/-- `‖eZ a - eZ b‖ ≤ 2π |a - b|`. -/
lemma norm_eZ_sub_le (a b : ℝ) : ‖eZ a - eZ b‖ ≤ 2 * Real.pi * |a - b| := by
  have h : eZ a - eZ b = eZ b * (eZ (a - b) - 1) := by
    rw [mul_sub, mul_one, ← eZ_add, show b + (a - b) = a from by ring]
  rw [h, norm_mul, eZ_norm, one_mul]
  unfold eZ
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((a - b : ℝ) : ℂ))
      = Complex.I * (((2 * Real.pi * (a - b) : ℝ)) : ℂ) by push_cast; ring]
  calc ‖Complex.exp (Complex.I * (((2 * Real.pi * (a - b) : ℝ)) : ℂ)) - 1‖
      ≤ ‖(2 * Real.pi * (a - b) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

end

end Work.BMF.Ssum
