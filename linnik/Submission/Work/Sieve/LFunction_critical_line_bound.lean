import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Work.Sieve.LFunction_critical_line_absorb
import Submission.Work.Sieve.LFunction_imprimitive_factor

namespace Work.Sieve

open DirichletCharacter

/-!
# The critical-line bound `‖L(1/2 + it, χ)‖ ≤ C q^{1/3} log(2q+2) (1+|t|)^{1/3}`

An absolute constant `C` bounds every non-principal Dirichlet `L`-function of level `q` on the
critical line by `C · q^{1/3} · log(2q + 2) · (1 + |t|)^{1/3}`.

This is weaker than the classical *convexity* (Phragmén–Lindelöf) bound
`(q(1+|t|))^{1/4+ε}`; the slack in the exponents `1/3` versus `1/4` is precisely what pays for the
two loss factors that the passage to the critical line and to imprimitive characters introduces.

## Proof

* **Primitive `ψ` mod `N`.**  `Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`
  gives, for primitive non-trivial `ψ` and `0 ≤ σ ≤ 1`,
  `log ‖L(σ+iT,ψ)‖ ≤ ((1-σ)/2)(log N + log(2+|T|)) + log(log(N(2+|T|)) + 2) + 6`.
  At `σ = 1/2` this is `log` of `e^6 · (N(2+|T|))^{1/4} · (log(N(2+|T|)) + 2)`, which is the
  statement `critical_primitive_bound` below.

* **Absorption.**  `Work.Sieve.LFunction_critical_line_absorb` takes the arithmetic output of the
  primitive bound, evaluated at the conductor `f = χ.conductor`, and turns it into
  `C_a · f^{7/24} · log(2f+2) · (1+|t|)^{1/3}`: the exponent `1/4` is raised to `7/24` (with
  `7/24 < 1/3`), the logarithmic factor is absorbed into the power surplus `1/12`, and the
  `2 + |T|` is replaced by `1 + |t|`.

* **Imprimitive `χ` mod `q`.**  `Work.Sieve.LFunction_imprimitive_factor` bounds
  `‖L(1/2+it,χ)‖ ≤ C_i · q^{1/24} · ‖L(1/2+it,χ.primitiveCharacter)‖`: this is
  `LFunction_changeLevel` (the Euler product over the primes dividing the level) combined with the
  divisor bound `∏_{p|q}(1+p^{-1/2}) ≤ C · q^{1/24}`.  Since `χ.conductor ∣ q`, the conductor can be
  replaced by `q` in the absorbed primitive bound, and the exponents add up:
  `1/24 + 7/24 = 1/3`. -/

/-! ## The primitive case on the critical line, from convexity -/

private theorem critical_primitive_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 → ψ.IsPrimitive → ∀ t : ℝ,
      ‖DirichletCharacter.LFunction ψ ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * ((N : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by
  refine ⟨Real.exp 6, Real.exp_pos 6, ?_⟩
  intro N _inst ψ hψ hprim t
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have ht2 : (1 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by nlinarith
  have hXpos : (0 : ℝ) < (N : ℝ) * (2 + |t|) := lt_of_lt_of_le one_pos hX1
  have hlogpos : 0 < Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
    have := Real.log_nonneg hX1; linarith
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs ψ hψ hprim
      (σ := (1 : ℝ) / 2) (T := t) (by norm_num) (by norm_num)
  rw [mul_comm Complex.I (t : ℂ)] at hcx
  have hcast : (((1 : ℝ) / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hcast] at hcx
  have hEpos : 0 < Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by positivity
  have hlogeq : Real.log (Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
        * (Real.log ((N : ℝ) * (2 + |t|)) + 2)))
      = ((1 - (1 : ℝ) / 2) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
        + Real.log (Real.log ((N : ℝ) * (2 + |t|)) + 2) + 6 := by
    rw [Real.log_mul (by positivity) (ne_of_gt (by positivity)),
        Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hXpos _)) (ne_of_gt hlogpos),
        Real.log_rpow hXpos,
        Real.log_mul (ne_of_gt (by positivity : (0 : ℝ) < (N : ℝ)))
          (ne_of_gt (by positivity : (0 : ℝ) < 2 + |t|)),
        Real.log_exp]
    ring
  have hnorm_le : ‖DirichletCharacter.LFunction ψ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
          * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction ψ
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) with h0 | hpos
    · rw [← h0]; exact hEpos.le
    · have h1 : Real.log ‖DirichletCharacter.LFunction ψ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ Real.log (Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
              * (Real.log ((N : ℝ) * (2 + |t|)) + 2))) := by
        rw [hlogeq]
        exact hcx
      have h2 := (Real.log_le_iff_le_exp hpos).mp h1
      rwa [Real.exp_log hEpos] at h2
  simpa only [mul_assoc] using hnorm_le

/-! ## Assembly -/

theorem LFunction_critical_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
      ‖DirichletCharacter.LFunction χ ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (q : ℝ) ^ (1/3 : ℝ) * Real.log (2 * (q : ℝ) + 2) * (1 + |t|) ^ (1/3 : ℝ) := by
  obtain ⟨Cp, hCppos, hCp⟩ := critical_primitive_bound
  obtain ⟨Ca, hCapos, hCa⟩ := LFunction_critical_line_absorb
  obtain ⟨Ci, hCipos, hCi⟩ := LFunction_imprimitive_factor
  refine ⟨Ci * (Ca * Cp), by positivity, ?_⟩
  intro q _inst χ hχ t
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hq1
  have hf1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor))
  have hfpos : (0 : ℝ) < (χ.conductor : ℝ) := lt_of_lt_of_le one_pos hf1
  have hfq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hY1 : (1 : ℝ) ≤ 1 + |t| := by have := abs_nonneg t; linarith
  have hYpos : (0 : ℝ) < 1 + |t| := lt_of_lt_of_le one_pos hY1
  have h2tpos : (0 : ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have hXpos : (0 : ℝ) < (χ.conductor : ℝ) * (2 + |t|) := mul_pos hfpos h2tpos
  have hX1 : (1 : ℝ) ≤ (χ.conductor : ℝ) * (2 + |t|) := by nlinarith
  have h1 := hCi q χ hχ t
  have h2 := hCp (N := χ.conductor) χ.primitiveCharacter hne hprim t
  have h3 := hCa (χ.conductor : ℝ) t hf1
  have hXeq : ((χ.conductor : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
      = (χ.conductor : ℝ) ^ ((1 : ℝ) / 4) * (2 + |t|) ^ ((1 : ℝ) / 4) :=
    Real.mul_rpow hfpos.le h2tpos.le
  have h2b : ‖DirichletCharacter.LFunction χ.primitiveCharacter
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Ca * Cp) * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24) * Real.log (2 * (χ.conductor : ℝ) + 2)
          * (1 + |t|) ^ ((1 : ℝ) / 3) := by
    have h3' : (χ.conductor : ℝ) ^ ((1 : ℝ) / 4) * (2 + |t|) ^ ((1 : ℝ) / 4)
          * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2)
        ≤ Ca * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
            * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3) := h3
    calc ‖DirichletCharacter.LFunction χ.primitiveCharacter
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cp * ((χ.conductor : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 4)
            * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2) := h2
      _ = Cp * (((χ.conductor : ℝ) ^ ((1 : ℝ) / 4) * (2 + |t|) ^ ((1 : ℝ) / 4))
            * (Real.log ((χ.conductor : ℝ) * (2 + |t|)) + 2)) := by rw [hXeq]; ring
      _ ≤ Cp * (Ca * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
            * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left h3' hCppos.le
      _ = (Ca * Cp) * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
            * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3) := by ring
  have hqq : (q : ℝ) ^ ((1 : ℝ) / 24) * (q : ℝ) ^ ((7 : ℝ) / 24) = (q : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hqpos]
    norm_num
  have hF : (χ.conductor : ℝ) ^ ((7 : ℝ) / 24) ≤ (q : ℝ) ^ ((7 : ℝ) / 24) :=
    Real.rpow_le_rpow hfpos.le hfq (by norm_num)
  have hLfpos : 0 < Real.log (2 * (χ.conductor : ℝ) + 2) := by
    apply Real.log_pos; linarith
  have hL : Real.log (2 * (χ.conductor : ℝ) + 2) ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_le_log (by linarith)
    linarith
  have h4 : (χ.conductor : ℝ) ^ ((7 : ℝ) / 24) * Real.log (2 * (χ.conductor : ℝ) + 2)
      ≤ (q : ℝ) ^ ((7 : ℝ) / 24) * Real.log (2 * (q : ℝ) + 2) :=
    mul_le_mul hF hL hLfpos.le (Real.rpow_nonneg hqpos.le _)
  have hLHS : (Ca * Cp) * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
        * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)
      = (Ca * Cp) * ((χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
          * Real.log (2 * (χ.conductor : ℝ) + 2)) * (1 + |t|) ^ ((1 : ℝ) / 3) := by ring
  have hRHS : (Ca * Cp) * (q : ℝ) ^ ((7 : ℝ) / 24)
        * Real.log (2 * (q : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)
      = (Ca * Cp) * ((q : ℝ) ^ ((7 : ℝ) / 24)
          * Real.log (2 * (q : ℝ) + 2)) * (1 + |t|) ^ ((1 : ℝ) / 3) := by ring
  have h5 : (Ca * Cp) * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
        * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)
      ≤ (Ca * Cp) * (q : ℝ) ^ ((7 : ℝ) / 24) * Real.log (2 * (q : ℝ) + 2)
          * (1 + |t|) ^ ((1 : ℝ) / 3) := by
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity)
  calc ‖DirichletCharacter.LFunction χ ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Ci * (q : ℝ) ^ ((1 : ℝ) / 24)
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := h1
    _ ≤ Ci * (q : ℝ) ^ ((1 : ℝ) / 24) * ((Ca * Cp) * (χ.conductor : ℝ) ^ ((7 : ℝ) / 24)
          * Real.log (2 * (χ.conductor : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left h2b (by positivity)
    _ ≤ Ci * (q : ℝ) ^ ((1 : ℝ) / 24) * ((Ca * Cp) * (q : ℝ) ^ ((7 : ℝ) / 24)
          * Real.log (2 * (q : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = Ci * (Ca * Cp) * ((q : ℝ) ^ ((1 : ℝ) / 24) * (q : ℝ) ^ ((7 : ℝ) / 24))
          * Real.log (2 * (q : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3) := by ring
    _ = Ci * (Ca * Cp) * (q : ℝ) ^ ((1 : ℝ) / 3)
          * Real.log (2 * (q : ℝ) + 2) * (1 + |t|) ^ ((1 : ℝ) / 3) := by rw [hqq]

end Work.Sieve
