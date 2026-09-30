import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_defs
import Submission.Work.BMF.n4_perr_defs
import Submission.Work.BMF.n4_log_integral_bound
import Submission.Work.BMF.n4wa_filter_prime_not_dvd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **From the `[P,2P]` prime-character window bound to the pointwise bound on `psum`.**

Given (as a hypothesis, so that no `sorry`-laden module is used) the N4a window estimate
`hW`: for `P ≥ Pw`, every modulus `q ≥ 1`, every character `χ` mod `q` and every
`|t| ≤ exp((log P)^{21/20})`,
`‖Σ_{p ∈ primesIn P (2P)} χ(p) p^{it} − (χ = 1 ? ∫_P^{2P} v^{it}/log v dv : 0)‖ ≤ C P exp(−c (log P)^{1/12})`,
there are `c', C', P₀` (with `0 < c'`, `0 < C'`, `1 ≤ P₀`) such that for `P ≥ P₀`,
`q ≥ 1`, `(q : ℝ) ≤ (log P)^A`, every `χ` mod `q` and `|t| ≤ exp((log P)^{21/20})`,
`‖psum P q χ t‖ ≤ C' π₀(P)/(1+|t|) · 1_{χ=1} + n4Perr C' c' P q`,
i.e. the filtered prime sum `psum P q χ t = Σ_{p ∈ admP P q} χ(p) p^{it}` is bounded by the
principal term `C' π₀(P)/(1+|t|)` plus the error `C' P exp(−c'(log P)^{1/12}) + C' ω(q)`.

Route (all ingredients already proved in the workspace):
* `psum P q χ t` is by definition `Σ_{p ∈ (primesIn P (2P)).filter (· ∤ q)} χ(p) p^{it}`, and
  `Work.BMF.n4wa_filter_prime_not_dvd` identifies it with the *unfiltered* sum
  `Σ_{p ∈ primesIn P (2P)} χ(p) p^{it}` appearing in `hW` (a prime `p ∣ q` is a non-unit mod
  `q`, so `χ p = 0`);
* for `χ = 1` use `hW` and `Work.BMF.n4_log_integral_bound`,
  `‖∫_P^{2P} v^{it}/log v‖ ≤ Cm π₀(P)/(1+|t|)`, then the triangle inequality;
* for `χ ≠ 1` the main term of `hW` vanishes, so `‖psum‖ ≤ C P exp(−c(log P)^{1/12})`;
* take `c' := c`, `C' := max Cm C 1`, absorb `C ≤ C'` by monotonicity. -/
theorem n4_psum_of_window (A : ℝ) (hA : 0 < A) {c C Pw : ℝ} (hc : 0 < c)
    (hW : ∀ P : ℝ, Pw ≤ P → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log P ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) →
      ‖∑ p ∈ primesIn P (2 * P), χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)
        - (if χ = 1 then ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)
           else 0)‖
        ≤ C * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))) :
    ∃ c' C' P₀ : ℝ, 0 < c' ∧ 0 < C' ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.log P ^ A → ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) →
      ‖psum P q χ t‖ ≤ C' * pi0 P / (1 + |t|) * (if χ = 1 then (1 : ℝ) else 0)
        + n4Perr C' c' P q := by
  obtain ⟨Cm, Pm, _hCm, hPm, hInt⟩ := n4_log_integral_bound
  refine ⟨c, max Cm (max C 1), max Pw (max Pm 1), hc, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_right C 1))
      (le_max_right Cm (max C 1))
  · exact le_trans (le_max_right Pm 1) (le_max_right Pw (max Pm 1))
  · intro P hP q _ hq χ t ht
    have hPw : Pw ≤ P := le_trans (le_max_left Pw (max Pm 1)) hP
    have hPm : Pm ≤ P :=
      le_trans (le_max_left Pm 1) (le_trans (le_max_right Pw (max Pm 1)) hP)
    have hP1 : 1 ≤ P :=
      le_trans (le_trans (le_max_right Pm 1) (le_max_right Pw (max Pm 1))) hP
    have hP0 : (0 : ℝ) < P := lt_of_lt_of_le zero_lt_one hP1
    have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP1
    have hpi0 : 0 ≤ pi0 P := by rw [pi0]; exact div_nonneg hP0.le hlogP
    have hden : (0 : ℝ) < 1 + |t| := by positivity
    set Cl : ℝ := max Cm (max C 1) with hCl
    have hClpos : 0 < Cl := by
      rw [hCl]
      exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_right C 1))
        (le_max_right Cm (max C 1))
    -- the admissible-prime sum equals the unfiltered sum appearing in `hW`
    have hS : psum P q χ t
        = ∑ p ∈ primesIn P (2 * P), χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t) := by
      rw [psum, admP]
      exact n4wa_filter_prime_not_dvd P q χ t
    have hW' := hW P hPw q hq χ t ht
    rw [← hS] at hW'
    -- the two absorptions
    have hstep1 : Cm * pi0 P / (1 + |t|) ≤ Cl * pi0 P / (1 + |t|) := by
      rw [hCl]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cm (max C 1)) hpi0) hden.le
    have hstep2 : C * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))
        ≤ Cl * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) := by
      rw [hCl]
      have h1 : C * P ≤ max Cm (max C 1) * P :=
        mul_le_mul_of_nonneg_right
          (le_trans (le_max_left C 1) (le_max_right Cm (max C 1))) hP0.le
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    have hω : 0 ≤ Cl * (q.primeFactors.card : ℝ) :=
      mul_nonneg hClpos.le (Nat.cast_nonneg _)
    have hstep2' : C * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))
        ≤ Cl * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))
          + Cl * (q.primeFactors.card : ℝ) := by linarith [hstep2, hω]
    by_cases hchi : χ = 1
    · -- principal character: keep the main term and use the integral bound
      rw [if_pos hchi] at hW'
      rw [if_pos hchi, mul_one]
      unfold n4Perr
      have htri : ‖psum P q χ t‖ ≤
          ‖psum P q χ t
            - ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)‖
          + ‖∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)‖ := by
        have h := norm_add_le
          (psum P q χ t
            - ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ))
          (∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ))
        rw [sub_add_cancel] at h
        exact h
      have hIntJ : ‖∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)‖
          ≤ Cm * pi0 P / (1 + |t|) := hInt P hPm t
      calc ‖psum P q χ t‖
          ≤ ‖psum P q χ t
              - ∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)‖
            + ‖∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)‖ := htri
        _ ≤ C * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) + Cm * pi0 P / (1 + |t|) :=
            add_le_add hW' hIntJ
        _ ≤ (Cl * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))
              + Cl * (q.primeFactors.card : ℝ)) + Cl * pi0 P / (1 + |t|) :=
            add_le_add hstep2' hstep1
        _ = Cl * pi0 P / (1 + |t|)
              + (Cl * P * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ))
                + Cl * (q.primeFactors.card : ℝ)) := by ring
    · -- non-principal character: the main term vanishes
      rw [if_neg hchi, sub_zero] at hW'
      rw [if_neg hchi]
      unfold n4Perr
      rw [mul_zero, zero_add]
      linarith [hW', hstep2']

end Work.BMF
