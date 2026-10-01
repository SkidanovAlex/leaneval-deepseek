import Mathlib
import Submission.Work.ZeroDensity.Ingham.fourthMomentDefs

/-!
# The pointwise product `stepPair p · conj (stepPair q)`

`stepPair m n t = 1_{t ≥ 2π(m-1)²} 1_{t ≥ 2π(n-1)²} (√(mn))⁻¹ e^{-i t log(mn)}`
(see `Work.ZeroDensity.Ingham.fourthMomentDefs`), a single indicator times a single exponential.

Its product against the conjugate of another such object is again of the same shape: the two
thresholds are merged by taking `max`, the two square-root factors multiply (as `√(PQ) = √P√Q`),
and the two exponentials combine into `e^{i t (log Q - log P)}` because conjugation flips the sign
of `-i t log Q`.

* `starRingEnd_stepPair`: the conjugate of one `stepPair`, in the same normal form;
* `stepPair_mul_conj_apply`: the general product identity, valid for all `m n m' n'`;
* `stepPair_mul_conj_eq`: the form requested, with the `max` thresholds written out.
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

-- The hypotheses `1 ≤ p.1` etc. are not needed for this identity (it holds for all naturals);
-- they are kept because they are part of the requested statement.
set_option linter.unusedVariables false

noncomputable section

/-- The conjugate of `stepPair m n t`, in the same normal form (the exponential's sign flipped). -/
lemma starRingEnd_stepPair (m n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (stepPair m n t)
      = if 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
          ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹ *
            Complex.exp (Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ))
        else 0 := by
  rw [stepPair_apply]
  by_cases h : 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t
  · rw [if_pos h, map_mul]
    have hreal : (starRingEnd ℂ) ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹
        = ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    have hexp : (starRingEnd ℂ)
          (Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ))))
        = Complex.exp (Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hreal, hexp, if_pos h]
  · rw [if_neg h, map_zero, if_neg h]

/-- The general product of a `stepPair` with the conjugate of another one. -/
lemma stepPair_mul_conj_apply (m n m' n' : ℕ) (t : ℝ) :
    stepPair m n t * (starRingEnd ℂ) (stepPair m' n' t)
      = if 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t
          ∧ 2 * Real.pi * ((m' : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n' : ℝ) - 1) ^ 2 ≤ t then
        ((Real.sqrt (((m : ℝ) * (n : ℝ)) * ((m' : ℝ) * (n' : ℝ))) : ℂ))⁻¹ *
          Complex.exp (Complex.I *
            ((t * (Real.log ((m' : ℝ) * (n' : ℝ)) - Real.log ((m : ℝ) * (n : ℝ))) : ℝ) : ℂ))
      else 0 := by
  rw [starRingEnd_stepPair m' n' t, stepPair_apply]
  by_cases hp : 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t
  · by_cases hq : 2 * Real.pi * ((m' : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n' : ℝ) - 1) ^ 2 ≤ t
    · rw [if_pos hp, if_pos hq, if_pos ⟨hp.1, hp.2, hq.1, hq.2⟩]
      have hsqrt : ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹
            * ((Real.sqrt ((m' : ℝ) * (n' : ℝ)) : ℂ))⁻¹
          = ((Real.sqrt (((m : ℝ) * (n : ℝ)) * ((m' : ℝ) * (n' : ℝ))) : ℂ))⁻¹ := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ (m : ℝ) * (n : ℝ) by positivity), Complex.ofReal_mul,
          mul_inv]
      have hexp : Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ)))
            * Complex.exp (Complex.I * ((t * Real.log ((m' : ℝ) * (n' : ℝ)) : ℝ) : ℂ))
          = Complex.exp (Complex.I *
              ((t * (Real.log ((m' : ℝ) * (n' : ℝ)) - Real.log ((m : ℝ) * (n : ℝ))) : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        have harg : t * (Real.log ((m' : ℝ) * (n' : ℝ)) - Real.log ((m : ℝ) * (n : ℝ)))
            = t * Real.log ((m' : ℝ) * (n' : ℝ)) - t * Real.log ((m : ℝ) * (n : ℝ)) := by ring
        rw [harg]
        push_cast
        ring
      calc ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹
              * Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ)))
            * (((Real.sqrt ((m' : ℝ) * (n' : ℝ)) : ℂ))⁻¹
              * Complex.exp (Complex.I * ((t * Real.log ((m' : ℝ) * (n' : ℝ)) : ℝ) : ℂ)))
          = (((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹
                * ((Real.sqrt ((m' : ℝ) * (n' : ℝ)) : ℂ))⁻¹)
              * (Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ)))
                * Complex.exp (Complex.I * ((t * Real.log ((m' : ℝ) * (n' : ℝ)) : ℝ) : ℂ))) := by
              ring
        _ = ((Real.sqrt (((m : ℝ) * (n : ℝ)) * ((m' : ℝ) * (n' : ℝ))) : ℂ))⁻¹ *
              Complex.exp (Complex.I *
                ((t * (Real.log ((m' : ℝ) * (n' : ℝ)) - Real.log ((m : ℝ) * (n : ℝ))) : ℝ) : ℂ)) := by
              rw [hsqrt, hexp]
    · rw [if_pos hp, if_neg hq, mul_zero,
        if_neg (fun hc => hq ⟨hc.2.2.1, hc.2.2.2⟩)]
  · rw [if_neg hp, zero_mul, if_neg (fun hc => hp ⟨hc.1, hc.2.1⟩)]

theorem stepPair_mul_conj_eq (p q : ℕ × ℕ)
    (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2) (hq1 : 1 ≤ q.1) (hq2 : 1 ≤ q.2) (t : ℝ) :
    stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)
      = ((Real.sqrt (((p.1 : ℝ) * (p.2 : ℝ)) * ((q.1 : ℝ) * (q.2 : ℝ))) : ℂ))⁻¹ *
        (Set.Ici (max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
                       (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2)))).indicator
          (fun s => Complex.exp (Complex.I * ((s * (Real.log ((q.1 : ℝ) * (q.2 : ℝ)) - Real.log ((p.1 : ℝ) * (p.2 : ℝ))) : ℝ) : ℂ))) t := by
  rw [stepPair_mul_conj_apply]
  by_cases h : max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
      (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2)) ≤ t
  · have hAB : max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2) ≤ t :=
      le_trans (le_max_left _ _) h
    have hCD : max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2) ≤ t :=
      le_trans (le_max_right _ _) h
    obtain ⟨hA, hB⟩ := max_le_iff.mp hAB
    obtain ⟨hC, hD⟩ := max_le_iff.mp hCD
    have hmem : t ∈ Set.Ici
        (max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
          (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2))) := h
    rw [if_pos ⟨hA, hB, hC, hD⟩, Set.indicator_of_mem hmem]
  · have hconj : ¬ ((2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2 ≤ t)
        ∧ (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2 ≤ t)) := by
      intro hc
      exact h (max_le (max_le hc.1.1 hc.1.2) (max_le hc.2.1 hc.2.2))
    have hnm : t ∉ Set.Ici
        (max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
          (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2))) := h
    rw [if_neg (fun hc => hconj ⟨⟨hc.1, hc.2.1⟩, ⟨hc.2.2.1, hc.2.2.2⟩⟩), Set.indicator_of_notMem hnm,
      mul_zero]

end

end Work.ZeroDensity.Ingham
