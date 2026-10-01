import Mathlib
import Submission.Work.LinnikAreas.RealZeroCount.Defs

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.RealZeroCount

open DirichletCharacter

/-- A non-principal character is not induced by the trivial character. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h
  have h2 : χ = 1 := by
    rw [← changeLevel_primitiveCharacter (χ := χ), h, changeLevel_one]
  exact hχ h2

/-- The completed `L`-function of a non-trivial Dirichlet character does not vanish on the
half-plane `Re s ≥ 1`. -/
lemma completedLFunction_ne_zero_of_one_le_re {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℂ m) (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    completedLFunction ψ s ≠ 0 := by
  intro hc
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h := LFunction_eq_completed_div_gammaFactor ψ s (Or.inl h0)
  rw [hc, zero_div] at h
  exact (LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs) h

/-- For a non-principal character `χ` and a real `β ≥ 1`, the completed `L`-function of the
primitive character inducing `χ` does not vanish at `β`; hence `β` is not a zero of `χ`. -/
lemma zeroMult_eq_zero_of_one_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {β : ℝ} (hβ : 1 ≤ β) :
    Work.LinnikContract.zeroMult χ ((β : ℂ)) = 0 := by
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [Work.LinnikContract.zeroMult]
  by_contra hz
  refine (completedLFunction_ne_zero_of_one_le_re χ.primitiveCharacter
    (primitiveCharacter_ne_one hχ) (s := (β : ℂ)) ?_) ?_
  · simpa using hβ
  · exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hz

theorem realZeroCountFinsum_eq_zero_of_nonpos {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {t : ℝ} (ht : t ≤ 0) :
    Work.LinnikAreas.realZeroCountFinsum q χ t = 0 := by
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  unfold Work.LinnikAreas.realZeroCountFinsum
  have hfun :
      (fun β : ℝ => if Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
          Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t
        then (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) else 0)
        = fun _ => 0 := by
    funext β
    exact if_neg (by
      rintro ⟨hz, hl⟩
      have hl' : (1 - β) * Real.log (q : ℝ) ≤ 0 := by
        have h1 : Work.LinnikContract.lamOf q ((β : ℂ)) = (1 - β) * Real.log (q : ℝ) := by
          simp [Work.LinnikContract.lamOf]
        rw [h1] at hl
        exact le_trans hl ht
      have hβ : 1 ≤ β := by
        have h2 : 1 - β ≤ 0 :=
          nonpos_of_mul_nonpos_right (by rw [mul_comm]; exact hl') hlog
        linarith
      exact hz (zeroMult_eq_zero_of_one_le hχ hβ))
  rw [hfun]
  simp

end Work.LinnikAreas.RealZeroCount
