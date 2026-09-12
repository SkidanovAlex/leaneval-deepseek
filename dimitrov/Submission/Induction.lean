import Mathlib
import Submission.Conjugates
import Submission.Powers
import Submission.ConjPoly
import Submission.DescentCount
import Submission.DescentCore

/-!
# Master induction: the challenge reduces to the analytic engine

This module proves the challenge theorem under the single hypothesis
`EngineStatement`: for the *fixed number field `K`*, every element `β` with
`pow2 (minpoly ℤ β)` irreducible satisfies the house bound:

    (2 : ℝ) ^ (1 / (4 * |argSet β| : ℝ)) ≤ house β .

The proof is strong induction on `n := natDegree (minpoly ℤ α)` (all inside the
single number field `K`; the descent `α ↦ α²` stays in `K`).

* **Irreducible branch** (`pow2 (minpoly ℤ α)` irreducible): the engine lemma
  applies directly.

* **Reducible branch**: `Submission.Descent.pow2_irreducible_or_negclosed`
  gives that the conjugate set `S := conjugateValues α` is closed under
  negation.  Then the descent `α ↦ β := α²` applies:
  - `(minpoly ℤ β).natDegree * 2 = (minpoly ℤ α).natDegree`, so the degree
    strictly decreases (from `card_conjugateValues_sq_two_mul` and
    `minpoly_natDegree_eq_card`), enabling strong induction;
  - `|argSet β| * 2 = |argSet α|` (`argSet_sq_card_two_mul`), so the phase
    count halves exactly;
  - `house β = (house α)^2` (`house_sq`), so
    `house α = sqrt (house β) ≥ 2^(1/(8 |argSet β|)) = 2^(1/(4 |argSet α|))`.
  - `β ≠ 0`, `IsIntegral ℤ β`, and `¬ IsOfFinOrder β` (else `α` would be a
    root of unity), so the induction hypothesis applies to `β`.

This is the whole proof of the phase-refined Schinzel–Zassenhaus bound except
for the analytic engine (capacity/Dubinin/Pólya–Bertrandias), which is the
content of `EngineStatement`.
-/

noncomputable section

open scoped Complex
open scoped Real

namespace Submission.Induction

open Submission.Conjugates
open Submission.Powers

variable {K : Type*} [Field K] [NumberField K]

/-- The house bound for an element whose phase count is `(argSet β).card`. -/
def Bound (α : K) : Prop :=
  (2 : ℝ) ^ (1 / (4 * ((argSet α).card : ℝ))) ≤ NumberField.house α

/-- The analytic engine, specialized to the fixed field `K`: the bound for the
case where `pow2 (minpoly ℤ β)` is irreducible. -/
def EngineStatement (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ (β : K), IsIntegral ℤ β → β ≠ 0 →
    ¬ IsOfFinOrder β → Irreducible (pow2 (minpoly ℤ β)) → Bound β

/-- `β = α²` is not a root of unity if `α` is not. -/
lemma not_rootOfUnity_sq {α : K} (h : ¬ IsOfFinOrder α) : ¬ IsOfFinOrder (α ^ 2) := by
  intro h2
  rw [isOfFinOrder_iff_pow_eq_one] at h2
  rcases h2 with ⟨m, hmpos, hm⟩
  exact h (by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 * m, by omega, ?_⟩
    calc
      α ^ (2 * m) = (α ^ 2) ^ m := by rw [pow_mul]
      _ = 1 := hm)

/-- Exponent identity used in the descent: for `m > 0`,
`2 ^ (1/(8m))` squares to `2 ^ (1/(4m))`. -/
lemma rpow_sq_half (m : ℕ) (hm : 0 < m) :
    ((2 : ℝ) ^ (1 / (8 * (m : ℝ)))) ^ 2 = (2 : ℝ) ^ (1 / (4 * (m : ℝ))) := by
  have h2le : (0 : ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_mul_natCast h2le (1 / (8 * (m : ℝ))) 2]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  field_simp [hmR]
  ring

lemma sq_le_sq_of_nonneg {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (h : c ^ 2 ≤ b ^ 2) : c ≤ b := by
  nlinarith

/-- **Main reduction.**  Assuming the engine, the house bound holds for every
nonzero algebraic integer that is not a root of unity. -/
theorem dimitrov_of_engine (engine : EngineStatement K) (α : K)
    (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) (hROU : ¬ IsOfFinOrder α) : Bound α := by
  classical
  let p : ℕ → Prop := fun n : ℕ =>
    ∀ (β : K), IsIntegral ℤ β → β ≠ 0 → ¬ IsOfFinOrder β →
      (minpoly ℤ β).natDegree = n → Bound β
  have hp : ∀ n : ℕ, p n := by
    intro n
    refine Nat.strong_induction_on n (p := p) ?_
    intro n ih
    intro β hβ h0 hROU hdeg
    rcases Submission.Descent.pow2_irreducible_or_negclosed β hβ with h2irr | hneg
    · -- Irreducible: engine.
      exact engine β hβ h0 hROU h2irr
    · -- Reducible: descend to γ := β².
      let γ : K := β ^ 2
      have hγ_int : IsIntegral ℤ γ := by
        simpa [γ] using hβ.pow 2
      have hγ0 : γ ≠ 0 := by
        simpa [γ] using pow_ne_zero 2 h0
      have hγ_ROU : ¬ IsOfFinOrder γ := by
        simpa [γ] using not_rootOfUnity_sq hROU
      have hdeg2 : (minpoly ℤ γ).natDegree * 2 = n := by
        calc
          (minpoly ℤ γ).natDegree * 2
              = (conjugateValues γ).card * 2 := by
                  rw [Submission.ConjPoly.minpoly_natDegree_eq_card γ hγ_int]
          _ = (conjugateValues β).card := by
                  change (conjugateValues (β ^ 2)).card * 2 = (conjugateValues β).card
                  exact Submission.Descent.card_conjugateValues_sq_two_mul β h0 hneg
          _ = n := by
                  rw [← Submission.ConjPoly.minpoly_natDegree_eq_card β hβ, hdeg]
      have hdeg_lt : (minpoly ℤ γ).natDegree < n := by
        have hpos : 0 < (minpoly ℤ γ).natDegree := minpoly.natDegree_pos hγ_int
        omega
      have hbγ : Bound γ := by
        exact ih (minpoly ℤ γ).natDegree hdeg_lt γ hγ_int hγ0 hγ_ROU rfl
      -- Now lift the bound from γ to β.
      let m : ℕ := (argSet γ).card
      have hmpos : 0 < m := by
        dsimp [m]
        refine Finset.card_pos.mpr ?_
        obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
        exact ⟨(σ γ).arg, by simp [argSet, conjugateValues]⟩
      have hma : (argSet β).card = 2 * m := by
        have hc := Submission.Descent.argSet_sq_card_two_mul β h0 hneg
        dsimp [m, γ]
        omega
      have hcast : NumberField.house γ = (NumberField.house β) ^ 2 := by
        dsimp [γ]
        exact Submission.Descent.house_sq β
      have hb_sq : (2 : ℝ) ^ (1 / (4 * (m : ℝ))) ≤ (NumberField.house β) ^ 2 := by
        rw [← hcast]
        have harg : (argSet γ).card = m := rfl
        simpa [Bound, γ, harg] using hbγ
      have hb_half : (2 : ℝ) ^ (1 / (8 * (m : ℝ))) ≤ NumberField.house β := by
        have hsq := rpow_sq_half m hmpos
        have hbβnonneg : 0 ≤ NumberField.house β := NumberField.house_nonneg β
        have h2nonneg : 0 ≤ (2 : ℝ) ^ (1 / (8 * (m : ℝ))) := by positivity
        apply sq_le_sq_of_nonneg h2nonneg hbβnonneg
        calc
          ((2 : ℝ) ^ (1 / (8 * (m : ℝ)))) ^ 2 = (2 : ℝ) ^ (1 / (4 * (m : ℝ))) := hsq
          _ ≤ (NumberField.house β) ^ 2 := hb_sq
      have hexp : (1 / (4 * ((argSet β).card : ℝ)) : ℝ) = 1 / (8 * (m : ℝ)) := by
        have hcast : ((argSet β).card : ℝ) = ((2 * m : ℕ) : ℝ) := by exact_mod_cast hma
        rw [hcast]
        norm_num
        have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
        field_simp [hmR]
        ring
      rw [Bound]
      rw [hexp]
      exact hb_half
  exact hp (minpoly ℤ α).natDegree α hα hα0 hROU rfl

end Submission.Induction

end
