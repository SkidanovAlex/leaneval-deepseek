import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.LinnikContract

/-!
# The case split of HB Lemma 9.5 (`h ≥ 5`)

`HBTheorem1_complex_h5plus` (`∃ q₀, ∀ q ≥ q₀, ∀ χ₁ ρ₁, IsMin1WideAt 10 χ₁ ρ₁ →
5 ≤ orderOf χ₁ → 348/1000 ≤ lamOf q ρ₁`) is proved by two mutually exclusive arguments, both of
which derive a contradiction from `λ₁ ≤ 348/1000`:

* **Case A**: every power `χ₁ᵏ` (`1 ≤ k ≤ 4`) has order at most `log(conductor)`, so HB Lemma 2.5
  gives `φ = 1/4` and the `1/8` supply applies (the `(9.16)` combination with `λ* = λ₁`);
* **Case B**: otherwise (`h5CaseB`), using the two repulsion inputs `λ₂ ≥ λ₁ + 0.472` and
  `λ₀ ≥ 0.82`, the `1/6` supply and the base point `λ* = min(λ₀, λ₂)`.

This file contains only that bookkeeping, so that it is independent of the two (large) cases.
-/

/-- `L52Hyp` is monotone in the slack `ε`. -/
theorem L52Hyp_mono_eps {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {c ε ε' δ : ℝ} (h : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) (hε : ε ≤ ε') :
    Commons.NumberTheory.Linnik.L52Hyp χ c ε' δ := by
  intro s h1 h2 h3
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have := h s h1 h2 h3
  nlinarith [hlog]

/-- **The assembly of HB Lemma 9.5's `h ≥ 5` case** from its two halves.

`hA` is Case A with its supply hypothesis in *disjunctive* form (the `1/8` supply holds either
because `orderOf χ ≤ log(conductor)` or because `χ ^ 60 = 1`); `hB` is Case B, which needs
`6 ≤ orderOf χ₁`.  The two branches are complementary: if some power `χ₁ᵏ` satisfies neither
disjunct, then `orderOf χ₁ ∤ 60` (since `orderOf χ₁ ∣ 60` would give `(χ₁ᵏ)^60 = 1`), so with
`5 ≤ orderOf χ₁` we get `6 ≤ orderOf χ₁`. -/
theorem h5plus_of_cases
    (hA : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ → lamOf q ρ₁ ≤ 348/1000 →
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        ((orderOf (χ₁ ^ k) : ℝ) ≤ Real.log ((((χ₁ ^ k).conductor : ℕ) : ℝ)) ∨
          (χ₁ ^ k) ^ 60 = 1)) → False)
    (hB : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 6 ≤ orderOf χ₁ → lamOf q ρ₁ ≤ 348/1000 →
      False) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ →
      348/1000 ≤ lamOf q ρ₁ := by
  obtain ⟨qA, hA'⟩ := hA
  obtain ⟨qB, hB'⟩ := hB
  refine ⟨max qA qB, ?_⟩
  intro q hq inst χ₁ ρ₁ hm h5
  have hqA : qA ≤ q := le_trans (le_max_left _ _) hq
  have hqB : qB ≤ q := le_trans (le_max_right _ _) hq
  by_contra hcon
  push_neg at hcon
  have hle : lamOf q ρ₁ ≤ 348/1000 := le_of_lt hcon
  by_cases hdisj : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      ((orderOf (χ₁ ^ k) : ℝ) ≤ Real.log ((((χ₁ ^ k).conductor : ℕ) : ℝ)) ∨ (χ₁ ^ k) ^ 60 = 1)
  · exact hA' q hqA χ₁ ρ₁ hm h5 hle hdisj
  · push_neg at hdisj
    obtain ⟨k, hk1, hk4, hkA, hkB⟩ := hdisj
    have hpow_ne : (χ₁ ^ k) ^ 60 ≠ 1 := hkB
    have h60 : ¬ (orderOf χ₁ ∣ 60) := by
      intro hdvd
      refine hpow_ne ?_
      have h1 : χ₁ ^ 60 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      rw [← pow_mul, Nat.mul_comm k 60, pow_mul, h1, one_pow]
    have h6 : 6 ≤ orderOf χ₁ := by
      by_contra hcon6
      push_neg at hcon6
      have hfive : orderOf χ₁ = 5 := by omega
      exact h60 (by rw [hfive]; norm_num)
    exact hB' q hqB χ₁ ρ₁ hm h6 hle

end Work.ZeroFreeTables.HB94
