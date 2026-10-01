import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.LinnikAreas.DhRepel

open scoped Classical BigOperators

/-- Monotonicity of the finitely supported sum `∑ᶠ` for a pointwise dominated pair:
if `f ≤ g` pointwise, `g` is nonnegative and has finite support, then `∑ᶠ f ≤ ∑ᶠ g`.
(The case where `f` itself has infinite support is handled by the convention `∑ᶠ f = 0`
for a function with infinite support.) -/
lemma finsum_le_finsum_of_le {α : Type*} {f g : α → ℝ} (hfg : ∀ a, f a ≤ g a)
    (hg0 : ∀ a, 0 ≤ g a) (hfin : Function.HasFiniteSupport g) :
    (∑ᶠ a, f a) ≤ ∑ᶠ a, g a := by
  by_cases hf : Function.HasFiniteSupport f
  · exact finsum_le_finsum' hf hfin hfg
  · rw [finsum_of_not_hasFiniteSupport hf]
    exact finsum_nonneg hg0

/-- **Multiplicity-weighted near sum bounded by the zero count in the rectangle.**
The multiplicity-weighted sum of the zeros `u` of `L(·,χ)` with `|Im u| ≤ 10 log q` and
`λ(u) = (1 - Re u) log q ≤ t` is at most the number (with multiplicity) of the zeros in the
rectangle `1 - t/log q ≤ Re ≤ 1`, `|Im| ≤ 10 log q`.

Indeed `λ(u) ≤ t` is equivalent to `Re u ≥ 1 - t/log q` (as `log q > 0`), and every zero
counted by `zeroMult` has `Re < 1` (`boxMaxZeroAux.zeroMult_re_lt_one`), so the near sum's
support is contained in the rectangle; the two `finsum`s are therefore sums over the same
finite box and the integrands agree there, while both are nonnegative. -/
theorem nearSumLeZeroCountIn {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧ |u.im| ≤ 10 * Real.log (q : ℝ) ∧
        Work.LinnikContract.lamOf q u ≤ t
      then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
      ≤ Work.LinnikAreas.zeroCountIn χ (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)) := by
  classical
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  -- the finite box containing (the support of) both integrands
  have hbox : ({u : ℂ | Work.LinnikContract.zeroMult χ u ≠ 0 ∧
      1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 10 * Real.log (q : ℝ)} :
      Set ℂ).Finite :=
    boxMaxZeroAux.finite_zeroMult_box χ (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ))
  -- pointwise domination of the two integrands
  have hpoint : ∀ u : ℂ,
      (if Work.LinnikContract.zeroMult χ u ≠ 0 ∧ |u.im| ≤ 10 * Real.log (q : ℝ) ∧
          Work.LinnikContract.lamOf q u ≤ t
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
      ≤ (if 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 10 * Real.log (q : ℝ)
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0) := by
    intro u
    by_cases hc : Work.LinnikContract.zeroMult χ u ≠ 0 ∧ |u.im| ≤ 10 * Real.log (q : ℝ) ∧
        Work.LinnikContract.lamOf q u ≤ t
    · -- a near zero: `λ(u) ≤ t` gives `Re u ≥ 1 - t/log q`, and `Re u < 1`
      obtain ⟨hzm, him, hlam⟩ := hc
      have h1 : (1 - u.re) * Real.log (q : ℝ) ≤ t := by
        simpa only [Work.LinnikContract.lamOf] using hlam
      have h2 : 1 - u.re ≤ t / Real.log (q : ℝ) := (le_div_iff₀ hlog).mpr h1
      have hcond : 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ) :=
        ⟨by linarith, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hzm), him⟩
      rw [if_pos ⟨hzm, him, hlam⟩, if_pos hcond]
    · -- otherwise the left-hand side vanishes
      rw [if_neg hc]
      by_cases hc2 : 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ)
      · rw [if_pos hc2]; exact Nat.cast_nonneg _
      · rw [if_neg hc2]
  -- the right-hand integrand has finite support, inside the box
  have hgfin : Function.HasFiniteSupport (fun u : ℂ =>
      if 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 10 * Real.log (q : ℝ)
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0) := by
    refine hbox.subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_cases hc2 : 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im| ≤ 10 * Real.log (q : ℝ)
    · rw [if_pos hc2] at hu
      exact ⟨Nat.cast_ne_zero.mp hu, hc2.1, hc2.2.1, hc2.2.2⟩
    · rw [if_neg hc2] at hu
      exact absurd rfl hu
  have hmain : (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
        |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
      then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
      ≤ (∑ᶠ u : ℂ, if 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im| ≤ 10 * Real.log (q : ℝ)
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0) :=
    finsum_le_finsum_of_le hpoint (fun u => by
      by_cases hc2 : 1 - t / Real.log (q : ℝ) ≤ u.re ∧ u.re ≤ 1 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ)
      · rw [if_pos hc2]; exact Nat.cast_nonneg _
      · rw [if_neg hc2]) hgfin
  unfold Work.LinnikAreas.zeroCountIn
  exact hmain

end Work.LinnikAreas.DhRepel
