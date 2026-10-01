/-
# `InvNearSum` is antitone in the radius `δ`

`Work.ZeroFreeTables.InvNearSum N χ s δ` (HB Lemma 3.1's near-zero sum) is the finitely
supported sum over the zeros `u` of `Λ(χ,·)` within `δ` of the test point `1 + i·Im s`,
weighted by the multiplicity and by `Re (1/(s-u))`.  Since the multiplier does not depend
on `δ`, the sum is just the sum of the *same nonnegative* summands over a set of `u` that
grows with `δ`; hence it is antitone in `δ` (for `δ ≤ 1`, `Re s ≥ 1`).

The two ingredients are:

* every nonzero summand comes from a genuine zero `u` of `Λ(χ,·)` with **positive**
  multiplicity (`pdiv` is the divisor of an entire function, hence `≥ 0`), and
* such a zero satisfies `Re u < 1` (`Commons.NumberTheory.Linnik.completedL_zero_strip`),
  so `Re s ≥ 1 > Re u` forces `Re (1/(s-u)) ≥ 0`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum

namespace Work.ZeroFreeTables.P9

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- The divisor of an analytic function at a point of its domain is the vanishing order,
as an integer. -/
private lemma divisor_eq_order {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  simp only [analyticOrderNatAt]
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- The divisor defining `pdiv` has finite support (it is the divisor of the meromorphic
function `Λ(χ,·)` inside a compact closed ball). -/
private lemma pdiv_support_finite_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) :
    (Function.support (fun u : ℂ => Work.ZeroFreeTables.pdiv N χ s u)).Finite := by
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  rw [show (fun u : ℂ => Work.ZeroFreeTables.pdiv N χ s u)
      = fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u from rfl]
  exact MeromorphicOn.divisor_support_finite_of_subset hAn.meromorphicOn
    (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _)

/-- A nonzero value of the divisor `pdiv` at `u` means that `u` is a zero of
`Λ(χ,·)`; the divisor value itself is a (nonnegative) multiplicity. -/
private lemma pdiv_ne_zero_imp_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) {u : ℂ} (h : Work.ZeroFreeTables.pdiv N χ s u ≠ 0) :
    DirichletCharacter.completedLFunction χ u = 0 ∧
      0 ≤ ((Work.ZeroFreeTables.pdiv N χ s u : ℤ) : ℝ) := by
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hu : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    by_contra hmem
    exact h (by
      show Work.ZeroFreeTables.pdiv N χ s u = 0
      unfold Work.ZeroFreeTables.pdiv
      rw [MeromorphicOn.divisor_def]
      simp [hmem])
  have hval : Work.ZeroFreeTables.pdiv N χ s u
      = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
    unfold Work.ZeroFreeTables.pdiv
    exact divisor_eq_order hAn hu
  have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
    intro h0
    exact h (by rw [hval, h0]; simp)
  refine ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero hord, ?_⟩
  rw [hval]
  exact Int.cast_nonneg (Nat.cast_nonneg _)

/-- The near-disk multiplier is monotone in the radius, provided the kernel is
nonnegative. -/
private lemma ite_mul_le_ite_mul {r e t δ δ' : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e) (hδ' : δ' ≤ δ) :
    r * (if t ≤ δ' then e else 0) ≤ r * (if t ≤ δ then e else 0) := by
  by_cases h : t ≤ δ
  · rw [if_pos h]
    by_cases h' : t ≤ δ'
    · rw [if_pos h']
    · rw [if_neg h', mul_zero]; exact mul_nonneg hr he
  · have h' : ¬ t ≤ δ' := fun hc => h (le_trans hc hδ')
    rw [if_neg h, if_neg h']

theorem InvNearSum_anti {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} (hs : 1 ≤ s.re) {δ δ' : ℝ} (hδ' : δ' ≤ δ) (hδ : δ ≤ 1) :
    Work.ZeroFreeTables.InvNearSum N χ s δ' ≤ Work.ZeroFreeTables.InvNearSum N χ s δ := by
  have hfin : (Function.support (fun u : ℂ => Work.ZeroFreeTables.pdiv N χ s u)).Finite :=
    pdiv_support_finite_aux χ hχ s
  -- every nonzero summand is a genuine zero, and contributes a nonnegative amount
  have hne : ∀ u : ℂ, Work.ZeroFreeTables.pdiv N χ s u ≠ 0 →
      0 ≤ ((Work.ZeroFreeTables.pdiv N χ s u : ℤ) : ℝ) ∧ 0 ≤ ((1 / (s - u)).re) := by
    intro u hp
    refine ⟨(pdiv_ne_zero_imp_aux χ hχ s hp).2, ?_⟩
    have hz : DirichletCharacter.completedLFunction χ u = 0 :=
      (pdiv_ne_zero_imp_aux χ hχ s hp).1
    have hu : u.re < 1 := (Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hprim hz).2
    rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re]
    linarith
  unfold Work.ZeroFreeTables.InvNearSum
  refine finsum_le_finsum' ?_ ?_ ?_
  · exact hfin.subset (fun u hu => by
      simp only [Function.mem_support] at hu ⊢
      intro h0; exact hu (by simp [h0]))
  · exact hfin.subset (fun u hu => by
      simp only [Function.mem_support] at hu ⊢
      intro h0; exact hu (by simp [h0]))
  · intro u
    dsimp only
    by_cases hp : Work.ZeroFreeTables.pdiv N χ s u = 0
    · rw [hp]; simp
    · obtain ⟨hnn, hre⟩ := hne u hp
      exact ite_mul_le_ite_mul hnn hre hδ'

end Work.ZeroFreeTables.P9
