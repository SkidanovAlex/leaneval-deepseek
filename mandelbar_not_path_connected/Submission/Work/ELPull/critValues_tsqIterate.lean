import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Critical values of `(Tsq c)^[m]` lie on the critical orbit of `Tantibar c`

`Tsq c = (Tantibar c)^[2]` is the holomorphic second iterate of the antiholomorphic quadratic
`Tantibar c`.  Its critical values are `Tantibar c 0` and `(Tantibar c)^[2] 0`, i.e. the first
two points of the critical orbit of `Tantibar c`.

Because the critical points of an iterate propagate along the orbit (chain rule), every critical
value of `(Tsq c)^[m]` is obtained by applying some power `(Tsq c)^[n] = (Tantibar c)^[2n]`
(`0 ≤ n ≤ m-1`) to one of those two points; hence it is a point `(Tantibar c)^[k] 0` of the
critical orbit with `1 ≤ k ≤ 2m`.

This is the statement `critValues_tsqIterate` needed for the pull-back bijection of the EL area.
-/

noncomputable section

open Function
namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar)

/-- `(Tantibar c)^[2] z = Tantibar c (Tantibar c z)`. -/
@[simp]
lemma Tantibar_iterate_two_apply (c z : ℂ) :
    (Tantibar c)^[2] z = Tantibar c (Tantibar c z) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]

/-- **Critical values of `Tsq c`.**  If `deriv (Tsq c) z = 0` then `Tsq c z` is the first or the
second point of the critical orbit of `Tantibar c`. -/
lemma critValue_Tsq (c z : ℂ) (hz : deriv (Work.Landing.Tsq c) z = 0) :
    Work.Landing.Tsq c z = (Tantibar c)^[1] 0 ∨ Work.Landing.Tsq c z = (Tantibar c)^[2] 0 := by
  rw [Work.ELRig.deriv_Tsq] at hz
  rcases mul_eq_zero.mp hz with h4z | hz2
  · rcases mul_eq_zero.mp h4z with h40 | hz0
    · exact absurd h40 (by norm_num)
    · right
      rw [hz0]
      simp [Work.Landing.Tsq, Tantibar]
  · left
    have hsq : (z ^ 2 + star c) ^ 2 = 0 := by rw [hz2, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [Work.Landing.Tsq_apply, hsq, zero_add]
    rw [Function.iterate_one]
    simp [Tantibar]

/-- `(Tsq c)^[n]` applied to the `j`-th point of the critical orbit of `Tantibar c`. -/
lemma Tsq_iterate_apply_T (c : ℂ) (n j : ℕ) :
    (Work.Landing.Tsq c)^[n] ((Tantibar c)^[j] 0) = (Tantibar c)^[2 * n + j] 0 := by
  rw [Work.ELRig.Tsq_eq_Tantibar_iterate_two c, ← Function.iterate_mul]
  exact (Function.iterate_add_apply (Tantibar c) (2 * n) j 0).symm

/-- **Critical values of `(Tsq c)^[m]` lie on the critical orbit of `Tantibar c`.** -/
theorem critValues_tsqIterate {c : ℂ} (m : ℕ) :
    ∀ z : ℂ, deriv ((Work.Landing.Tsq c)^[m]) z = 0 →
      ∃ k ∈ Finset.Icc 1 (2 * m),
        (Work.Landing.Tsq c)^[m] z = (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 := by
  intro z hz
  have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  rw [Work.ELRig.deriv_iterate_eq_prod hdiff] at hz
  rw [Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, hi, hdi⟩ := hz
  rw [Finset.mem_range] at hi
  have hcv := critValue_Tsq c ((Work.Landing.Tsq c)^[i] z) hdi
  have h1 : (Work.Landing.Tsq c)^[m] z
      = (Work.Landing.Tsq c)^[m - i] ((Work.Landing.Tsq c)^[i] z) := by
    conv_lhs => rw [show m = (m - i) + i from (Nat.sub_add_cancel (le_of_lt hi)).symm]
    rw [Function.iterate_add_apply]
  have h2 : (Work.Landing.Tsq c)^[m - i] ((Work.Landing.Tsq c)^[i] z)
      = (Work.Landing.Tsq c)^[m - i - 1]
          ((Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[i] z)) := by
    conv_lhs =>
      rw [show m - i = (m - i - 1) + 1 from
        (Nat.sub_add_cancel (Nat.sub_pos_of_lt hi)).symm]
    rw [Function.iterate_add_apply, Function.iterate_one]
  rcases hcv with hcv | hcv
  · refine ⟨2 * (m - i - 1) + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]; omega
    · rw [h1, h2, hcv]
      exact Tsq_iterate_apply_T c (m - i - 1) 1
  · refine ⟨2 * (m - i - 1) + 2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]; omega
    · rw [h1, h2, hcv]
      exact Tsq_iterate_apply_T c (m - i - 1) 2

end Work.ELPull
