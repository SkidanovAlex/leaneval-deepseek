/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Npair6SupAux/ip6_cs_cd` — Cauchy–Schwarz for `IP6 1…1` at finite smoothness order

The Cauchy–Schwarz clause of the level-six inner product `IP6`,

  `|IP6 1 … 1 α f g| ≤ CC · |f|_{ℋ⁶} · |g|_{ℋ⁶}`,

is needed by the `N₀`-row of the strong-solution route for profiles that are only `C⁶` on
the open quadrant (and honestly in `ℋ⁶`) — not `C^∞`, so the `SmoothOpen`-based
`StrongPersist.IP6_cs_coeffs` does not apply to them.

The finite-order statement is exactly the `Transfer.CSQ` chain of the transfer chapter,
viewed at level six:

* `IP6 1 1 1 1 1 1 1 1 1 1 α` is the paper's recursion `HkIPStep 1 1` applied five times
  on top of `H1IP α` (`IP6`, `IP4`, definitionally — `IPit α 5` below is that composite);
* `Transfer.CSQ α n IP CC` is `|IP X Y| ≤ CC |X|_{ℋⁿ} |Y|_{ℋⁿ}` for `X, Y ∈ Cⁿ(Qd) ∩ ℋⁿ`;
* the base case `Transfer.CSQ_one` is Cauchy–Schwarz for `H1IP` from `HkMem α 1` alone
  (constant `10^22`, `H1IP_cs_of_mem`);
* one lift is `Transfer.CSQ_succ`: it multiplies the constant by `3 · max 1 (max c₁ c₂)`
  and spends exactly the finite-order descent (`Transfer.HkMem_descent_Q0Sm`,
  `Transfer.HkSq_Dz_le_Q0Sm`, `CoercivityStep.Norm.HkSq_Dth_le`).

Five lifts therefore give the bound at level six with the `α`-free constant
`(3 · max 1 (max 1 1))^5 · 10^22`, and the hypotheses `ContDiffOn ℝ 6` are literally the
class `Q0Sm 6` of the open quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_one
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The paper's recursion `IP^{n+1} = HkIPStep 1 1 IP^n` iterated `n` times on top of
`H1IP α`: `IPit α 0 = H1IP α`, `IPit α (n+1) = HkIPStep 1 1 (IPit α n)`.

`IPit α 5` is the concrete level-six pairing of this chapter: with all ten step
coefficients equal to one, `Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α` is `IPit α 5`
by definitional unfolding. -/
def IPit (α : ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | (n + 1) => Work.Coercivity.HkIPStep 1 1 (IPit α n)

/-- The recursion step of `IPit`, by definition. -/
theorem IPit_succ (α : ℝ) (n : ℕ) :
    IPit α (n + 1) = Work.Coercivity.HkIPStep 1 1 (IPit α n) := rfl

/-- **The finite-order Cauchy–Schwarz chain for the iterated pairing.**  The `n`-fold
iterate of one step of the paper's recursion on top of `H1IP` satisfies a Cauchy–Schwarz
bound at level `n + 1` with the explicit, `α`-free constant
`(3 · max 1 (max 1 1))^n · 10^22`.

The proof is `Transfer.CSQ_one` (level 1, constant `10^22`) followed by `n` applications of
`Transfer.CSQ_succ`; each step multiplies the constant by `3 · max 1 (max 1 1)`, so the
constant is `(3 · max 1 (max 1 1))^n · 10^22`.  No positivity of the coefficients is
needed (`c₁ = c₂ = 1 > 0` here). -/
theorem CSQ_iter (α : ℝ) (hα : 0 < α) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.CSQ α (n + 1) (IPit α n)
      (((3 : ℝ) * max 1 (max 1 1)) ^ n * (10 : ℝ) ^ 22) := by
  have hKpos : (0 : ℝ) ≤ (3 : ℝ) * max 1 (max 1 1) := by
    have hmax : (0 : ℝ) < (3 : ℝ) * max 1 (max 1 1) := by
      rw [show max 1 (max 1 1) = (1 : ℝ) from by simp]
      norm_num
    exact le_of_lt hmax
  induction n with
  | zero =>
      have h := Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα
      simp only [Work.FTS.CoercivityFix.Transfer.CSQ, IPit, pow_zero, one_mul]
      exact fun X Y _ _ hX hY => h X Y hX hY
  | succ n ih =>
      have hstep := Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα (n + 1)
        (IP := IPit α n) (CC := ((3 : ℝ) * max 1 (max 1 1)) ^ n * (10 : ℝ) ^ 22)
        (c₁ := 1) (c₂ := 1)
        (mul_nonneg (pow_nonneg hKpos n) (by norm_num)) (by norm_num) (by norm_num) ih
      have hconst : (3 : ℝ) * max 1 (max 1 1)
            * (((3 : ℝ) * max 1 (max 1 1)) ^ n * (10 : ℝ) ^ 22)
          = ((3 : ℝ) * max 1 (max 1 1)) ^ (n + 1) * (10 : ℝ) ^ 22 := by
        rw [pow_succ]
        ring
      rw [hconst] at hstep
      exact hstep

/-- **Cauchy–Schwarz for `IP6 1 … 1` at finite smoothness order.**  There is a constant
`CC > 0` and a range `α ∈ (0, α₂]` such that for every pair of profiles which are `C⁶` on
the open quadrant and honestly in `ℋ⁶`, the level-six pairing is bounded by
`CC |f|_{ℋ⁶} |g|_{ℋ⁶}`. -/
theorem ip6_cs_cd : ∃ CC α₂ : ℝ, 0 < CC ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ u v : Work.FTS.Galerkin.Fn,
    ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.HkMem α 6 u → Work.Spaces.HkMem α 6 v →
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
      ≤ CC * Work.Spaces.HkNorm α 6 u * Work.Spaces.HkNorm α 6 v := by
  refine ⟨((3 : ℝ) * max 1 (max 1 1)) ^ 5 * (10 : ℝ) ^ 22, 1, ?_, one_pos, ?_⟩
  · have hmax : (0 : ℝ) < (3 : ℝ) * max 1 (max 1 1) := by
      rw [show max 1 (max 1 1) = (1 : ℝ) from by simp]
      norm_num
    exact mul_pos (pow_pos hmax 5) (by norm_num)
  · intro α hα u v hu hv hmu hmv
    have h := CSQ_iter α hα.1 5
    have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α = IPit α 5 := rfl
    rw [hIP6]
    have hu6 : Work.FTS.CoercivityFix.Transfer.Q0Sm 6 u := hu
    have hv6 : Work.FTS.CoercivityFix.Transfer.Q0Sm 6 v := hv
    exact h u v hu6 hv6 hmu hmv

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
