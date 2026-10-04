import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform bounds for the iterated derivatives of a compactly supported smooth function

If `F : (Fin n → ℝ) → ℂ` vanishes outside the Euclidean ball of radius `√2`
(`∑ i, (y i)^2 ≤ 2`), then `F` has compact support, and since `F` is smooth its `m`-th
iterated derivative `iteratedFDeriv ℝ m F` is continuous; a continuous function with
compact support is bounded. This gives the auxiliary bound `exists_iteratedFDeriv_bound`
used by the `L^∞` estimate for the Friedrichs truncation in the short-time existence
argument.

The only geometry needed is that the set `{y : Fin n → ℝ | ∑ i, (y i)^2 ≤ 2}` is compact:
it is contained in the product of the intervals `[-2, 2]` (in the sup norm on `Fin n → ℝ`,
`∑ i, (y i)^2 ≤ 2` forces `|y i| ≤ 2` for every `i`), and it is closed by continuity of
`y ↦ ∑ i, (y i)^2`.
-/

namespace Work.Diff.STE.Lead.KSBP

/-- A function on `Fin n → ℝ` which vanishes where `2 < ∑ i, (y i) ^ 2` has compact support
(its topological support is contained in the compact set `{y | ∑ i, (y i) ^ 2 ≤ 2}`). -/
theorem hasCompactSupport_of_sq_sum_bound {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hF0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → F y = 0) : HasCompactSupport F := by
  have hcont : Continuous fun y : Fin n → ℝ => ∑ i, (y i) ^ 2 := by fun_prop
  have hKcl : IsClosed {y : Fin n → ℝ | ∑ i, (y i) ^ 2 ≤ 2} :=
    isClosed_Iic.preimage hcont
  refine HasCompactSupport.intro' (K := {y : Fin n → ℝ | ∑ i, (y i) ^ 2 ≤ 2}) ?_ hKcl ?_
  · -- the sup-norm box `[-2,2]^n` is compact and contains the set
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (-2 : ℝ)) (b := 2))) hKcl ?_
    intro y hy
    rw [Set.mem_univ_pi]
    intro i
    have h1 : (y i) ^ 2 ≤ ∑ j, (y j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : (y i) ^ 2 ≤ (2 : ℝ) ^ 2 := by norm_num at *; linarith
    have h3 : |y i| ≤ |(2 : ℝ)| := sq_le_sq.mp h2
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h3
    exact abs_le.mp h3
  · intro y hy
    exact hF0 y (not_le.mp hy)

theorem exists_iteratedFDeriv_bound {n m : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hF0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → F y = 0)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m F y‖ ≤ A := by
  have hcs : HasCompactSupport F := hasCompactSupport_of_sq_sum_bound F hF0
  obtain ⟨C, hC0, hC⟩ := HasCompactSupport.exists_bound_iteratedFDeriv hcs hFs m
  exact ⟨C, hC0, fun y => hC m le_rfl y⟩

end Work.Diff.STE.Lead.KSBP
