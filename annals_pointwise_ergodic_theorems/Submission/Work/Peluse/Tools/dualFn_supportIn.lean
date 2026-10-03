import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# The support of Peluse's dual function `F₂`

`dualFn M P f₀ f₁ (x) = (1/M) ∑_{y ∈ [M]} f₀ (x - P y) · f₁ (x + y - P y)` is Peluse's dual
function of Corollary 3.8 in the case `ℓ = 2`, `m = 2`, `P₁ = X`.  The purpose of this module is
the support statement recorded in `Submission/Work/Peluse/PLAN.md` §3: if `f₀` and `f₁` are
supported in `[-N, N]`, then `F₂` is supported in `[-dSup P N M, dSup P N M]` with
`dSup P N M = N + polySup P M`, where `polySup P M = ∑_i |a_i| M^i` dominates `|P y|` on `[0, M]`.

The proof is elementary: if `|x| > N + polySup P M` then for every `y ∈ [1, M]` we have
`|x - P y| ≥ |x| - |P y| > N`, so already the *first* factor `f₀ (x - P y)` vanishes.

## Main results

* `eval_abs_le_polySup` — the bound on `|P y|` that defines `polySup` (the same statement as the
  sibling target `Work.Peluse.Tools.polySup_bound`, proved here so that this module is
  self-contained);
* `dualFn_supportIn` — the support statement for `dualFn`.
-/

set_option autoImplicit false

-- the hypotheses `hM`, `hs1`, `hMN` of the target statement are not needed for the support
-- bound (only `hs0` and the definition of `dSup` are); silence the unused-variable linter.
set_option linter.unusedVariables false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Tools

noncomputable section

/-- `polySup P M = ∑_i |a_i| M^i` dominates `|P y|` for every integer `y` with `0 ≤ y ≤ M`.

This is the elementary estimate behind the definition of `dSup`. -/
theorem eval_abs_le_polySup (P : Polynomial ℤ) {M : ℕ} {y : ℤ} (h0 : 0 ≤ y)
    (hy : y ≤ (M : ℤ)) : |P.eval y| ≤ ((Work.Peluse.polySup P M : ℕ) : ℤ) := by
  rw [Work.Peluse.polySup]
  have hsum : P.eval y = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * y ^ i :=
    Polynomial.eval_eq_sum_range y
  rw [hsum]
  have hcast : ((∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs * M ^ i : ℕ) : ℤ)
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i).natAbs : ℤ) * (M : ℤ) ^ i := by
    push_cast
    rfl
  rw [hcast]
  have hyM : |y| ≤ (M : ℤ) := by rw [abs_of_nonneg h0]; exact hy
  calc |∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * y ^ i|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * y ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i).natAbs : ℤ) * (M : ℤ) ^ i := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_pow]
        apply mul_le_mul
        · exact le_of_eq (Int.natCast_natAbs (P.coeff i)).symm
        · exact pow_le_pow_left₀ (abs_nonneg y) hyM i
        · exact pow_nonneg (abs_nonneg y) i
        · exact Int.natCast_nonneg _

theorem dualFn_supportIn {N M : ℕ} (hM : 0 < M) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N) (hs1 : Work.Peluse.SupportIn f₁ N) (hMN : M ≤ N) :
    Work.Peluse.SupportIn (Work.Peluse.dualFn M P f₀ f₁) (Work.Peluse.dSup P N M) := by
  intro x hx
  rw [Work.Peluse.dSup] at hx
  simp only [Work.Peluse.dualFn]
  rw [Finset.sum_eq_zero (fun y hy => ?_), mul_zero]
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  -- the first factor already vanishes, because `|x - P y| > N`
  have hkey : (N : ℤ) < |x - P.eval ((y : ℕ) : ℤ)| := by
    have hS : |P.eval ((y : ℕ) : ℤ)| ≤ ((Work.Peluse.polySup P M : ℕ) : ℤ) :=
      eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy2)
    have hx' : (N : ℤ) + ((Work.Peluse.polySup P M : ℕ) : ℤ) < |x| := by
      rw [← Int.natCast_natAbs x]
      exact_mod_cast hx
    have := abs_sub_abs_le_abs_sub x (P.eval ((y : ℕ) : ℤ))
    linarith
  have hnat : N < (x - P.eval ((y : ℕ) : ℤ)).natAbs := by
    have hcast : (N : ℤ) < (((x - P.eval ((y : ℕ) : ℤ)).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hkey
    exact_mod_cast hcast
  rw [hs0 _ hnat, zero_mul]

end

end Work.Peluse.Tools
