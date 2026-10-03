import Mathlib
import Submission.Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le
import Submission.Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.LSeries

open scoped BigOperators

/-- `χ₄` as a function of `n : ℕ`, explicitly: `χ₄(n) = 1` if `n ≡ 1 (4)`, `-1` if `n ≡ 3 (4)`
and `0` otherwise.  This is the "`chi4_cast_eq`" rewriting used throughout. -/
private lemma chi4Fun_natCast_eq (n : ℕ) :
    Commons.NumberTheory.DirichletCharacter.chi4Fun (n : ZMod 4)
      = if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0 := by
  have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 4 <;>
    simp [Commons.NumberTheory.DirichletCharacter.chi4Fun, ZMod.val_natCast, h]

/-- `χ₄` as a function of `n : ℕ`, explicitly: `χ₄(n) = 1` if `n ≡ 1 (4)`, `-1` if `n ≡ 3 (4)`
and `0` otherwise.  This is the "`chi4_cast_eq`" rewriting used throughout. -/
private lemma chi4_natCast_eq (n : ℕ) :
    Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4)
      = if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0 := by
  rw [Commons.NumberTheory.DirichletCharacter.chi4_apply]
  exact chi4Fun_natCast_eq n

/-- `χ₄` is not the trivial character, so its Dirichlet series converges for `re s > 0`. -/
private lemma chi4_ne_one :
    Commons.NumberTheory.DirichletCharacter.chi4 ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h3 : Commons.NumberTheory.DirichletCharacter.chi4 (3 : ZMod 4)
      = (1 : DirichletCharacter ℂ 4) 3 := by rw [h]
  rw [Commons.NumberTheory.DirichletCharacter.chi4_apply,
      Commons.NumberTheory.DirichletCharacter.chi4Fun_three,
      MulChar.one_apply (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)] at h3
  norm_num at h3

/-- **Logarithmic bound for `L(·,χ₄)` near the line `re s = 1`**, valid for `1 ≤ |Im s|`:
there are `C, c > 0` with `‖L(σ+it, χ₄)‖ ≤ C log(|t|+2)` whenever `1 ≤ |t|` and
`σ ≥ 1 - c/log(|t|+2)`.  Here `χ₄` is `Commons.NumberTheory.DirichletCharacter.chi4`.

PROOF.  Combine the partial-sum bound
`Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one_le`
with the fact that the partial sums converge to `L(·,χ₄)` wherever `re s > 0`
(`Commons.NumberTheory.LSeries.LFunction_eq_tendsto_partial_sums`, applied to `χ₄`; use
`chi4_cast_eq`-style rewriting to identify `chi4 (n : ZMod 4)` with the explicit function
`n ↦ if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0`; the key fact is
`ZMod.val_natCast`).  Then pass to the limit in the inequality (`le_of_tendsto'`).  A COMPLETE
proof of exactly this (for `2 ≤ |t|` and slightly different names) is in the workspace file
`Submission/Chi4ZFR.lean` — it was removed only because the final `chi4_cast_eq` step needed
fixing; the rest of the argument there can be copied verbatim. -/
theorem exists_bound_LFunction_chi4_near_one :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ →
      ‖DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_bound_partial_sums_chi4_near_one_le
  refine ⟨C, min c (1 / 2), hC, lt_min hc (by norm_num), ?_⟩
  intro σ t ht hσ
  set L : ℝ := Real.log (|t| + 2) with hLdef
  -- `L ≥ 1` because `|t| + 2 ≥ 3 > e`
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact le_trans h1
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht]))
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  -- the hypothesis with `min c (1/2)` implies the one with `c`
  have hσ' : 1 - c / L ≤ σ := by
    have hmin : min c (1 / 2) / L ≤ c / L :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
  -- the hypothesis also forces `σ > 0` (indeed `σ ≥ 1/2`)
  have hσpos : 0 < σ := by
    have hmin : min c (1 / 2) / L ≤ 1 / 2 := by
      calc min c (1 / 2) / L ≤ (1 / 2) / L :=
            div_le_div_of_nonneg_right (min_le_right _ _) hLpos.le
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ hLpos]; linarith
    linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  -- convergence of the partial sums to `L(·,χ₄)`
  have hlim := LFunction_eq_tendsto_partial_sums
    Commons.NumberTheory.DirichletCharacter.chi4 chi4_ne_one (s := s)
    (by rw [hsre]; exact hσpos)
  -- the partial sums are bounded, uniformly in `N`
  have hbound' : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4)
          / (n : ℂ) ^ s‖ ≤ C * L := by
    intro N
    have h := hbound σ t ht hσ' N
    rw [← hLdef] at h
    simpa [hsdef, chi4Fun_natCast_eq] using h
  have hlimnorm : Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N,
        Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4) / (n : ℂ) ^ s‖)
      Filter.atTop (nhds ‖DirichletCharacter.LFunction
        Commons.NumberTheory.DirichletCharacter.chi4 s‖) := hlim.norm
  exact le_of_tendsto' hlimnorm hbound'

end Commons.NumberTheory.LSeries
