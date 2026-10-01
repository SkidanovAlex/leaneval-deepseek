import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs

set_option linter.unusedVariables false

namespace Work.LinnikAreas.JutilaPieces

/-! ## Elementary auxiliary estimates for the Abel weight

These are the (formerly `private`) helper lemmas of
`Submission/Work/ZeroDensity/Jutila/S3GAbelSharp.lean`, re-homed here so that the
`S₃` assembly can reference them across modules. -/

private lemma log_two_mul_sub_abs_bound (X : ℕ) (α : ℝ) :
    |Real.log (X : ℝ) - α| ≤ 2 * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
  by_cases hX : X = 0
  · subst hX
    simp only [Nat.cast_zero, mul_zero, Real.log_zero, zero_sub, abs_neg]
    linarith [abs_nonneg α]
  have hX0 : (0 : ℝ) < (X : ℝ) := by positivity
  have hlog : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log (X : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hX0)
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsplit : Real.log (X : ℝ) - α
      = -(Real.log 2) + (Real.log (2 * (X : ℝ)) - α) := by rw [hlog]; ring
  calc |Real.log (X : ℝ) - α| = |-(Real.log 2) + (Real.log (2 * (X : ℝ)) - α)| := by rw [hsplit]
    _ ≤ |-(Real.log 2)| + |Real.log (2 * (X : ℝ)) - α| := abs_add_le _ _
    _ = Real.log 2 + |Real.log (2 * (X : ℝ)) - α| := by rw [abs_neg, abs_of_nonneg hlog2nn]
    _ ≤ 2 * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
        linarith [abs_nonneg (Real.log (2 * (X : ℝ)) - α)]

private lemma log_succ_sub_log_bounds (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ∧
      Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) := by positivity
  have hdiv : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
      = Real.log (((m : ℝ) + 1) / (m : ℝ)) :=
    (Real.log_div (by positivity) (ne_of_gt hm0)).symm
  constructor
  · rw [hdiv]
    have h := Real.one_sub_inv_le_log_of_pos hx
    have heq : 1 - (((m : ℝ) + 1) / (m : ℝ))⁻¹ = 1 / ((m : ℝ) + 1) := by
      rw [inv_div]; field_simp; ring
    rwa [heq] at h
  · rw [hdiv]
    have h := Real.log_le_sub_one_of_pos hx
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp; ring
    rwa [heq] at h

private lemma sqrt_div_self (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) / (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  rw [div_eq_div_iff (ne_of_gt hm0) (ne_of_gt hs), one_mul, ← pow_two, Real.sq_sqrt hm0.le]

private lemma inv_mul_sqrt_eq (m : ℕ) (hm : 1 ≤ m) :
    (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
  rw [show (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = Real.sqrt (m : ℝ) / (m : ℝ) from by ring,
    sqrt_div_self m hm]

private lemma wfun_abs_le (X : ℕ) (α β : ℝ) :
    |Work.LinnikAreas.Density4.BzS3.wfun α β X| ≤
      4 * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  have h1 := log_two_mul_sub_abs_bound X α
  have h2 := log_two_mul_sub_abs_bound X β
  rw [Work.LinnikAreas.Density4.BzS3.wfun, abs_mul]
  calc |Real.log (X : ℝ) - α| * |Real.log (X : ℝ) - β|
      ≤ (2 * (1 + |Real.log (2 * (X : ℝ)) - α|)) * (2 * (1 + |Real.log (2 * (X : ℝ)) - β|)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by ring

private lemma wfun_diff_le (m : ℕ) (hm : 1 ≤ m) (α β : ℝ) :
    |Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1) - Work.LinnikAreas.Density4.BzS3.wfun α β m|
      ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hδlb, hδub⟩ := log_succ_sub_log_bounds m hm
  have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hbound : |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| ≤ 1 / (m : ℝ) := by
    rw [abs_of_nonneg (le_trans (by positivity) hδlb)]
    exact hδub
  simp only [Work.LinnikAreas.Density4.BzS3.wfun, hcast]
  have hfac : (Real.log ((m : ℝ) + 1) - α) * (Real.log ((m : ℝ) + 1) - β)
      - (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)
      = (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
        * ((Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)) := by ring
  rw [hfac, abs_mul]
  have h2 : |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
      ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ) := by
    have hsplit : (Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)
        = (Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β)
          + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    calc |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
        = |((Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β))
            + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))| := by rw [hsplit]
      _ ≤ |(Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β)|
            + |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| := abs_add_le _ _
      _ ≤ (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + 1 / (m : ℝ) :=
          add_le_add (abs_add_le _ _) hbound
  have hone : (1 : ℝ) ≤ 1 / (m : ℝ) * (m : ℝ) := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hm0)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  calc |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)|
        * |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
      ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ)) :=
        mul_le_mul hbound h2 (abs_nonneg _) (by positivity)
    _ ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1) := by
        have h3 : (0 : ℝ) ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| := by positivity
        have : (1 : ℝ) / (m : ℝ) ≤ 1 := by
          rw [div_le_one hm0]; exact hm1
        nlinarith [h3, this, hm0]

private lemma log_pred_sub_abs_le (X : ℕ) (hX : 2 ≤ X) (γ : ℝ) :
    |Real.log (((X - 1 : ℕ)) : ℝ) - γ| ≤ |Real.log (X : ℝ) - γ| + 1 := by
  have h1 : 1 ≤ X - 1 := by omega
  have hδ := (log_succ_sub_log_bounds (X - 1) h1).2
  have hcast : ((X - 1 : ℕ) : ℝ) + 1 = (X : ℝ) := by
    have h : X - 1 + 1 = X := by omega
    rw [← h]; push_cast; ring
  have hp0 : (0 : ℝ) < (((X - 1 : ℕ)) : ℝ) := by
    exact_mod_cast (by omega : 0 < X - 1)
  have hδ' : Real.log (X : ℝ) - Real.log (((X - 1 : ℕ)) : ℝ) ≤ 1 := by
    have h := hδ
    rw [hcast] at h
    have h2 : 1 / (((X - 1 : ℕ)) : ℝ) ≤ 1 := by
      rw [div_le_one hp0]; exact_mod_cast h1
    linarith [h, h2]
  have hle0 : Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ) ≤ 0 := by
    have hmono : Real.log (((X - 1 : ℕ)) : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast (by omega : X - 1 ≤ X))
    linarith
  have habs : |Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)| ≤ 1 := by
    rw [abs_of_nonpos hle0]
    linarith [hδ']
  have hsplit : Real.log (((X - 1 : ℕ)) : ℝ) - γ
      = (Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)) + (Real.log (X : ℝ) - γ) := by ring
  rw [hsplit]
  calc |(Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)) + (Real.log (X : ℝ) - γ)|
      ≤ |Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)| + |Real.log (X : ℝ) - γ| :=
        abs_add_le _ _
    _ ≤ |Real.log (X : ℝ) - γ| + 1 := by linarith [habs]

/-- Pointwise bounds for the Abel weight `wfun α β m = (log m − α)(log m − β)` and its increment,
the five elementary estimates used by the sharp Abel error term of the `S₃` assembly.
These are verbatim transcriptions of the `private` lemmas
`log_two_mul_sub_abs_bound`, `wfun_abs_le`, `wfun_diff_le`, `log_pred_sub_abs_le` and
`inv_mul_sqrt_eq` of `Submission/Work/ZeroDensity/Jutila/S3GAbelSharp.lean` (which cannot be
referenced across modules because they are `private`); read that file for the proofs.

Conjuncts:
1. `|log X − α| ≤ 2·(1 + |log(2X) − α|)`;
2. `|wfun α β X| ≤ 4·(1+|log(2X)−α|)·(1+|log(2X)−β|)`;
3. for `m ≥ 1`, `|wfun α β (m+1) − wfun α β m| ≤ (1/m)·(|log m − α| + |log m − β| + 1)`;
4. for `X ≥ 2`, `|log(X−1) − γ| ≤ |log X − γ| + 1`;
5. for `m ≥ 1`, `(1/m)·√m = 1/√m`. -/
theorem S3GWfunPointwise :
    (∀ (X : ℕ) (α : ℝ),
        |Real.log (X : ℝ) - α| ≤ 2 * (1 + |Real.log (2 * (X : ℝ)) - α|))
    ∧ (∀ (X : ℕ) (α β : ℝ),
        |Work.LinnikAreas.Density4.BzS3.wfun α β X| ≤
          4 * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|))
    ∧ (∀ (m : ℕ) (hm : 1 ≤ m) (α β : ℝ),
        |Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)
            - Work.LinnikAreas.Density4.BzS3.wfun α β m|
          ≤ (1 / (m : ℝ))
              * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
    ∧ (∀ (X : ℕ) (hX : 2 ≤ X) (γ : ℝ),
        |Real.log (((X - 1 : ℕ) : ℝ)) - γ| ≤ |Real.log (X : ℝ) - γ| + 1)
    ∧ (∀ (m : ℕ) (hm : 1 ≤ m),
        (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = 1 / Real.sqrt (m : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X α
    exact log_two_mul_sub_abs_bound X α
  · intro X α β
    exact wfun_abs_le X α β
  · intro m hm α β
    exact wfun_diff_le m hm α β
  · intro X hX γ
    exact log_pred_sub_abs_le X hX γ
  · intro m hm
    exact inv_mul_sqrt_eq m hm

end Work.LinnikAreas.JutilaPieces
