import Submission.FUP.HilbertLine

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# §4, step 8 (first part): the compactly supported truncations of the modified weight

Cohen's §4 applies `prop:Ew_is_psh` (Proposition 3.3) to the **compactly supported truncations**

  `T_n = ∑_{k < n} ω̃_k`

of the modified weight `ω̃ = ∑_k ω̃_k`, and then passes to the limit using Lemma 3.1
(`lem:Ew_conv_cpct_subsets`).  These are exactly the `T` appearing in
`modify_weight_statement`.

This module collects the structural properties of the truncations: they are `C³`, compactly
supported, nonpositive, converge pointwise to `ω̃`, and their iterated derivatives are the finite
sums of the derivatives of the pieces (so that the second-derivative condition of
`exact_psh_extension_statement` follows from
`SecondDerivSum.sum_abs_integral_second_deriv_le` by finite additivity).
-/

/-- The compactly supported truncation `T_n = ∑_{k<n} ω̃_k` of the modified weight. -/
noncomputable def truncSum (n : ℕ) (w : ℝᵈ → ℝ) : ℝᵈ → ℝ :=
  fun x => ∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w x

lemma truncSum_apply (n : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    truncSum (d := d) n w x = ∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w x := rfl

/-- The truncations are `C³`. -/
theorem truncSum_contDiff (n : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiff ℝ 3 (truncSum (d := d) n w) := by
  refine ContDiff.sum fun k _ => ?_
  by_cases hk1 : 1 ≤ k
  · exact contDiff_omegaTildePiece k hw hk1
  · have heq : omegaTildePiece (d := d) k w = omegaPiece k w :=
      funext fun x => omegaTildePiece_of_lt k w (by omega : k < 2) x
    rw [heq]
    exact contDiff_omegaPiece hw k le_rfl

/-- The truncations are compactly supported. -/
theorem truncSum_hasCompactSupport (n : ℕ) (w : ℝᵈ → ℝ) :
    HasCompactSupport (truncSum (d := d) n w) := by
  induction n with
  | zero =>
      rw [show truncSum (d := d) 0 w = 0 from funext fun x => by simp [truncSum]]
      exact HasCompactSupport.zero
  | succ m ih =>
      rw [show truncSum (d := d) (m + 1) w
            = truncSum (d := d) m w + omegaTildePiece (d := d) m w from
          funext fun x => by simp [truncSum, Finset.sum_range_succ]]
      exact ih.add (hasCompactSupport_omegaTildePiece m w)

/-- The truncations are nonpositive (they are partial sums of nonpositive pieces). -/
lemma truncSum_nonpos (n : ℕ) {w : ℝᵈ → ℝ}
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) (x : ℝᵈ) :
    truncSum (d := d) n w x ≤ 0 :=
  Finset.sum_nonpos fun k _ => hwk k x

/-- The `a`-th iterated derivative (`a ≤ 3`) of the truncation is the finite sum of the iterated
derivatives of the pieces. -/
theorem iteratedFDeriv_truncSum (n a : ℕ) (ha : a ≤ 3) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (x : ℝᵈ) :
    iteratedFDeriv ℝ a (truncSum (d := d) n w) x
      = ∑ k ∈ Finset.range n, iteratedFDeriv ℝ a (omegaTildePiece (d := d) k w) x := by
  have hcd : ∀ k ∈ Finset.range n, ContDiff ℝ a (omegaTildePiece (d := d) k w) := by
    intro k _
    by_cases hk1 : 1 ≤ k
    · exact (contDiff_omegaTildePiece k hw hk1).of_le (by exact_mod_cast ha)
    · have heq : omegaTildePiece (d := d) k w = omegaPiece k w :=
        funext fun x => omegaTildePiece_of_lt k w (by omega : k < 2) x
      rw [heq]
      exact contDiff_omegaPiece hw k ha
  have h4 : iteratedFDeriv ℝ a
        (fun y => ∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w y) x
      = ∑ k ∈ Finset.range n, iteratedFDeriv ℝ a (omegaTildePiece (d := d) k w) x := by
    have h3 := iteratedFDeriv_sum (𝕜 := ℝ) (f := fun k => omegaTildePiece (d := d) k w)
      (u := Finset.range n) (i := a) hcd
    rw [h3, Finset.sum_apply]
  have h2 : truncSum (d := d) n w
      = fun y => ∑ k ∈ Finset.range n, omegaTildePiece (d := d) k w y := by
    funext y
    simp only [truncSum]
  rw [h2]
  exact h4

/-- The truncations converge pointwise to the modified weight. -/
theorem truncSum_tendsto (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    Tendsto (fun n => truncSum (d := d) n w x) atTop (𝓝 (omegaTildeSum w x)) := by
  obtain ⟨N, hN⟩ := exists_pow_gt_norm (d := d) x
  rw [omegaTildeSum_eq_sum_range N w hN]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  rw [truncSum_apply]
  have hsub : Finset.range (N + 1) ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hvan : ∀ k, k ∈ Finset.range n → k ∉ Finset.range (N + 1) →
      omegaTildePiece (d := d) k w x = 0 := by
    intro k hk1 hk2
    have hk3 : N + 1 ≤ k := by
      by_contra hc
      push Not at hc
      exact hk2 (Finset.mem_range.mpr hc)
    exact omegaTildePiece_eq_zero_of_norm_le_pred k (by omega) w (by
      calc ‖x‖ ≤ (2 : ℝ) ^ N := le_of_lt hN
        _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega))
  exact Finset.sum_subset hsub hvan

end Submission.FUP
