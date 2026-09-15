import Submission.FUP.GrowthTilde
import Submission.FUP.Step8
import Submission.FUP.ExtensionOperator
import Submission.FUP.EomegaTail

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# §4 of Cohen's paper: the modified weight

This module assembles `modify_weight_statement` — the paper's `lem:modify_weight_lemma` — from
the pieces proved in `ModifyWeightAssemble`, `SecondDerivSum`, `HilbertPointwise`,
`HilbertLinear`, `Step8` and `GrowthTilde`:

* `ω̃ = ∑_k ω̃_k` is the modified weight, `T_n = ∑_{k<n} ω̃_k` its compactly supported truncations;
* `ω̃ ≤ ω`, `ω̃ = 0` on `B₂`, `ω̃` and all `T_n` are Lipschitz with a constant `C_reg · C(d)`;
* the growth functionals of `ω̃` and of every `T_n` are bounded by `C(P(d) C_reg + 2^13 C_gr)`;
* each `T_n` satisfies the two conditions of `prop:Ew_is_psh`.
-/

/-- **`lem:modify_weight_lemma`.**  For every nonpositive weight `ω` with Kohn–Nirenberg
regularity and finite Beurling–Malliavin growth there are a modified weight `ω̃ ≤ ω` and
compactly supported truncations `T_n ↑ ω̃` with the properties listed in
`Submission.FUP.modify_weight_statement`. -/
theorem modify_weight_statement_proof (hd : 1 ≤ d) : modify_weight_statement (d := d) := by
  intro Creg Cgr hCreg hCgr
  have hLippos : 0 < omegaLipConst d := by
    rw [omegaLipConst, tildeLipConst]
    have h2 := pieceConst_pos d
    have h3 := gkLipConst_nonneg d
    linarith
  refine ⟨400 * (Creg * tildeConst d) + 256 * Cgr,
    32 * Creg * tildeConst d + 256 * Cgr + 4 * (Creg * pieceConst d) + 1,
    Creg * omegaLipConst d, 8 * (Creg * pieceConst d) + 8192 * Cgr + 1,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tildeConst_pos d
    positivity
  · have h1 := tildeConst_pos d
    have h2 := pieceConst_pos d
    positivity
  · positivity
  · have h1 := pieceConst_pos d
    positivity
  intro w hωnonpos hωzero hωcont hωbound hωgrowth
  have hωreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro x
    have h := hωbound 0 (by norm_num) x
    simpa [norm_iteratedFDeriv_zero] using h
  have hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0 := by
    intro k x
    rw [omegaTildePiece]
    split_ifs with hk
    · exact omegaPiece_nonpos hωnonpos k x
    · simp only [omegaTilde]
      exact add_nonpos (omegaPiece_nonpos hωnonpos k x)
        (gk_nonpos k (by omega) hCreg.le hωreg x)
  refine ⟨omegaTildeSum (d := d) w, fun n => truncSum (d := d) n w,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact truncSum_contDiff n hωcont
  · intro n
    exact truncSum_hasCompactSupport n w
  · intro n x
    exact truncSum_nonpos n hwk x
  · intro x
    exact truncSum_tendsto w x
  · exact contDiff_omegaTildeSum (d := d) hd hωcont
  · intro x
    exact omegaTildeSum_le_self w hωzero hCreg.le hωreg x
  · intro x hx
    exact omegaTildeSum_eq_zero_of_norm_le w hωzero hx
  · intro x₁ x₂
    exact lipschitz_omegaTildeSum (d := d) hd hωcont hωzero hCreg hωbound x₁ x₂
  · exact hasFiniteGrowth_omegaTildeSum (d := d) hd hωcont hωnonpos hωzero hCreg hωbound
      hωgrowth hwk
  · intro n x₁ x₂
    exact lipschitz_truncSum (d := d) hd n hωcont hωzero hCreg hωbound x₁ x₂
  · intro n
    exact hasFiniteGrowth_truncSum (d := d) hd n hωcont hωnonpos hωzero hCreg hωbound
      hωgrowth hwk
  · intro n x y hy
    exact abs_hilbertLine_truncSum_le (d := d) hd n hωcont hωnonpos hωzero hCreg hωbound
      hωgrowth hwk x y hy
  · intro n x y v hy hv hvperp
    exact integral_iteratedFDeriv_two_truncSum_ge (d := d) hd n hωcont hωnonpos hωzero hCreg
      hωbound hωgrowth x y v hy hv hvperp
  · intro K hK
    exact tendstoUniformlyOn_EomegaC_truncSum (d := d) hd hωcont hωnonpos hωzero hCreg
      hωbound hωgrowth hwk K hK

end Submission.FUP
