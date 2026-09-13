/-
# Monotonicity of the concrete operator family `Fop`

`Fop C ε M = tr(C ∘ M) + ε σ₂(M)`.  The operator is *elliptic* on the range of operators on which
`C + ε • cof(T)` is positive semidefinite: adding a positive semidefinite increment `N = S - T ⪰ 0`
to the argument increases `Fop` by `tr((C + ε • cof T) ∘ N) + ε σ₂(N) ≥ 0`.

This is what replaces the comparison principle in the maximum-principle step of the growth lemma:
if `φ` is a solution (`Fop C ε (D²φ) = 0`) and `Φ` is a strict supersolution
(`Fop C ε (D²Φ) > 0`) with `D²Φ ⪰ -R • 1`, `D²φ ⪯ R • 1` for `R` small enough, then `φ - Φ` cannot
attain an interior minimum.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

theorem pairOp_add_left (S₁ S₂ M : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp (S₁ + S₂) M = pairOp S₁ M + pairOp S₂ M := by
  unfold pairOp
  simp only [add_apply, inner_add_left, Finset.sum_add_distrib]

/-- **Monotonicity of `Fop`.**  If `S ⪰ T` (quadratic-form sense) and `C + ε • cofOp T ⪰ 0`, then
`Fop C ε T ≤ Fop C ε S`. -/
theorem Fop_mono {C S T : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {ε : ℝ} (hε : 0 ≤ ε)
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hST : ∀ v : ℝ⁴, 0 ≤ ⟪(S - T) v, v⟫)
    (hCT : ∀ v : ℝ⁴, 0 ≤ ⟪(C + ε • cofOp T) v, v⟫) :
    Fop C ε T ≤ Fop C ε S := by
  set N : ℝ⁴ →L[ℝ] ℝ⁴ := S - T with hNdef
  have hNsym : N.IsSymmetric := hS.sub hT
  have hNpos : ∀ v : ℝ⁴, 0 ≤ ⟪N v, v⟫ := hST
  have hST_eq : S = T + N := by rw [hNdef]; abel
  have hexp : s2 S = s2 T + s2 N + pairOp (cofOp T) N := by
    rw [hST_eq, s2_add_expansion hT hNsym]
  have hcofT : (cofOp T).IsSymmetric := by
    rw [cofOp]
    exact LinearMap.IsSymmetric.sub
      (LinearMap.IsSymmetric.smul (c := trOp T) (by simp) LinearMap.IsSymmetric.one) hT
  have hCεsym : (C + ε • cofOp T).IsSymmetric :=
    hC.add (LinearMap.IsSymmetric.smul (c := ε) (by simp) hcofT)
  have hpair : 0 ≤ pairOp (C + ε • cofOp T) N := by
    have h := Commons.Analysis.Trace.trace_comp_ge_of_quadform_bounds
      (C := C + ε • cofOp T) (N := N) hCεsym hNsym (c₁ := 0)
      (fun v => by simpa using hCT v) hNpos
    rw [pairOp_eq_trace]
    simpa using h
  have hs2N : 0 ≤ s2 N := s2_nonneg_of_quadform_nonneg hNsym hNpos
  have hsplit : pairOp (C + ε • cofOp T) N = pairOp C N + ε * pairOp (cofOp T) N := by
    rw [pairOp_add_left, pairOp_const_smul_left]
  have hCsplit : pairOp C S = pairOp C T + pairOp C N := by
    rw [hST_eq, pairOp_add]
  have hgoal : Fop C ε S
      = Fop C ε T + (pairOp C N + ε * pairOp (cofOp T) N + ε * s2 N) := by
    unfold Fop
    rw [hexp, hCsplit]
    ring
  rw [hgoal]
  have hmain : 0 ≤ pairOp C N + ε * pairOp (cofOp T) N + ε * s2 N := by
    have h1 := hpair
    rw [hsplit] at h1
    nlinarith [h1, hs2N, hε]
  linarith

end

end Submission
