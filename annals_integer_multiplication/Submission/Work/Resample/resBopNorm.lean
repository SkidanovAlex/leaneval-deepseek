import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.tensorNorm

/-!
# Operator norm of `resBop`

`B = ⊗ᵢ resB sᵢ tᵢ α` is the tensor (Kronecker) product of the one-dimensional matrices
`resB sᵢ tᵢ α` from Theorem 4.1.  Since each one-dimensional factor satisfies
`‖(resB sᵢ tᵢ α).mulVec v‖ ≤ ‖v‖` (a component of `HvdH.ResMath1DProp`), the tensor product
is a contraction in the sup norm, by `Work.Resample.tensorNorm`.
-/

namespace Work.Resample

/-- The one-dimensional factor of the tensor `resBop`, written as a flat sum against the
unbundled entry function `rB`, is the `mulVec` of the bundled matrix `HvdH.resB`. -/
lemma rB_sum_eq_mulVec (s t α : ℕ) (x : Fin t → ℂ) :
    (fun j : Fin s => ∑ k : Fin t, rB s t α (j : ℕ) (k : ℕ) * x k) =
      (HvdH.resB s t α).mulVec x := by
  funext j
  rw [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro k _
  rw [rB, unb_apply]

theorem resBopNorm (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts)
    (hM : HvdH.ResMath1DProp) (v : Fin ts.prod → ℂ) :
    ‖Work.Resample.resBop ss ts α v‖ ≤ ‖v‖ := by
  -- The two dimension lists have the same length `D`.
  have hlen : ss.length = ts.length := by
    have h1 : ss.length = HvdH.D := h.1
    have h2 : ts.length = HvdH.D := h.2.1
    omega
  -- Each one-dimensional factor is a contraction.
  have hm : ∀ i < ts.length, ∀ x : Fin (ts.getD i 0) → ℂ,
      ‖(fun j : Fin (ss.getD i 0) =>
          ∑ k : Fin (ts.getD i 0),
            (fun i => rB (ss.getD i 0) (ts.getD i 0) α) i (j : ℕ) (k : ℕ) * x k)‖ ≤
        (fun _ : ℕ => (1 : ℝ)) i * ‖x‖ := by
    intro i hi x
    have hiD : i < HvdH.D := lt_of_lt_of_eq hi h.2.1
    obtain ⟨hs, hst, _hlt, hcop, hrat⟩ := h.2.2.2.2.2 i hiD
    obtain ⟨-, -, -, -, -, -, -, hbnd⟩ :=
      hM (ss.getD i 0) (ts.getD i 0) α p hs hst hcop h.2.2.2.1 h.2.2.2.2.1 hrat
    have heq : (fun j : Fin (ss.getD i 0) =>
          ∑ k : Fin (ts.getD i 0), rB (ss.getD i 0) (ts.getD i 0) α (j : ℕ) (k : ℕ) * x k) =
        (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec x :=
      rB_sum_eq_mulVec _ _ _ x
    rw [heq]
    simpa using hbnd x
  have htn := tensorNorm ts ss hlen
      (fun i => rB (ss.getD i 0) (ts.getD i 0) α) (fun _ : ℕ => (1 : ℝ)) hm v
  rw [resBop, tensorLin_apply]
  simpa using htn

end Work.Resample
