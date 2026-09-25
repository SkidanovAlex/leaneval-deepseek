/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary definitions for the `L²` bound `Work.NN.Core.czB_L2_bounded`

This file contains the flat Laplacian on `ℂⁿ = Fin n → ℂ`, written through the Wirtinger
derivatives, which is the second order operator driving the energy identity
`Σ_k ∫ ‖∂_k u‖² = -(1/4) ∫ u · conj (Δ u)` used for the requested `L²` bound.

* `flatLap f z = 4 * Σ_k ∂_k (∂̄_k f) z`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

/-- The flat Laplacian on `ℂⁿ`, written in Wirtinger form: `Δ f = 4 Σ_k ∂_k ∂̄_k f`. -/
noncomputable def flatLap {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  4 * ∑ k : Fin n, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k f w) z

@[simp] lemma flatLap_apply {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    flatLap f z = 4 * ∑ k : Fin n, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k f w) z :=
  rfl

/-- The Wirtinger form with the two derivatives exchanged (for `C²` functions). -/
lemma flatLap_eq_sum_dbarCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    flatLap f z
      = 4 * ∑ k : Fin n, Work.CR.Flat.dbarCoord k (fun w => Work.CR.Flat.dCoord k f w) z := by
  rw [flatLap_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Work.CR.Flat.Cauchy.dbarCoord_dCoord_comm k k f z hf).symm

end Work.NN.Core
