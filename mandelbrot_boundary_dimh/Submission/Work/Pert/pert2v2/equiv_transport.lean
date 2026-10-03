import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Repel.chain_preimage_mem

/-!
# `Work.Pert.pert2v2.equiv_transport` — transporting the `R`-block's fields along the `ℤ`-action

The two-piece glue produces `R` on `DR = ⋃_{n : ℤ} (· + n) '' (Ulow ∪ Uhigh)` with
`MandelDim.IsTEquivariantOn R DR`, and the six `PertData` `R`-fields are proven on the *charts*
(`Ulow`, `Uhigh`) at first.  Since the contract asks for them on the band (= the translation
saturation of the charts), they have to be transported along the `ℤ`-action.  `Work.Repel`'s
`chainPre_equiv_add_int` does the `R`-side; this file packages the transport for `R_close`
(the `d.E`-side is `ParabData.E_add_nat`-like, transported by the same walk).
-/

namespace Work.Pert.pert2v2

open MandelDim

/-- **`ℤ`-transport of a T-equivariant map's own equivariance.**  (Restatement of
`Work.Repel.chainPre_equiv_add_int` at the interface, kept here so the assembly has one import.) -/
theorem R_add_int {R : ℂ → ℂ} {DR : Set ℂ} (hR : MandelDim.IsTEquivariantOn R DR) (n : ℤ) {w : ℂ}
    (hw : w ∈ DR) : R (w + (n : ℂ)) = R w + (n : ℂ) :=
  Work.Repel.chainPre_equiv_add_int hR n hw

/-- **`ℤ`-transport of a `T`-equivariant target map along a `T`-invariant domain.**  If `E` is
`T`-equivariant on the `T`-invariant `S` then so is it along the whole walk: `E (w+n) = E w + n`. -/
theorem E_add_int {E : ℂ → ℂ} {S : Set ℂ} (hS : MandelDim.IsTInvariant S)
    (hE : ∀ w ∈ S, w + 1 ∈ S → E (w + 1) = E w + 1) :
    ∀ (n : ℤ) (w : ℂ), w ∈ S → E (w + (n : ℂ)) = E w + (n : ℂ) := by
  intro n w hw
  have hEq : MandelDim.IsTEquivariantOn E S := ⟨hS, fun z hz => hE z hz ((hS z).mp hz)⟩
  exact Work.Repel.chainPre_equiv_add_int hEq n hw

/-- **`R_close` on the saturation from `R_close` on a fundamental window.**  If `‖R x + 1/α - E x‖ < δ`
holds on a `T`-invariant set `S` on which both `R` and `E` are `T`-equivariant, then it holds on
every `ℤ`-translate of a point of `S` — which is exactly the step from "the chart" to "the band". -/
theorem R_close_transport {R E : ℂ → ℂ} {DR S : Set ℂ} {α : ℂ} {δ : ℝ}
    (hDR : MandelDim.IsTEquivariantOn R DR) (hS : MandelDim.IsTInvariant S) (hsub : S ⊆ DR)
    (hE : ∀ w ∈ S, w + 1 ∈ S → E (w + 1) = E w + 1)
    (h : ∀ w ∈ S, ‖R w + 1 / α - E w‖ < δ) :
    ∀ (n : ℤ) (w : ℂ), w ∈ S → w + (n : ℂ) ∈ S →
      ‖R (w + (n : ℂ)) + 1 / α - E (w + (n : ℂ))‖ < δ := by
  intro n w hw _
  rw [R_add_int hDR n (hsub hw), E_add_int hS hE n w hw]
  have hstep : ‖R w + (n : ℂ) + 1 / α - (E w + (n : ℂ))‖ = ‖R w + 1 / α - E w‖ := by
    congr 1
    ring
  rw [hstep]
  exact h w hw

end Work.Pert.pert2v2
