/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT/WeakDescent`: tools for the diagonal-honesty strengthening of `EllWeakPos`

The level-`0` route of §'Elliptic Regularity Estimates' (Step 2 of `prop:H2`, i.e. the two
integrations by parts of `remov/AeI1PaperHolds`) needs one hypothesis that the current
`TT.EllWeakPos` does **not** carry: the *diagonal second-order honesty*

  `Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)`

i.e. the honesty of `∂_θθ(z ∂_zu)` (equivalently `IPMem (grad u) (ang2 (grad u))`).  It is not
implied by the other fields — the separable counterexample of `H2W/AeWAux/NOTES_aeI1Data_FALSE.md`
(four reviews) — and it is exactly what makes the `θ`-flux
`θ ↦ σ·(z∂_zΨ)·∂_θ(z∂_zΨ)` absolutely continuous with vanishing endpoint values; with only
`HkMem α 0 (grad u)` — even with the *first-order* mixed honesty
`HkMem α 0 (fun z θ => z * pz (pth u) z θ)` — the step is false (declared FALSE by a dispatched
prover: that honesty gives only the trace of `U = z∂_zu`, not the pairing `⟨U, ∂_θθU⟩`).
Full diagnosis: `AeI1Paper_repair.md`, `Cores/AeStep2AngAux/NOTES_MixedMem_FALSE.md`.

This module holds the *plumbing* of the strengthening, so that applying it is mechanical:

* `smoothOpen_diagHon` — the diagonal-honesty integrand `z ↦ z ∂_z∂_θθΨ` is smooth on the open
  quadrant whenever `Ψ` is (`D_z ∘ ∂_z ∘ ∂_θ²`), the smoothness witness that the level-descent
  `HkMem_descend_open` of the new conjunct needs;
* `EllWeakPos.descend_data` — the level-descent of the four `HkMem` fields of `EllWeakPos`,
  *including* the diagonal-honesty field (taken as a hypothesis at the higher level).

Both are stated with hypotheses only, so this module builds independently of whether the field has
been added to `EllWeakPos`; the seven construction sites listed in `NOTES_DELIVERY.md` §9 use
`EllWeakPos.descend_data` in place of their four-field anonymous constructor.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The diagonal-honesty integrand `z ↦ z ∂_z∂_θθΨ` is smooth of every finite order on the open
quadrant as soon as the same holds for `∂_θθΨ`: it is `D_z (∂_z (∂_θθΨ))`, and `SmoothOpen` is
closed under `D_z` and `∂_z`. -/
theorem smoothOpen_diagHon {Ψ : ℝ → ℝ → ℝ}
    (hB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pthIter 2 Ψ)).mpr hB
  have hDz : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz h2
  have hfun : Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)
      = fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := rfl
  rw [hfun] at hDz
  exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hDz

/-- **Level-descent of the four `HkMem` fields of `EllWeakPos`**, the diagonal-honesty field
included (it is taken here as a hypothesis at the higher level `l`): the smoothness witnesses of
the four integrands and the four honesty fields at level `l` give the four honesty fields at any
level `k ≤ l`. -/
theorem EllWeakPos.descend_data {α : ℝ} {k l : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hkl : k ≤ l)
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hA : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmF : Work.Spaces.HkMem α l F)
    (hmA : Work.Spaces.HkMem α l (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmB : Work.Spaces.HkMem α l (Work.Spaces.pthIter 2 Ψ))
    (hmZ : Work.Spaces.HkMem α l (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.Spaces.HkMem α k F ∧
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) ∧
      Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
  ⟨HkMem_descend_open (α := α) hkl hF hmF,
    HkMem_descend_open (α := α) hkl hA hmA,
    HkMem_descend_open (α := α) hkl hB hmB,
    HkMem_descend_open (α := α) hkl (smoothOpen_diagHon hB) hmZ⟩

end Work.FTS.EllipticEst.TT

end
