import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the formal tower of the nonlinearity (flat DeTurck case)

`Work.Diff.STE.flat.towerExp Φ j` is the `j`-th formal time derivative of the nonlinearity `Φ`,
expressed as a function of the space point `x` and of the spatial `2`-jets `(J₀, …, J_{j-1})` of the
first `j` time derivatives of the unknown, with the recursion (see
`Submission.Work.Diff.STE.flat.TowerDefs`)

`towerExp Φ (j+2) (x, Js) = ∑ i, (D_i H_{j+1})(x, J₀, …, J_j) [J_{i+1}]`,

which is *by construction* the chain rule for `∂_t (H_{j+1}(x, jets))` under `∂_t J_i = J_{i+1}`.

This file proves the piece of that chain rule needed for the "derivative tower" step of the plan of
`TowerDefs.lean` (step 3): if for every `i : Fin j` the path `s ↦ Δ i.castSucc s` has derivative
`Δ i.succ t` at `t` within `[0, τ)`, and the tower `towerExp Φ j` is differentiable at the jets
`fun i : Fin j => Δ i.castSucc t`, then

`s ↦ towerExp Φ j (x, fun i : Fin j => Δ i.castSucc s)`

has derivative `towerExp Φ (j+1) (x, fun l : Fin (j+1) => Δ l t)` at `t` within `[0, τ)`.

The mathematical content is exactly the chain rule, the multilinearity of the Fréchet derivative,
and the (definitional) identification of `towerExp Φ (j+1)` with the sum of the partial derivatives
of `towerExp Φ j` against the "velocity" components `Δ i.succ t`.  The two elementary facts about
the Fréchet derivative that are used are isolated above as `fderiv_prod_slice` (the derivative of a
slice of a function on a product) and `fderiv_prod_slice_sum` (its decomposition along the
coordinates).
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

noncomputable section

/-- **The derivative of a slice of a function on a product.**  If `G : E × (ι → V) → W` is
differentiable at `(a, J)`, then the derivative of the slice `Js ↦ G (a, Js)` at `J` applied to `v`
is the derivative of `G` at `(a, J)` applied to `(0, v)`. -/
theorem fderiv_prod_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (G : E × (ι → V) → W) (a : E) (J v : ι → V)
    (hG : DifferentiableAt ℝ G (a, J)) :
    fderiv ℝ G (a, J) (0, v) = fderiv ℝ (fun Js : ι → V => G (a, Js)) J v := by
  have h : HasFDerivAt (fun Js : ι → V => G (a, Js))
      ((fderiv ℝ G (a, J)).comp (ContinuousLinearMap.inr ℝ E (ι → V))) J :=
    hG.hasFDerivAt.comp J (hasFDerivAt_prodMk_right a J)
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- **The derivative of a slice, decomposed along the coordinates.**  For `G` differentiable at
`(a, J)`, the derivative of the slice `Js ↦ G (a, Js)` at `J` applied to `v` is the sum of its
values on the coordinate vectors `Function.update 0 i (v i)`. -/
theorem fderiv_prod_slice_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (G : E × (ι → V) → W) (a : E) (J v : ι → V)
    (hG : DifferentiableAt ℝ G (a, J)) :
    fderiv ℝ G (a, J) (0, v) =
      ∑ i : ι, fderiv ℝ (fun Js : ι → V => G (a, Js)) J (Function.update 0 i (v i)) := by
  have hsum : (∑ i : ι, Function.update (0 : ι → V) i (v i)) = v := by
    ext j
    simp only [Finset.sum_apply, Function.update_apply, Pi.zero_apply]
    rw [Finset.sum_ite_eq]
    simp
  calc fderiv ℝ G (a, J) (0, v)
      = fderiv ℝ (fun Js : ι → V => G (a, Js)) J v := fderiv_prod_slice G a J v hG
    _ = fderiv ℝ (fun Js : ι → V => G (a, Js)) J (∑ i : ι, Function.update 0 i (v i)) := by
          rw [hsum]
    _ = ∑ i : ι, fderiv ℝ (fun Js : ι → V => G (a, Js)) J (Function.update 0 i (v i)) := by
          rw [map_sum]

/-- **The chain rule for the formal tower.**  If the jet path `s ↦ (Δ 0 s, …, Δ (j-1) s)` has
velocity `(Δ 1 t, …, Δ j t)` at `t` within `[0, τ)` and the tower `towerExp Φ j` is differentiable
at the corresponding jets, then the composition with the tower has derivative `towerExp Φ (j+1)`
there. -/
theorem towerExp_hasDerivWithinAt {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : 1 ≤ j)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (x : Fin n → ℝ) (t : ℝ) (Δ : Fin (j + 1) → ℝ → Work.Diff.STE.Flat.Jet n)
    (hdiff : DifferentiableAt ℝ (Work.Diff.STE.flat.towerExp Φ j)
      (x, fun i : Fin j => Δ i.castSucc t))
    (hΔ : ∀ i : Fin j, HasDerivWithinAt (fun s : ℝ => Δ i.castSucc s) (Δ i.succ t)
      (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.flat.towerExp Φ j
        (x, fun i : Fin j => Δ i.castSucc s))
      (Work.Diff.STE.flat.towerExp Φ (j + 1) (x, fun l : Fin (j + 1) => Δ l t))
      (Set.Ico (0 : ℝ) τ) t := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  -- the jet path and its velocity
  have hpath : HasDerivWithinAt
      (fun s : ℝ => (x, fun i : Fin (k + 1) => Δ i.castSucc s))
      ((0 : Fin n → ℝ), fun i : Fin (k + 1) => Δ i.succ t) (Set.Ico (0 : ℝ) τ) t :=
    HasDerivWithinAt.prodMk (hasDerivWithinAt_const t (Set.Ico (0 : ℝ) τ) x)
      (hasDerivWithinAt_pi.mpr (fun i => hΔ i))
  -- the chain rule
  have hchain := HasFDerivAt.comp_hasDerivWithinAt t hdiff.hasFDerivAt hpath
  -- identify the derivative with the next entry of the tower (the definitional recursion)
  have heq : (fderiv ℝ (towerExp Φ (k + 1))
        (x, fun i : Fin (k + 1) => Δ i.castSucc t)) (0, fun i : Fin (k + 1) => Δ i.succ t)
      = towerExp Φ (k + 2) (x, fun l : Fin (k + 2) => Δ l t) := by
    rw [fderiv_prod_slice_sum (towerExp Φ (k + 1)) x _ _ hdiff]
    rw [towerExp_succ_succ]
  rw [← heq]
  exact hchain

end

end Work.Diff.STE.flat
