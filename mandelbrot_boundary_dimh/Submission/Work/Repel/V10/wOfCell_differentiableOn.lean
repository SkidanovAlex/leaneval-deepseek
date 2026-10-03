import Mathlib
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.chain_preimage_mem
import Submission.Work.Repel.walk_of_sub
import Submission.Work.L62.chain

/-!
# `Work.Repel.wOfCell_differentiableOn`

The map `wOfCell q` of Shishikura's §6 composite (`Submission/Work/Repel/chain_v9_chase.lean`),

  `w' q w = wOf (ĥ^[j] (uOfSrc q w) - k)`,   `q = (j, k, n)`, `ĥ = R - β`,

is the level-0 target of the cell `q`: it first takes the level-1 source
`u = (φ₁|Sm1)⁻¹ (s·π w)` of `w`, walks `j` steps down the chain `W ·` (i.e. applies `ĥ^[j]`,
sending the shifted fibre `W j + k` onto `W 0 + k`), removes the integer shift `k`, and finally
lifts `φ₁ u'/s` back to the level-0 plane by `wOf`.

This file proves that this map is holomorphic on the source region

  `Src q = B n ∩ {w | s·π w ∈ φ₁ '' (W j + k)}`

of the cell.  The proof is the pointwise chase, in the same order as the map:

* `uOfSrc q w = uOf (s·π w)` is differentiable within `Src q`: `π` is entire and, on `Src q`, the
  substituted point `s·π w` lies in `φ₁ '' Sm1`, the set on which `uOf` is differentiable by
  hypothesis (`huOfD`, the resolution of the "differentiability at the boundary of the closed
  disc `Sm1`" issue recorded in the §6 progress notes);
* the walk `ĥ^[i] u` (`i < j`) stays in the open set `DR` — its unshifted part lies in
  `W (j - i) ⊆ DR` (`W j ⊆ DR` for `j ≥ 1`) and `DR` is `T`-invariant, so the integer shift is
  harmless — hence `ĥ^[j]` is differentiable at `u` (`R` is differentiable on `DR` and `DR` is
  open);
* the shifted endpoint `ĥ^[j] u - k` lies in `W 0` (the chain walk is a bijection
  `W j + k → W 0 + k`), and `wOf` is differentiable on `W 0` (`V10.wOf_differentiableOn`).

Note the hypothesis `hj : 1 ≤ j` is *not* used by the argument: for `j = 0` the statement is
vacuous (`∀ i < 0` is empty and `wOfCell (0,k,n)` is `wOf (· - k)`, differentiable on a region of
`B n`); `j ≥ 1` is exactly the regime of the cells of the count, where `W j + k ⊆ Sm1` is one of
the cell's defining properties.  We keep it since it is the statement we were asked to prove.
-/

namespace Work.Repel

open MandelDim Set Metric Filter Topology

noncomputable section

/-- **The walk of a `T`-translate of a chain fibre stays in `DR`.**  If `u ∈ W j + k` for a chain
`W ·`, then the first `j` points of the orbit of `u` under `ĥ = R - β` lie in `DR`: the unshifted
part is in `W (j - i) ⊆ DR`, and `DR` is invariant under integer translations. -/
lemma wOfCell_walk_mem_DR {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ}
    {ρ sgn C₀ C₁ C₁' : ℝ} {W : ℕ → Set ℂ}
    (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hReq : MandelDim.IsTEquivariantOn R DR) {j : ℕ} {k : ℤ} {u : ℂ}
    (hu : u ∈ (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W j) :
    ∀ i < j, (fun w => R w - β)^[i] u ∈ DR := by
  obtain ⟨w₀, hw₀, hw₀eq⟩ := hu
  have hTeq : MandelDim.IsTEquivariantOn (fun w => R w - β) DR :=
    Work.L62.isTEquivariantOn_sub hReq
  intro i hi
  have hwalk : ∀ t < i, (fun w => R w - β)^[t] w₀ ∈ DR := by
    intro t ht
    exact h.W_subset_DR (j := j - t) (by omega)
      (chainPre_iterate_mem h (j := j) (i := t) (by omega) hw₀)
  have hmem : (fun w => R w - β)^[i] w₀ ∈ DR :=
    h.W_subset_DR (j := j - i) (by omega)
      (chainPre_iterate_mem h (j := j) (i := i) (by omega) hw₀)
  rw [show u = w₀ + (k : ℂ) from hw₀eq.symm,
    chainPre_iterate_add_int hTeq i k hwalk]
  exact Work.Horn.MandelDim.IsTInvariant.add_int hReq.1 hmem k

/-- **Differentiability of the `j`-fold iterate along a walk.**  If `R` is differentiable on `DR`
and the first `j` points of the orbit of `u` under `ĥ = R - β` are neighbourhoods of `DR`, then
`ĥ^[j]` is differentiable at `u`.  No invariance of `DR` is needed, only the pointwise hypothesis
(the `T`-translation of the walk in `DR` is what supplies it in the application). -/
lemma wOfCell_differentiableAt_iterate {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ}
    (hR : DifferentiableOn ℂ R DR) :
    ∀ {j : ℕ} {u : ℂ}, (∀ i < j, DR ∈ 𝓝 ((fun w => R w - β)^[i] u)) →
      DifferentiableAt ℂ ((fun w => R w - β)^[j]) u := by
  intro j
  induction j with
  | zero =>
      intro u _
      exact differentiableAt_id
  | succ n ih =>
      intro u hu
      have h1 : DifferentiableAt ℂ (fun w : ℂ => R w - β) ((fun w => R w - β)^[n] u) :=
        (hR.differentiableAt (hu n (Nat.lt_succ_self n))).sub_const β
      have h2 : DifferentiableAt ℂ ((fun w => R w - β)^[n]) u :=
        ih (fun i hi => hu i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      have h3 := h1.comp u h2
      simpa only [Function.iterate_succ'] using h3

/-- **The target of a cell lies in `W 0`.**  For `w ∈ Src q` the level-1 source
`u = uOf (s·π w)` lies in the shifted fibre `W j + k` (by injectivity of `φ₁` on `Sm1`), and the
chain walk `ĥ^[j] : W j + k → W 0 + k` is the integer translate of `ĥ^[j] : W j → W 0`; dividing by
the shift, `ĥ^[j] u - k ∈ W 0`. -/
lemma wOfCell_target_mem (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hSm : (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.Src (j, k, n)) :
    (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w))
      - ((k : ℤ) : ℂ) ∈ V.W 0 := by
  obtain ⟨w₀, hw₀, hw₀eq⟩ := V.uOfSrc_mem_fibre hSm hw
  have hiter₀ : ∀ i < j, (fun x : ℂ => V.R x - V.β)^[i] w₀ ∈ V.DR := fun i hi =>
    V.hIsChain.W_subset_DR (j := j - i) (by omega)
      (chainPre_iterate_mem V.hIsChain (j := j) (i := i) (by omega) hw₀)
  rw [show V.uOf (V.s * MandelDim.piExp w) = w₀ + (k : ℂ) from hw₀eq.symm,
    chainPre_iterate_add_int (Work.L62.isTEquivariantOn_sub V.hReq) j k hiter₀]
  simpa using V.hIsChain.iterate_mem hw₀

/-- **The level-1 source is holomorphic on the cell.**  On `Src q` the point `s·π w` lies in the
image `φ₁ '' Sm1`, where `uOf` is differentiable by hypothesis; `π` is entire. -/
lemma wOfCell_uOfSrc_differentiableWithinAt (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hSm : (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j ⊆ V.Sm1)
    (huOfD : DifferentiableOn ℂ V.uOf (V.P₁.φ '' V.Sm1)) {w : ℂ}
    (hw : w ∈ V.Src (j, k, n)) :
    DifferentiableWithinAt ℂ (fun w : ℂ => V.uOf (V.s * MandelDim.piExp w))
      (V.Src (j, k, n)) w := by
  have hSmin : V.s * MandelDim.piExp w ∈ V.P₁.φ '' V.Sm1 := Set.image_mono hSm hw.2
  have hinner : DifferentiableWithinAt ℂ (fun z : ℂ => V.s * MandelDim.piExp z)
      (V.Src (j, k, n)) w :=
    ((differentiable_piExp.const_mul V.s).differentiableAt).differentiableWithinAt
  have houter : DifferentiableWithinAt ℂ V.uOf (V.P₁.φ '' V.Sm1)
      ((fun z : ℂ => V.s * MandelDim.piExp z) w) := huOfD _ hSmin
  exact houter.comp w hinner (fun z hz => Set.image_mono hSm hz.2)

/-- **`wOfCell q` is holomorphic on the source region of the cell `q = (j,k,n)`.** -/
theorem wOfCell_differentiableOn (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j ⊆ V.Sm1)
    (huOfD : DifferentiableOn ℂ V.uOf (V.P₁.φ '' V.Sm1)) :
    DifferentiableOn ℂ (V.wOfCell (j, k, n)) (V.Src (j, k, n)) := by
  intro w hw
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => V.wOf ((fun x : ℂ => V.R x - V.β)^[j]
      (V.uOf (V.s * MandelDim.piExp w)) - ((k : ℤ) : ℂ)))
    (V.Src (j, k, n)) w
  -- the level-1 source lies in the shifted chain fibre `W j + k`
  have hu_fibre : V.uOf (V.s * MandelDim.piExp w)
      ∈ (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j :=
    V.uOfSrc_mem_fibre hSm hw
  -- the walk of that source under `ĥ` stays on the chain, hence in the open set `DR`
  have hwalk : ∀ i < j, (fun x : ℂ => V.R x - V.β)^[i]
      (V.uOf (V.s * MandelDim.piExp w)) ∈ V.DR :=
    wOfCell_walk_mem_DR V.hIsChain V.hReq hu_fibre
  -- therefore `ĥ^[j]` is differentiable at the source
  have hIter : DifferentiableAt ℂ ((fun x : ℂ => V.R x - V.β)^[j])
      (V.uOf (V.s * MandelDim.piExp w)) :=
    wOfCell_differentiableAt_iterate V.hRdiff (fun i hi => V.hDRopen.mem_nhds (hwalk i hi))
  -- and the source `uOfSrc` itself is differentiable there
  have hUof : DifferentiableWithinAt ℂ (fun w : ℂ => V.uOf (V.s * MandelDim.piExp w))
      (V.Src (j, k, n)) w :=
    wOfCell_uOfSrc_differentiableWithinAt V hSm huOfD hw
  have hIn : DifferentiableWithinAt ℂ
      (fun w : ℂ => (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w)))
      (V.Src (j, k, n)) w :=
    hIter.comp_differentiableWithinAt w hUof
  have hInSub : DifferentiableWithinAt ℂ
      (fun w : ℂ => (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w))
        - ((k : ℤ) : ℂ)) (V.Src (j, k, n)) w :=
    hIn.sub_const _
  -- the endpoint lands in `W 0`, where `wOf` is holomorphic (the chain walk is onto `W 0 + k`)
  exact (V.wOf_differentiableOn _ (wOfCell_target_mem V hSm hw)).comp w hInSub
    (fun y hy => wOfCell_target_mem V hSm hy)

end

end Work.Repel
