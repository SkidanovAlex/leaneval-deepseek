import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_image_mem
import Submission.Work.Repel.V10.wOfCell_differentiableOn

/-!
# `Work.Repel.chain_v9_diff` : holomorphy of the §6 target map on the round source region

The §6 target map of a cell `q = (j,k,n)` is

  `wOfCell q w = wOf (ĥ^[j] (uOf (s·π w)) − k)`,   `ĥ = R − β`.

`wOfCell_differentiableOn` proves that it is holomorphic on the *half-open box* source region `Src`
of `chain_v9_chase`.  Here we redo that for the *round* source region `Raw j k` of
`chain_v9_src` (hence, by restriction, for `SrcC j k n = Raw j k ∩ ball (w_c + n) (1/2)`), which is
the region actually used by the assembly: `Raw` is open, so the Baire/identity argument of
`Work.Repel.uniform_iterate_of_orbit` applies.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The level-1 source of a point of the raw source region lies in the shifted chain fibre. -/
theorem uOfSrc_mem_fib {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.Raw j k) : V.uOf (V.s * MandelDim.piExp w) ∈ V.fib j k := by
  obtain ⟨u, hu, hπ⟩ := hw
  exact (V.uOf_unique (hSm hu) hπ) ▸ hu

/-- The chain walk of a point of the `n`-th source region ends in `W 0`. -/
theorem wOfCell_target_mem_Raw {j : ℕ} (hj : 1 ≤ j) {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.Raw j k) :
    (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w)) - ((k : ℤ) : ℂ)
      ∈ V.W 0 :=
  chain_image_mem V (V.uOfSrc_mem_fib hSm hw)

/-- **`wOfCell q` is holomorphic on the raw source region `Raw j k`.** -/
theorem wOfCell_differentiableOn_Raw {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1)
    (huOfD : DifferentiableOn ℂ V.uOf (V.P₁.φ '' V.Sm1)) :
    DifferentiableOn ℂ (V.wOfCell (j, k, n)) (V.Raw j k) := by
  intro w hw
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => V.wOf ((fun x : ℂ => V.R x - V.β)^[j]
      (V.uOf (V.s * MandelDim.piExp w)) - ((k : ℤ) : ℂ)))
    (V.Raw j k) w
  have hu_fibre : V.uOf (V.s * MandelDim.piExp w) ∈ V.fib j k := V.uOfSrc_mem_fib hSm hw
  have hwalk : ∀ i < j, (fun x : ℂ => V.R x - V.β)^[i]
      (V.uOf (V.s * MandelDim.piExp w)) ∈ V.DR :=
    wOfCell_walk_mem_DR V.hIsChain V.hReq hu_fibre
  have hIter : DifferentiableAt ℂ ((fun x : ℂ => V.R x - V.β)^[j])
      (V.uOf (V.s * MandelDim.piExp w)) :=
    wOfCell_differentiableAt_iterate V.hRdiff (fun i hi => V.hDRopen.mem_nhds (hwalk i hi))
  have hSmin : V.s * MandelDim.piExp w ∈ V.P₁.φ '' V.Sm1 := Set.image_mono hSm hw
  have hUof : DifferentiableWithinAt ℂ (fun w : ℂ => V.uOf (V.s * MandelDim.piExp w))
      (V.Raw j k) w := by
    refine (huOfD _ hSmin).comp w ?_ (fun z hz => ?_)
    · exact ((differentiable_piExp.const_mul V.s).differentiableAt).differentiableWithinAt
    · exact Set.image_mono hSm hz
  have hIn : DifferentiableWithinAt ℂ
      (fun w : ℂ => (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w)))
      (V.Raw j k) w :=
    hIter.comp_differentiableWithinAt w hUof
  have hInSub : DifferentiableWithinAt ℂ
      (fun w : ℂ => (fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w))
        - ((k : ℤ) : ℂ)) (V.Raw j k) w :=
    hIn.sub_const _
  exact (V.wOf_differentiableOn _ (V.wOfCell_target_mem_Raw hj hSm hw)).comp w hInSub
    (fun y hy => V.wOfCell_target_mem_Raw hj hSm hy)

/-- **`wOfCell q` is holomorphic on the source region of a cell.** -/
theorem wOfCell_differentiableOn_SrcC {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1)
    (huOfD : DifferentiableOn ℂ V.uOf (V.P₁.φ '' V.Sm1)) :
    DifferentiableOn ℂ (V.wOfCell (j, k, n)) (V.SrcC j k n) :=
  (V.wOfCell_differentiableOn_Raw hj hSm huOfD).mono Set.inter_subset_left

/-- The target point of a source point of the cell lies in `ball wt₀ ρ₀`. -/
theorem wOfCell_mem_ball {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.SrcC j k n) : V.wOfCell (j, k, n) w ∈ Metric.ball V.wt₀ V.ρ₀ :=
  (V.wOfCell_spec (V.wOfCell_target_mem_Raw hj hSm hw.1)).1

/-- The `π`-image of the target point of a source point of the cell. -/
theorem piExp_wOfCell {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {w : ℂ}
    (hw : w ∈ V.SrcC j k n) :
    MandelDim.piExp (V.wOfCell (j, k, n) w) =
      V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[j] (V.uOf (V.s * MandelDim.piExp w))
        - ((k : ℤ) : ℂ)) / V.s :=
  (V.wOfCell_spec (V.wOfCell_target_mem_Raw hj hSm hw.1)).2

end V10

end

end Work.Repel
