import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.JepsSubDefs
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsSubAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Continuity of the slot-wise difference integrand on the open quadrant.**

`Work.FTS.StrongEps.HkIntDiff α k A B` is the expression obtained from
`Work.Spaces.HkIntegrand α k ·` by replacing every derivative slot `D_z^i`, `D_z^j D_θ^i` with the
*difference of the corresponding slots of `A` and `B`* (see
`Submission/Work/FTS/StrongEps/JepsSubDefs.lean`).  For `A = J_ε f` and `B = f` every slot of `A`
is, on the open quadrant, the `J_ε`-image of the corresponding slot of `f` (`mixed_Jeps`), hence
continuous there because `J_ε` preserves continuity on `Quad`
(`Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps`), and the two weights `w/ sin(2θ)^{η/2}` and
`Wt α` are continuous on `Quad` (`Work.FTS.StrongEps.JepsHkMem.continuousOn_wdiv`,
`...continuousOn_Wt`).  The slots of `f` itself are continuous on `Quad` because `f` is `C^∞`
there (`Work.FTS.LocData.contDiffOn_mixed`, `...contDiffOn_DzIter`, or the ready-made
`Work.FTS.StrongEps.JepsHkMem.continuousOn_mixed_of_smooth`,
`...continuousOn_DzIter_of_smooth`).

Declare it in namespace `Work.FTS.StrongEps.JepsSubAux` (full name
`Work.FTS.StrongEps.JepsSubAux.continuousOn_HkIntDiff`).

Route: unfold `HkIntDiff`; on `Quad` replace `DzIter i (Jeps ρ ε f)` by `Jeps ρ ε (DzIter i f)`
and `mixed j i (Jeps ρ ε f)` by `Jeps ρ ε (mixed j i f)` using `ContinuousOn.congr` together with
`mixed_Jeps` (all four equalities hold at *every* point of `Quad`; `mixed i 0 = DzIter i` holds by
`rfl`), then assemble the finite sums with `continuousOn_finsetSum`, `ContinuousOn.add`,
`ContinuousOn.mul`, `ContinuousOn.pow` and `split_ifs`. -/
theorem continuousOn_HkIntDiff (α : ℝ) (k : ℕ) {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    ContinuousOn (fun q : ℝ × ℝ => HkIntDiff α k (Jeps ρ ε f) f q.1 q.2) Quad := by
  classical
  -- the two weights are continuous on the quadrant
  have hw : ContinuousOn (fun q : ℝ × ℝ =>
      Work.Spaces.w q.1 / Real.sin (2 * q.2) ^ (Work.Spaces.eta / 2)) Quad :=
    JepsHkMem.continuousOn_wdiv
  have hWt : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) Quad :=
    JepsHkMem.continuousOn_Wt α
  -- the slots of `f` are continuous on the quadrant
  have hDz : ∀ i : ℕ, ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter i f q.1 q.2) Quad :=
    fun i => JepsHkMem.continuousOn_DzIter_of_smooth hf i
  have hMx : ∀ j i : ℕ, ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Quad :=
    fun j i => JepsHkMem.continuousOn_mixed_of_smooth hf j i
  -- the explicit expression in which every slot of `J_ε f` has been replaced by `J_ε` of the
  -- corresponding slot of `f`
  let TZ : ℕ → ℝ × ℝ → ℝ := fun i q =>
    ((Jeps ρ ε (Work.Spaces.DzIter i f) q.1 q.2 - Work.Spaces.DzIter i f q.1 q.2)
      * (Work.Spaces.w q.1 / Real.sin (2 * q.2) ^ (Work.Spaces.eta / 2))) ^ 2
  let TM : ℕ → ℕ → ℝ × ℝ → ℝ := fun i j q =>
    if 1 ≤ i ∧ i + j ≤ k
      then ((Jeps ρ ε (Work.Spaces.mixed j i f) q.1 q.2 - Work.Spaces.mixed j i f q.1 q.2)
        * Work.Spaces.Wt α q.1 q.2) ^ 2
      else 0
  have hTZ : ∀ i : ℕ, ContinuousOn (TZ i) Quad := fun i =>
    (((JepsHkMem.continuousOn_Jeps hρ hε (hDz i)).sub (hDz i)).mul hw).pow 2
  have hTM : ∀ i j : ℕ, ContinuousOn (TM i j) Quad := fun i j => by
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [TM, hc]
      exact (((JepsHkMem.continuousOn_Jeps hρ hε (hMx j i)).sub (hMx j i)).mul hWt).pow 2
    · simp only [TM, hc]
      exact continuousOn_const
  have hT : ContinuousOn (fun q : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), TZ i q)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), TM i j q) Quad := by
    refine ContinuousOn.add ?_ ?_
    · apply continuousOn_finsetSum
      intro i hi
      exact hTZ i
    · apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      exact hTM i j
  -- the pointwise identification on the quadrant, then the target follows by `congr`
  refine hT.congr ?_
  intro q hq
  have hz : 0 < q.1 := hq.1
  have hθ : q.2 ∈ Set.Ioo 0 (π / 2) := hq.2
  have hslot : ∀ i : ℕ, Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2
      = Jeps ρ ε (Work.Spaces.DzIter i f) q.1 q.2 := fun i =>
    (mixed_Jeps ρ hρ hε hf hz hθ i 0).trans rfl
  have hslotm : ∀ j i : ℕ, Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2
      = Jeps ρ ε (Work.Spaces.mixed j i f) q.1 q.2 := fun j i =>
    mixed_Jeps ρ hρ hε hf hz hθ j i
  change HkIntDiff α k (Jeps ρ ε f) f q.1 q.2
    = (∑ i ∈ Finset.range (k + 1), TZ i q)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), TM i j q
  rw [HkIntDiff]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp only [TZ]; rw [hslot i]
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [TM, hc]; rw [hslotm j i]
      · simp only [TM, hc]; simp

end Work.FTS.StrongEps.JepsSubAux
