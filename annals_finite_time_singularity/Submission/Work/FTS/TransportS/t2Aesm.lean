import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Continuity on the open quadrant for `SmoothOpen` data

The transport chapter works in the *open* quadrant class `SmoothOpen` (smoothness on
`z > 0`, `0 < θ < π/2`) rather than in `SmoothQuad`.  The two continuity lemmas below
transfer the `TransportS.HardDefs` cluster to that class; they are the analogues of
`Work.FTS.H2.continuousOn_mixed_Qd` and of the (private)
`Work.FTS.H2.continuousOn_H4PairInt_smoothQuad`. -/

theorem continuousOn_mixed_open {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2) Work.FTS.H2.Qd :=
  (hu.mixed j i).continuousOn

theorem continuousOn_DzIter_open {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j u p.1 p.2) Work.FTS.H2.Qd :=
  (hu.DzIter j).continuousOn

/-- The uncurried pairing integrand `H4PairInt α u v` is continuous on the open quadrant as
soon as `u` and `v` are `C^∞` there. -/
theorem continuousOn_H4PairInt_open (α : ℝ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.H4PairInt α u v p.1 p.2) Work.FTS.H2.Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i u p.1 p.2 * Work.FTS.H2.Whz p.1 p.2)
        * (Work.Spaces.DzIter i v p.1 p.2 * Work.FTS.H2.Whz p.1 p.2)) Work.FTS.H2.Qd :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_DzIter_open hu i).mul Work.FTS.H2.continuousOn_Whz_Qd).mul
        ((continuousOn_DzIter_open hv i).mul Work.FTS.H2.continuousOn_Whz_Qd)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i u p.1 p.2 * Work.FTS.H2.Wm α p.1 p.2)
          * (Work.Spaces.mixed j i v p.1 p.2 * Work.FTS.H2.Wm α p.1 p.2) else 0))
      Work.FTS.H2.Qd :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => by
      split_ifs with h
      · exact ((continuousOn_mixed_open hu j i).mul (Work.FTS.H2.continuousOn_Wm_Qd α)).mul
          ((continuousOn_mixed_open hv j i).mul (Work.FTS.H2.continuousOn_Wm_Qd α))
      · exact continuousOn_const
  have key : (fun p : ℝ × ℝ => Work.FTS.H2.H4PairInt α u v p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i u p.1 p.2 * Work.FTS.H2.Whz p.1 p.2)
              * (Work.Spaces.DzIter i v p.1 p.2 * Work.FTS.H2.Whz p.1 p.2))
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then
                  (Work.Spaces.mixed j i u p.1 p.2 * Work.FTS.H2.Wm α p.1 p.2)
                    * (Work.Spaces.mixed j i v p.1 p.2 * Work.FTS.H2.Wm α p.1 p.2) else 0) := by
    funext p
    rfl
  rw [key]
  exact h1.add h2

/-- The coefficient `f · D_z g` of the transport pairing is `C^∞` on the open quadrant when
`f` and `g` are. -/
theorem smoothOpen_mul_Dz {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) := by
  refine ContDiffOn.mul ?_ ?_
  · exact hf
  · exact hg.Dz

/-! ## The main statement -/

theorem t2Aesm : Work.FTS.TransportS.T2Aesm := by
  intro α f g hα hsf hsg
  have hsfO : Work.FTS.EllipticEst.SmoothOpen f := hsf.1
  have hsgQ : Work.FTS.LocData.SmoothQuad g := hsg.1.1
  have hsgO : Work.FTS.EllipticEst.SmoothOpen g :=
    ContDiffOn.mono hsgQ (by
      intro p hp
      obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨by linarith, hθ1, hθ2⟩)
  have hu : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    smoothOpen_mul_Dz hsfO hsgO
  constructor
  · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (Work.FTS.TransportS.continuousOn_Hhard_Qd hsfO hsgQ))
  · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_H4PairInt_open α hu hsgO))

end Work.FTS.TransportS
