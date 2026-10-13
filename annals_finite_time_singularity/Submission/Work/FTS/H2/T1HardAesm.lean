import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Joint continuity of `T1Hard` on the open quadrant

Every factor of
`T1Hard α f g z θ = f z θ · w(z)² · ( D_θ(D_z^4 g) · D_z^4 g · sin(2θ)^{-η}
  + (∑_{(j,i)} D_θ(D_z^jD_θ^i g) · D_z^jD_θ^i g) · sin(2θ)^{-γ} )`
is continuous on `(0,∞) × (0,π/2)`: `f` and all the `D`-derivatives of `g` are smooth on
the open neighbourhood `nbhU ⊇ Qd` of the closed quadrant, while `w` is continuous off the
axis `z = 0` and `sin(2θ)^{-p}` is continuous where `sin(2θ) > 0`. -/


/-- A function smooth on a neighbourhood of the closed quadrant is continuous on the
open quadrant. -/
private lemma contOn_uncurry_nbhd {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    ContinuousOn (Function.uncurry f) Qd :=
  h.continuousOn.mono Qd_subset_nbhU

private lemma contOn_sinpow_Qd (p : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => (Real.sin (2 * y.2)) ^ p) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _y hy => Or.inl (ne_of_gt (sin_two_pos_Qd hy.2)))

private lemma contOn_w_Qd : ContinuousOn (fun y : ℝ × ℝ => Work.Spaces.w y.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun y hy => ?_)
  exact pow_ne_zero 2 (ne_of_gt hy.1)

private lemma contOn_mixed (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Qd :=
  contOn_uncurry_nbhd (Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j)

private lemma contOn_Dth_mixed (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.mixed j i g) p.1 p.2) Qd :=
  contOn_uncurry_nbhd (Work.Spaces.SmoothNbhd.Dth
    (Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j))

/-- `T1Hard α f g` is jointly continuous on the open quadrant. -/
private lemma contOn_T1Hard (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (fun p : ℝ × ℝ => T1Hard α f g p.1 p.2) Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Qd := contOn_uncurry_nbhd hsmf
  have hD4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2) Qd :=
    contOn_uncurry_nbhd (Work.Spaces.SmoothNbhd.Dth (Work.Spaces.SmoothNbhd.DzIter hsmg 4))
  have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 4 g p.1 p.2) Qd :=
    contOn_uncurry_nbhd (Work.Spaces.SmoothNbhd.DzIter hsmg 4)
  have hsinη : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)) Qd :=
    contOn_sinpow_Qd (-Work.Spaces.eta)
  have hsinγ : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.gam α)) Qd :=
    contOn_sinpow_Qd (-Work.Spaces.gam α)
  have hB1 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2
        * Work.Spaces.mixed 3 1 g p.1 p.2) Qd :=
    (contOn_Dth_mixed g hsmg 3 1).mul (contOn_mixed g hsmg 3 1)
  have hB2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2
        * Work.Spaces.mixed 2 2 g p.1 p.2) Qd :=
    (contOn_Dth_mixed g hsmg 2 2).mul (contOn_mixed g hsmg 2 2)
  have hB3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2
        * Work.Spaces.mixed 1 3 g p.1 p.2) Qd :=
    (contOn_Dth_mixed g hsmg 1 3).mul (contOn_mixed g hsmg 1 3)
  have hB4 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
        * Work.Spaces.mixed 0 4 g p.1 p.2) Qd :=
    (contOn_Dth_mixed g hsmg 0 4).mul (contOn_mixed g hsmg 0 4)
  have hB : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2 * Work.Spaces.mixed 3 1 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2 * Work.Spaces.mixed 2 2 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2 * Work.Spaces.mixed 1 3 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
          * Work.Spaces.mixed 0 4 g p.1 p.2)) Qd :=
    ((hB1.add hB2).add hB3).add hB4
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      f p.1 p.2 * (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2 * Work.Spaces.DzIter 4 g p.1 p.2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)
          + (Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2
              * Work.Spaces.mixed 3 1 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2
              * Work.Spaces.mixed 2 2 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2
              * Work.Spaces.mixed 1 3 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
              * Work.Spaces.mixed 0 4 g p.1 p.2)
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.gam α))) Qd :=
    (hf.mul (contOn_w_Qd.pow 2)).mul
      (((hD4.mul h4).mul hsinη).add (hB.mul hsinγ))
  simpa only [T1Hard] using key

theorem T1HardAesm (α : ℝ) (f g : ℝ → ℝ → ℝ) (hsmf : Work.Spaces.SmoothNbhd f)
    (hsmg : Work.Spaces.SmoothNbhd g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.H2.T1Hard α f g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hc := contOn_T1Hard α f g hsmf hsmg
  exact Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => T1Hard α f g p.1 p.2)
    (by simpa only [Qd] using hc)

end Work.FTS.H2
