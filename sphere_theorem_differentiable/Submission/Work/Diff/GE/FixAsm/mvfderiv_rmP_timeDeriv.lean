import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.GE.hasDerivAt_mvfderiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.FixAsm

/-- **Clairaut for `rmP` along a Ricci flow.**  The `s`-derivative of the (spatial) `mvfderiv` of
the curvature pairing `y ↦ rmP (G s) y (A y) (B y) (C y) (D y)` at a fixed point `x` and a fixed
tangent vector `v` is the `mvfderiv` of its pointwise `s`-derivative, which by `rmP_evol_fixed` is
`ΔRm + reactionMap(Rm)`.

This is the "differentiate under the integral / interchange the two derivatives" step of Hamilton's
gradient estimate: the family `(s, y) ↦ rmP (G s) y (A y) (B y) (C y) (D y)` is jointly `C^∞` near
`(t, x)` (`rmP_jointSmoothNoCompact`, smooth manifold structure only, no compactness), so
`hasDerivAt_mvfderiv` (Clairaut–Schwarz in the fixed chart at `x`) applies, and the pointwise
`s`-derivative is identified with `ΔRm + reactionMap(Rm)` at every base point by
`EvolA.rmP_evol_fixed`. -/
theorem mvfderiv_rmP_timeDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothField (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothField (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothField (I := I) (M := M) D) :
    HasDerivWithinAt
      (fun s : ℝ ↦ mvfderiv I
        (fun y : M ↦ Submission.Diff.rmP (G s) y (A y) (B y) (C y) (D y)) x v)
      (mvfderiv I
        (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (A y) (B y) (C y) (D y)
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y (A y) (B y) (C y) (D y))
        x v)
      (Set.Ico 0 T) t := by
  -- `G` is jointly smooth on the open set `Ioo 0 T`
  have hJ : IsOpen (Set.Ioo 0 T) := isOpen_Ioo
  have hG : Submission.Diff.JointSmooth G (Set.Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.subset_univ _))
  -- joint smoothness of the family `(s, y) ↦ rmP (G s) y (A y) (B y) (C y) (D y)` near `(t, x)`
  have hsm : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (A p.2) (B p.2) (C p.2) (D p.2))
      t x :=
    Work.Diff.GE.rmP_jointSmoothNoCompact (I := I) (M := M) hLC hJ hG ht x hA hB hC hD
  -- Clairaut: interchange the time derivative with the spatial `mvfderiv`
  have hcl := Work.Diff.GE.hasDerivAt_mvfderiv (I := I) (M := M) (t := t) (x := x) (v := v)
    (Φ := fun s : ℝ ↦ fun y : M ↦ Submission.Diff.rmP (G s) y (A y) (B y) (C y) (D y)) hsm
  -- the pointwise `s`-derivative is `ΔRm + reactionMap(Rm)` at every base point
  have hderiv_eq : (fun y : M ↦ deriv
        (fun s : ℝ ↦ Submission.Diff.rmP (G s) y (A y) (B y) (C y) (D y)) t)
      = fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (A y) (B y) (C y) (D y)
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y (A y) (B y) (C y) (D y) := by
    funext y
    exact (Work.Diff.GE.EvolA.rmP_evol_fixed hLC hLV G T hflow t ht y (A y) (B y) (C y) (D y)).deriv
  rw [hderiv_eq] at hcl
  exact hcl.hasDerivWithinAt

end Work.Diff.GE.FixAsm
