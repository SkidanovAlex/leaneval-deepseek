import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.EXT.covK_mlieBracket_family
import Submission.Work.Diff.EXT.covK_spatialDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **The Koszul pairing for a jointly smooth family of metrics.**  If the metric family `G` is
jointly smooth on the open set `V` (`JointMet G V`) and the families of tangent fields `σ`, `X`, `Z`
are jointly smooth on `V` (`JointField`), then so is
`(t,y) ↦ (G t).inner y (∇^{G t}_{X t} σ t)(y) (Z t y)`, the metric pairing of the Levi-Civita
connection of `G t` applied to `σ t` in the direction `X t`, against `Z t`.

ROUTE.  At a point `p ∈ V` use the pointwise Koszul formula for the fixed metric `G p.1`
(`Submission.Work.Diff.EXT.kosDefs.lcOf_pairing_at`, which is Mathlib's
`leviCivitaConnection_apply_inner` with the instance inner product transported to `G p.1`), or
reprove it inline: with `letI : RiemannianBundle _ := ⟨(G p.1).toRiemannianMetric⟩`, Mathlib's
`CovariantDerivative.leviCivitaConnection_apply_inner` *is* the Koszul formula for `G p.1`
(`exact` suffices, since `lcOf (G p.1) = leviCivitaConnection I M` and `inner ℝ = (G p.1).inner`
are definitional).  The formula holds for all `q` near `p` in `V`, because the slices `σ q.1`,
`X q.1`, `Z q.1` are differentiable at `q.2` (they are smooth there, as `V` is open; see
`Work.Diff.EXT.contMDiffAt_slice` in `Submission/Work/Diff/EXT/covK_mlieBracket_family.lean`).

The six terms of the Koszul expression are jointly smooth on `V`:

* the three pairings `(t,y) ↦ (G t).inner y (A t y) (B t y)`:
  `Work.Diff.EXT.covK_metric_pairing_family`;
* the three terms `(t,y) ↦ mvfderiv I (fun y' ↦ (G t).inner y' (A t y') (B t y')) y (C t y)`:
  `Work.Diff.EXT.covK_spatialDeriv` applied to the jointly smooth pairing and to the jointly smooth
  family `C`;
* the three bracket terms `(t,y) ↦ (G t).inner y (A t y) (mlieBracket I (B t) (C t) y)`:
  `Work.Diff.EXT.covK_mlieBracket_family` + `Work.Diff.EXT.covK_metric_pairing_family`.

Conclude by `ContMDiffOn.congr` with the Koszul expression on `V`. -/
theorem covK_koszul_pairing_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {σ X Z : ℝ → TField (I := I) (M := M)}
    (hσ : JointField σ V) (hX : JointField X V) (hZ : JointField Z V) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Submission.Diff.lcOf (G p.1) (σ p.1) p.2
        (X p.1 p.2)) (Z p.1 p.2)) V := by sorry

end Work.Diff.EXT
