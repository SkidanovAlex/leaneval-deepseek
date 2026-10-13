import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The trace-strengthened family interpolation** (the statement proved in the sibling module
`Submission/Work/FTS/EllSol/PkgK5/i0Family_le_openTrace.lean`): the `i = 0` family of the paper's
§7 mixed-derivative interpolation for data of the open quadrant whose radial slices vanish at the
two angular endpoints in the sense of *limits*. -/
abbrev InterpFam (k : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))

end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The wall** (`D_z∂_θ` with the four HkMem hypotheses and the endpoint traces): the
open-class form of the paper's §7 mixed interpolation at the level of `D_z∂_θ`, proved in
`Submission/Work/FTS/EllSol/PkgK5/wall_of_interp.lean` from `InterpFam`. -/
abbrev WallK5 (k : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V))

end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The input bundle**: the smoothness, the memberships and the three norm transfers from the
shifted unknown `ellShift α g Φg` to the elliptic residual `EllResid α g Φg`. -/
abbrev InputsK5 (k : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) ∧
      Work.Spaces.HkMem α k (Work.Elliptic.EllResid α g Φg) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2
        (Work.Elliptic.EllResid α g Φg))) ∧
      α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (Work.Elliptic.EllResid α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
              (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k g) ∧
      Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
              (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g)

end Work.FTS.EllSol.PkgK5
