import Mathlib
import Submission.Work.Diff.GE.ExtTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

theorem extDD_antisymm_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.SmoothFunT (I := I) (M := M) (τ F))
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G : Π y : M, TangentSpace I y) (c : ℝ),
      τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (F : ι → (Π y : M, TangentSpace I y))
    (hF : Work.Diff.GE.SmoothTuple (I := I) (M := M) F) :
    Work.Diff.GE.extDD cov τ x X Y F - Work.Diff.GE.extDD cov τ x Y X F
      = - (Finset.univ.sum
            (fun i => τ (Function.update F i
              (fun y => LeanEval.Geometry.SphereTheorem.curv cov X Y (F i) y)) x)) := by sorry

end Work.Diff.GE
