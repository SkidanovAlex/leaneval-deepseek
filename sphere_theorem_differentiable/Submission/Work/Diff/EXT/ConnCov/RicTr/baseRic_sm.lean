import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.MP.ricAtJointContinuousOn
import Submission.Work.Diff.EXT.rmP_field_contMDiffAt
import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of `baseRic` on smooth fields (the base case of the `Ric`-tower)

`Work.Diff.EXT.ConnCov.baseRic g` is the pointwise Ricci tensor `RIC₀ X Y Z y = Ric_y(X y, Y y)`
of a smooth metric `g` viewed as an `ATower.Op3 0`; it is the base of the tower
`tower (lcOf g) (baseRic g) k` of covariant derivatives of the Ricci tensor, whose smoothness on
smooth fields is the base case required by the tower-smoothness induction of the `ConnCov` area
(`Work.Diff.EXT.ATower.tower_slotAdd_smF` and friends).

Here we prove it: for globally smooth fields `A`, `B` (and any `C`),

`y ↦ Ric_y(A y, B y)`  is `C^∞`.

## Route

`ricAt` is a *tensorial* object: on the chart at a point `x₀` the bilinearity of `ricAt` together
with the expansion of a section in the coordinate frame `σᵢ = cFrame x₀ i` gives

`Ric_y(A y, B y) = ∑ᵢⱼ αᵢ(y) βⱼ(y) · Ric_y(σᵢ y, σⱼ y)`,

with `αᵢ = (bB.coord i) ∘ coordFun x₀ A` the chart coordinates of `A`; and the Ricci trace read in
the coordinate frame is the contraction of the *inverse Gram matrix* with the curvature components
(these are `Work.Diff.MP.ricAt_coordFrame_expansion` and
`Work.Diff.MP.ricAt_gramInv_chart_expansion`).  Every factor of the resulting sum is smooth in `y`:
the coefficients because the chart coordinates of a smooth field are smooth
(`Submission.ChartCurv.contMDiffAt_coordFun`), and the inverse Gram matrix / curvature components
along the constant family `G ≡ g` because these are *jointly* smooth in `(t, y)`
(`Work.Diff.GE.gramInv_jointSmooth`, `Work.Diff.GE.rmC4_jointSmooth`).

Since `ContMDiff` is a pointwise condition, this gives the claim.
-/

set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicTr

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Smoothness of `y ↦ Ric_y(A y, B y)` at a point.**  For a smooth metric `g` and fields `A`, `B`
which are `C^∞` at `x₀`, the function `y ↦ ricAt (lcOf g) y (A y) (B y)` is `C^∞` at `x₀`.

This is the local form of the target; it is stated separately because the argument is a purely
local one (chart at `x₀`). -/
theorem ricAt_field_contMDiffAt
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) {x₀ : M}
    {A B : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Submission.Diff.ricAt (Submission.Diff.lcOf g) y (A y) (B y)) x₀ := by
  -- every metric has a smooth Levi-Civita connection
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth
  -- the metric `g` provides the Riemannian-bundle instances used by the chart calculus
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the constant family of metrics is jointly smooth on `univ`
  have hJS : Submission.Diff.JointSmooth (fun _ : ℝ => g) Set.univ := by
    rw [Submission.Diff.JointSmooth, Set.univ_prod_univ, contMDiffOn_univ]
    exact g.contMDiff.comp contMDiff_snd
  -- the slicing `y ↦ (0, y)` is smooth at `x₀`
  have hpair : ContMDiffAt I ((𝓘(ℝ, ℝ)).prod I) ∞ (fun y : M => ((0 : ℝ), y)) x₀ :=
    contMDiffAt_const.prodMk contMDiffAt_id
  -- the chart coordinates of a smooth field are smooth
  have hcoef : ∀ (V : Π y : M, TangentSpace I y), CMDiff ∞ (T% V) →
      ∀ i : Fin (Module.finrank ℝ E),
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y : M => (Module.finBasis ℝ E).coord i
            (Submission.ChartCurv.coordFun x₀ V y)) x₀ := by
    intro V hV i
    have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞ (Submission.ChartCurv.coordFun x₀ V) x₀ :=
      Submission.ChartCurv.contMDiffAt_coordFun (I := I) (M := M) x₀ hV
        (mem_chart_source H x₀)
    exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord i)).contMDiffAt.comp x₀ h1
  -- the chart model of the Ricci tensor is smooth at `x₀`
  have hmodel : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A y))
          * ((Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B y))
          * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv (fun _ : ℝ => g) x₀ 0 y k l
                * Work.Diff.GE.rmC4 (fun _ : ℝ => g) x₀ 0 y k i l j) x₀ := by
    refine ContMDiffAt.sum (fun i _ => ContMDiffAt.sum (fun j _ => ?_))
    refine ((hcoef A hA i).mul (hcoef B hB j)).mul ?_
    refine ContMDiffAt.sum (fun k _ => ContMDiffAt.sum (fun l _ => ?_))
    exact (((Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) isOpen_univ hJS (t₀ := 0)
        trivial x₀ k l).comp x₀ hpair).mul
      ((Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC isOpen_univ hJS (t₀ := 0)
        trivial x₀ k i l j).comp x₀ hpair))
  -- on the chart at `x₀` the Ricci tensor *is* that model
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)] with y hy
  exact Work.Diff.MP.ricAt_gramInv_chart_expansion (I := I) (M := M) hLC
    (fun _ : ℝ => g) x₀ 0 hy A B

theorem baseRic_sm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞))
    (A B C : Π y : M, TangentSpace I y)
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) :
    Work.Diff.EXT.ATower.SmF I M
      (Work.Diff.EXT.ConnCov.baseRic g
        (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) A B C) := by
  -- `SmF` unfolds to `ContMDiff I 𝓘(ℝ,ℝ) ∞`, which is the pointwise condition `ContMDiffAt`
  show ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun y : M => Submission.Diff.ricAt (Submission.Diff.lcOf g) y (A y) (B y))
  intro x₀
  exact ricAt_field_contMDiffAt (I := I) (M := M) g hA hB

end Work.Diff.EXT.ConnCov.RicTr
