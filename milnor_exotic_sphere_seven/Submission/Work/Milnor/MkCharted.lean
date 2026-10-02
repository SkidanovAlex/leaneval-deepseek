import Mathlib
import Submission.Work.Milnor.Clutch
import Submission.Work.Milnor.Topology
import Submission.Work.Morse.Transfer
import Submission.Work.Morse.contMDiff_push
import Submission.Work.Morse.mfderiv_push
import Submission.Work.Morse.hasNondegHessian_push

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Mk k` re-charted over `ℝ⁷`

`Mk k` is constructed (`Submission.Work.Milnor.Clutch`) as a manifold charted over the product model
`ℝ⁴ × ℝ³`.  Here we push that structure forward along the linear isometry `ℝ⁴ × ℝ³ ≃ ℝ⁷`, obtaining
an *explicit* `ChartedSpace (EuclideanSpace ℝ (Fin 7)) (Mk k)` (instead of the anonymous structure
produced by `Work.Model.prod_transfer`), together with the transfer lemmas comparing smoothness,
manifold derivatives and nondegenerate Hessians between the two structures.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

noncomputable section

/-- The model space `ℝ⁴ × ℝ³` of the product charted structure on `Mk k`. -/
abbrev mkE : Type := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)

/-- The product model with corners used in the construction of `Mk k`. -/
abbrev prodModel : ModelWithCorners ℝ mkE (ModelProd (EuclideanSpace ℝ (Fin 4))
    (EuclideanSpace ℝ (Fin 3))) := (𝓡 4).prod (𝓡 3)

/-- The linear isometry identifying `ℝ⁴ × ℝ³` with `ℝ⁷`. -/
def mkModelIso : mkE ≃L[ℝ] EuclideanSpace ℝ (Fin 7) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 3)).symm

/-- The charted-space structure on `Mk k` modelled on `ℝ⁷`: the product atlas pushed forward along
`mkModelIso`.  This is an *explicit* structure, so its atlas can be unfolded. -/
@[instance_reducible] noncomputable def mkChartedSpace (k : ℤ) :
    ChartedSpace (EuclideanSpace ℝ (Fin 7)) (Mk k) :=
  Work.Morse.pushChartedSpace (Work.Morse.modelHomeo prodModel mkModelIso)

end

section Transfers

open scoped Manifold ContDiff Topology
open Submission.Milnor

variable (k : ℤ)
attribute [local instance] mkChartedSpace

/-- `Mk k`, with the pushed-forward atlas, is a smooth manifold modelled on `ℝ⁷`. -/
theorem mk_isManifold : IsManifold (𝓡 7) ∞ (Mk k) :=
  Work.Morse.push_isManifold (M := Mk k) (I := prodModel) mkModelIso

attribute [local instance] mk_isManifold

/-- Smoothness of a real function on `Mk k` is the same in the product structure and in the
`ℝ⁷` structure. -/
theorem mk_contMDiff_iff {f : Mk k → ℝ} :
    ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ f ↔ ContMDiff prodModel 𝓘(ℝ, ℝ) ∞ f :=
  Work.Morse.contMDiff_push (M := Mk k) (I := prodModel) (E' := EuclideanSpace ℝ (Fin 7))
    mkModelIso f

/-- The manifold derivative of a real function on `Mk k` in the `ℝ⁷` structure, in terms of the
derivative in the product structure. -/
theorem mk_mfderiv (f : Mk k → ℝ) (x : Mk k) :
    mfderiv (𝓡 7) 𝓘(ℝ, ℝ) f x
      = (mfderiv prodModel 𝓘(ℝ, ℝ) f x).comp
          (mkModelIso.symm : EuclideanSpace ℝ (Fin 7) →L[ℝ] mkE) :=
  Work.Morse.mfderiv_push (M := Mk k) (I := prodModel) (E' := EuclideanSpace ℝ (Fin 7))
    mkModelIso f x

/-- The critical points of a real function on `Mk k` do not depend on which of the two structures
one uses. -/
theorem mk_mfderiv_eq_zero_iff {f : Mk k → ℝ} {x : Mk k} :
    mfderiv (𝓡 7) 𝓘(ℝ, ℝ) f x = 0 ↔ mfderiv prodModel 𝓘(ℝ, ℝ) f x = 0 := by
  rw [mk_mfderiv k f x]
  constructor
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := mkModelIso.symm.surjective v
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 7) →L[ℝ] ℝ => L w) h
  · intro h
    rw [h]
    exact ContinuousLinearMap.zero_comp _

/-- Nondegeneracy of the Hessian at a point does not depend on which of the two structures one
uses. -/
theorem mk_hasNondegHessian {f : Mk k → ℝ} {x : Mk k}
    (h : HasNondegHessian (I := prodModel) (n := ∞) f x) :
    HasNondegHessian (I := 𝓡 7) (n := ∞) f x :=
  Work.Morse.hasNondegHessian_push (M := Mk k) (I := prodModel)
    (E' := EuclideanSpace ℝ (Fin 7)) mkModelIso h

end Transfers

end Work.Milnor
