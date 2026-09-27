import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.chartedSpaceChangeModel
import Submission.Work.Drive.exists_chartedSpace_isManifold_projective

/-!
# `ℝP³ × ℝ` as a smooth `4`-manifold, with the model `ℝ⁴`

The bordism (`3 + 2 + 2`) invariance of the mod-`2` triple intersection number in a `3`-manifold
(`Work.Drive.even_ncard_meet32_encoded`, `Submission/Work/Drive/even_ncard_meet32_encoded.lean`) is
stated for an ambient `4`-manifold of the shape `M × ℝ` with `M` a `3`-manifold, and requires that
`M × ℝ` carry a `ChartedSpace` *modelled on* `EuclideanSpace ℝ (Fin 4)` together with the corresponding
`IsManifold` instance.  This file provides both for `M = ℝP³`.

**The structure chosen.**  It is the *product* structure (`Work.Drive.projCharted 3` on `ℝP³`, the
trivial structure on `ℝ`, `prodChartedSpace`) transported along the canonical **linear isometry**

`psiLin : (ℝ³ × ℝ) ≃L[ℝ] ℝ⁴`,

i.e. `chartedSpaceChangeModel psiLin.toHomeomorph`.  Its charts at a point are therefore, explicitly,
`psiLin ∘ (projChart i × id)` — the projective chart followed by a *linear* map.  This is the point of
the construction: the remaining obligation for the ends clause (the `Meet3Hyp` transversality fields for
the encoded chains, `Submission/Work/Drive/ENDS_ODD_STATUS.md` §2) is an `mfderiv` computation, and with
this structure `mfderiv` is the composition of the product derivative with the *linear* `psiLin`, so
`TripleTransverse` is the conjugate (by an invertible linear map, hence equivalent) of the product
derivative condition, whose `ℝP³`-components are the workspace's `projChart`/`planeClassDeriv`
machinery.

(An alternative, transported from the half-line model space `(0,∞) × ℝP³` along
`(0,∞) × ℝP³ ≃ₜ ℝP³ × ℝ` — `Homeomorph.chartedSpace halfLineProjectiveCharted halfLineProjSwap` —
also works, but its charts involve `exp` and its inverse, which would make the `mfderiv` computation
nonlinear.)

**Formalisation note.**  The structures are stated with the type written as
`Projectivization ℝ (Eucl 3) × ℝ`: `Eucl 3` is an `abbrev` for `EuclideanSpace ℝ (Fin 4)`, so the two
notations are *definitionally* equal (fine for elaboration), but instance *search* runs at reducible
transparency and does not see through `Fin (3 + 1) = Fin 4`.  The structures are therefore built with
explicit instance arguments in the notation the consumers use.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option linter.style.haveILetI false

/-- The linear isometry `ℝ ≃L[ℝ] ℝ¹` (the `1`-dimensional factor of the product model). -/
def lineLin : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm).trans
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm)

/-- **The canonical linear isometry `ℝ³ × ℝ ≃L[ℝ] ℝ⁴`**: it changes the model of the product
`ℝP³ × ℝ` to `EuclideanSpace ℝ (Fin 4)`. -/
def psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
    lineLin).trans (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)).symm

/-- **The smooth structure on `ℝP³ × ℝ` modelled on `ℝ⁴`**: the product structure transported along the
linear isometry `Work.Drive.psiLin`, so that its charts are `psiLin ∘ (projChart i × id)`. -/
@[instance_reducible]
noncomputable def projTimesLineCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Projectivization ℝ (Eucl 3) × ℝ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ
  exact chartedSpaceChangeModel (𝕜 := ℝ) psiLin.toHomeomorph

/-- **`ℝP³ × ℝ` is a smooth `4`-manifold** for the transported structure. -/
theorem isManifold_projTimesLineCharted :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 4)) _ _ (EuclideanSpace ℝ (Fin 4)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (Eucl 3) × ℝ) _ projTimesLineCharted := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  haveI h3 : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
    isManifold_projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ
  haveI h1 : IsManifold (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) ℝ := inferInstance
  haveI hprod : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (Projectivization ℝ (Eucl 3)) ℝ
  exact isManifold_changeModel (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3) × ℝ)
    (E' := EuclideanSpace ℝ (Fin 4)) (M := Projectivization ℝ (Eucl 3) × ℝ)
    psiLin.toHomeomorph psiLin.contDiff psiLin.symm.contDiff hprod

-- The transported structure is made the instance on `ℝP³ × ℝ` **inside this module**: the attribute
-- is `local`, so it is not forced on the rest of the workspace.
attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

end

end Work.Drive
