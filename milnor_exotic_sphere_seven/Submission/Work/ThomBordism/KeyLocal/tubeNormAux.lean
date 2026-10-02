import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeNormDefs
import Submission.Work.ThomBordism.KeyLocal.mpunPullbackSnd
import Submission.Work.ThomBordism.KeyLocal.varyingMatGauge
import Submission.Work.ThomBordism.padGaussFunM_continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# Auxiliary lemmas for the tube-level normal reading

Two pieces of bookkeeping that the target `Work.ThomBordism.KeyLocal.tubeNormReading` consumes:

* `mpunPullbackSnd_punct` — `Work.ThomBordism.KeyLocal.mpunPullbackSnd` with an *arbitrary* source
  set `S` (rather than the literal `V ⁻¹' {0}ᶜ`): the model class `Mpun n ↥W` only sees the second
  coordinate, relative to any set on which that coordinate does not vanish.  The target needs the
  source set to be the *punctured tube base set*, and in the relative cohomology of a pair the source
  set is part of the *type*, so the general form is not an instance of the literal one.
* `continuousOn_feFrameGauge` — the frame gauge `feFrameGauge S σ = orientMat S (ogMk σ) *
  frameMatrix S σ.1` is continuous on the chart set `chartSet S` of the Stiefel manifold (where
  `orientMat S` is continuous, `continuousOn_orientMat`).  The target composes it with the tube
  frame `tubeFrame` (whose continuity comes from `continuousOn_padGFrameM` /
  `continuousOn_gframe`), giving the continuous gauge family of `varyingMatGauge`.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

/-- **The model class `Mpun n ↥W` only depends on the second coordinate** — with an arbitrary
source set `S` on which the second coordinate does not vanish.  This is
`Work.ThomBordism.KeyLocal.mpunPullbackSnd` with the source set generalised (the proof is the same:
the source set never enters except as the source of the pullback). -/
theorem mpunPullbackSnd_punct {n : ℕ} {B : Type} [TopologicalSpace B] {W : Set B}
    {X : Type} [TopologicalSpace X] (P : C(X, ↥W)) (V : C(X, EuclideanSpace ℝ (Fin n)))
    (S : Set X) (hSV : ∀ x ∈ S, V x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    (Work.Thom.relCohMap
        (⟨fun x => ((P x : ↥W), V x), P.continuous.prodMk V.continuous⟩ :
          C(X, ↥W × EuclideanSpace ℝ (Fin n)))
        S (Work.Thom.Punct ↥W n) hSV ℤ n).hom (Work.Thom.Mpun n ↥W)
      = (Work.Thom.relCohMap V S ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hSV ℤ n).hom
        (Work.ThomBordism.stdModelGen n) := by
  classical
  -- the constant base map `↥W → PUnit`
  set cst : C(↥W, PUnit) := ⟨fun _ => PUnit.unit, continuous_const⟩ with hcst
  set bm : C(↥W × EuclideanSpace ℝ (Fin n), PUnit × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun p => (cst p.1, p.2), cst.continuous.comp continuous_fst |>.prodMk continuous_snd⟩ with hbm
  -- `Mpun` over `↥W` is the pullback of `Mpun` over `PUnit`
  have hMpun : Work.Thom.Mpun n ↥W
      = (Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit) :=
    (Work.Thom.Mpun_natural_map (n := n) cst).symm
  -- the two maps
  set pv : C(X, ↥W × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => (P x, V x), P.continuous.prodMk V.continuous⟩ with hpv
  set wv : C(X, PUnit × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => (PUnit.unit, V x), continuous_const.prodMk V.continuous⟩ with hwv
  have hcomp : bm.comp pv = wv := by
    apply ContinuousMap.ext; intro x; rfl
  have hpsi2 : wv = (psiUnit n).comp V := by
    apply ContinuousMap.ext; intro x; rfl
  -- the chain of pullbacks
  rw [show (Work.Thom.relCohMap pv S (Work.Thom.Punct ↥W n) hSV ℤ n).hom
        (Work.Thom.Mpun n ↥W)
      = (Work.Thom.relCohMap pv S (Work.Thom.Punct ↥W n) hSV ℤ n).hom
        ((Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit)) from
    congrArg (fun y => (Work.Thom.relCohMap pv S (Work.Thom.Punct ↥W n)
      hSV ℤ n).hom y) hMpun]
  rw [show (Work.Thom.relCohMap pv S (Work.Thom.Punct ↥W n) hSV ℤ n).hom
        ((Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit))
      = (Work.Thom.relCohMap (bm.comp pv) S (Work.Thom.Punct PUnit n)
          hSV ℤ n).hom (Work.Thom.Mpun n PUnit) from
    Work.Thom.relCohMap_compA_apply S (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n) pv bm
      hSV (fun _ hp => hp) hSV ℤ n (Work.Thom.Mpun n PUnit)]
  rw [show (Work.Thom.relCohMap (bm.comp pv) S (Work.Thom.Punct PUnit n)
        hSV ℤ n) = Work.Thom.relCohMap wv S (Work.Thom.Punct PUnit n)
        hSV ℤ n from
    Work.Thom.relCohMap_congrA S (Work.Thom.Punct PUnit n) hcomp
      hSV hSV ℤ n]
  rw [show (Work.Thom.relCohMap wv S (Work.Thom.Punct PUnit n) hSV ℤ n)
      = Work.Thom.relCohMap ((psiUnit n).comp V) S (Work.Thom.Punct PUnit n)
        hSV ℤ n from
    Work.Thom.relCohMap_congrA S (Work.Thom.Punct PUnit n) hpsi2
      hSV hSV ℤ n]
  -- the right-hand side
  rw [stdModelGen_eq_pullback n]
  rw [show (Work.Thom.relCohMap V S ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
        hSV ℤ n).hom
        ((Work.Thom.relCohMap (psiUnit n) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
          (Work.Thom.Punct PUnit n) (fun v hv => hv) ℤ n).hom (Work.Thom.Mpun n PUnit))
      = (Work.Thom.relCohMap ((psiUnit n).comp V) S (Work.Thom.Punct PUnit n)
          hSV ℤ n).hom (Work.Thom.Mpun n PUnit) from
    (Work.Thom.relCohMap_compA_apply S ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
      (Work.Thom.Punct PUnit n) V (psiUnit n) hSV (fun v hv => hv)
      hSV ℤ n (Work.Thom.Mpun n PUnit))]

/-! ## Continuity of the frame gauge along the tube frame -/

/-- **The frame gauge is continuous on the chart set of the chart** (as a function on the subtype
`↥(chartSet S)`).  This is `matLin (orientMat S (ogMk σ) * frameMatrix S σ.1)`, a composite of
`continuous_matLin`, the matrix product, `continuousOn_orientMat` (on `baseSet S`) and the
continuity of the frame matrix in the frame. -/
theorem continuous_feFrameGauge_subtype {k : ℕ} (S : ChartIdx k 10) :
    Continuous fun σ : ↥(chartSet S) => feFrameGauge S σ.1 := by
  show Continuous fun σ : ↥(chartSet S) =>
    matLin (orientMat S (ogMk k 10 σ.1) * frameMatrix S (σ.1).1)
  refine continuous_matLin.comp ?_
  show Continuous fun σ : ↥(chartSet S) =>
    orientMat S (ogMk k 10 σ.1) * frameMatrix S (σ.1).1
  refine Continuous.matrix_mul ?_ ?_
  · exact (continuousOn_orientMat S).comp_continuous
      ((ogMk k 10).continuous.comp continuous_subtype_val)
      (fun σ => (mem_baseSet_iff S σ.1).mpr σ.2)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ)
        (((S.1.equivFinOfCardEq S.2).symm a : ↥S.1) : Fin (k + 10))).continuous.comp
      ((continuous_apply b).comp (continuous_subtype_val.comp continuous_subtype_val))

/-- **The Stiefel point of the tube frame is continuous.** -/
theorem continuous_tubeFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) : Continuous (tubeFrame E C ND i) := by
  have hpad : ContinuousOn (fun x : V.pt => padGFrame E ND i x) (ND.D.baseSet i) :=
    continuousOn_padGFrameM E ND 10 (by norm_num) i
  refine Continuous.subtype_mk (hpad.comp_continuous
    ((tubeFoot E C).continuous.comp continuous_subtype_val) (fun y => y.2)) _


/-- **The frame gauge of the tube frame is continuous** on the part of the tube base set lying in
the chart set of `S`. -/
theorem continuous_feFrameGauge_tubeFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (S : ChartIdx k 10)
    (hchartSet : ∀ y : ↥(tubeBaseSet E C ND i), tubeFrame E C ND i y ∈ chartSet S) :
    Continuous (fun y : ↥(tubeBaseSet E C ND i) => feFrameGauge S (tubeFrame E C ND i y)) := by
  show Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
    matLin (orientMat S (ogMk k 10 (tubeFrame E C ND i y))
      * frameMatrix S (tubeFrame E C ND i y).1))
  refine continuous_matLin.comp (Continuous.matrix_mul ?_ ?_)
  · exact (continuousOn_orientMat S).comp_continuous
      ((ogMk k 10).continuous.comp (continuous_tubeFrame E C ND i))
      (fun y => (mem_baseSet_iff S (tubeFrame E C ND i y)).mpr (hchartSet y))
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      (((S.1.equivFinOfCardEq S.2).symm a : ↥S.1) : Fin (k + 10))).continuous.comp
      ((continuous_apply b).comp (continuous_subtype_val.comp (continuous_tubeFrame E C ND i)))

end

end Work.ThomBordism.KeyLocal
