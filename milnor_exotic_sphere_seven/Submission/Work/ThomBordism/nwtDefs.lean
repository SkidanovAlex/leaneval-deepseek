import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.PontryaginThom.Splitting

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The orthonormal complement data of the normal bundle of an embedding

`Work.Tubular.exists_euclidean_normalBundle` builds the *Euclidean* normal bundle of an embedding
`E : EmbeddingData V (8+k)` with `NormalData ND`, using the isometric insertion `insCLM` and the
reading map `readCLM` (coordinates in an orthonormal frame of the normal space).

`ComplementData` wants the same data in the *coordinate* spaces `Fin (8+k) → ℝ` and `Fin k → ℝ`
(this is the shape in which `Work.ThomBordism.PontryaginThom.nonempty_bundleIso_splitting` consumes
it).  This file records the two conjugated maps `complP`, `complI`, guarded outside the base set
exactly as `Work.ThomBordism.PontryaginThom.coverData` is, together with the immediate identities
they satisfy.
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The projection of the orthonormal normal bundle, in the coordinate spaces (junk value
`complProj i.2` outside the base set, so that `P ∘ I = id` holds everywhere). -/
def complP (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ) := by
  classical
  exact if x ∈ ND.D.baseSet i then
    (eucToFun k).comp ((Work.Tubular.readCLM E ND i x).comp (funToEuc (8 + k)))
  else LinearMap.toContinuousLinearMap (complProj i.2)

/-- The insertion of the orthonormal normal bundle, in the coordinate spaces (junk value
`complInj i.2` outside the base set). -/
def complI (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : (Fin k → ℝ) →L[ℝ] (Fin (8 + k) → ℝ) := by
  classical
  exact if x ∈ ND.D.baseSet i then
    (eucToFun (8 + k)).comp ((Work.Tubular.insCLM E ND i x).comp (funToEuc k))
  else LinearMap.toContinuousLinearMap (complInj i.2)

theorem complP_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    complP E ND i x
      = (eucToFun k).comp ((Work.Tubular.readCLM E ND i x).comp (funToEuc (8 + k))) := by
  rw [complP, if_pos hx]

theorem complI_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    complI E ND i x
      = (eucToFun (8 + k)).comp ((Work.Tubular.insCLM E ND i x).comp (funToEuc k)) := by
  rw [complI, if_pos hx]

@[simp] theorem complP_apply_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (u : Fin (8 + k) → ℝ) :
    complP E ND i x u
      = eucToFun k (Work.Tubular.readCLM E ND i x (funToEuc (8 + k) u)) := by
  rw [complP_of_mem E ND i hx]; rfl

@[simp] theorem complI_apply_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (v : Fin k → ℝ) :
    complI E ND i x v
      = eucToFun (8 + k) (Work.Tubular.insCLM E ND i x (funToEuc k v)) := by
  rw [complI_of_mem E ND i hx]; rfl

/-- `P ∘ I = id`. -/
theorem complP_comp_complI (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) :
    (complP E ND i x).comp (complI E ND i x) = ContinuousLinearMap.id ℝ (Fin k → ℝ) := by
  by_cases hx : x ∈ ND.D.baseSet i
  · rw [complP_of_mem E ND i hx, complI_of_mem E ND i hx]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, funToEuc_eucToFun,
      Work.Tubular.readCLM_insCLM E ND i hx, eucToFun_funToEuc,
      ContinuousLinearMap.id_apply]
  · rw [show complP E ND i x = LinearMap.toContinuousLinearMap (complProj i.2) from by
        rw [complP, if_neg hx],
      show complI E ND i x = LinearMap.toContinuousLinearMap (complInj i.2) from by
        rw [complI, if_neg hx]]
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 := congrArg (fun g => g v) (complProj_complInj i.2)
    simpa [ContinuousLinearMap.comp_apply] using h1

/-- Continuity of the projection along the cover. -/
theorem continuousOn_complP (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => complP E ND i x) (ND.D.baseSet i) :=
  (ContinuousOn.congr
    ((continuousOn_const (c := eucToFun k)).clm_comp
      ((Work.Tubular.continuousOn_readCLM E ND i).clm_comp
        (continuousOn_const (c := funToEuc (8 + k)))))
    (fun x hx => (complP_of_mem E ND i hx)))

/-- Continuity of the insertion along the cover. -/
theorem continuousOn_complI (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => complI E ND i x) (ND.D.baseSet i) :=
  (ContinuousOn.congr
    ((continuousOn_const (c := eucToFun (8 + k))).clm_comp
      ((Work.Tubular.continuousOn_insCLM E ND i).clm_comp
        (continuousOn_const (c := funToEuc k))))
    (fun x hx => (complI_of_mem E ND i hx)))

end

end Work.ThomBordism

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom

noncomputable section

variable {V : Work.ThomBordism.Man8}

/-- The tangent bundle of `V`, reindexed along the finite chart cover `chartCover`. -/
noncomputable def Zt0 (V : Work.ThomBordism.Man8) : RealBundle V.pt (Euc 8)
    (Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt))) :=
  RealBundle.reindex (Work.TangentClasses.tangentBundle (𝓘(ℝ, Euc 8)) V.pt)
    (Work.Thom.chartCover (H := Euc 8) (M := V.pt))
    (fun x => by
      obtain ⟨i, hi⟩ := Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x
      exact ⟨i, hi⟩)

/-- The bundle whose complexification is `Work.Thom.complexifiedTangentBundleFinite`, i.e. the
reindexed tangent bundle with the fibre transported along `Work.Thom.modelLinearEquiv`.
(No fibre ascription: the model fibre is `ℝ ^ finrank ℝ (Euc 8)`, which is the fibre in which
`Work.Thom.p1Tangent'` is defined.) -/
noncomputable def Zt1 (V : Work.ThomBordism.Man8) :=
  RealBundle.mapFibre (Work.Thom.modelLinearEquiv (E := Euc 8)) (Zt0 V)

/-- `Zt1` is the bundle appearing in `complexifiedTangentBundleFinite`. -/
theorem complexifiedTangentBundleFinite_eq (V : Work.ThomBordism.Man8) :
    Work.Thom.complexifiedTangentBundleFinite (𝓘(ℝ, Euc 8)) V.pt
      = Work.Thom.complexificationCore (Zt1 V) := rfl

/-- `Work.Thom.p1Tangent'` is `p₁` of `Zt1`. -/
theorem p1Tangent'_eq_pontryagin1_Zt1 (V : Work.ThomBordism.Man8) :
    V.p1 = Work.Thom.pontryagin1 (Zt1 V) := rfl

/-- `Work.Thom.p2Tangent'` is `c₄` of the complexification of `Zt1`. -/
theorem p2Tangent'_eq_chernClass_Zt1 (V : Work.ThomBordism.Man8) :
    V.p2 = Work.Thom.chernClass (Module.finrank ℝ (Euc 8)) 4
      (Work.Thom.complexificationCore (Zt1 V)) := rfl

end

end Work.ThomBordism
