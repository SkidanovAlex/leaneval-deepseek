import Submission.Work.ThomBordism._gtd.P3
import Submission.Work.ThomBordism.gtdFrameProj_padEuc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric
open Work.ThomBordism.PontryaginThom Work.ThomBordism.Gauss Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem continuousOn_padGFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x : V.pt => padGFrame E ND i x) (ND.D.baseSet i) := by
  rw [continuousOn_pi]
  intro a
  have hfun : (fun x : V.pt => padGFrame E ND i x a)
      = fun x => padEuc k 10 (by norm_num)
          ((if (a : ℕ) = 0 then sigma E ND i x else 1) • Tubular.orthFrame E ND i x a) := by
    funext x
    show padIsom k (gframe E ND i x a)
      = padEuc k 10 (by norm_num)
          ((if (a : ℕ) = 0 then sigma E ND i x else 1) • Tubular.orthFrame E ND i x a)
    rw [gframe_apply, map_smul, padIsom_apply, map_smul]
  rw [hfun]
  refine (padEuc k 10 (by norm_num)).continuous.comp_continuousOn ?_
  refine ContinuousOn.smul (f := fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
    (g := fun x : V.pt => Tubular.orthFrame E ND i x a) ?_
    (Tubular.continuousOn_orthFrame E ND i a)
  by_cases ha : (a : ℕ) = 0
  · rw [show (fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
        = fun x => sigma E ND i x from funext fun x => by rw [if_pos ha]]
    exact continuousOn_sigma E ND i
  · rw [show (fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
        = fun _ => (1 : ℝ) from funext fun x => by rw [if_neg ha]]
    exact continuousOn_const

theorem continuousOn_padGaussStiefel (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (padGaussStiefel E ND i) (ND.D.baseSet i) := by
  refine Tubular.continuousOn_subtype_of_eqOn (g := padGaussStiefel E ND i)
    (f := fun x : V.pt => padGFrame E ND i x) (continuousOn_padGFrame E ND i) ?_
  intro x hx
  rw [padGaussStiefel_of_mem E ND i hx]

theorem continuous_padGaussFun (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (padGaussFun E ND) := by
  rw [continuous_iff_continuousAt]
  intro x
  set i := ND.D.indexAt x with hi
  have hmem : x ∈ ND.D.baseSet i := ND.D.mem_baseSet_at x
  have hopen : IsOpen (ND.D.baseSet i) := ND.D.isOpen_baseSet i
  have hloc : ContinuousOn (fun y => ogMk k 10 (padGaussStiefel E ND i y)) (ND.D.baseSet i) :=
    (ogMk k 10).continuous.comp_continuousOn (continuousOn_padGaussStiefel E ND i)
  refine (hloc.continuousAt (hopen.mem_nhds hmem)).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with y hy
  rw [padGaussStiefel_of_mem E ND i hy]
  exact (padGaussFun_eq E ND i hy).symm

/-- The plane of the chartwise padded Gauss map is the padded normal plane (spelling in
`Quotient.mk''`). -/
theorem projOfPlane_padGFrame' (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    projOfPlane k 10 (Quotient.mk'' (⟨padGFrame E ND i x,
        padGFrame_orthonormal E ND i hx⟩ : Stiefel k 10))
      = padEndEuc k 10 (by norm_num)
          (((Tubular.normalSpace E x).subtypeL).comp
            ((Tubular.normalSpace E x).orthogonalProjectionOnto)) := by
  rw [projOfPlane_mk k 10 (⟨padGFrame E ND i x,
    padGFrame_orthonormal E ND i hx⟩ : Stiefel k 10)]
  show frameProj (padGFrame E ND i x) = _
  rw [show padGFrame E ND i x
      = fun j => padEuc k 10 (by norm_num) (gframe E ND i x j) from rfl]
  rw [gtdFrameProj_padEuc (k := k) (m := 10) (by norm_num)
    (orthonormal_gframe E ND i hx)]
  rw [span_gframe E ND i hx]

/-- The plane of the chartwise padded Gauss map is the padded normal plane. -/
theorem projOfPlane_padGFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    projOfPlane k 10 (ogMk k 10 (⟨padGFrame E ND i x,
        padGFrame_orthonormal E ND i hx⟩ : Stiefel k 10))
      = padEndEuc k 10 (by norm_num)
          (((Tubular.normalSpace E x).subtypeL).comp
            ((Tubular.normalSpace E x).orthogonalProjectionOnto)) := by
  show projOfPlane k 10 (Quotient.mk'' (⟨padGFrame E ND i x,
      padGFrame_orthonormal E ND i hx⟩ : Stiefel k 10)) = _
  exact projOfPlane_padGFrame' E ND i hx

/-- **The plane of the padded Gauss map is the padded normal plane.** -/
theorem projOfPlane_padGauss (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (x : V.pt) :
    projOfPlane k 10 (padGaussFun E ND x)
      = padEndEuc k 10 (by norm_num)
          (((Tubular.normalSpace E x).subtypeL).comp
            ((Tubular.normalSpace E x).orthogonalProjectionOnto)) := by
  rw [padGaussFun_eq E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)]
  exact projOfPlane_padGFrame E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)

end

end Work.ThomBordism.Grassmann
