import Submission.Work.ThomBordism.gaussDefs
import Submission.Work.ThomBordism.gtdFrameProj_padEuc
import Submission.Work.ThomBordism._gtd.P4

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gauss map of the normal data, padded to an arbitrary ambient dimension

`Work.ThomBordism.Grassmann.padGaussFun` (`_gtd/P3`, `_gtd/P4`) is the oriented Gauss map
`V → G̃r_k(ℝ^{k+10})` of the normal data of an embedding `V ↪ ℝ^{8+k}`, built on the
**σ-corrected** normal frame `Work.ThomBordism.gframe` (the correction of
`Work.ThomBordism.orthFrameOrientation` which makes the frames of two charts `SO(k)`-related, i.e.
which orients the normal bundle by the orientation of `V`).  Its ambient dimension `10` is the one
of the family producers (`Work.PTGeometric.GenuineTubeGeometry.mU = 10`).

This file provides the same map **padded to an arbitrary `m ≥ 8`**, which is what an interface that
carries the *oriented* Gauss data of a tube at an arbitrary `mU`
(`Submission/Work/ThomBordism/NOTE_TIE_AND_SIGN_FREEDOM.md` §3) needs: the plane of the tautological
bundle over `G̃r_k(ℝ^{k+m})` and the plane of the tube's σ-corrected normal frame have to be
comparable *in the same ambient space*.  Everything here is the verbatim generalisation of `_gtd/P3`
+ `_gtd/P4` with `padEuc k 10` replaced by `padEuc k m`; the key input
`Work.ThomBordism.gtdFrameProj_padEuc` is already general in `m`.

## Main definitions and results

* `Work.ThomBordism.padIsomM`, `Work.ThomBordism.padGFrameM`, `Work.ThomBordism.padGaussFunM`
* `Work.ThomBordism.padGFrameM_orthonormal`
* `Work.ThomBordism.projOfPlane_padGaussM` — the plane of the padded Gauss map is the padded
  orthogonal projection onto the normal space at the point, i.e. literally
  `Work.PTGeometric.padEndEuc k m hm (work.Tubular.normalSpace-projection)`, which is the expression
  appearing in `Work.PTGeometric.GenuineTubeGeometry.coord_collapse` via
  `Work.PTGeometric.tubeNormalProj`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom
open Work.ThomBordism.Gauss
open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The padding `padEuc k m hm` as a **linear isometry** `ℝ^{8+k} → ℝ^{k+m}` (it is an isometric
insertion: `Work.PTGeometric.norm_padEuc`). -/
def padIsomM (k m : ℕ) (hm : 8 ≤ m) : Work.Tubular.Euc (8 + k) →ₗᵢ[ℝ] Work.PTGeometric.Amb (k + m) :=
  { toLinearMap := Work.PTGeometric.padEuc k m hm
    norm_map' := fun x => Work.PTGeometric.norm_padEuc k m hm x }

theorem padIsomM_apply (k m : ℕ) (hm : 8 ≤ m) (x : Work.Tubular.Euc (8 + k)) :
    padIsomM k m hm x = Work.PTGeometric.padEuc k m hm x := rfl

/-- `padIsomM` preserves inner products. -/
theorem padIsomM_inner (k m : ℕ) (hm : 8 ≤ m) (x y : Work.Tubular.Euc (8 + k)) :
    inner ℝ (padIsomM k m hm x) (padIsomM k m hm y) = inner ℝ x y :=
  (padIsomM k m hm).inner_map_map x y

/-- The **padded σ-corrected normal frame** of the normal data at a point, in ambient dimension
`k + m`. -/
def padGFrameM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (m : ℕ) (hm : 8 ≤ m)
    (i : CoverIdx V k) (x : V.pt) : Fin k → Work.PTGeometric.Amb (k + m) :=
  fun a => padIsomM k m hm (gframe E ND i x a)

/-- The padded σ-corrected normal frame is orthonormal. -/
theorem padGFrameM_orthonormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Orthonormal ℝ (padGFrameM E ND m hm i x) := by
  rw [orthonormal_iff_ite]
  intro a b
  show inner ℝ (padIsomM k m hm (gframe E ND i x a)) (padIsomM k m hm (gframe E ND i x b))
    = if a = b then (1 : ℝ) else 0
  rw [padIsomM_inner]
  exact (orthonormal_iff_ite.mp (orthonormal_gframe E ND i hx)) a b

/-- **The `m`-padded oriented Gauss map of the normal data** of an embedding. -/
def padGaussFunM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (m : ℕ) (hm : 8 ≤ m)
    (x : V.pt) : OG k m :=
  ogMk k m ⟨padGFrameM E ND m hm (ND.D.indexAt x) x,
    padGFrameM_orthonormal E ND m hm (ND.D.indexAt x) (ND.D.mem_baseSet_at x)⟩

/-- The chartwise form of the padded Gauss map. -/
theorem padGaussFunM_eq (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (x : V.pt) :
    padGaussFunM E ND m hm x = ogMk k m ⟨padGFrameM E ND m hm (ND.D.indexAt x) x,
      padGFrameM_orthonormal E ND m hm (ND.D.indexAt x) (ND.D.mem_baseSet_at x)⟩ := rfl

/-- **The plane of the padded Gauss map is the padded normal plane**: the general-`m` form of
`Work.ThomBordism.Grassmann.projOfPlane_padGauss` (`_gtd/P4`), and the expression that the
`coord_collapse` field of `Work.PTGeometric.GenuineTubeGeometry` produces through
`Work.PTGeometric.tubeNormalProj`. -/
theorem projOfPlane_padGaussM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (x : V.pt) :
    Work.PTGeometric.projOfPlane k m (padGaussFunM E ND m hm x)
      = Work.PTGeometric.padEndEuc k m hm
          (((Work.Tubular.normalSpace E x).subtypeL).comp
            ((Work.Tubular.normalSpace E x).orthogonalProjectionOnto)) := by
  rw [padGaussFunM_eq]
  show Work.PTGeometric.projOfPlane k m (Quotient.mk'' (⟨padGFrameM E ND m hm (ND.D.indexAt x) x,
    padGFrameM_orthonormal E ND m hm (ND.D.indexAt x) (ND.D.mem_baseSet_at x)⟩ : Stiefel k m)) = _
  rw [Work.PTGeometric.projOfPlane_mk k m (⟨padGFrameM E ND m hm (ND.D.indexAt x) x,
    padGFrameM_orthonormal E ND m hm (ND.D.indexAt x) (ND.D.mem_baseSet_at x)⟩ : Stiefel k m)]
  show Work.PTGeometric.frameProj (padGFrameM E ND m hm (ND.D.indexAt x) x) = _
  rw [show padGFrameM E ND m hm (ND.D.indexAt x) x
      = fun j => Work.PTGeometric.padEuc k m hm
          (gframe E ND (ND.D.indexAt x) x j) from rfl]
  rw [gtdFrameProj_padEuc (k := k) (m := m) hm
    (orthonormal_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x))]
  rw [span_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)]

end

end Work.ThomBordism
