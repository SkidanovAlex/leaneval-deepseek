import Submission.Work.ThomBordism._gtd.P2
import Submission.Work.ThomBordism.OrthFrame.Assembly

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

/-- The padding `padEuc k 10 _` as a linear isometry. -/
def padIsom (k : ℕ) : Euc (8 + k) →ₗᵢ[ℝ] Amb (k + 10) :=
  { toLinearMap := (padEuc k 10 (by norm_num) : Euc (8 + k) →ₗ[ℝ] Amb (k + 10))
    norm_map' := fun x => norm_padEuc k 10 (by norm_num) x }

theorem padIsom_apply (k : ℕ) (x : Euc (8 + k)) :
    padIsom k x = padEuc k 10 (by norm_num) x := rfl

theorem padIsom_inner (k : ℕ) (x y : Euc (8 + k)) :
    inner ℝ (padIsom k x) (padIsom k y) = inner ℝ x y :=
  (padIsom k).inner_map_map x y

/-- The padded σ-corrected normal frame. -/
def padGFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Fin k → Amb (k + 10) :=
  fun a => padIsom k (gframe E ND i x a)

theorem padGFrame_orthonormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Orthonormal ℝ (padGFrame E ND i x) := by
  rw [orthonormal_iff_ite]
  intro a b
  show inner ℝ (padIsom k (gframe E ND i x a))
    (padIsom k (gframe E ND i x b)) = _
  rw [padIsom_inner]
  exact (orthonormal_iff_ite.mp (orthonormal_gframe E ND i hx)) a b

/-- The padded Gauss map, chartwise. -/
def padGaussStiefel (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Stiefel k 10 := by
  classical
  exact if h : x ∈ ND.D.baseSet i then
    ⟨padGFrame E ND i x, padGFrame_orthonormal E ND i h⟩
    else Classical.choice (nonempty_stiefel k 10)

theorem padGaussStiefel_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (h : x ∈ ND.D.baseSet i) :
    padGaussStiefel E ND i x = ⟨padGFrame E ND i x, padGFrame_orthonormal E ND i h⟩ := by
  classical
  rw [padGaussStiefel]
  exact dif_pos h

/-- Two charts give the same padded frame up to the `SO(k)`-action. -/
theorem padGFrame_soAct (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    padGFrame E ND i x
      = soActFun (gauge E ND j x
          * frameChange E ND i j x
          * gauge E ND i x) (padGFrame E ND j x) := by
  funext a
  change padIsom k (gframe E ND i x a)
    = ∑ b, (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) b a
      • padIsom k (gframe E ND j x b)
  have h := congrFun (gframe_expand E ND i j hx) a
  rw [h]
  change padIsom k (∑ b, (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) b a
      • gframe E ND j x b)
    = ∑ b, (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) b a
      • padIsom k (gframe E ND j x b)
  simp only [map_sum, map_smul]

/-- The padded Gauss map is independent of the chart. -/
theorem padGaussStiefel_eq (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    Quotient.mk (grassmannSetoid k 10) (padGaussStiefel E ND i x)
      = Quotient.mk (grassmannSetoid k 10) (padGaussStiefel E ND j x) := by
  rw [padGaussStiefel_of_mem E ND i hx.1, padGaussStiefel_of_mem E ND j hx.2]
  refine Quotient.sound ⟨⟨gauge E ND i x
      * frameChange E ND j i x
      * gauge E ND j x,
      isSO_gchange E ND j i ⟨hx.2, hx.1⟩⟩, ?_⟩
  apply Subtype.ext
  exact padGFrame_soAct E ND j i ⟨hx.2, hx.1⟩

/-- The padded Gauss map as a function on `V`. -/
def padGaussFun (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (x : V.pt) :
    OG k 10 :=
  ogMk k 10 (padGaussStiefel E ND (ND.D.indexAt x) x)

theorem padGaussFun_eq (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    padGaussFun E ND x = ogMk k 10 ⟨padGFrame E ND i x,
      padGFrame_orthonormal E ND i hx⟩ := by
  have h := padGaussStiefel_eq E ND (ND.D.indexAt x) i ⟨ND.D.mem_baseSet_at x, hx⟩
  rw [padGaussStiefel_of_mem E ND i hx] at h
  show ogMk k 10 (padGaussStiefel E ND (ND.D.indexAt x) x) = _
  exact h

end

end Work.ThomBordism.Grassmann
