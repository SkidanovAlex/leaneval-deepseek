import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.Grassmann.coframingDefs
import Submission.Work.ThomBordism.concatBlockCoord
import Submission.Work.ThomBordism.FrameSigns.Charts
import Submission.Work.ThomBordism.sourceZeroSet_boundary_homeo_spec_coord
import Submission.Work.PTGeometric.WeakRegion.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lead chapter (orientation comparison): helper definitions

Shared vocabulary for `S1_K1det`, `S2_bdryTransfer`, `S3_tubeDet`, `S4_collarChart`
(see `ASSEMBLY.md`).  No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

/-! ## Small definitions -/

/-- The `±1` sign of a real number (`0 ↦ -1`, junk). -/
def sgnZ (r : ℝ) : ℤ := if 0 < r then 1 else -1

/-- **The block determinant** of a frame `[A | N]` of `ℝ^{9+k}` (level directions `A`, normal
directions `N`), read against the fixed reference splitting `CofAtlas.sigma k` (any fixed reference
only changes a global constant). -/
def blockDet (k : ℕ) (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
    (N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k) : ℝ :=
  LinearMap.det ((A.coprod N).toLinearMap ∘ₗ (CofAtlas.sigma k).symm.toLinearMap)

/-- The orthonormal frame (`Quotient.out`) of an oriented plane, as a linear map `ℝ^k → ℝ^{k+m}`. -/
def ogFrameCLM {k m : ℕ} (Γ : Work.ThomBordism.Grassmann.OG k m) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + m)) :=
  ∑ a : Fin k, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
    ((Quotient.out Γ).1 a)

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-- The flat source homotopy of the family, on the whole of `ℝ^{9+k}`. -/
def srcHf (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
  flatSourceHomotopy8 (k := k) (familySource G m hpow).H (familySource G m hpow).φ

open Classical in
/-- **The raw level function of the source construction** on `ℝ^{9+k}` (the `v` of
`sourceRawAmbientData_tied_collar.lean`, Step 4; junk `0` on the base-point preimage). -/
def vSrc (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) → EuclideanSpace ℝ (Fin (k + G.mU)) := fun u =>
  if h : srcHf G m hpow u = D.t₀ then 0 else (G.coord ⟨srcHf G m hpow u, h⟩).2

/-- The type of the specified boundary identification of the source zero set. -/
abbrev BdryId (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) : Type :=
  ↥(sourceZeroSet G m hpow ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) ≃ₜ
    (Σ a : Fin m × ι, (Fam a.2).pt)

/-- The specification of `sourceZeroSet_boundary_homeo_spec_coord` (the tube dictionary). -/
def BdryIdSpec (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow) : Prop :=
  ∀ x, (G.emb (h x).1.2).e (h x).2
        = Work.Tubular.cubeToEuc (8 + k) G.R
            (Work.ThomBordism.blockTubePoint G m
              (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1))))
    ∧ ((h x).1.1 : ℕ)
        = (Work.ThomBordism.outerStep G m
            (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)))).1
    ∧ ((Fintype.equivFin ι (h x).1.2) : ℕ)
        = (Work.ThomBordism.innerStep G m
            (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)))).1

/-- **The collar–piece parametrisation** `Ψ_{a,i}(t, u) = (t, spatial part of h⁻¹(a, φᵢ⁻¹ u))`:
the inverse of the collar chart of the level set at the piece `a`, chart `i`, in the identity
coordinates of the half-space `ℝ^{9+k}`. -/
def collarPiece (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) :
    CofAtlas.E9 → EuclideanSpace ℝ (Fin ((8 + k) + 1)) := fun z =>
  consVec (z 0) (tailVec
    ((h.symm ⟨a, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm (tail 8 z)⟩).1).1)

end


end Work.ThomBordism.LeadChapter
