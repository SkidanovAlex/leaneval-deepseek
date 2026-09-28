import Mathlib
import Submission.Work.SSS.serreE1CoefExplicit

/-!
# The alternating-face differential on nondegenerate simplices

The normalized chain complex `N_*(X)` of a simplicial set is free on the *nondegenerate* simplices
of `X` in each degree, and its differential sends a nondegenerate simplex `σ` to the alternating sum
`∑_i (-1)^i d_i σ` of its faces, a degenerate face contributing `0`.  Consequently the tensor
complex `N_*(X) ⊗ M` has, in the coordinates `∐_{σ ∈ ND_n} M`, the differential
`∑_i (-1)^i (face_i ⊗ id)`.

`Work.SSS.faceD` is that differential, exposed as a morphism so that its agreement with the
differential of `Work.SSS.tensorComplex (X.normalizedChainComplex ℤ) M` (through the explicit
coefficient isomorphism `Work.SSS.serreE1CoefIsoIso`) is a concrete statement — the bridge that
lets the differential `d¹` of the E¹ page be compared with `∂ ⊗ id`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

attribute [local instance] Classical.propDecidable

variable (X : SSet.{0}) (M : ModuleCat ℤ)

/-- **The alternating-face differential** `∐_{σ ∈ ND_{j+1}} M ⟶ ∐_{τ ∈ ND_j} M`: a nondegenerate
`(j+1)`-simplex `σ` is sent to `∑_i (-1)^i [d_i σ]`, where `[d_i σ]` is the class of the face `d_iσ`
in the `d_iσ`-summand if that face is nondegenerate, and `0` otherwise. -/
noncomputable def faceD (j : ℕ) :
    (∐ (fun _ : X.nonDegenerate (j+1) => M)) ⟶ (∐ (fun _ : X.nonDegenerate j => M)) := by
  classical
  exact Sigma.desc (fun σ : X.nonDegenerate (j+1) =>
    ∑ i : Fin (j+2), (-1 : ℤ) ^ (i : ℕ) •
      (if h : X.δ i σ.1 ∈ X.nonDegenerate j then
        Sigma.ι (fun _ : X.nonDegenerate j => M) ⟨X.δ i σ.1, h⟩
       else 0))

/-- The `σ`-component of `faceD`: on the `σ`-summand it is the alternating sum of the face maps. -/
@[simp]
lemma faceD_ι (j : ℕ) (σ : X.nonDegenerate (j+1)) :
    Sigma.ι (fun _ : X.nonDegenerate (j+1) => M) σ ≫ faceD X M j =
      ∑ i : Fin (j+2), (-1 : ℤ) ^ (i : ℕ) •
        (if h : X.δ i σ.1 ∈ X.nonDegenerate j then
          Sigma.ι (fun _ : X.nonDegenerate j => M) ⟨X.δ i σ.1, h⟩
         else 0) := by
  classical
  exact Sigma.ι_desc _ _

/-- **The alternating-face differential, indexed by `nIndex`** (the index type used by the
coefficient isomorphism `Work.SSS.serreE1CoefIsoIso`). -/
noncomputable def faceD' (j : ℕ) :
    (∐ (fun _ : Work.SSS.nIndex X (j+1) => M)) ⟶ (∐ (fun _ : Work.SSS.nIndex X j => M)) :=
  (Work.SSS.coprodReindexIso X (j+1) M).inv ≫ faceD X M j ≫
    (Work.SSS.coprodReindexIso X j M).hom

end

end Work.SSS
