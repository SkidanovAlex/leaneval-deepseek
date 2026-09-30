import Mathlib
import Submission.Work.SSSR.serreE1CoefExplicit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

attribute [local instance] Classical.propDecidable

variable (X : SSet.{0}) (M : ModuleCat R)

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
coefficient isomorphism `Work.SSSR.serreE1CoefIsoIso`). -/
noncomputable def faceD' (j : ℕ) :
    (∐ (fun _ : Work.SSSR.nIndex X (j+1) => M)) ⟶ (∐ (fun _ : Work.SSSR.nIndex X j => M)) :=
  (Work.SSSR.coprodReindexIso X (j+1) M).inv ≫ faceD X M j ≫
    (Work.SSSR.coprodReindexIso X j M).hom

end

end Work.SSSR
