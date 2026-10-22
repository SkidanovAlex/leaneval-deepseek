import Mathlib
import Submission.Work.ANALYTIC.primedFamily
import Submission.Work.ANALYTIC.exists_tower_F_EAdata
import Submission.Work.ANALYTIC.EA_truncF_whiskerLeft
import Submission.Work.ANALYTIC.truncDataElemDeltaElem

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

/-!
# The identity `h₃` of REFS/03 §1 for the specific towers `F = truncF`, `F' = FP`

The two sides of `h₃` are morphisms `P ⊗ P ⟶ ∏^bnd ℤ`, so it suffices to compare them after
precomposing with the epimorphism `EApp : ℤ[(ℕ∪∞)²] ⟶ P ⊗ P`
(`Work.ATOM.Toolkit.PP_desc`), and then to compare the classifying sections of the two resulting
morphisms `ℤ[(ℕ∪∞)²] ⟶ ∏^bnd ℤ`.

* Right hand side: `EApp ≫ FP ≫ cBounded = χ ≫ cBounded` (`Work.ANALYTIC.FP_spec`), and
  `χ = zmap pairMor ≫ P_proj` by definition, so this is the classifying section of
  `boundedSeq.obj.map pairMor.op deltaElem` (`Work.ANALYTIC.zmapSymm` together with
  `Work.ANALYTIC.P_proj_cBounded`, i.e. `P_proj ≫ cBounded ↦ deltaElem`).
* Left hand side: `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)` by definition, and `EA` is the descent of the
  truncation data (`Work.ANALYTIC.EA_truncF_whiskerLeft`), so this is the classifying section of
  `truncDataElem (ℕ∪∞) deltaElem`.

The two elements agree (`Work.ANALYTIC.truncDataElemDeltaElem`), which is the pointwise identity
`δ_m(j)·[k ≤ m] = δ_m(pairFunP (k,j))` of the truncation data.
-/

/-- `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)`, and `EApp` is an epimorphism (it is an isomorphism
followed by two tensorings of the cokernel projection `P_proj = cokernel.π P_map`, which are
epimorphisms because `tensorLeft`/`tensorRight` are left adjoints). -/
private theorem epiEApp_h3 : Epi Work.ATOM.EApp := by
  have h2 : Epi (LightCondensed.P_proj ▷ Work.ATOM.zfree LightProfinite.NatUnionInfty) :=
    Functor.map_epi (MonoidalCategory.tensorRight (Work.ATOM.zfree LightProfinite.NatUnionInfty))
      (cokernel.π LightCondensed.P_map)
  have h3 : Epi (LightCondensed.P ◁ LightCondensed.P_proj) :=
    Functor.map_epi (MonoidalCategory.tensorLeft LightCondensed.P)
      (cokernel.π LightCondensed.P_map)
  rw [Work.ATOM.EApp]
  exact epi_comp _ _

/-- **The identity `h₃` of REFS/03 §1**: `m ≫ F = F' ≫ g`, i.e.
`(id_P ⊗ cBounded) ≫ (truncation family) = F' ≫ cBounded`, where `F'` is the primed family
`Work.ANALYTIC.FP` built in `Submission/Work/ANALYTIC/primedFamily.lean`.
On generators `(k,j)`: both sides send `e_k ⊗ e_j` to `δ_j·[j ≥ k]`; equivalently, after
precomposing with the epimorphism `EApp` and using `EApp ≫ FP = chi`, both sides become the map
`ℤ[(ℕ∪∞)²] ⟶ ∏^bnd ℤ` sending `[(k,j)]` to `π_{≥k}δ_j = δ_j·[j ≥ k]`. -/
theorem h3_identity :
    (LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ Work.ANALYTIC.truncF =
      Work.ANALYTIC.FP ≫ Work.ANALYTIC.cBounded := by
  haveI : Epi Work.ATOM.EApp := epiEApp_h3
  apply (cancel_epi Work.ATOM.EApp).mp
  -- `P_proj ≫ cBounded` is the morphism classified by the null sequence `deltaElem`
  have heq : freeHomEquiv LightProfinite.NatUnionInfty boundedSeq =
      Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty boundedSeq := rfl
  have hsymm : (LightCondensed.P_proj ≫ cBounded) =
      (Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty boundedSeq).symm deltaElem := by
    rw [← heq]
    exact P_proj_cBounded
  -- the left hand side, as a classifying section
  have hL : Work.ATOM.EApp ≫ ((LightCondensed.P ◁ cBounded) ≫ truncF)
      = truncPhi LightProfinite.NatUnionInfty deltaElem := by
    have h1 : (Work.ATOM.EA LightProfinite.NatUnionInfty ≫ (LightCondensed.P ◁ LightCondensed.P_proj))
        ≫ ((LightCondensed.P ◁ cBounded) ≫ truncF)
      = Work.ATOM.EA LightProfinite.NatUnionInfty
        ≫ ((LightCondensed.P ◁ (LightCondensed.P_proj ≫ cBounded)) ≫ truncF) := by
      rw [Category.assoc]
      congr 1
      rw [← Category.assoc, MonoidalCategory.whiskerLeft_comp]
    calc Work.ATOM.EApp ≫ ((LightCondensed.P ◁ cBounded) ≫ truncF)
        = (Work.ATOM.EA LightProfinite.NatUnionInfty ≫ (LightCondensed.P ◁ LightCondensed.P_proj))
            ≫ ((LightCondensed.P ◁ cBounded) ≫ truncF) := rfl
      _ = Work.ATOM.EA LightProfinite.NatUnionInfty
            ≫ ((LightCondensed.P ◁ (LightCondensed.P_proj ≫ cBounded)) ≫ truncF) := h1
      _ = truncPhi LightProfinite.NatUnionInfty
            (Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty boundedSeq
              (LightCondensed.P_proj ≫ cBounded)) :=
          EA_truncF_whiskerLeft LightProfinite.NatUnionInfty
            (LightCondensed.P_proj ≫ cBounded)
      _ = truncPhi LightProfinite.NatUnionInfty deltaElem := by
          rw [hsymm, Equiv.apply_symm_apply]
  -- the right hand side, as a classifying section
  have hR : Work.ATOM.EApp ≫ (FP ≫ cBounded)
      = truncPhi LightProfinite.NatUnionInfty deltaElem := by
    calc Work.ATOM.EApp ≫ (FP ≫ cBounded)
        = (Work.ATOM.EApp ≫ FP) ≫ cBounded := (Category.assoc _ _ _).symm
      _ = chi ≫ cBounded := by rw [FP_spec]
      _ = (Work.ATOM.zmap pairMor ≫ LightCondensed.P_proj) ≫ cBounded := rfl
      _ = Work.ATOM.zmap pairMor ≫ (LightCondensed.P_proj ≫ cBounded) := Category.assoc _ _ _
      _ = Work.ATOM.zmap pairMor
            ≫ (Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty boundedSeq).symm deltaElem := by
          rw [hsymm]
      _ = (Work.ATOM.homFreeEquiv Work.ATOM.NS2 boundedSeq).symm
            (boundedSeq.obj.map (pairMor).op deltaElem) :=
          zmapSymm boundedSeq Work.ATOM.NS2 LightProfinite.NatUnionInfty pairMor deltaElem
      _ = truncPhi LightProfinite.NatUnionInfty deltaElem := by
          rw [← truncDataElemDeltaElem]; rfl
  rw [hL, hR]

end Work.ANALYTIC
