import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.Tubular.ThomComparison
import Submission.Work.Tubular.ThomRepOfLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Shared vocabulary for the dictionary step (M4) of `collapseLocalisation_ambientV2`

The endgame of the ambient collapse localisation compares two classes of
`H^{8+k}(S^{8+k}, S^{8+k}∖{some p})`, `p = E.e x`:

* the pullback `g^*βf` of the `ν⁺`-avatar of the chart model class along the Pontryagin–Thom
  collapse, and
* the translate `(T_{-p})^*σ` of the model class `σ` on `(S,S∖{0})`.,

Both are compared after restricting to the *open tube* `C.openTube`, where the collapse is
explicitly `some ∘ normalBlowUp ∘ C.inv` and the two model classes agree by the homotopy (F1).
This file collects the small definitions of that comparison, so that the four independent pieces
(the injectivity of the restriction, the two image computations, and the localisation/degree
bookkeeping) can be stated against one fixed vocabulary.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The punctured open tube `{y ∈ C.openTube | y ≠ E.e x}`, described pointwise in the ambient
Euclidean space. -/
abbrev openTubePtset (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) : Set ↥C.openTube :=
  {y | (y.1 : Work.Tubular.Euc (8 + k)) ≠ E.e x}

/-- The inclusion of the open tube into the one-point compactification `S^{8+k}`, `y ↦ some y`. -/
def someOpen (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    C(↥C.openTube, OnePoint (Work.Tubular.Euc (8 + k))) :=
  ⟨fun y => OnePoint.some y.1,
    OnePoint.continuous_coe.comp continuous_subtype_val⟩

@[simp] theorem someOpen_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (y : ↥C.openTube) :
    someOpen E C y = OnePoint.some (y.1 : Work.Tubular.Euc (8 + k)) := rfl

/-- `someOpen` is a map of the pairs `(openTube, openTube∖p) → (S, S∖{some p})`. -/
theorem someOpen_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ openTubePtset E C x,
      someOpen E C y ∈ ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
  fun y hy hcon => hy (OnePoint.coe_injective hcon)

/-- The two inclusions `openTube ↪ S^{8+k}` (via `some`) and `Euc ↪ S^{8+k}` are compatible. -/
theorem someOpen_eq_eucIncl_comp (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    someOpen E C
      = (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
          C(Work.Tubular.Euc (8 + k), OnePoint (Work.Tubular.Euc (8 + k)))).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥C.openTube, Work.Tubular.Euc (8 + k))) := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- **The tube model class**: the pull-back of the standard model generator along the translation
`y ↦ y - E.e x` on the closed tube.  This is the class against which both sides of the dictionary
are compared after restricting to the open tube. -/
noncomputable def tubeTransModel (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (Work.ThomBordism.tubePtSet E C x) :=
  (Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x)
    (Work.ThomBordism.tubePtSet E C x) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (Work.ThomBordism.tubeTransMap_mem E C x) ℤ (8 + k)).hom
    (Work.ThomBordism.stdModelGen (8 + k))

/-- `some` restricted to the closed tube, as a map into the punctured sphere. -/
def tubeSome (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    C(↥(Work.ThomBordism.tubeInvPunct E C),
      ↥(({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))) :=
  ⟨fun y => ⟨OnePoint.some ((y.1 : ↥C.U) : Work.Tubular.Euc (8 + k)),
      fun hcon => Work.ThomBordism.tubeInvPunct_sub E C x y.2 (OnePoint.coe_injective hcon)⟩,
    Continuous.subtype_mk
      (OnePoint.continuous_coe.comp
        (continuous_subtype_val.comp continuous_subtype_val)) _⟩

end

end Work.ThomBordism
