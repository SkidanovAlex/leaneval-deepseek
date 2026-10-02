import Mathlib
import Submission.Work.Transgression.Statement
import Submission.Work.Transgression.Gysin
import Submission.Work.Transgression.Pieces
import Submission.Work.Transgression.KunnethInjQ2
import Submission.Work.Transgression.PsiClass
import Submission.Work.Transgression.H4Vanishing
import Submission.Work.Transgression.Algebra
import Submission.Work.Transgression.MVDefs
import Submission.Work.Transgression.MV
import Submission.Work.Transgression.Geo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The transgression: `H⁴` of the punctured total space is cyclic of order `|a + b|`

`Work.Transgression.PuncturedCohCard a b` — the number of elements of `H⁴` of the punctured total
space `E ∖ 0` of `clutchBundle a b` is `|a + b|` — is the Mayer–Vietoris (transgression)
computation of the sphere bundle `(D⁴ × S³) ∪_{q ↦ qᵃ(·)qᵇ} (D⁴ × S³)`.

The assembly is in `Submission/Work/Transgression/MV.lean`
(`Work.Transgression.puncturedCohCard_of_inputs`), on top of the geometric inputs of
`Submission/Work/Transgression/Geo.lean`: the two retractions `rhoU`, `rhoV` are onto on `H³`, the
overlap retraction `rhoW` is a homotopy equivalence, and the two composites
`rhoU ∘ iotaU = prjB ∘ rhoW`, `rhoV ∘ iotaV = ψ ∘ rhoW` compute the restrictions to the overlap.
The vanishing of `H⁴` on the two pieces is `Work.Transgression.H4Vanishing`, the Künneth
injectivity for `S³ × S³` is `Work.Transgression.KunnethInjQ2`, and the class of the clutching map
is `Work.Transgression.PsiClass`.
-/

namespace Work.Transgression

open Work.TangentClasses CategoryTheory Limits

noncomputable section

/-- The underlying linear map of a composite pullback is the composite of the pullbacks. -/
lemma HMap_comp_hom {B₁ B₂ B₃ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    [TopologicalSpace B₃] (f : C(B₁, B₂)) (g : C(B₂, B₃)) (n : ℕ) :
    (HMap f n).hom.comp (HMap g n).hom = (HMap (g.comp f) n).hom := by
  rw [HMap_comp f g n, ModuleCat.hom_comp]

theorem PuncturedCohCardAll : ∀ a b : ℤ, Work.Transgression.PuncturedCohCard a b := by
  intro a b
  refine Work.Transgression.puncturedCohCard_of_inputs a b
    (Work.Transgression.H4Vanishing a b).1 (Work.Transgression.H4Vanishing a b).2
    (Work.Transgression.Geo.surjective_HMap_rhoU a b 3)
    (Work.Transgression.Geo.surjective_HMap_rhoV a b 3)
    (Work.Transgression.Geo.bijective_HMap_rhoW a b 3) ?_ ?_
    (fun x h1 h2 => Work.Transgression.KunnethInjQ2 x h1 h2) ?_
  · rw [Work.Transgression.HMap_comp_hom (Work.Transgression.MV.iotaU a b)
        (Work.Transgression.rhoU a b) 3,
      Work.Transgression.HMap_comp_hom (Work.Transgression.rhoW a b)
        (Work.Transgression.prjB) 3]
    rw [Work.Transgression.Geo.rhoU_iotaU]
  · rw [Work.Transgression.HMap_comp_hom (Work.Transgression.MV.iotaV a b)
        (Work.Transgression.rhoV a b) 3,
      Work.Transgression.HMap_comp_hom (Work.Transgression.rhoW a b)
        (Work.Transgression.psi a b) 3]
    rw [Work.Transgression.Geo.rhoV_iotaV]
  · exact Work.Transgression.PsiClass a b Work.Transgression.MV.gen3
      Work.Transgression.MV.gen3_generates

end

end Work.Transgression
