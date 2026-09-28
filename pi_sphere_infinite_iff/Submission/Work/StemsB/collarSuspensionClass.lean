import Mathlib
import Submission.Work.StemsB.collar_thomClass
import Submission.Work.StemsB.serreSphere_collar_les_degenerates

/-!
# The suspension class of the collar pair

For the collar pair `(Q, C) = (↥(sphLoopBig b) × Y, sphLoopCollarProd b Y)` of the sphere model
(`b ≥ 1`, `Y` an arbitrary space) the long exact sequence of the pair degenerates
(`Work.StemsB.serreSphere_collar_delta_surjective`): the connecting homomorphism
`δ : H^n(C;ℤ) ⟶ H^{n+1}(Q,C;ℤ)` is surjective in every degree.  The pair also carries a **Thom
class** (`Work.StemsB.collar_thomClass`): a class `τ ∈ H^b(Q,C;ℤ)` for which cupping,
`x ↦ π^*(x) ⌣ τ`, is a bijection `H^k(Y;ℤ) → H^{k+b}(Q,C;ℤ)` in every degree.

This file records the consequence: **there is a class `s ∈ H^{b-1}(C;ℤ)` whose transgression is the
Thom class**, `δ(s) = τ`.  This is the "suspension class" of the collar — the class whose
transgression is the fundamental class of the disc pair — i.e. the object called `s` in
`D2_PLAN.md` §2 item 4.  Together with the exactness of the pair sequence (`ker δ = im i^*`) it
splits the pair sequence.

The identity `δ(s) = τ` is stated after transporting `τ` along the arithmetic identity
`(b - 1) + 1 = b`, since `pairδ` lands in degree `(b - 1) + 1`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The projection `↥(sphLoopBig b) × Y → Y`. -/
def collarProjY (b : ℕ) : C(↥(sphLoopBig b) × Y, Y) :=
  ⟨fun p => p.2, by fun_prop⟩

/-- **The suspension class of the collar pair.**  There is a class `τ ∈ H^b(Q,C;ℤ)` with the Thom
property of the collar pair and a class `s ∈ H^{b-1}(C;ℤ)` whose connecting image is `τ`. -/
theorem collarSuspensionClass (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ (s : Work.Cohomology.singularCohomology ℤ (b - 1)
          (TopCat.of ↥(sphLoopCollarProd b Y)))
      (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)),
      (∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
        (Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) k b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ k).hom x) τ)) ∧
      (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
          (b - 1)).hom s =
        (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℤ
            (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
          (by omega : b - 1 + 1 = b)).symm) τ := by
  obtain ⟨τ, hτ⟩ := collar_thomClass b hb Y
  have hsurj : Function.Surjective (Work.Cohomology.pairδ ℤ
      (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y) (b - 1)).hom :=
    serreSphere_collar_delta_surjective (R := ℤ) (Y := Y) b hb (b - 1)
  obtain ⟨s, hs⟩ := hsurj ((eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℤ
      (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)).homology t)
      (by omega : b - 1 + 1 = b)).symm) τ)
  exact ⟨s, τ, hτ, hs⟩

end

end Work.StemsB
