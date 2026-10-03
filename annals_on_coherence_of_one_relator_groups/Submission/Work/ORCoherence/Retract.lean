import Submission.Work.ORCoherence.Imports

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u

/-- A projective left `R`-module is a retract of a free `R`-module. -/
theorem projective_retract_free {R : Type u} [Ring R] (P : ModuleCat.{u} R) [Projective P] :
    ∃ (X : Type u) (s : P ⟶ (ModuleCat.free R).obj X)
      (π : (ModuleCat.free R).obj X ⟶ P), s ≫ π = 𝟙 P := by
  classical
  let eLin : (↑P →₀ R) →ₗ[R] ↑P := Finsupp.lift (↑P) R (↑P) (fun p : ↑P => p)
  let e : ModuleCat.of R (↑P →₀ R) ⟶ P := ModuleCat.ofHom eLin
  have hsingle : ∀ p : ↑P, eLin (Finsupp.single p 1) = p := by
    intro p
    erw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp
  have hsurj : Function.Surjective (ModuleCat.ofHom eLin) := by
    intro p
    exact ⟨Finsupp.single p 1, hsingle p⟩
  haveI : Epi e := (ModuleCat.epi_iff_surjective e).mpr hsurj
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) e
  exact ⟨P, s, e, hs⟩

end Work.ORCoherence
