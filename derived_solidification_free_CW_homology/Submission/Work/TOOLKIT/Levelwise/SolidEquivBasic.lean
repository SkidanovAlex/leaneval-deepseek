/-
AREA TOOLKIT/Levelwise — elementary invariance properties of `SolidEquiv`:
it only depends on the morphism up to composing with isomorphisms on either side.
-/
import Submission.Work.TOOLKIT.Basic

open CategoryTheory Limits
open Submission.Blueprint

noncomputable section

namespace Work.TOOLKIT.Levelwise

/-- Precomposition with an isomorphism is a bijection on `Hom`-sets. -/
theorem bijective_precomp_iso {X X' Z : DCat} (e : X' ⟶ X) (he : IsIso e) :
    Function.Bijective (fun u : X ⟶ Z => e ≫ u) := by
  refine ⟨fun a b h => ?_, fun v => ⟨inv e ≫ v, ?_⟩⟩
  · simpa using congrArg (fun w => inv e ≫ w) h
  · simp [IsIso.hom_inv_id_assoc]

/-- `SolidEquiv` is invariant under composing with isomorphisms. -/
theorem solidEquiv_iso_conj {X Y X' Y' : DCat} (e : X' ⟶ X) (f : X ⟶ Y) (e' : Y ⟶ Y')
    (he : IsIso e) (he' : IsIso e') : SolidEquiv (e ≫ f ≫ e') ↔ SolidEquiv f := by
  have key : ∀ N : SDCat, (fun u : Y' ⟶ iD.obj N => (e ≫ f ≫ e') ≫ u) =
      (fun u : X ⟶ iD.obj N => e ≫ u) ∘ (fun u : Y ⟶ iD.obj N => f ≫ u) ∘
        (fun v : Y' ⟶ iD.obj N => e' ≫ v) := by
    intro N
    funext u
    simp [Category.assoc]
  constructor
  · intro h N
    have hb : Function.Bijective (fun u : Y' ⟶ iD.obj N => (e ≫ f ≫ e') ≫ u) := h N
    rw [key N] at hb
    exact (Function.Bijective.of_comp_iff (fun u : Y ⟶ iD.obj N => f ≫ u)
      (bijective_precomp_iso _ he')).mp
      ((Function.Bijective.of_comp_iff' (bijective_precomp_iso _ he)
        ((fun u : Y ⟶ iD.obj N => f ≫ u) ∘ (fun v : Y' ⟶ iD.obj N => e' ≫ v))).mp hb)
  · intro h N
    have hb : Function.Bijective (fun u : Y ⟶ iD.obj N => f ≫ u) := h N
    rw [key N]
    exact (Function.Bijective.of_comp_iff' (bijective_precomp_iso _ he)
      ((fun u : Y ⟶ iD.obj N => f ≫ u) ∘ (fun v : Y' ⟶ iD.obj N => e' ≫ v))).mpr
      ((Function.Bijective.of_comp_iff (fun u : Y ⟶ iD.obj N => f ≫ u)
        (bijective_precomp_iso _ he')).mpr hb)

end Work.TOOLKIT.Levelwise
