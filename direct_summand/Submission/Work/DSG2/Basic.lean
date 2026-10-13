import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG2: Chow's lemma over a Noetherian base — basic infrastructure

This file collects the elementary facts about proper morphisms, Noetherian schemes and
immersions on which the Chow construction (`Submission/Work/DSG2/Chow.lean`) rests.

Main results

* `Work.DSG2.isNoetherian_of_isProper` : a proper scheme over a Noetherian affine base is
  a Noetherian scheme.
* `Work.DSG2.isClosedImmersion_of_isImmersion_of_isProper` : an immersion which is proper is a
  closed immersion.
* `Work.DSG2.isProper_of_isProper_comp` : a morphism which is proper after composing with a
  separated morphism is proper.
* `Work.DSG2.isSeparated_pspace_toSpec` : `ℙ^N_A → Spec A` is separated.

-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

open LeanEval.AlgebraicGeometry.DirectSummand

variable {A : Type u} [CommRing A]

/-- A scheme proper over a Noetherian affine base is a Noetherian scheme. -/
theorem isNoetherian_of_isProper [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] : IsNoetherian X := by
  have h₁ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have h₂ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact AlgebraicGeometry.IsNoetherian.mk (X := X)

/-- If `f : X ⟶ Y` is an immersion and proper, then it is a closed immersion. -/
theorem isClosedImmersion_of_isImmersion_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] [IsProper f] : IsClosedImmersion f :=
  IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- An immersion whose composite with a separated morphism is proper is a closed immersion. -/
theorem isClosedImmersion_of_isImmersion_of_isSeparated {X Y Z : Scheme.{u}} (i : X ⟶ Y)
    (g : Y ⟶ Z) [IsImmersion i] [IsSeparated g] [IsProper (i ≫ g)] : IsClosedImmersion i := by
  have : IsProper i := IsProper.of_comp i g
  exact isClosedImmersion_of_isImmersion_of_isProper i

/-- A morphism which is proper after composing with a separated morphism is proper. -/
theorem isProper_of_isProper_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper (f ≫ g)] [IsSeparated g] : IsProper f :=
  IsProper.of_comp f g

/-- `ℙ^N_A = Proj A[x₀,…,x_N]` is separated over `Spec A`. -/
instance isSeparated_pspace_toSpec (N : ℕ) : IsSeparated (DSMap.PSpace.toSpec A N) := by
  unfold DSMap.PSpace DSMap.PSpace.toSpec DSMap.PGr
  infer_instance

end Work.DSG2
