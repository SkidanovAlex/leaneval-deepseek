import Mathlib
import Submission.Work.DISC.Defs

/-!
# AREA DISC — discrete free light condensed abelian groups are projective

The discrete light condensed abelian group `ΔM` on an abelian group `M` is left adjoint to the
functor `Γ = LightCondensed.underlying (ModuleCat ℤ)` which evaluates a light condensed
`ℤ`-module at the point (`LightCondensed.discreteUnderlyingAdj`).

We prove here that `Γ` preserves epimorphisms.  Indeed, a morphism `A ⟶ B` of light condensed
`ℤ`-modules is an epimorphism iff it is locally surjective w.r.t. surjections of light profinite
sets (`LightCondMod.epi_iff_locallySurjective_on_lightProfinite`).  Applying this with the source
equal to the one-point light profinite set `↧PUnit`, a section `b ∈ B(↧PUnit)` admits a lift
`a' ∈ A(S')` over some surjection `S' ↠ ↧PUnit`; such an `S'` is nonempty, so there is a point
`s : ↧PUnit ⟶ S'` and restricting `a'` along `s` gives a lift of `b` in `A(↧PUnit)`.

Consequently `Δ` carries projective objects of `ModuleCat ℤ` (i.e. retracts of free abelian
groups) to projective objects of `LightCondAb`, by `CategoryTheory.Adjunction.map_projective`,
and the free abelian group `ℤ[J] = J →₀ ℤ` is projective.  This is the DISC input
"discrete free abelian groups are projective" (`Submission.Blueprint.DiscProp`).
-/

namespace Work.DISC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

/-- The point-sections functor `A ↦ A(↧PUnit)` on light condensed `ℤ`-modules preserves
epimorphisms: an epimorphism of light condensed modules is locally surjective
(`LightCondMod.epi_iff_locallySurjective_on_lightProfinite`), every cover of the one-point light
profinite set is split by a point of the cover, and restricting a local lift along such a point
gives a global lift. -/
instance underlying_preservesEpimorphisms :
    (LightCondensed.underlying (ModuleCat.{0} ℤ)).PreservesEpimorphisms where
  preserves := by
    intro X Y f hf
    rw [ModuleCat.epi_iff_surjective]
    show Function.Surjective ⇑(f.hom.app (op (↧PUnit : LightProfinite.{0})))
    intro y
    -- local surjectivity over the point: `y` lifts on a cover `S'` of the point
    obtain ⟨S', φ, hφ, x, hx⟩ :=
      (LightCondMod.epi_iff_locallySurjective_on_lightProfinite (R := ℤ) f).mp hf
        (↧PUnit : LightProfinite.{0}) y
    -- any cover of the point is nonempty, hence contains a point
    obtain ⟨s, -⟩ := hφ PUnit.unit
    let σ : (↧PUnit : LightProfinite.{0}) ⟶ S' :=
      CompHausLike.ofHom _ ⟨fun _ => s, continuous_const⟩
    -- restricting the local lift along the point `σ` gives a global lift
    refine ⟨X.obj.map (op σ) x, ?_⟩
    -- `σ ≫ φ = 𝟙`, since `↧PUnit` is terminal
    have hcomp : op φ ≫ op σ = 𝟙 (op (↧PUnit : LightProfinite.{0})) := by
      have : Subsingleton ((↧PUnit : LightProfinite.{0}) ⟶ (↧PUnit : LightProfinite.{0})) :=
        ⟨fun a b => by ext z⟩
      exact Subsingleton.elim _ _
    -- naturality of `f`, the defining property of `x`, and `σ ≫ φ = 𝟙`
    rw [NatTrans.naturality_apply f.hom (op σ) x, hx,
      ← Functor.map_comp_apply Y.obj (op φ) (op σ) y, hcomp]
    simp

/-- The discrete light condensed `ℤ`-module on a projective `ℤ`-module is projective: the
discrete functor is left adjoint to the point-sections functor, which preserves epimorphisms. -/
theorem projective_discrete_of_projective (P : ModuleCat.{0} ℤ) (hP : Projective P) :
    Projective ((LightCondensed.discrete (ModuleCat ℤ)).obj P) :=
  (LightCondensed.discreteUnderlyingAdj (C := ModuleCat.{0} ℤ)).map_projective P hP

/-- The free `ℤ`-module `J →₀ ℤ` on a small type `J` is projective. -/
theorem projective_finsupp (J : Type) : Projective (ModuleCat.of ℤ (J →₀ ℤ)) :=
  ModuleCat.projective_of_free (Finsupp.basisSingleOne (R := ℤ) (ι := J))

/-- The discrete light condensed abelian group `Δ(ℤ[J])` on a free abelian group is projective
in light condensed abelian groups. -/
theorem projective_discrete_free (J : Type) :
    CategoryTheory.Projective
      ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ (J →₀ ℤ))) :=
  projective_discrete_of_projective _ (projective_finsupp J)

end

end Work.DISC
