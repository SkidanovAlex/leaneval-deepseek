import Submission.Work.DISC.Defs
import Submission.Work.DISC.isSolid_iff_sections
import Submission.Work.DISC.vanishing_equiv
import Submission.Work.DISC.diff_bijective
import Submission.Work.DISC.sections_disc
import Submission.Work.DISC.projective_discrete_free

/-!
# AREA DISC — discrete objects are solid; discrete free groups are projective

Main result: `Work.DISC.disc_prop : Submission.Blueprint.DiscProp`.

The proof of solidity of discrete objects `ΔM` reduces, via the section criterion
`Work.DISC.isSolid_iff_sections`, to the statement that the sections at every light profinite
set `S` of the map `(1 - shift)^* : (ΔM)^P ⟶ (ΔM)^P` are bijective.  Those sections are
identified in `Work.DISC.sections_disc` with the locally constant functions on
`S × (ℕ∪{∞})` vanishing on `S × {∞}`, on which `(1-shift)^*` acts by
`f ↦ f - f ∘ (id × shift)`.  That model is in turn identified in
`Work.DISC.vanishing_equiv` with the null sequences `Work.DISC.NullSeq S M`, on which the map
becomes the difference of consecutive terms, a bijection by `Work.DISC.diff_bijective`.

Projectivity of the discrete free abelian groups is `Work.DISC.projective_discrete_free`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

/-- Discrete light condensed abelian groups are solid. -/
theorem isSolid_disc (M : ModuleCat.{0} ℤ) : isSolid (disc M) := by
  rw [isSolid_iff_sections]
  intro S
  obtain ⟨e, he⟩ := sections_disc M S
  obtain ⟨e', he'⟩ := vanishing_equiv S M
  have hdiff : Function.Bijective (NullSeq.diff (S := S) (M := M)) := diff_bijective S M
  let E : ↥((ihomP (disc M)).obj.obj (op S)) ≃ NullSeq S M := e.trans e'
  have hE : ∀ x, E ((oneMinusShiftStar (disc M)).hom.app (op S) x) = NullSeq.diff (E x) := by
    intro x
    show e' (e ((oneMinusShiftStar (disc M)).hom.app (op S) x)) = NullSeq.diff (e' (e x))
    rw [he x, he' (e x)]
  have hbijf : Function.Bijective ((oneMinusShiftStar (disc M)).hom.app (op S)) := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h : NullSeq.diff (E x) = NullSeq.diff (E y) := by rw [← hE x, ← hE y, hxy]
      exact E.injective (hdiff.1 h)
    · obtain ⟨n, hn⟩ := hdiff.2 (E y)
      refine ⟨E.symm n, ?_⟩
      have h1 : E ((oneMinusShiftStar (disc M)).hom.app (op S) (E.symm n)) =
          NullSeq.diff (E (E.symm n)) := hE (E.symm n)
      rw [Equiv.apply_symm_apply, hn] at h1
      exact E.injective h1
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbijf

/-- Discrete free abelian groups are projective light condensed abelian groups. -/
theorem projective_disc_free (J : Type) :
    Projective ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ (J →₀ ℤ))) :=
  projective_discrete_free J

/-- **AREA DISC.** Discrete light condensed abelian groups are solid, and discrete free abelian
groups are projective light condensed abelian groups. -/
theorem disc_prop : Submission.Blueprint.DiscProp :=
  ⟨fun M => isSolid_disc M, fun J => projective_disc_free J⟩

/-- The direct form of solidity of discrete objects: `(1 - shift)^*` is invertible on `(ΔM)^P`. -/
theorem isIso_oneMinusShiftStar_disc (M : ModuleCat.{0} ℤ) :
    IsIso (oneMinusShiftStar (disc M)) :=
  isSolid_disc M

/-- The discrete light condensed abelian groups, as a functor with values in solid abelian groups.

This is the functorial form of `DiscProp.1`: it is the composite of
`LightCondensed.discrete (ModuleCat ℤ)` with the full inclusion `Solid ⥤ LightCondAb`. -/
noncomputable def discSolid : ModuleCat.{0} ℤ ⥤ Solid :=
  isSolid.lift (LightCondensed.discrete (ModuleCat ℤ)) (fun M => isSolid_disc M)

end Work.DISC
