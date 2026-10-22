import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup

/-!
# Extensionality of morphisms of light condensed abelian groups along generalized points

`Work.ANALYTIC.GenPointsExt` says that a morphism `∏^bnd ℤ ⟶ ∏^bnd ℤ` is determined by its
values on the generalized points `ℤ[S] ⟶ ∏^bnd ℤ`, `S` ranging over the light profinite sets.
It is the special case `M = N = ∏^bnd ℤ` of the general fact that morphisms of light condensed
abelian groups are determined by their values on sections over light profinite sets.

The proof is a three-line application of the free–forget adjunction for light condensed
`ℤ`-modules: `Work.ATOM.homFreeEquiv S M : (ℤ[S] ⟶ M) ≃ M(S)` is a *natural* equivalence
(`Work.ATOM.homFreeEquiv_naturality_target`), so evaluating `g ≫ u` at the section
`homFreeEquiv S M g` recovers `u.hom.app S (x)`; and a morphism of sheaves is determined by its
components (`LightCondensed.hom_ext`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- **Extensionality along generalized points.**  A morphism `u : M ⟶ N` of light condensed
abelian groups is determined by the composites `g ≫ u` with the generalized points
`g : ℤ[S] ⟶ M`, `S` light profinite. -/
theorem hom_eq_of_zfree_comp_eq {M N : LightCondAb} {u v : M ⟶ N}
    (h : ∀ (S : LightProfinite.{0}) (g : Work.ATOM.zfree S ⟶ M), g ≫ u = g ≫ v) : u = v := by
  apply LightCondensed.hom_ext
  rintro ⟨T⟩
  ext x
  -- `x` is the section of `M` over `T` classified by the generalized point
  -- `g = homFreeEquiv T M |>.symm x`, so the hypothesis applied to `g` computes `u` and `v` at `x`.
  have hg := congrArg (Work.ATOM.homFreeEquiv T N)
    (h T ((Work.ATOM.homFreeEquiv T M).symm x))
  rw [Work.ATOM.homFreeEquiv_naturality_target T u,
    Work.ATOM.homFreeEquiv_naturality_target T v, Equiv.apply_symm_apply] at hg
  exact hg

/-- **`GenPointsExt`**: morphisms `∏^bnd ℤ ⟶ ∏^bnd ℤ` are determined by their values on the
generalized points `ℤ[S] ⟶ ∏^bnd ℤ` (`S` light profinite). -/
theorem genPointsExt : Work.ANALYTIC.GenPointsExt :=
  fun _ _ h => hom_eq_of_zfree_comp_eq h

end Work.ANALYTIC
