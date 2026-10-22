import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.SdPrelude
import Submission.Work.ANALYTIC.CechPt.sd_zf_iso_Cdisc

/-!
# The identification of the dual Čech complex with the discrete locally constant functions

The target statement `Work.ANALYTIC.CechPt.DualAugContractible` concerns the augmented complex

`𝟙 ⟶ (ℤ[C_0] ⟹ 𝟙) ⟶ (ℤ[C_1] ⟹ 𝟙) ⟶ ⋯`

whose terms are the *single duals* `sd (zf (cechTerm p)) = (ℤ[C_p] ⟹ 𝟙)` of the free modules on
the Čech terms.

`Submission/Work/ANALYTIC/CechPt/sd_zf_iso_Cdisc.lean` (a colleague's file) identifies each single
dual with the discrete light condensed abelian group of locally constant `ℤ`-valued functions:
`sd (zf T) ≅ Cdisc T`.  This module records that identification as a single *definition*
`sdBridge T`, so that the contractibility of the dual complex can be proved by transporting the
chain contraction of the (free, exact) complex of locally constant functions across it.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- **The bridge**: for a light profinite set `T`, the single dual `ℤ[T] ⟹ 𝟙` of the free light
condensed abelian group on `T` is the discrete group `C(T,ℤ)_disc` of locally constant `ℤ`-valued
functions on `T`.

This is the isomorphism `sd_zf_iso_Cdisc` of `sd_zf_iso_Cdisc.lean`, made into a definition (so
that its compatibility with maps in `T` can be stated). -/
noncomputable def sdBridge (T : LightProfinite.{0}) : sd (zf T) ≅ Work.ANALYTIC.Cdisc T :=
  (CategoryTheory.ihom (Work.DISC.zfree T)).mapIso (lcDiscIntIso.symm) ≪≫
    @asIso _ _ _ _ (sdIsoHom T (ModuleCat.of ℤ ℤ)) (sdIsoHom_isIso T _)

end Work.ANALYTIC.CechPt
