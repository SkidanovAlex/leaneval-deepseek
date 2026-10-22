import Mathlib
import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.Main
import Submission.Work.ANALYTIC.Unconditional
import Submission.Work.ANALYTIC.cBounded_solidEquiv
-- the pieces of the route, see `Submission/Work/ANALYTIC/MuT_Route.lean`
import Submission.Work.ANALYTIC.MuTAssembly
import Submission.Work.ANALYTIC.haar_basisIso
import Submission.Work.ANALYTIC.solidDual_iso_biprod
import Submission.Work.ANALYTIC.exists_kTilde
import Submission.Work.ANALYTIC.solidDual_iso_zfree_of_finite

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-- **AN3, existence form (REFS/03 §4).**  For every light profinite `T` there is a morphism
`mu : ℤ[T] ⟶ ℤ■[T] = ihom(C(T,ℤ)_disc, ℤ)` which is a solid-equivalence.  The intended witness is
the evaluation pairing `μ_T` (so that a later step can name it as `Classical.choose` of this), but
this statement only asks for the mathematical content.

Objects: `Cdisc T` and `solidDual T := (ihom (Cdisc T)).obj 𝟙_` are in
`Submission/Work/ANALYTIC/SolidDual.lean`, with `Cdisc_obj_obj : Cdisc T (S) = LocallyConstant S (LocallyConstant T ℤ)`
(definitionally) — use these explicit sections.  Note `𝟙_ LightCondAb = Z` definitionally
(`unit_eq_Z`), and `WeaklyLocallyConstant`/`LocallyConstant.comapₗ` are the tools for the
functoriality of `Cdisc`.

Route (REFS/03 §4), all ingredients now available in this area:
1. Build the evaluation pairing `uncurry mu : Cdisc T ⊗ ℤ[T] ⟶ 𝟙_` (equivalently
   `mu := MonoidalClosed.curry pairing`); at the level of `S`-points it sends
   `f : LocallyConstant S (LocallyConstant T ℤ)` and `[t]` to `f(s)(t)`.  Use
   `LightCondensed.freeForgetAdjunction`, `(coherentTopology LightProfinite).yonedaEquiv` (see
   `Work.ANALYTIC.freeHomEquiv` in `Submission/Work/ANALYTIC/RealCond.lean`), and the unitor.
2. Show that `LocallyConstant T ℤ` has a Haar/Schauder `ℤ`-basis: the functionals
   `f ↦ f(a_j) − f(e_{n(j)-1} a_j)` of REFS/03 §1 (the "new points" construction, the same
   combinatorics area ATOM uses for `ℤ[S]`), triangular with respect to the levels, every
   `f ∈ C(T_m, ℤ)` having finitely many nonzero coordinates.  Hence `solidDual T ≅ prodZModel`
   (`Submission/Work/ANALYTIC/ProdZModel.lean`) for infinite `T` (and `solidDual T ≅ ℤ[T]` for
   finite `T`).
3. Identify `mu` with the standard map (`e_j ↦ δ_j` under that iso), and conclude that `mu` is a
   solid-equivalence using AN1 (`Work.ANALYTIC.cBounded_solidEquiv`, the null sequence
   `P ⟶ ∏^bnd ℤ`) and AN2 (`Work.ANALYTIC.solidEquiv_boundedSeqIncl`,
   `∏^bnd ℤ ⟶ ∏ℤ`): the null-sequence map `g : P ⟶ ℤ[T]` of REFS/03 §1 is a solid-equivalence by
   the same scheme as AN1, `g ≫ mu` is the standard map `P ⟶ ∏^bnd ℤ ⟶ ∏ℤ` (a solid-equivalence
   by AN1 + AN2), so 2-out-of-3 (`Submission.Blueprint.ToolkitProp.of_comp_left` /
   `of_comp_right`) gives that `mu` is a solid-equivalence.

**Correction (see `Submission/Work/ANALYTIC/MuT_Route.lean`).**  Step 3 above is not correct as
stated: the null sequence `g : P ⟶ ℤ[T]` of REFS/03 §1 (*any* one with `g ≫ qred = gRed`) is *not*
a solid-equivalence, because `qred : ℤ[T] ⟶ ℤ̃[T]` is a split epimorphism and is not a
solid-equivalence, so two-out-of-three forces `¬ SolidEquiv g`.  The proof below therefore uses the
*reduced* null sequence `k : ℤ̃[T] ⟶ ∏ℤ` (`Work.ANALYTIC.exists_kTilde`), ATOM's splitting
`ℤ[T] ≅ ℤ[pt] ⊞ ℤ̃[T]`, the Haar basis `LC T ≅ (JIdx →₀ ℤ)` (`Work.ANALYTIC.haar_basisIso`), the
resulting `solidDual T ≅ Z ⊞ ∏ℤ` (`Work.ANALYTIC.solidDual_iso_biprod`), closure of
solid-equivalences under biproducts (`Work.ANALYTIC.solidEquiv_biprod`) and the finite case
(`Work.ANALYTIC.solidDual_iso_zfree_of_finite`).  The assembly itself is verified in
`Submission/Work/ANALYTIC/MuTAssembly.lean` (`Work.ANALYTIC.exists_muT_of_pieces_all`).
-/
theorem exists_muT (T : LightProfinite) (hTK : Submission.Blueprint.ToolkitProp) :
    ∃ (mu : (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ solidDual T),
      Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map mu) := by
  refine Work.ANALYTIC.exists_muT_of_pieces_all T hTK ?_ ?_ ?_ ?_
  · intro hInf
    haveI : Infinite T := hInf
    exact Work.ANALYTIC.haar_basisIso T
  · intro hInf
    haveI : Infinite T := hInf
    exact Work.ANALYTIC.solidDual_iso_biprod T (Classical.choose (Work.ANALYTIC.haar_basisIso T))
  · intro hInf
    haveI : Infinite T := hInf
    exact Work.ANALYTIC.exists_kTilde T
  · intro hFin
    haveI : Finite T := hFin
    exact Work.ANALYTIC.solidDual_iso_zfree_of_finite T

end

end Work.ANALYTIC
