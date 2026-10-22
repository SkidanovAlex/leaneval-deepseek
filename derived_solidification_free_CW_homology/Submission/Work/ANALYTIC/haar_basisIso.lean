import Mathlib
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ANALYTIC.HaarBasisMain

/-!
# `haar_basisIso`: `C(T,ℤ)` is free on the Haar/Schauder basis

For an infinite light profinite set `T`, the `ℤ`-module `C(T,ℤ) = LC T` of locally constant
`ℤ`-valued functions is free, with basis the cylinders `fCyl T j` (`j : ℕ`) together with the
constant function `1`; the dual coordinates are the functionals `phiJ T j` of `HaarDefs.lean`
(`phiJ T ∞` being the evaluation at the base point `s₀`).

The proof is in `Submission/Work/ANALYTIC/HaarBasisMain.lean`, where the theorem is also stated as
`Work.ANALYTIC.Haar.haar_basisIso` with `Haar.LC` in place of `LC` (see below): the two linear maps

* `psi : (JIdx →₀ ℤ) →ₗ[ℤ] LC T`, `Finsupp.single j 1 ↦ fJ T j`, and
* `phiLin : LC T →ₗ[ℤ] (JIdx →₀ ℤ)`, `lam ↦ (j ↦ phiJ T j lam)` (well defined because
  `phiJ T j lam = 0` for `lvl j` larger than a level through which `lam` factors),

are mutually inverse: `phiLin ∘ psi = id` is the biorthogonality
`Work.ANALYTIC.haar_biorth`, and `psi ∘ phiLin = id` is the level-`N` expansion
`Work.ANALYTIC.haar_expand` (every locally constant function factors through `e_N` for some `N`,
by `Profinite.exists_locallyConstant`).

## A note on the name `LC`

The statement below uses the abbreviation `Work.ANALYTIC.LC` (defined here, privately, as
`LocallyConstant ↥T ℤ`).  `Submission/Work/ANALYTIC/HaarDefs.lean` places the same definition in
the `Haar` namespace as `Work.ANALYTIC.Haar.LC`, because
`Submission/Work/ANALYTIC/preSolid_setup.lean` uses the name `Work.ANALYTIC.LC` for the degreewise
extension of `tensorLeft P` to cochain complexes; a module importing both `preSolid_setup` and this
file would therefore see two declarations with the same name.  Such a module should use
`Work.ANALYTIC.Haar.haar_basisIso` from `Submission/Work/ANALYTIC/HaarBasisMain.lean` instead,
which is the same theorem with `Haar.LC` for `LC` and imports nothing that clashes.
-/

namespace Work.ANALYTIC

/-- The abbreviation of `LocallyConstant ↥T ℤ` used by the statement of `haar_basisIso`; it is
`Work.ANALYTIC.Haar.LC` (the two are definitionally equal).  It is `private` so that importing
this file together with `preSolid_setup` (which uses `Work.ANALYTIC.LC` for another definition)
does not clash: from the outside, the type of `haar_basisIso` below unfolds to the one with
`Work.ANALYTIC.Haar.LC`. -/
private abbrev LC (T : LightProfinite.{0}) : Type := LocallyConstant ↥T ℤ

theorem haar_basisIso (T : LightProfinite.{0}) [Infinite T] :
    ∃ e : CategoryTheory.Iso (ModuleCat.of ℤ (Work.ANALYTIC.LC T))
        (ModuleCat.of ℤ (Work.ANALYTIC.Haar.JIdx →₀ ℤ)),
      (∀ (lam : Work.ANALYTIC.LC T) (j : Work.ANALYTIC.Haar.JIdx),
        e.hom.hom lam j = Work.ANALYTIC.Haar.phiJ T j lam) ∧
      (∀ j : Work.ANALYTIC.Haar.JIdx,
        e.inv.hom (Finsupp.single j 1) = Work.ANALYTIC.Haar.fJ T j) :=
  Haar.haar_basisIso T

end Work.ANALYTIC
