import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.Basic

/-!
# The Cantor cover of the interval (foundations for the base case of AN5)

This module fixes the objects used by the Čech argument for the base case `S = PUnit` of
homotopy invariance (`Work.ANALYTIC.profinite_HI_pt`): the light profinite Cantor set
`C = {0,1}^ℕ`, its finite levels `C_n = {0,1}^{n+1}` with the projections `C ⟶ C_n`, and the
binary-expansion map `β : C ⟶ [0,1]` (a surjection of light condensed sets, i.e. an
epimorphism).

The route (REFS/04 §1–2 with `S = PUnit`) is:

* `C_•` = the Čech nerve of `β` (`C_p = C ×_[0,1] ⋯ ×_[0,1] C`, a light profinite set because
  `[0,1]` is Hausdorff), with the Čech complex `R = (ℤ[C_0] ⟶ ℤ[C_1] ⟶ ⋯)` in degrees `≤ 0`
  and the augmentation `R ⟶ single 0 ℤ[[0,1]]`;
* `R ⟶ single 0 ℤ[[0,1]]` is a quasi-isomorphism (the Čech nerve of a cover is a hypercover:
  the cover `{C ⟶ [0,1]}` refines, over any test object `T ⟶ [0,1]`, to a clopen cover of `T`
  admitting local sections);
* the level structure `C_p = lim_n N_n^{(p)}` (`N_n^{(p)}` = `(p+1)`-tuples of level-`n` dyadic
  intervals with a common point) exhibits the *dual* augmented complex
  `E = (ℤ ⟶ C(C_0,ℤ) ⟶ C(C_1,ℤ) ⟶ ⋯)` as the filtered colimit of the level-`n` augmented
  complexes, each of which is exact (the level-`n` nerve is a tree), so `E` is exact and hence
  (it is a bounded-below exact complex of discrete `=` solid groups) contractible;
* levelwise `μ` (`Work.ANALYTIC.exists_muT`, AN3) identifies `ℤ[C_•]` with the solid complex
  `ℤ■[C_•] = ihom(E,ℤ)` up to solid-equivalence, and the contractibility of `E` transfers to a
  homotopy equivalence `ℤ■[C_•] ⟶ ℤ■[∗] = ℤ`;
* two-out-of-three (`ToolkitProp`) then gives `SolidEquiv (ℤ[[0,1]] ⟶ ℤ)`.

`binaryExp_epi` below is the first input; it is stated separately so that it can be proved by a
colleague.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open scoped unitInterval

noncomputable section

namespace Work.ANALYTIC.CechPt

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The light profinite Cantor set `{0,1}^ℕ`. -/
abbrev cantor : LightProfinite.{0} :=
  ∏ᶜ (fun _ : ℕ => FintypeCat.toLightProfinite.obj (FintypeCat.of (Fin 2)))

/-- The interval `[0,1]`, as a light condensed set. -/
abbrev intervalCond : LightCondSet.{0} :=
  topCatToLightCondSet.obj (TopCat.of unitInterval)

end Work.ANALYTIC.CechPt
