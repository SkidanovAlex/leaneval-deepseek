import Mathlib
import Submission.Work.ANALYTIC.CechPt.DoubleDual
import Submission.Work.ATOM.Main

/-!
# The dual Čech complex of the Cantor cover

This module contains the *dual* Čech complex of the Cantor cover (the paper's `E_•`, i.e.
`0 → ℤ → C(C_0,ℤ) → C(C_1,ℤ) → ⋯`), whose contractibility is the paper's §1 input, together with
the canonical map comparing it with the free Čech complex.

In the canonical double-dual model of `Submission/Work/ANALYTIC/CechPt/DoubleDual.lean` the terms
of the dual complex are `E^p = sd (ℤ[T_p])` and the differentials are the transposes
`(pre (dR p)).app 𝟙` of the Čech differentials `dR p = ∑ i, (-1)^i ℤ[cechFace p i]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

open Work.ATOM

/-- The Čech differential `∑ i, (-1)^i ℤ[cechFace p i] : ℤ[T_{p+1}] ⟶ ℤ[T_p]`. -/
noncomputable def dR (p : ℕ) : zf (cechTerm (p+1)) ⟶ zf (cechTerm p) :=
  ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) • zmap (cechFace p i)

/-- The transpose of the Čech differential: `sd (ℤ[T_p]) ⟶ sd (ℤ[T_{p+1}])`. -/
noncomputable def dE (p : ℕ) : sd (zf (cechTerm p)) ⟶ sd (zf (cechTerm (p+1))) :=
  (MonoidalClosed.pre (dR p)).app (𝟙_ LightCondAb)

/-- The augmentation of the dual complex: the "constant function `1`", i.e. the transpose of the
sum map `ℤ[T_0] ⟶ ℤ`. -/
noncomputable def rho : (𝟙_ LightCondAb) ⟶ sd (zf (cechTerm 0)) :=
  MonoidalClosed.curry ((ρ_ (zf (cechTerm 0))).hom ≫ zmap (toPt (cechTerm 0)) ≫
    Work.ATOM.unitIso.inv)

/-- The assertion that the augmented *dual* Čech complex of the Cantor cover is contractible:
the terms are `E^p = (ℤ[T_p] ⟹ 𝟙)` (`p ≥ 0`) with the transpose differentials `dE`, augmented by
`rho : 𝟙 ⟶ E^0` (the constant function `1`), and the data below is a contracting homotopy.

This is the paper's REFS/04 §1 statement: `0 → ℤ → C(C_0,ℤ) → C(C_1,ℤ) → ⋯` is a bounded-below
exact complex of free abelian groups, hence contractible. -/
def DualAugContractible : Prop :=
  ∃ (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q))),
    (rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb)) ∧
    (dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0)))) ∧
    (∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1)))))

end Work.ANALYTIC.CechPt
