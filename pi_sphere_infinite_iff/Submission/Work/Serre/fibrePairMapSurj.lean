import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.B1Rel.Final
import Submission.Work.Serre.B1Rel.relKronMapR_natural

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

/-- The relative edge map of a Serre fibration is surjective in degree `r`:
`H^r(B,{b};ℚ) → H^r(E, p⁻¹{b};ℚ)`.  (Both reviews of this statement agree it is true, indeed an
isomorphism: in the relative Serre spectral sequence of `p` the only `E₂`-entries of total degree
`r` are `(r,0)` and `(0,r)`, and the latter is `0` for `B` path connected.) -/
theorem fibrePairMapSurj (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Surjective (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ r).hom := by
  exact Work.Serre.B1Rel.fibrePairMapSurj_aux r N hr hrN hB p hp hvan hpc hgen b
    (fun β c => Work.Serre.B1Rel.relKronMapR_natural (p ⁻¹' {b}) ({b} : Set B) p
      (fun x hx => hx) r β c)

end Work.Serre
