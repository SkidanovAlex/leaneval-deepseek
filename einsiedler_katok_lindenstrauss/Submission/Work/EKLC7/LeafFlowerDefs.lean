import Mathlib
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.FlowerDefs

/-!
# `Work.EKLC7.LeafFlowerDefs` — the flower family for the leafwise-measure construction

Pisa 6.15: for every `n` there is a countable family of `(n,T)`-flowers whose bases cover
almost everything.  For the construction of leafwise measures (Pisa 6.19) one needs the
*uniform* form: countably many flowers whose radii are unbounded and whose bases cover a.e.,
so that at a.e. point `x` and for every prescribed radius `ρ` one has a flower whose atom at
`x` contains the plaque of radius `ρ` through `x`.

`Work.EKLC7.FlowerFam U μ` is exactly this datum.  It is the only geometric input of the
construction of leafwise measures performed in `Submission/Work/EKLC7/LeafNu*.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract
open Work.EKLComp

/-- **A family of flowers with unbounded radii.**  `E n` is the (measurable) base of the
`n`-th flower, `Z n` its domain, `m n` its σ-algebra (an `IsPlaqueAlgebra`), and `R n` the
radius of the plaque contained in the atoms at the base points (Pisa Definition 6.14).

The last field is the content of Pisa Corollary 6.15 in the uniform form used in the patching
step (6.19a): at almost every `x` and for every radius `ρ` there is a flower whose base
contains `x` and whose plaques have radius at least `ρ`. -/
structure FlowerFam (U : Subgroup SL3) (μ : Measure X3) where
  /-- the radii of the flowers -/
  R : ℕ → ℝ
  /-- the bases of the flowers -/
  E : ℕ → Set X3
  /-- the domains of the flowers -/
  Z : ℕ → Set X3
  /-- the σ-algebras of the flowers -/
  m : ℕ → MeasurableSpace X3
  /-- every radius is at least `1`, so that `Box1 U` is always inside the plaques -/
  one_le : ∀ n, 1 ≤ R n
  /-- the bases are Borel -/
  measE : ∀ n, MeasurableSet (E n)
  /-- each member of the family is a flower -/
  big : ∀ n, BigPlaqueOn U (R n) (E n) (Z n) (m n)
  /-- the bases cover a.e. for every radius -/
  cover : ∀ ρ : ℝ, 0 < ρ → ∀ᵐ x ∂μ, ∃ n, ρ ≤ R n ∧ x ∈ E n

/-- The assertion that a family of flowers with unbounded radii exists (as a `Prop`, so that it
can be the conclusion of a theorem). -/
abbrev FlowerFamP (U : Subgroup SL3) (μ : Measure X3) : Prop := Nonempty (FlowerFam U μ)

end Work.EKLC7
