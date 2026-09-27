import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.ProdPlaqueDefs

/-!
# Product-box flowers (C5b, the geometric input of the product structure)

The tower identity `Work.EKLProd.slicing_identity_gen` (Pisa Lemma 8.10) needs a pair of plaque
algebras `(Z, mH)`, `(Z, mT)` with `mH ≤ mT` and — this is the point — **fibre-independent
shapes**.  With a *ball* plaque (`EKLComp.orbitPlaque`) the `T`-shape at a point of the plaque is
a cut of the ball and depends on the fibre; with the **product box**
`prodBox T U R = (V R ∩ T) * (V R ∩ U)` of this development the shapes of the two refinements
`mT`, `mU` are *translates of the fixed balls* `V R ∩ T`, `V R ∩ U`, which is exactly what makes
the substitution of step 3 produce a fibre-independent answer (see
`EKLComp/ProductPlan.md` §8.4 and §9).

This module fixes the vocabulary.  `Work.EKLProd.ProdFlowerFam H T U μ` is the datum needed for
the tower-based derivation of `P_Product` from `H = T·U`: countably many product-box flowers of
positive `μ`-measure whose (measurable) bases cover `μ`-almost everything, together with the two
strip algebras of each.  Its existence is the *geometric* input; it is to be built from the
cross-section of `EKLRelCross.pisa_crosssection` in the same way as the ball-plaque flower family
`E.KLComp.flowers_exist` / `EKLC7.FlowerFamExists` (the only change: collars are boxes `B_T B_U·c`
instead of balls `B_H·c`, and the σ-algebra is the join of the box-collars with the pullbacks of
the `T`-part and `U`-part maps).

`co n : X₃ → SL₃` is the *plaque coordinate* of the `n`-th flower (it is indexed by the flower:
different flowers have different transversals, and a flower-independent coordinate would force the
atoms of different flowers to coincide, which is impossible for a mixing flow): for `x ∈ Z n` lying in the atom of the transversal point
`c` it is the unique `g ∈ prodBox T U R` with `x = g • c`.  The fields are:

* `co_mem`, `co_smul`: `co` takes values in the product box, and inside an atom it is
  multiplicative (`co (h • x) = h * co x` for `h` in the `H`-shape at `x`);
* `shapeH`, `shapeT`, `shapeU`: the shapes of the three plaque algebras are the sets of group
  elements mapping `co x` into the product box;
* `meas_co`, `meas_tp`, `meas_up`: the measurability of `co` and of its `T`-part and `U`-part
  (the last two are the `Borel`-measurability of `hT`, `hU` composed with `co`, used to build the
  Borel test functions `1_A ∘ tpart ∘ co`, `1_B ∘ upart ∘ co` of the tower identity).
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- **A family of product-box flowers** for the product structure `H = T·U`.  See the module
docstring for the meaning of the fields. -/
structure ProdFlowerFam (H T U : Subgroup SL3) (μ : Measure X3) where
  /-- side length of the product box `(V R ∩ T) * (V R ∩ U)` -/
  R : ℝ
  /-- the box contains `Box1 T` and `Box1 U`, so the normalising sets are inside the shapes -/
  one_le_R : 1 ≤ R
  /-- domains of the flowers -/
  Z : ℕ → Set X3
  /-- bases of the flowers -/
  G : ℕ → Set X3
  /-- the `H`-plaque algebra of the `n`-th flower -/
  mH : ℕ → MeasurableSpace X3
  /-- the `T`-strip algebra of the `n`-th flower -/
  mT : ℕ → MeasurableSpace X3
  /-- the `U`-strip algebra of the `n`-th flower -/
  mU : ℕ → MeasurableSpace X3
  /-- the plaque coordinate of the `n`-th flower (in `prodBox T U R`, relative to the base point
  of the atom): indexed by the flower, since different flowers have different transversals -/
  co : ℕ → X3 → SL3
  measG : ∀ n, MeasurableSet (G n)
  GZ : ∀ n, G n ⊆ Z n
  Zpos : ∀ n, μ (Z n) ≠ 0
  cover : μ (⋃ n, G n)ᶜ = 0
  plaqH : ∀ n, IsPlaqueAlgebra H (Z n) (mH n)
  plaqT : ∀ n, IsPlaqueAlgebra T (Z n) (mT n)
  plaqU : ∀ n, IsPlaqueAlgebra U (Z n) (mU n)
  alignT : ∀ n, mH n ≤ mT n
  alignU : ∀ n, mH n ≤ mU n
  meas_co : ∀ n, Measurable (co n)
  co_mem : ∀ n, ∀ x ∈ Z n, co n x ∈ prodBox T U R
  /-- the atoms of a product-box flower have free `H`-orbits -/
  freeZ : ∀ n, ∀ x ∈ Z n, ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • x = h₂ • x → h₁ = h₂
  /-- the coordinate is multiplicative inside an atom -/
  co_smul : ∀ n, ∀ x ∈ Z n, ∀ h ∈ H, h • x ∈ atom (mH n) x → co n (h • x) = h * co n x
  /-- the shape of the `H`-plaque algebra is a translate of the product box -/
  shapeH : ∀ n, ∀ x ∈ Z n,
    shape (mH n) H x = {g : SL3 | g ∈ H ∧ g * co n x ∈ prodBox T U R}
  /-- the shape of the `T`-strip algebra is a translate of the `T`-ball -/
  shapeT : ∀ n, ∀ x ∈ Z n,
    shape (mT n) T x = {g : SL3 | g ∈ T ∧ g * co n x ∈ prodBox T U R}
  /-- the shape of the `U`-strip algebra is a translate (conjugate) of the `U`-ball -/
  shapeU : ∀ n, ∀ x ∈ Z n,
    shape (mU n) U x = {g : SL3 | g ∈ U ∧ g * co n x ∈ prodBox T U R}
  /-- the measurable `T`-part of the coordinate -/
  meas_tp : ∀ n, Measurable (fun x : X3 => hT T U (co n x))
  /-- the measurable `U`-part of the coordinate -/
  meas_up : ∀ n, Measurable (fun x : X3 => hU T U (co n x))

end Work.EKLProd
