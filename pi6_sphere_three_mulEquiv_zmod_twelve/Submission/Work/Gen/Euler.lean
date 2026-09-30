import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.TangentClasses.Tangent
import Submission.Work.Thom.manifoldP1

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — the two bundles of the Euler sequence of `ℂPⁿ`, over the standard chart cover

`Work.Gen.stdTangentC n` is the **complexified tangent bundle of `ℂPⁿ`** presented over the
standard `(n+1)`-chart cover (`Work.Projective.euclidChart n i`), with the standard complex fibre
`ℂ^{2n}`; `Work.Gen.eulerTarget n` is the **(n+1)-fold sum of `ℂ ⊗_ℝ O(1)`**, written out as
explicit gluing data with the *diagonal* transition functions `diag(z_i/z_j, …, z_j/z_i, …)` — this
is what the Euler sequence `(ℂ ⊗_ℝ TℂPⁿ) ⊕ ε² ≅ (n+1)·(ℂ ⊗_ℝ O(1))` identifies the tangent bundle
with, and it is the form in which its total Chern class `(1 − u²)^{n+1}` (with `u = c₁(O(1))`) can
be read off.

For `n = 4` these are the two bundles whose comparison gives `p₁(TℂP⁴) = 5u²`, `p₂ = 10u⁴`.
-/

open Work.Projective

open scoped Manifold ContDiff

namespace Work.Gen

noncomputable section

/-- The standard `(n+1)`-chart cover of `ℂPⁿ`, as a family of charts of the Euclidean atlas. -/
def stdChart (n : ℕ) (i : Fin (n + 1)) :
    atlas (EuclideanSpace ℝ (Fin (2 * n))) (CP n) :=
  ⟨euclidChart n i, euclidChart_mem_atlas i⟩

theorem stdChart_source (n : ℕ) (i : Fin (n + 1)) : (stdChart n i).1.source = chartSet i := by
  show (euclidChart n i).source = chartSet i
  rw [euclidChart, OpenPartialHomeomorph.trans_source]
  ext x
  constructor
  · intro h
    exact h.1
  · intro hx
    exact ⟨hx, Set.mem_univ _⟩

theorem stdChart_covers (n : ℕ) : ∀ x : CP n, ∃ i, x ∈ (stdChart n i).1.source :=
  fun x => by
    obtain ⟨i, hi⟩ := exists_mem_chartSet x
    exact ⟨i, by rw [stdChart_source]; exact hi⟩

/-- **The complexified tangent bundle of `ℂPⁿ` over the standard chart cover**: the tangent bundle
of the Euclidean charted space `ℂPⁿ` (whose model space is already the standard Euclidean one, so
no change of fibre is needed), restricted to the `(n+1)` standard charts, then complexified. -/
def stdTangentC (n : ℕ) :
    VectorBundleCore ℂ (CP n) (EuclideanSpace ℂ (Fin (2 * n))) (Fin (n + 1)) :=
  Work.Thom.complexificationCore
    ((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (CP n)).reindex
      (stdChart n) (stdChart_covers n))

/-- The **hyperplane class** `u = c₁(O(1)) ∈ H²(ℂPⁿ;ℤ)` of the projective space, in the
normalisation of the tautological dual line bundle `Work.Gen.tautDual n`. -/
def uCoh (n : ℕ) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (CP n)))).homology 2 :=
  Work.Thom.chernClass 1 1 (tautDual n)

/-- `u ⌣ u ∈ H⁴(ℂPⁿ;ℤ)`, the square of the hyperplane class. -/
def uSq (n : ℕ) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (CP n)))).homology 4 :=
  Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (CP n))) 2 2 (uCoh n) (uCoh n)

/-- `u⁴ = (u ⌣ u) ⌣ (u ⌣ u) ∈ H⁸(ℂPⁿ;ℤ)`. -/
def uFourth (n : ℕ) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (CP n)))).homology 8 :=
  Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (CP n))) 4 4 (uSq n) (uSq n)

end

end Work.Gen
