import Mathlib
import Submission.Work.Whitney.Cup
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Whitney.ConjTop
import Submission.Work.Whitney.nonempty_bundleIso_complexificationCore_realifiedCore
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# `p₁` of the underlying real bundle of a complex line bundle

Deliverable item 4 of area WHITNEY, last piece: for a complex **line** bundle `L` with underlying
real bundle `L_ℝ = Work.Whitney.realifiedCore L`,

  `p₁(L_ℝ) = c₁(L) ⌣ c₁(L)`.

The computation is the one announced in `README.md` (ADDENDUM W2.6):

  `p₁(L_ℝ) = - c₂(L_ℝ ⊗_ℝ ℂ) = - c₂(L ⊕ L̄) = - c₁(L) ⌣ c₁(L̄) = c₁(L) ⌣ c₁(L)`,

where the second equality is `Work.Whitney.nonempty_bundleIso_complexificationCore_realifiedCore`
(`E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē`, proved, axiom-clean), the third is the `(1,1)` instance of the top-degree
multiplicativity `Work.Whitney.chernClass_whitneySum_top` (`= Work.Whitney.TopClassMul`, proved),
and the last is the conjugation sign rule `Work.Whitney.chernClass_one_conjCore`
(`c₁(L̄) = -c₁(L)`).

Note the classical caveat recorded in the deliverable: `p₁` is the *integral* Pontryagin class, and
for a complex line bundle the identity `p₁(L_ℝ) = c₁(L)²` is an honest integral identity (no
2-torsion correction); the corresponding *additivity* `p₁(E⊕F) = p₁E + p₁F` for real bundles holds
only modulo 2-torsion, see `README.md` ADDENDUM W3.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Bilinearity of the graded cup product (API) -/

/-- **The graded cup product is additive in its second argument.** -/
theorem cupChern_add_right (a b : ℕ) (x : Coh ℤ (2 * a) B) (y y' : Coh ℤ (2 * b) B) :
    cupChern a b x (y + y') = cupChern a b x y + cupChern a b x y' := by
  rw [cupChern_def, cupChern_def, cupChern_def]
  rw [Work.Cohomology.cupH'_add_right]
  exact (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm).map_add _ _

/-- **The graded cup product is odd in its second argument.** -/
theorem cupChern_neg_right (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    cupChern a b x (-y) = - cupChern a b x y := by
  rw [cupChern_def, cupChern_def]
  have h1 : Work.Cohomology.cupH' ℤ (ssB B) (2 * a) (2 * b) x (-y)
      = - (Work.Cohomology.cupH' ℤ (ssB B) (2 * a) (2 * b) x y) :=
    map_neg (Work.Cohomology.cupH' ℤ (ssB B) (2 * a) (2 * b) x) y
  rw [h1]
  exact (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm).map_neg _

/-! ## The Pontryagin class of the underlying real bundle of a complex line bundle -/

/-- **`p₁` of the underlying real bundle of a complex line bundle**: `p₁(L_ℝ) = c₁(L) ⌣ c₁(L)`.

The underlying real bundle is `Work.Whitney.realifiedCore L`, whose fibre is `ℝ²`. -/
theorem pontryagin1_realifiedLine {ι : Type} [Fintype ι]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.pontryagin1 (realifiedCore L)
      = cupChern 1 1 (Work.Thom.chernClass 1 1 L) (Work.Thom.chernClass 1 1 L) := by
  rw [Work.Thom.pontryagin1_def]
  obtain ⟨e⟩ := nonempty_bundleIso_complexificationCore_realifiedCore L
  rw [Work.Thom.chernClass_BundleIso _ _ e]
  rw [Work.Whitney.chernClass_whitneySum_top L (conjCore L)]
  rw [chernClass_one_conjCore L]
  rw [cupChern_neg_right]
  simp

end

end Work.Whitney
