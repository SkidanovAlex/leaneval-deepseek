import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_sumEps_whitneySum
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Thom.realSumStable
import Submission.Work.Thom.sumStableCorollaries
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# Stability of the Chern and Pontryagin classes for the direct sum

The *stability* theorem of the Thom chapter (`Work.Thom.chernClass_sumEps`, ADDENDUM 24) says
`c_j(Z ⊕ ε¹) = c_j(Z)`.  This module transfers it to the direct sum
`Work.Whitney.whitneySum` of this subproject (which is the same bundle in the same standard fibre,
but glued along the *explicit* splitting `Work.Whitney.sumFibreC` instead of the
`Classical.choice`-based `Work.Thom.prodFinEquiv`):

* `Work.Whitney.sumEpsR_eq_whitneySumR` — the *real* presentations coincide on the nose, because
  `Work.Thom.rhoR k` **is** `Work.Whitney.sumFibreR k 1` (`rfl`); this gives the isomorphism
  `Work.Whitney.nonempty_bundleIso_sumEpsR_whitneySumR` needed by deliverable item 1;
* `Work.Whitney.nonempty_bundleIso_sumEpsR_whitneySumR` — the two presentations of `Z ⊕ ε¹` for a
  real bundle `Z` are isomorphic;
* **`Work.Whitney.chernClass_whitneySum_trivial`** — `c_j(Z ⊕ ε¹) = c_j(Z)` for the complex direct
  sum `Work.Whitney.whitneySum` (the trivial-summand case of the Whitney formula);
* **`Work.Whitney.chernClass_complexification_whitneySumR_trivial`** and
  **`Work.Whitney.pontryagin1_whitneySumR_trivial`** — the same for the *complexification* of a real
  direct sum, and for the first Pontryagin class in the Milnor–Stasheff normalisation
  `Work.Thom.pontryagin1` (deliverable item 3, the trivial-summand case).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type} [Inhabited ι₀]

/-! ## The two real presentations coincide -/

/-- **The two real presentations of `Z ⊕ ε¹` are the same gluing data**, because the splittings
`Work.Thom.rhoR k` and `Work.Whitney.sumFibreR k 1` are the same term of Mathlib
(`EuclideanSpace.finAddEquivProd … |>.symm`). -/
theorem sumEpsR_eq_whitneySumR {k : ℕ}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) :
    Work.Thom.sumEpsR ι₀ Z
      = whitneySumR Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀) := by
  refine Work.Thom.bundleCore_ext ?_ ?_ (fun i j x => ?_)
  · funext p
    rw [Work.Thom.sumEpsR_baseSet, whitneySumR_baseSet, Work.Thom.bundleSum_baseSet]
  · funext x
    rw [Work.Thom.sumEpsR_indexAt, whitneySumR_indexAt, Work.Thom.bundleSum_indexAt]
  · rw [Work.Thom.sumEpsR_coordChange, whitneySumR_coordChange,
      Work.Thom.bundleSum_trivial_coordChange]
    rfl

/-- **The two real presentations of `Z ⊕ ε¹` are isomorphic** (an instance of
`Work.Whitney.sumEpsR_eq_whitneySumR`). -/
theorem nonempty_bundleIso_sumEpsR_whitneySumR {k : ℕ}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) :
    Nonempty (BundleIso (Work.Thom.sumEpsR ι₀ Z)
      (whitneySumR Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀))) :=
  ⟨(sumEpsR_eq_whitneySumR (ι₀ := ι₀) Z) ▸ BundleIso.refl _⟩

/-! ## Stability for the complex direct sum -/

/-- **Stability of the Chern classes for the complex direct sum**:
`c_j(Z ⊕ ε¹) = c_j(Z)`.  This is the trivial-summand case of the Whitney formula, transferred from
`Work.Thom.chernClass_sumEps` along the isomorphism
`Work.Whitney.nonempty_bundleIso_sumEps_whitneySum`. -/
theorem chernClass_whitneySum_trivial [Fintype ι] [Fintype ι₀] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    Work.Thom.chernClass (m + 1) j
        (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))
      = Work.Thom.chernClass m j Z := by
  obtain ⟨e⟩ := nonempty_bundleIso_sumEps_whitneySum (ι₀ := ι₀) Z
  exact Work.Thom.chernClass_eq_of_bundleIso_sumEps Z _ e.symm j

/-- **Stability for the complexification of a real direct sum**:
`c_j((Z ⊕ ε¹) ⊗_ℝ ℂ) = c_j(Z ⊗_ℝ ℂ)`. -/
theorem chernClass_complexification_whitneySumR_trivial [Fintype ι] [Fintype ι₀] {k : ℕ}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) (j : ℕ) :
    Work.Thom.chernClass (k + 1) j
        (Work.Thom.complexificationCore
          (whitneySumR Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)))
      = Work.Thom.chernClass k j (Work.Thom.complexificationCore Z) := by
  have h := sumEpsR_eq_whitneySumR (ι₀ := ι₀) Z
  rw [← h]
  exact Work.Thom.chernClass_complexification_sumEpsR ι₀ Z _ (BundleIso.refl _) j

/-- **Stability of the first Pontryagin class for the real direct sum**:
`p₁(Z ⊕ ε¹) = p₁(Z)` in the Milnor–Stasheff normalisation
`Work.Thom.pontryagin1 = -c₂(· ⊗_ℝ ℂ)` (deliverable item 3, trivial-summand case). -/
theorem pontryagin1_whitneySumR_trivial [Fintype ι] [Fintype ι₀] {k : ℕ}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) :
    Work.Thom.pontryagin1
        (whitneySumR Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀))
      = Work.Thom.pontryagin1 Z := by
  have h := sumEpsR_eq_whitneySumR (ι₀ := ι₀) Z
  rw [← h]
  exact Work.Thom.pontryagin1_sumEpsR ι₀ Z _ (BundleIso.refl _)

end

end Work.Whitney
