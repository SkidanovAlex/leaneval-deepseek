import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.relComplex_empty_homology_iso

/-!
# The `Good` predicate for the empty open set

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W` (see `Work.Cohomology.pd_good`).  For `W = ∅` both clauses are vacuous in content but
genuinely discharged: the singular (co)chain complexes of the empty space have zero terms, hence
zero homology, and every compact subset of `∅` is `∅`.

This is the base case of the finite-union accumulation used in the assembly of the duality theorem
(`Good ∅ → Good (finite unions) → Good M`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Homology of a complex vanishing in one degree -/

/-- A chain complex whose `m`-th term is the zero object has vanishing `m`-th homology. -/
theorem isZero_homology_of_isZero_X {K : ChainComplex (ModuleCat ℤ) ℕ} (m : ℕ)
    (h : CategoryTheory.Limits.IsZero (K.X m)) :
    CategoryTheory.Limits.IsZero (K.homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- A cochain complex whose `m`-th term is the zero object has vanishing `m`-th homology. -/
theorem isZero_homology_of_isZero_X_cochain {K : CochainComplex (ModuleCat ℤ) ℕ} (m : ℕ)
    (h : CategoryTheory.Limits.IsZero (K.X m)) :
    CategoryTheory.Limits.IsZero (K.homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- **The singular homology of the empty space vanishes.** -/
theorem isZero_singularChains_homology_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (m : ℕ) :
    CategoryTheory.Limits.IsZero ((singularChains ℤ Y).homology m) :=
  isZero_homology_of_isZero_X m (isZero_singularChains_of_isEmpty Y m)

/-- **The relative cohomology of the pair `(∅, ∅)` vanishes.** -/
theorem isZero_relComplex_empty_homology (M : TopCat) (k : ℕ) :
    CategoryTheory.Limits.IsZero
      ((relComplex ℤ (TopCat.of (∅ : Set M))
        (pdRelSub (∅ : Set M) (∅ : Set M))).homology k) := by
  haveI hA : IsEmpty (↥(pdRelSub (∅ : Set M) (∅ : Set M))) := ⟨fun x => x.1.2⟩
  haveI hY : IsEmpty (↥(TopCat.of (∅ : Set M))) := ⟨fun x => x.2⟩
  haveI : IsIso (relIncl ℤ (TopCat.of (∅ : Set M))
      (pdRelSub (∅ : Set M) (∅ : Set M))) := isIso_relIncl_of_isEmpty _ _
  have h0 : CategoryTheory.Limits.IsZero
      ((singularCochainComplex ℤ (TopCat.of (∅ : Set M))).homology k) :=
    isZero_homology_of_isZero_X_cochain k (isZero_singularCochainComplex_of_isEmpty _ k)
  exact IsZero.of_iso h0 (asIso (HomologicalComplex.homologyMap (relIncl ℤ
    (TopCat.of (∅ : Set M)) (pdRelSub (∅ : Set M) (∅ : Set M))) k))

/-! ## `Good ∅` -/

/-- **The `Good` predicate holds for the empty open set.** -/
theorem good_empty {M : TopCat} [T2Space M] (N : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology N) :
    Work.Cohomology.Good N c (∅ : Set M) isOpen_empty := by
  intro k m hkm
  haveI hY : IsEmpty (↥(TopCat.of (∅ : Set M))) := ⟨fun x => x.2⟩
  constructor
  · intro y
    have hsub : Subsingleton ↥((singularChains ℤ (TopCat.of (∅ : Set M))).homology m) :=
      ModuleCat.subsingleton_of_isZero (isZero_singularChains_homology_of_isEmpty _ m)
    exact ⟨∅, Set.empty_subset _, isCompact_empty, 0, Subsingleton.elim _ _⟩
  · intro K hKW hKc x hx
    have hK : K = ∅ := by
      ext y
      constructor
      · intro hy
        exact absurd (hKW hy) (by simp)
      · intro hy
        exact absurd hy (by simp)
    subst hK
    have hsub : Subsingleton ↥((relComplex ℤ (TopCat.of (∅ : Set M))
        (pdRelSub (∅ : Set M) (∅ : Set M))).homology k) :=
      ModuleCat.subsingleton_of_isZero (isZero_relComplex_empty_homology M k)
    exact ⟨∅, Set.empty_subset _, Set.empty_subset _, isCompact_empty, Subsingleton.elim _ _⟩

end

end Work.Cohomology
