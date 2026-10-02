import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.SectionStability
import Submission.Work.Whitney.exists_bundleIso_comap_tautQuotient_whitneySum
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Stability of the Chern classes of a Whitney sum along a nowhere-zero section

Let `A` be a complex gluing-data bundle of rank `r+1` over `Y` (in the standard fibre
`EuclideanSpace ℂ (Fin (r+1))`), let `B` be a complex gluing-data bundle of rank `s+1`, and let
`σ : Y → ↥(zeroComplement (realification A))` be a continuous nowhere-zero section of `A`.  Then

  `c_k(A ⊕ B) = c_k(σ^*(Q_A) ⊕ B)`   for all `k`,

where `Q_A = Work.Thom.tautQuotient A` is the tautological quotient of `A` over its punctured total
space.  The proof is

* `c_k(A ⊕ B) = c_k(τ^*(Q_{A ⊕ B}))` for the nowhere-zero section `τ = (σ, 0)` of `A ⊕ B`
  (`Work.Whitney.chernClass_eq_of_nowhereZeroSection`), and then
* `τ^*(Q_{A ⊕ B}) ≅ σ^*(Q_A) ⊕ B`
  (`Work.Whitney.exists_bundleIso_comap_tautQuotient_whitneySum`), an isomorphism of bundles over
  `Y` whose fibre map is the canonical identification
  `(A_y ⊕ B_y)/ℂ·(σ_y,0) ≅ (A_y/ℂ·σ_y) ⊕ B_y`.

The two bundles live in slightly different (but propositionally equal) ranks `(r+1)+s` and
`r+(s+1)`, which is what `chernClass_BundleIso_of_eq` takes care of.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## Isomorphism-invariance of the Chern classes across equal (but syntactically different) ranks

`Work.Thom.chernClass m j Z` requires the model fibre to be *syntactically* `EuclideanSpace ℂ (Fin m)`,
so two bundles whose ranks are equal only propositionally cannot be compared by
`Work.Thom.chernClass_BundleIso` directly.  The following lemma removes that obstruction. -/

/-- **Isomorphism-invariance of `Work.Thom.chernClass` across propositionally equal ranks**: if
`m = m'` and `Z`, `Z'` are isomorphic complex bundles in the standard fibres `ℂ^m`, `ℂ^{m'}` over
`Y`, then their `k`-th Chern classes agree. -/
theorem chernClass_BundleIso_of_eq {m m' : ℕ} (h : m = m') {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin m')) ι')
    (e : BundleIso Z Z') (k : ℕ) :
    Work.Thom.chernClass m k Z = Work.Thom.chernClass m' k Z' := by
  subst h
  exact Work.Thom.chernClass_BundleIso Z Z' e

/-! ## The stability lemma -/

theorem chernClass_whitneySum_stability {Y : Type} [TopologicalSpace Y]
    {ι_A ι_B : Type} [Fintype ι_A] [Fintype ι_B] {r s : ℕ}
    (A : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (r + 1))) ι_A)
    (B : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (s + 1))) ι_B)
    (σ : C(Y, ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hσ : ∀ y, (((σ y : ↥(Work.Thom.zeroComplement (Work.Thom.realification A))) :
      (Work.Thom.realification A).TotalSpace)).1 = y) (k : ℕ) :
    Work.Thom.chernClass ((r + 1) + (s + 1)) k (Work.Whitney.whitneySum A B)
      = Work.Thom.chernClass (r + (s + 1)) k
          (Work.Whitney.whitneySum (Work.Thom.bundleComap (Work.Thom.tautQuotient A) σ) B) := by
  obtain ⟨sB, hsB, ⟨e⟩⟩ :=
    exists_bundleIso_comap_tautQuotient_whitneySum (A := A) (B := B) (σ := σ) hσ
  have h1 := chernClass_eq_of_nowhereZeroSection (m := (r + 1) + s)
    (Z := whitneySum (m₁ := r + 1) (m₂ := s + 1) A B) sB hsB k
  have h2 := chernClass_BundleIso_of_eq (m := (r + 1) + s) (m' := r + (s + 1))
    (by omega)
    (bundleComap (tautQuotient (m := (r + 1) + s)
      (whitneySum (m₁ := r + 1) (m₂ := s + 1) A B)) sB)
    (whitneySum (m₁ := r) (m₂ := s + 1)
      (bundleComap (tautQuotient (m := r) A) σ) B) e k
  exact h1.trans h2

end

end Work.Whitney
