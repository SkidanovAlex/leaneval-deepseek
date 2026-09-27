import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.relChains_diagonal_injective

/-!
# The Mayer–Vietoris step: `GoodC` is closed under unions

This file proves `Work.Compact.Noncompact.goodC_union`:

`GoodC k A → GoodC k B → GoodV k (A ∩ B) → GoodC k (A ∪ B)`.

The two ingredients are

* the injectivity of the relative Mayer–Vietoris diagonal
  `H_{k+1}(X, (A ∪ B)ᶜ) → H_{k+1}(X, Aᶜ) ⊕ H_{k+1}(X, Bᶜ)`
  (`Work.Compact.Noncompact.relChains_diagonal_injective`, applied to the open cover
  `U = Aᶜ`, `V = Bᶜ`, so that `U ∩ V = (A ∪ B)ᶜ` and `U ∪ V = (A ∩ B)ᶜ`), and
* the uniqueness/vanishing clauses of `GoodC` for the two pieces, together with the vanishing
  hypothesis `GoodV k (A ∩ B)` in degree `k+2`.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {X : TopCat}

/-- Composition of the `relMapHom`s, expressed on elements. -/
lemma goodC_union_relMapHom_apply_comp {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) (n : ℕ)
    (x : (RC X A).homology n) :
    relMapHom (X := X) h₂ n (relMapHom (X := X) h₁ n x)
      = relMapHom (X := X) (h₁.trans h₂) n x := by
  rw [← ModuleCat.comp_apply, relMapHom_comp]

/-- `IsZero` of the relative homology transports across an equality of the sets. -/
lemma goodC_union_isZero_relChains_homology_of_eq {A B : Set X} (h : A = B) (n : ℕ)
    (h0 : IsZero ((Work.Cohomology.relChains X A).homology n)) :
    IsZero ((Work.Cohomology.relChains X B).homology n) := by
  rw [h] at h0
  exact h0

/-- **Injectivity of the relative Mayer–Vietoris diagonal at the level of the `hatH`-notation.**
Let `A, B ⊆ X` have open complements.  If `H_{k+2}(X, Aᶜ ∪ Bᶜ) = 0`, then a class in
`H_{k+1}(X, (A ∪ B)ᶜ)` which restricts to `0` in both `H_{k+1}(X, Aᶜ)` and `H_{k+1}(X, Bᶜ)` is
zero itself.

The relative Mayer–Vietoris sequence of the open cover `{Aᶜ, Bᶜ}` involves `Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ`
and `Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ`; the proof transports
`Work.Compact.Noncompact.relChains_diagonal_injective` (stated with `U ∩ V` and `U ∪ V` for
arbitrary open `U, V`) along the two set identities `Set.compl_union` and the functoriality of
`relMapHom` in the set. -/
lemma goodC_union_diag_injective {M : Type} [TopologicalSpace M] (A B : Set M) (k : ℕ)
    (hU : IsOpen (Aᶜ)) (hV : IsOpen (Bᶜ))
    (h0 : IsZero ((Work.Cohomology.relChains (TopCat.of M) (Aᶜ ∪ Bᶜ)).homology (k + 2))) :
    Function.Injective (fun u : (RC (TopCat.of M) ((A ∪ B)ᶜ)).homology (k + 1) =>
      (relMapHom (X := TopCat.of M)
          (Set.compl_subset_compl.mpr (Set.subset_union_left : A ⊆ A ∪ B)) (k + 1) u,
       relMapHom (X := TopCat.of M)
          (Set.compl_subset_compl.mpr (Set.subset_union_right : B ⊆ A ∪ B)) (k + 1) u)) := by
  have hdiag := relChains_diagonal_injective (X := TopCat.of M) Aᶜ Bᶜ hU hV k h0
  intro u v huv
  have hfst := congrArg Prod.fst huv
  have hsnd := congrArg Prod.snd huv
  have hl : (relMapHom (X := TopCat.of M) (Set.inter_subset_left : Aᶜ ∩ Bᶜ ⊆ Aᶜ) (k + 1))
        (relMapHom (X := TopCat.of M) (Set.compl_union A B).le (k + 1) u)
      = (relMapHom (X := TopCat.of M) (Set.inter_subset_left : Aᶜ ∩ Bᶜ ⊆ Aᶜ) (k + 1))
        (relMapHom (X := TopCat.of M) (Set.compl_union A B).le (k + 1) v) := by
    rw [goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
          (Set.inter_subset_left : Aᶜ ∩ Bᶜ ⊆ Aᶜ) (k + 1) u,
      goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
          (Set.inter_subset_left : Aᶜ ∩ Bᶜ ⊆ Aᶜ) (k + 1) v,
      relMapHom_eq_of_subset_eq ((Set.compl_union A B).le.trans Set.inter_subset_left)
        (Set.compl_subset_compl.mpr (Set.subset_union_left : A ⊆ A ∪ B))]
    exact hfst
  have hr : (relMapHom (X := TopCat.of M) (Set.inter_subset_right : Aᶜ ∩ Bᶜ ⊆ Bᶜ) (k + 1))
        (relMapHom (X := TopCat.of M) (Set.compl_union A B).le (k + 1) u)
      = (relMapHom (X := TopCat.of M) (Set.inter_subset_right : Aᶜ ∩ Bᶜ ⊆ Bᶜ) (k + 1))
        (relMapHom (X := TopCat.of M) (Set.compl_union A B).le (k + 1) v) := by
    rw [goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
          (Set.inter_subset_right : Aᶜ ∩ Bᶜ ⊆ Bᶜ) (k + 1) u,
      goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
          (Set.inter_subset_right : Aᶜ ∩ Bᶜ ⊆ Bᶜ) (k + 1) v,
      relMapHom_eq_of_subset_eq ((Set.compl_union A B).le.trans Set.inter_subset_right)
        (Set.compl_subset_compl.mpr (Set.subset_union_right : B ⊆ A ∪ B))]
    exact hsnd
  have hdiag' := hdiag (Prod.ext hl hr)
  have h2 := congrArg (relMapHom (X := TopCat.of M) (Set.compl_union A B).ge (k + 1)) hdiag'
  rw [goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
        (Set.compl_union A B).ge (k + 1) u,
    goodC_union_relMapHom_apply_comp (Set.compl_union A B).le
        (Set.compl_union A B).ge (k + 1) v,
    relMapHom_eq_of_subset_eq ((Set.compl_union A B).le.trans (Set.compl_union A B).ge)
      (subset_refl _),
    relMapHom_rfl] at h2
  simpa using h2

theorem goodC_union {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] (A B : Set M)
    (hA : GoodC k (TopCat.of M) A) (hB : GoodC k (TopCat.of M) B)
    (hAB : GoodV k (TopCat.of M) (A ∩ B)) : GoodC k (TopCat.of M) (A ∪ B) := by
  have hU : IsOpen (Aᶜ) := hA.1.isClosed.isOpen_compl
  have hV : IsOpen (Bᶜ) := hB.1.isClosed.isOpen_compl
  -- The vanishing of `H_{k+2}(X, Aᶜ ∪ Bᶜ) = H_{k+2}(X, (A ∩ B)ᶜ)`, obtained from `GoodV (A ∩ B)`.
  have hvan : ∀ n : ℕ, k + 1 < n →
      IsZero ((Work.Cohomology.relChains (TopCat.of M) (Aᶜ ∪ Bᶜ)).homology n) := by
    intro n hn
    have h0 : IsZero ((Work.Cohomology.relChains (TopCat.of M) ((A ∩ B)ᶜ)).homology n) :=
      hAB.2 n hn
    exact goodC_union_isZero_relChains_homology_of_eq (Set.compl_inter A B) n h0
  refine ⟨hA.1.union hB.1, ?_, ?_⟩
  · -- Uniqueness: a class of `H_{k+1}(X, (A ∪ B)ᶜ)` with trivial localizations on `A ∪ B` dies.
    intro u hu
    have hAl : (A ∪ B)ᶜ ⊆ Aᶜ := Set.compl_subset_compl.mpr (Set.subset_union_left : A ⊆ A ∪ B)
    have hBl : (A ∪ B)ᶜ ⊆ Bᶜ := Set.compl_subset_compl.mpr (Set.subset_union_right : B ⊆ A ∪ B)
    -- Restriction to `A` of `u` has trivial localizations, so it vanishes by `GoodC A`.
    have hzu : relMapHom (X := TopCat.of M) hAl (k + 1) u = 0 := by
      apply hA.2.1
      intro x hx
      have hcomp := goodC_union_relMapHom_apply_comp (X := TopCat.of M) hAl
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) (k + 1) u
      rw [hcomp, relMapHom_eq_of_subset_eq
        (hAl.trans (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)))
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (Set.mem_union_left B hx)))]
      exact hu x (Set.mem_union_left B hx)
    have hzv : relMapHom (X := TopCat.of M) hBl (k + 1) u = 0 := by
      apply hB.2.1
      intro x hx
      have hcomp := goodC_union_relMapHom_apply_comp (X := TopCat.of M) hBl
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) (k + 1) u
      rw [hcomp, relMapHom_eq_of_subset_eq
        (hBl.trans (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)))
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (Set.mem_union_right A hx)))]
      exact hu x (Set.mem_union_right A hx)
    exact goodC_union_diag_injective A B k hU hV (hvan (k + 2) (by omega))
      (by simp [hzu, hzv])
  · -- Vanishing in degrees `> k+1`, by injectivity of the diagonal into a zero target.
    intro j hj
    have hdj : (j - 1) + 1 = j := by omega
    have h0 : IsZero
        ((Work.Cohomology.relChains (TopCat.of M) (Aᶜ ∪ Bᶜ)).homology ((j - 1) + 2)) := by
      rw [show (j - 1) + 2 = j + 1 by omega]
      exact hvan (j + 1) (by omega)
    have hinj := goodC_union_diag_injective A B (j - 1) hU hV h0
    haveI hSA : Subsingleton ((RC (TopCat.of M) (Aᶜ)).homology ((j - 1) + 1)) := by
      rw [hdj]
      exact (ModuleCat.isZero_iff_subsingleton).1 (hA.2.2 j hj)
    haveI hSB : Subsingleton ((RC (TopCat.of M) (Bᶜ)).homology ((j - 1) + 1)) := by
      rw [hdj]
      exact (ModuleCat.isZero_iff_subsingleton).1 (hB.2.2 j hj)
    haveI : Subsingleton ((RC (TopCat.of M) ((A ∪ B)ᶜ)).homology ((j - 1) + 1)) :=
      Function.Injective.subsingleton hinj
    exact (ModuleCat.isZero_iff_subsingleton).2 (by rw [← hdj]; infer_instance)

end

end Work.Compact.Noncompact
