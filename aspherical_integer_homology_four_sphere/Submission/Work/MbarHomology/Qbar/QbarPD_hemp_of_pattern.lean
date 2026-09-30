import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Qbar

open Work.MbarHomology
open scoped BigOperators

/-- Farkas translation: the "tight + own constraint" combination of `empMu` at the pair `(f, i)`
evaluated on any test function `X` collapses, because `empMu f i` is supported on the two
constraints `empC1 f i`, `empC2 f i`, and each of them lies either in `qTight f` or equals `i`
(they are distinct, and `i ∉ qTight f`). -/
theorem empMu_sum_translate (f : Fin 865) (i : Fin 48) (X : Fin 48 → ℤ)
    (hi : i ∉ qTight f)
    (hne : empC1 f i ≠ empC2 f i)
    (hsub : ({empC1 f i, empC2 f i} : Finset (Fin 48)) ⊆ qTight f ∪ {i}) :
    (∑ k ∈ qTight f, empMu f i k * X k) + empMuI f i * X i
      = empMuA f i * X (empC1 f i) + empMuB f i * X (empC2 f i) := by
  have hg : ∀ k : Fin 48, empMu f i k * X k =
      (if k = empC1 f i then empMuA f i * X (empC1 f i) else 0)
        + (if k = empC2 f i then empMuB f i * X (empC2 f i) else 0) := by
    intro k; simp only [empMu]; split_ifs with h1 h2 <;> simp_all
  have hd : empC1 f i ∈ qTight f ∪ {i} := hsub (by simp)
  have he : empC2 f i ∈ qTight f ∪ {i} := hsub (by simp)
  have hdisj : Disjoint (qTight f) {i} := by
    rw [Finset.disjoint_singleton_right]; exact hi
  have hunion : ∑ k ∈ qTight f ∪ {i}, empMu f i k * X k
      = (∑ k ∈ qTight f, empMu f i k * X k) + empMuI f i * X i := by
    rw [Finset.sum_union hdisj, Finset.sum_singleton]
    rfl
  rw [← hunion, Finset.sum_congr rfl (fun k _ => hg k), Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [hd, he, ↓reduceIte]

theorem QbarPD_hemp_of_pattern
    (hpat : ∀ p : Fin 888,
      (∀ t : Fin 3, 0 ≤ Work.MbarHomology.lamValOf (p : ℕ) t) ∧
      (∀ j' : Fin 4,
        Work.MbarHomology.certMu1 (p : ℕ) * Work.MbarHomology.qNrm (Work.MbarHomology.certC1 (p : ℕ)) j'
          + Work.MbarHomology.certMu2 (p : ℕ) * Work.MbarHomology.qNrm (Work.MbarHomology.certC2 (p : ℕ)) j'
        = ∑ t : Fin 3, Work.MbarHomology.lamValOf (p : ℕ) t
            * Work.MbarHomology.qNrm (Work.MbarHomology.lamIdxOf (p : ℕ) t) j') ∧
      (0 < Work.MbarHomology.certMu1 (p : ℕ) * Work.MbarHomology.qRhs (Work.MbarHomology.certC1 (p : ℕ))
          + Work.MbarHomology.certMu2 (p : ℕ) * Work.MbarHomology.qRhs (Work.MbarHomology.certC2 (p : ℕ))
          - ∑ t : Fin 3, Work.MbarHomology.lamValOf (p : ℕ) t
              * Work.MbarHomology.qRhs (Work.MbarHomology.lamIdxOf (p : ℕ) t)))
    (hsup : ∀ (f : Fin 865) (i : Fin 48), Work.MbarHomology.empSelB f i = true →
      Work.MbarHomology.empPat f i < 888 ∧ i ∉ Work.MbarHomology.qTight f ∧
      Work.MbarHomology.empC1 f i ≠ Work.MbarHomology.empC2 f i ∧
      ({Work.MbarHomology.empC1 f i, Work.MbarHomology.empC2 f i} : Finset (Fin 48)) ⊆
        Work.MbarHomology.qTight f ∪ {i}) :
    ∀ (f : Fin 865) (i : Fin 48), Work.MbarHomology.empSelB f i = true →
      (∀ t : Fin 3, 0 ≤ Work.MbarHomology.empLamVal f i t) ∧
      (∀ j' : Fin 4,
        (∑ k ∈ Work.MbarHomology.qTight f, Work.MbarHomology.empMu f i k * Work.MbarHomology.qNrm k j')
            + Work.MbarHomology.empMuI f i * Work.MbarHomology.qNrm i j'
          = ∑ t : Fin 3, Work.MbarHomology.empLamVal f i t
              * Work.MbarHomology.qNrm (Work.MbarHomology.empLamIdx f i t) j') ∧
      (0 < (∑ k ∈ Work.MbarHomology.qTight f, Work.MbarHomology.empMu f i k * Work.MbarHomology.qRhs k)
          + Work.MbarHomology.empMuI f i * Work.MbarHomology.qRhs i
          - ∑ t : Fin 3, Work.MbarHomology.empLamVal f i t
              * Work.MbarHomology.qRhs (Work.MbarHomology.empLamIdx f i t)) := by
  intro f i hsel
  obtain ⟨hlt, hni, hne, hsub⟩ := hsup f i hsel
  obtain ⟨h1, h2, h3⟩ := hpat ⟨empPat f i, hlt⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t; exact h1 t
  · intro j'
    rw [empMu_sum_translate f i (fun k => qNrm k j') hni hne hsub]
    exact h2 j'
  · rw [empMu_sum_translate f i (fun k => qRhs k) hni hne hsub]
    exact h3

end Work.MbarHomology.Qbar
