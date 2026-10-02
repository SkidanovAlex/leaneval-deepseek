import Mathlib
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Whitney.chernClass_whitneySum_of_lt
import Submission.Work.Agree.PlumbDefs
import Submission.Work.Gen.chernProductSum_line
import Submission.Work.Gen.splitCommonCoverStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-! ## Two elementary tools

`Work.Whitney.chernClass_BundleIso_of_eq` (from the Whitney area) and
`Work.LerayHirsch.nonempty_bundleIso_lineSumCore_cover` (from the flag bundle module) are exactly the
two tools the assembly needs; they are restated here under local (private) names so that this module
does not have to import the heavy flag-bundle and stability modules. -/

/-- **Rank-cast invariance of the Chern classes**: isomorphic bundles whose ranks are equal only
propositionally have equal Chern classes. -/
private theorem chernClass_cast_rank {B : Type} [TopologicalSpace B] {m m' : ℕ} (h : m = m')
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m')) ι')
    (e : Work.Thom.BundleIso Z Z') (j : ℕ) :
    Work.Thom.chernClass m j Z = Work.Thom.chernClass m' j Z' := by
  subst h
  exact Work.Thom.chernClass_BundleIso Z Z' e

/-- **Congruence of the iterated sum of line bundles** in its family of summands: isomorphisms of
the summands induce an isomorphism of the iterated sums.  The two families may live over different
covers.  (A copy of `Work.LerayHirsch.nonempty_bundleIso_lineSumCore_cover`.) -/
private theorem lineSumCore_cover_iso {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (n : ℕ)
    (L : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (L' : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι')
    (h : ∀ i, Nonempty (Work.Thom.BundleIso (L i) (L' i))) :
    Nonempty (Work.Thom.BundleIso (Work.LerayHirsch.lineSumCore n L)
      (Work.LerayHirsch.lineSumCore n L')) := by
  induction n with
  | zero =>
      rw [Work.LerayHirsch.lineSumCore_zero, Work.LerayHirsch.lineSumCore_zero]
      exact ⟨Work.Thom.BundleIso.refl _⟩
  | succ n ih =>
      rw [Work.LerayHirsch.lineSumCore_succ, Work.LerayHirsch.lineSumCore_succ]
      obtain ⟨e₁⟩ := ih (L ∘ Fin.castSucc) (L' ∘ Fin.castSucc) (fun i => h i.castSucc)
      obtain ⟨e₂⟩ := h (Fin.last n)
      obtain ⟨e₃⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_first
        (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc))
        (Work.LerayHirsch.lineSumCore n (L' ∘ Fin.castSucc)) (L' (Fin.last n)) e₁
      obtain ⟨e₄⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
        (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n))
        (L' (Fin.last n)) e₂
      exact ⟨e₄.trans e₃⟩

/-! ## The `k ≥ 1` case, by reindexing onto the product cover

The common-cover step `Work.Gen.splitCommonCoverStep` gives the identity for a family `M'` of line
bundles and a line bundle `L'` over a *single* cover.  Here the two given covers `ι` (of `L`) and
`ι'` (of `M`) are merged into `ι × ι'` by `Work.Agree.reindexCore` along the two projections, and
the classes are transported back along the reindexing isomorphisms
(`Work.Agree.nonempty_bundleIso_reindexCore_self`), the congruence of the direct sum in its two
arguments (`nonempty_bundleIso_whitneySum_first`/`_snd`), the commutativity of the direct sum and the
pointwise congruence of `chernProductSum`. -/

/-- **`Work.Gen.splitDiagonal` in the case `k ≥ 1`.** -/
private theorem splitDiagonal_succ
    (hcrux : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1))
    (k : ℕ) (hk : 1 ≤ k)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (M : Fin k → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι') :
    Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum L (Work.LerayHirsch.lineSumCore k M))
      = Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore k M) k := by
  -- the two families, reindexed onto the product cover `ι × ι'`
  have hσ₁ : ∀ x : B, ∃ i : ι × ι', x ∈ L.baseSet i.1 :=
    fun x => ⟨(L.indexAt x, (M ⟨0, hk⟩).indexAt x), L.mem_baseSet_at x⟩
  have hσ₂ : ∀ i : Fin k, ∀ x : B, ∃ j : ι × ι', x ∈ (M i).baseSet j.2 :=
    fun i x => ⟨(L.indexAt x, (M i).indexAt x), (M i).mem_baseSet_at x⟩
  let M' : Fin k → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) (ι × ι') :=
    fun i => Work.Agree.reindexCore (M i) (fun j : ι × ι' => j.2) (hσ₂ i)
  let L' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) (ι × ι') :=
    Work.Agree.reindexCore L (fun j : ι × ι' => j.1) hσ₁
  -- the common-cover step
  have hcore := Work.Gen.splitCommonCoverStep hcrux k hk L' M'
  -- the isomorphism between the two presentations of the direct sum
  obtain ⟨eM⟩ := lineSumCore_cover_iso k M' M
    (fun i => ⟨(Work.Agree.nonempty_bundleIso_reindexCore_self (M i)
      (fun j : ι × ι' => j.2) (hσ₂ i)).some⟩)
  obtain ⟨eL⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self L
    (fun j : ι × ι' => j.1) hσ₁
  obtain ⟨e₁⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_first
    (Work.LerayHirsch.lineSumCore k M') (Work.LerayHirsch.lineSumCore k M) L' eM
  obtain ⟨e₂⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
    (Work.LerayHirsch.lineSumCore k M) L' L eL
  obtain ⟨e₃⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
    (Work.LerayHirsch.lineSumCore k M) L
  have hLHS : Work.Thom.chernClass (k + 1) k
        (Work.Whitney.whitneySum (Work.LerayHirsch.lineSumCore k M') L')
      = Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum L (Work.LerayHirsch.lineSumCore k M)) :=
    chernClass_cast_rank (by omega : k + 1 = 1 + k) _ _ (e₁.trans (e₂.trans e₃)) k
  have hRHS : Work.Whitney.chernProductSum L' (Work.LerayHirsch.lineSumCore k M') k
      = Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore k M) k :=
    (Work.LerayHirsch.chernProductSum_congr_first L' L
        (Work.LerayHirsch.lineSumCore k M') k
        (fun i => Work.Thom.chernClass_BundleIso (j := i) L' L eL)).trans
      (Work.Whitney.chernProductSum_congr_second L
        (Work.LerayHirsch.lineSumCore k M') (Work.LerayHirsch.lineSumCore k M) k
        (fun i => Work.Thom.chernClass_BundleIso (j := i)
          (Work.LerayHirsch.lineSumCore k M') (Work.LerayHirsch.lineSumCore k M) eM))
  rw [← hLHS, hcore, hRHS]

/-- **The split diagonal of the Whitney formula.**  For a complex line bundle `L` and an `k`-fold
direct sum `lineSumCore k M` of complex line bundles over a paracompact Hausdorff base, the
`(1,k)@k` case of the Whitney formula holds:

`c_k(L ⊕ (M 0 ⊕ … ⊕ M (k-1))) = chernProductSum L (lineSumCore k M) k`.

This is obtained from the hypothesis `hcrux` (the second-highest Chern class of a line sum:
`c_{n-1}(lineSumCore n N) = eSym n N (n-1)`) as follows.  First reindex the two families onto one
common cover (the `Fin.snoc` construction needs a single family: `lineSumCore` is defined by
recursion on a family of line bundles over *one* cover).  With `N : Fin (k+1) → line` over one cover
such that `N i ≃ M i` for `i < k` and `N (last k) ≃ L`, one has
`lineSumCore (k+1) N ≃ whitneySum (lineSumCore k M) L` (definitionally, up to the family rewrites
`Fin.snoc_castSucc`, `Fin.snoc_last`), so `hcrux (k+1) N` reads `c_k(lineSumCore k M ⊕ L) =
eSym (k+1) N k`, and `Work.Gen.eSym_succ` expands the right side as `eSym k M k + cupChern 1 (k-1)
(c₁ L) (eSym k M (k-1))`.  Now `eSym k M k = c_k(lineSumCore k M)` (`Work.Gen.lineSumCore_top_chern`)
and `eSym k M (k-1) = c_{k-1}(lineSumCore k M)` (`hcrux k`), so

`c_k(lineSumCore k M ⊕ L) = c_k(lineSumCore k M) + c₁(L) ⌣ c_{k-1}(lineSumCore k M)`,

whose right-hand side is `chernProductSum L (lineSumCore k M) k` by the collapse
`Work.Gen.chernProductSum_line` (plus `Work.Gen.chernProductSum_comm` if the derivation produces the
pair in the other order).  Finally transport the left-hand side to `c_k(L ⊕ lineSumCore k M)` along
the commutativity isomorphism `Work.Whitney.nonempty_bundleIso_whitneySum_comm` and
`Work.Thom.chernClass_BundleIso`, and the right-hand side along the pointwise reindexing
isomorphisms (`Work.Thom.chernClass_BundleIso`, `Work.LerayHirsch.chernProductSum_congr_first`,
`Work.Whitney.chernProductSum_congr_second`).

For the reindexing step: `Work.Agree.reindexCore` along `Prod.fst`/`Prod.snd` onto the product cover
`ι × ι'` (possible when the base is non-empty, so that `ι` and `ι'` have elements via `indexAt`;
for an empty base take `ι'' := PUnit` and the trivial bundles, using
`Work.LerayHirsch.nonempty_bundleIso_of_isEmpty_base`), together with
`Work.Agree.nonempty_bundleIso_reindexCore_self`,
`Work.LerayHirsch.nonempty_bundleIso_lineSumCore_cover`,
`Work.LerayHirsch.nonempty_bundleIso_whitneySum_first`/`_snd`.  The pattern to copy is
`Submission/Work/LerayHirsch/FlagBundle.lean` around `L' := Fin.snoc B' A'`.  The `k = 0` case can
be done directly (`Work.Whitney.chernProductSum_zero`, `Work.Thom.chernClass_zero_eq_oneH`). -/
theorem splitDiagonal
    (hcrux : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1))
    (k : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (M : Fin k → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι') :
    Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum L (Work.LerayHirsch.lineSumCore k M))
      = Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore k M) k := by
  cases k with
  | zero =>
      have h1 : Work.Thom.chernClass (1 + 0) 0
            (Work.Whitney.whitneySum L (Work.LerayHirsch.lineSumCore 0 M))
          = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) :=
        Work.Thom.chernClass_zero_eq_oneH _
      have h2 : Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore 0 M) 0
          = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
        rw [Work.Gen.chernProductSum_line L (Work.LerayHirsch.lineSumCore 0 M) 0,
          dif_neg (by omega : ¬ (1 ≤ 0))]
        exact (add_zero _).trans (Work.Thom.chernClass_zero_eq_oneH _)
      exact h1.trans h2.symm
  | succ j =>
      exact splitDiagonal_succ hcrux (j + 1) (by omega) L M

end

end Work.Gen
