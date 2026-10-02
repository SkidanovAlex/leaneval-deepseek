import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.TautSection
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses

/-!
# The *peeling* reduction of the Whitney sum formula

This file records the **valid** part of the reduction of the Whitney sum formula
`c_k(E ⊕ F) = Σ_{i+j=k} c_i(E)c_j(F)` to smaller ranks: the descent over the punctured total space
of one summand.

Let `A` have rank `r + 1` and `B` have rank `s`.  Over the punctured total space
`π : A∖0 → B` of `A`, the pullback of `A ⊕ B` carries the tautological nowhere-zero section, and the
class-level peeling (`Work.Whitney.chernClass_whitneySum_pullback_eq`) computes

  `π^*(c_k(A ⊕ B)) = c_k(Q_A ⊕ π^*B)`   (`Q_A = Work.Thom.tautQuotient A`, of rank `r`).

Since `π^*` is injective in degree `2k` as soon as `k ≤ r`
(`Work.Thom.bijective_proj_zeroComplementA`, the descent equation of the Chern recursion), the
Whitney formula in ranks `(r+1, s)` in degree `k ≤ r` follows from the formula in ranks `(r, s)`;
symmetrically one may peel the second summand.  Iterating, the Whitney formula for the ranks
`(m, n)` in degree `k ≤ min(m,n)` follows from its **diagonal** case `(k, k)` in degree `k`.

This is the direction in which the *descent* argument is complete; the remaining (irreducible) case
in each degree `k` is the diagonal one, which is exactly where the Euler-class multiplicativity
`Work.Whitney.TopClassMul` (and, for the intermediate degrees, the Leray–Hirsch input) is needed.
-/

noncomputable section

variable {r s k : ℕ}

/-- **The peeling step of the Whitney sum formula.**  If the Whitney formula holds in ranks
`(r, s)` in degree `k` (over an arbitrary base), then it holds in ranks `(r+1, s)` in degree `k`,
provided `k ≤ r` (so that the descent over `A∖0` is available in degree `2k`). -/
theorem chernClass_whitneySum_peelStep
    (hk : k ≤ r)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂),
      Work.Thom.chernClass (r + s) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (r + 1))) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂) :
    Work.Thom.chernClass (r + 1 + s) k (Work.Whitney.whitneySum A B)
      = Work.Whitney.chernProductSum A B k := by
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (Work.Whitney.punctProjE A) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification A)
      (Work.Thom.finrank_real_euclidean_complex (r + 1))
      (Work.Thom.thomClassRank (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) A) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (Work.Whitney.whitneySum A B) (Work.Whitney.punctProjE A),
    Work.Whitney.chernProductSum_CohMap A B (Work.Whitney.punctProjE A)]
  rw [Work.Whitney.chernClass_whitneySum_pullback_eq (E := A) (F := B) (m₁ := r) (m₂ := s)]
  rw [IH (Work.Thom.tautQuotient (m := r) A) (Work.Thom.bundleComap B (Work.Whitney.punctProjE A))]
  exact Work.LerayHirsch.chernProductSum_congr_first
    (Work.Thom.tautQuotient (m := r) A) (Work.Thom.bundleComap A (Work.Whitney.punctProjE A))
    (Work.Thom.bundleComap B (Work.Whitney.punctProjE A)) k
    (fun i => (Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient (j := i) A).symm)

end

end Work.Gen

namespace Work.Gen

open Work.TangentClasses

noncomputable section

/-- **The descent to the minimal rank.**  If the Whitney sum formula in degree `k` holds for every
pair whose **first** rank is exactly `k` (and with arbitrary second rank `n ≥ k`), then it holds for
every pair whose first rank is `≥ k`. -/
theorem chernClass_whitneySum_of_peel_fst (k : ℕ)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (n : ℕ),
      k ≤ n → ∀ (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₁)
        (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
      Work.Thom.chernClass (k + n) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k) :
    ∀ (m : ℕ), k ≤ m →
      ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (n : ℕ),
        k ≤ n → ∀ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
          (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
        Work.Thom.chernClass (m + n) k (Work.Whitney.whitneySum A B)
          = Work.Whitney.chernProductSum A B k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm B _ ι₁ ι₂ _ _ n hn A B
    rcases eq_or_lt_of_le hm with heq | hlt
    · subst heq
      exact IH n hn A B
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨r, rfl⟩
      exact chernClass_whitneySum_peelStep (r := r) (s := n) (k := k)
        (by omega)
        (fun {B'} _ {ι₁' ι₂'} _ _ A' B' => ih r (by omega) (by omega) n hn A' B')
        A B

end

end Work.Gen

namespace Work.Gen

open Work.TangentClasses

noncomputable section

/-- The right-hand side of the Whitney formula only depends on the Chern classes of its **second**
argument. -/
theorem chernProductSum_congr_second {B : Type} [TopologicalSpace B] {m₁ m₂ m₂' : ℕ}
    {ι₁ ι₂ ι₂' : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₂']
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (Z₂' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂') (k : ℕ)
    (h : ∀ i, Work.Thom.chernClass m₂ i Z₂ = Work.Thom.chernClass m₂' i Z₂') :
    Work.Whitney.chernProductSum Z₁ Z₂ k = Work.Whitney.chernProductSum Z₁ Z₂' k := by
  rw [Work.Whitney.chernProductSum, Work.Whitney.chernProductSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hik : i ≤ k
  · rw [dif_pos hik, dif_pos hik]
    congr 1
    rw [Work.Whitney.chernSummand_def, Work.Whitney.chernSummand_def, h (k - i)]
  · rw [dif_neg hik, dif_neg hik]

/-- **The peeling identity over the punctured total space of the *second* summand.** -/
theorem chernClass_whitneySum_pullback_eq_snd {r s k : ℕ}
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (r + (s + 1)) k
        (Work.Thom.bundleComap (Work.Whitney.whitneySum E F) (Work.Whitney.punctProjE F))
      = Work.Thom.chernClass (r + s) k
          (Work.Whitney.whitneySum (Work.Thom.bundleComap E (Work.Whitney.punctProjE F))
            (Work.Thom.tautQuotient (m := s) F)) := by
  obtain ⟨e₁⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm E F
  obtain ⟨e₁'⟩ := Work.Thom.BundleIso_comap_exists (Work.Whitney.whitneySum E F)
    (Work.Whitney.whitneySum F E) e₁ (Work.Whitney.punctProjE F)
  rw [Work.Whitney.chernClass_BundleIso_of_eq (by omega : r + (s + 1) = (s + 1) + r) _ _ e₁' k]
  rw [Work.Whitney.chernClass_whitneySum_pullback_eq (E := F) (F := E) (m₁ := s) (m₂ := r)]
  obtain ⟨e₂⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm (Work.Thom.tautQuotient (m := s) F)
    (Work.Thom.bundleComap E (Work.Whitney.punctProjE F))
  exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : s + r = r + s) _ _ e₂ k

/-- **The peeling step, second slot.** -/
theorem chernClass_whitneySum_peelStep_snd {r s k : ℕ} (hk : k ≤ s)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂),
      Work.Thom.chernClass (r + s) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (r + (s + 1)) k (Work.Whitney.whitneySum A B)
      = Work.Whitney.chernProductSum A B k := by
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (Work.Whitney.punctProjE B) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification B)
      (Work.Thom.finrank_real_euclidean_complex (s + 1))
      (Work.Thom.thomClassRank (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) B) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (Work.Whitney.whitneySum A B) (Work.Whitney.punctProjE B),
    Work.Whitney.chernProductSum_CohMap A B (Work.Whitney.punctProjE B)]
  rw [chernClass_whitneySum_pullback_eq_snd (E := A) (F := B) (r := r) (s := s)]
  rw [IH (Work.Thom.bundleComap A (Work.Whitney.punctProjE B))
    (Work.Thom.tautQuotient (m := s) B)]
  exact chernProductSum_congr_second (Work.Thom.bundleComap A (Work.Whitney.punctProjE B))
    (Work.Thom.tautQuotient (m := s) B) (Work.Thom.bundleComap B (Work.Whitney.punctProjE B)) k
    (fun i => (Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient (j := i) B).symm)

/-- **The descent to the minimal second rank**: if the formula holds for every pair whose second
rank is exactly `k`, it holds for every pair whose second rank is `≥ k`. -/
theorem chernClass_whitneySum_of_peel_snd (k : ℕ)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (m : ℕ),
      k ≤ m → ∀ (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
        (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₂),
      Work.Thom.chernClass (m + k) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k) :
    ∀ (n : ℕ), k ≤ n →
      ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (m : ℕ),
        k ≤ m → ∀ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
          (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
        Work.Thom.chernClass (m + n) k (Work.Whitney.whitneySum A B)
          = Work.Whitney.chernProductSum A B k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn B _ ι₁ ι₂ _ _ m hm A B
    rcases eq_or_lt_of_le hn with heq | hlt
    · subst heq
      exact IH m hm A B
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨s, rfl⟩
      exact chernClass_whitneySum_peelStep_snd (r := m) (s := s) (k := k)
        (by omega)
        (fun {B'} _ {ι₁' ι₂'} _ _ A' B' => ih s (by omega) (by omega) m hm A' B')
        A B

/-- **The Whitney sum formula reduces to its diagonal cases.**  If the formula holds in degree `k`
for two bundles *both* of rank `k` (over an arbitrary base), then it holds in degree `k` for any two
bundles of ranks `m, n ≥ k`. -/
theorem chernClass_whitneySum_of_diag (k : ℕ)
    (IHdiag : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₂),
      Work.Thom.chernClass (k + k) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k) :
    ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (m n : ℕ),
      k ≤ m → k ≤ n → ∀ (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₁)
        (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
      Work.Thom.chernClass (m + n) k (Work.Whitney.whitneySum A B)
        = Work.Whitney.chernProductSum A B k := by
  have H1 : ∀ (n : ℕ), k ≤ n →
      ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
        (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₁)
        (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
        Work.Thom.chernClass (k + n) k (Work.Whitney.whitneySum A' B')
          = Work.Whitney.chernProductSum A' B' k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn B _ ι₁ ι₂ _ _ A' B'
      rcases eq_or_lt_of_le hn with heq | hlt
      · subst heq
        exact IHdiag A' B'
      · rcases Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega) with ⟨s, rfl⟩
        exact chernClass_whitneySum_peelStep_snd (r := k) (s := s) (k := k)
          (by omega)
          (fun {B'} _ {ι₁' ι₂'} _ _ A'' B'' => ih s (by omega) (by omega) A'' B'')
          A' B'
  intro B _ ι₁ ι₂ _ _ m n hm hn A B
  exact chernClass_whitneySum_of_peel_fst k
    (fun {B} _ {ι₁ ι₂} _ _ n hn A' B' => H1 n hn A' B') m hm n hn A B

end

end Work.Gen

namespace Work.Gen

open Work.TangentClasses

noncomputable section

/-- **The line family reduces to its core cases.**  If the Whitney formula in degree `k` holds for a
*line* bundle and a bundle of rank exactly `k`, then it holds for a line bundle and a bundle of any
rank `n ≥ k`.  The proof peels the second summand
(`Work.Gen.chernClass_whitneySum_peelStep_snd`), whose descent hypothesis `k ≤ n - 1` holds
throughout the induction. -/
theorem chernClass_whitneySum_one_family (k : ℕ)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₂),
      Work.Thom.chernClass (1 + k) k (Work.Whitney.whitneySum L B')
        = Work.Whitney.chernProductSum L B' k) :
    ∀ (n : ℕ), k ≤ n →
      ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
        (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
        (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
        Work.Thom.chernClass (1 + n) k (Work.Whitney.whitneySum L B')
          = Work.Whitney.chernProductSum L B' k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn B _ ι₁ ι₂ _ _ L B'
    rcases eq_or_lt_of_le hn with heq | hlt
    · subst heq
      exact IH L B'
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨s, rfl⟩
      exact chernClass_whitneySum_peelStep_snd (r := 1) (s := s) (k := k)
        (by omega)
        (fun {B'} _ {ι₁' ι₂'} _ _ A' B'' => ih s (by omega) (by omega) A' B'')
        L B'

end

end Work.Gen
