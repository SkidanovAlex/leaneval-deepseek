import Mathlib
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Whitney.TautSection
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.TangentClasses

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-!
# The low-degree part of the Whitney sum formula

This module proves the *descent* part of the Whitney sum formula for the Chern classes
`Work.Thom.chernClass`: in the degrees `k ≤ max m₁ m₂ - 1` — exactly the range in which the
pullback `π^*` of the punctured total space is injective in degree `2k`
(`Work.Thom.bijective_proj_zeroComplementA`) — the formula for the ranks `(m₁, m₂)` follows from
the formula for all pairs of *strictly smaller* total rank.

* `Work.Whitney.chernClass_whitneySum_peelStep` — the peeling step of the first summand;
* `Work.Whitney.chernProductSum_congr_second` — the right-hand side depends only on the Chern
  classes of its second argument;
* `Work.Whitney.chernClass_whitneySum_pullback_eq_snd` — the peeling identity over the punctured
  total space of the second summand;
* `Work.Whitney.chernClass_whitneySum_peelStep_snd` — the peeling step of the second summand;
* `Work.Whitney.chernClass_whitneySum_of_lt` — **the target**: the Whitney sum formula in degree
  `k ≤ max m₁ m₂ - 1` follows from the formula in all strictly smaller total ranks.
-/

/-! ## The peeling step of the first summand -/

/-- **The peeling step of the Whitney sum formula.**  If the Whitney formula holds in ranks
`(r, s)` in degree `k` (over an arbitrary base), then it holds in ranks `(r+1, s)` in degree `k`,
provided `k ≤ r` (so that the descent over `A∖0` is available in degree `2k`). -/
theorem chernClass_whitneySum_peelStep {r s k : ℕ} (hk : k ≤ r)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂),
      Work.Thom.chernClass (r + s) k (whitneySum A' B') = chernProductSum A' B' k)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (r + 1))) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂) :
    Work.Thom.chernClass (r + 1 + s) k (whitneySum A B) = chernProductSum A B k := by
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (punctProjE A) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification A)
      (Work.Thom.finrank_real_euclidean_complex (r + 1))
      (Work.Thom.thomClassRank (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) A) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (whitneySum A B) (punctProjE A),
    chernProductSum_CohMap A B (punctProjE A)]
  rw [Work.Whitney.chernClass_whitneySum_pullback_eq (E := A) (F := B) (m₁ := r) (m₂ := s)]
  rw [IH (Work.Thom.tautQuotient (m := r) A) (Work.Thom.bundleComap B (punctProjE A))]
  exact Work.LerayHirsch.chernProductSum_congr_first
    (Work.Thom.tautQuotient (m := r) A) (Work.Thom.bundleComap A (punctProjE A))
    (Work.Thom.bundleComap B (punctProjE A)) k
    (fun i => (Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient (j := i) A).symm)

/-! ## The right-hand side depends only on the Chern classes of the second summand -/

/-- The right-hand side of the Whitney formula only depends on the Chern classes of its **second**
argument. -/
theorem chernProductSum_congr_second {m₁ m₂ m₂' : ℕ}
    {ι₁ ι₂ ι₂' : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₂']
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (Z₂' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂') (k : ℕ)
    (h : ∀ i, Work.Thom.chernClass m₂ i Z₂ = Work.Thom.chernClass m₂' i Z₂') :
    chernProductSum Z₁ Z₂ k = chernProductSum Z₁ Z₂' k := by
  rw [chernProductSum, chernProductSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hik : i ≤ k
  · rw [dif_pos hik, dif_pos hik]
    congr 1
    rw [chernSummand_def, chernSummand_def, h (k - i)]
  · rw [dif_neg hik, dif_neg hik]

/-! ## The peeling step of the second summand -/

/-- **The peeling identity over the punctured total space of the *second* summand.**  With
`m₁ = s + 1` and `m₂ = r`, the pullback of `c_k(E ⊕ F)` to the punctured total space of `F` is
`c_k(π^*E ⊕ Q_F)`, up to the commutativity of the direct sum. -/
theorem chernClass_whitneySum_pullback_eq_snd {r s k : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (r + (s + 1)) k
        (Work.Thom.bundleComap (whitneySum E F) (punctProjE F))
      = Work.Thom.chernClass (r + s) k
          (whitneySum (Work.Thom.bundleComap E (punctProjE F))
            (Work.Thom.tautQuotient (m := s) F)) := by
  obtain ⟨e₁⟩ := nonempty_bundleIso_whitneySum_comm E F
  obtain ⟨e₁'⟩ := Work.Thom.BundleIso_comap_exists (whitneySum E F) (whitneySum F E) e₁ (punctProjE F)
  rw [chernClass_BundleIso_of_eq (by omega : r + (s + 1) = (s + 1) + r) _ _ e₁' k]
  rw [Work.Whitney.chernClass_whitneySum_pullback_eq (E := F) (F := E) (m₁ := s) (m₂ := r)]
  obtain ⟨e₂⟩ := nonempty_bundleIso_whitneySum_comm (Work.Thom.tautQuotient (m := s) F)
    (Work.Thom.bundleComap E (punctProjE F))
  exact chernClass_BundleIso_of_eq (by omega : s + r = r + s) _ _ e₂ k

/-- **The peeling step, second slot.**  If the Whitney formula holds in ranks `(r, s)` in degree
`k`, then it holds in ranks `(r, s+1)` in degree `k`, provided `k ≤ s`. -/
theorem chernClass_whitneySum_peelStep_snd {r s k : ℕ} (hk : k ≤ s)
    (IH : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂),
      Work.Thom.chernClass (r + s) k (whitneySum A' B') = chernProductSum A' B' k)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (r + (s + 1)) k (whitneySum A B) = chernProductSum A B k := by
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (punctProjE B) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification B)
      (Work.Thom.finrank_real_euclidean_complex (s + 1))
      (Work.Thom.thomClassRank (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) B) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (whitneySum A B) (punctProjE B),
    chernProductSum_CohMap A B (punctProjE B)]
  rw [chernClass_whitneySum_pullback_eq_snd (E := A) (F := B) (r := r) (s := s)]
  rw [IH (Work.Thom.bundleComap A (punctProjE B)) (Work.Thom.tautQuotient (m := s) B)]
  exact chernProductSum_congr_second (Work.Thom.bundleComap A (punctProjE B))
    (Work.Thom.tautQuotient (m := s) B) (Work.Thom.bundleComap B (punctProjE B)) k
    (fun i => (chernClass_bundleComap_proj_eq_tautQuotient (j := i) B).symm)

/-! ## The assembly -/

/-
**THE LOW-DEGREE PART OF THE WHITNEY SUM FORMULA**: for `k ≤ max m₁ m₂ - 1` (exactly the range in
which `π^*` is injective in degree `2k`, `Work.Thom.bijective_proj_zeroComplementA`), the Whitney
formula follows from the FULL formula for all pairs of strictly smaller total rank (`IH`).

PLANNED ROUTE (all pieces are on disk; the descent engine is
`Work.Whitney.chernClass_whitneySum_pullback_eq`):

*Case `m₁ = 0` (and symmetrically `m₂ = 0`): `Work.Whitney.chernClass_whitneySum_rank_zero` collapses
the left side to `chernClass m₂ k Z₂`, and `Work.Whitney.chernProductSum_rank_zero_first`
(`Submission/Work/LerayHirsch/whitneySumFormulaOfLerayHirsch.lean`) collapses the right side; `hk` is
then automatic.*

*Case `m₁, m₂ ≥ 1`: put `D = chernClass (m₁+m₂) k (whitneySum Z₁ Z₂) - chernProductSum Z₁ Z₂ k` and
show `D = 0` by showing `π₁^*D = 0` or `π₂^*D = 0` and using injectivity.*  Write `m₁ = r + 1` and
`π = punctProjE Z₁ : X = Z₁∖0 → B`.
  1. `π^*(chernClass (m₁+m₂) k (whitneySum Z₁ Z₂)) = chernClass (m₁+m₂) k (bundleComap (whitneySum Z₁ Z₂) π)`
     by `Work.Thom.chernClass_comap`, then `Work.Whitney.whitneySum_bundleComap`, then
     `Work.Whitney.chernClass_whitneySum_pullback_eq` identifies it with
     `chernClass (r + m₂) k (whitneySum (tautQuotient Z₁) (bundleComap Z₂ π))`, a sum of total rank
     `(m₁-1) + m₂ < m₁ + m₂`: apply `IH` with `m₁' = r`, `m₂' = m₂`.
  2. `π^*(chernProductSum Z₁ Z₂ k) = chernProductSum (bundleComap Z₁ π) (bundleComap Z₂ π) k` by
     `Work.Whitney.chernProductSum_CohMap`; rewrite `chernClass r i (tautQuotient Z₁)` back to
     `π^*(chernClass (r+1) i Z₁)` — for `i ≤ r` this is
     `Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient_le` (in `TautSection.lean`), for
     `i = r + 1 = m₁ > k` the summand is out of range, for `i > m₁` both sides vanish
     (`Work.Thom.chernClass_eq_zero_of_lt`); compare the two sums with
     `Work.Whitney.chernProductSum_congr_first` (in `Submission/Work/LerayHirsch/`) or directly by
     `Finset.sum_congr`.
  3. Conclude `π^*D = 0`; symmetrically `π'^*D = 0` for `π' = punctProjE Z₂`.  `hk` gives `k ≤ m₁-1`
     or `k ≤ m₂-1`, so one of `π^*, π'^*` is injective in degree `2k`
     (`Work.Thom.bijective_proj_zeroComplementA`, used through the same `LinearEquiv.ofBijective`
     pattern as `Work.Thom.chernClass_succ_of_le`), whence `D = 0`.

The commutation of the sum with the pullback is `Work.Whitney.whitneySum_bundleComap` (an equality of
cores); the symmetric version of step 1 may use the commutativity isomorphism
`Work.Whitney.nonempty_bundleIso_whitneySum_comm` together with `Work.Thom.chernClass_BundleIso` if
peeling the second factor is preferred.

DO NOT declare this false.  If some bookkeeping (degree casts in `Coh`, `Finset.sum_congr` over
`chernProductSum`) is too heavy, prove intermediate results in the file.
-/
theorem chernClass_whitneySum_of_lt {m₁ m₂ k : ℕ}
    (IH : ∀ {m₁' m₂' : ℕ}, m₁' + m₂' < m₁ + m₂ →
      ∀ {B' : Type} [TopologicalSpace B'] {ι₁' ι₂' : Type} [Fintype ι₁'] [Fintype ι₂']
        (Z₁' : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin m₁')) ι₁')
        (Z₂' : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin m₂')) ι₂') (j : ℕ),
        Work.Thom.chernClass (m₁' + m₂') j (Work.Whitney.whitneySum Z₁' Z₂')
          = Work.Whitney.chernProductSum Z₁' Z₂' j)
    (hk : k ≤ max m₁ m₂ - 1)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) k (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.chernProductSum Z₁ Z₂ k := by
  rcases m₁ with _ | r
  · exact Work.LerayHirsch.whitneySumFormula_rank_zero m₂ Z₁ Z₂ k
  rcases m₂ with _ | s
  · have hk' : k ≤ r := by omega
    exact chernClass_whitneySum_peelStep (r := r) (s := 0) (k := k) hk'
      (fun A' B' => IH (by omega) A' B' k) Z₁ Z₂
  · have hk' : k ≤ max r s := by omega
    rcases le_max_iff.mp hk' with hr | hs
    · exact chernClass_whitneySum_peelStep (r := r) (s := s + 1) (k := k) hr
        (fun A' B' => IH (by omega) A' B' k) Z₁ Z₂
    · exact chernClass_whitneySum_peelStep_snd (r := r + 1) (s := s) (k := k) hs
        (fun A' B' => IH (by omega) A' B' k) Z₁ Z₂

end

end Work.Whitney
