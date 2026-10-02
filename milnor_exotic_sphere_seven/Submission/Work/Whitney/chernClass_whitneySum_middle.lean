import Mathlib
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.Whitney.puncturedParacompact
import Submission.Work.Tubular.PuncturedDiscPair.t2Space_sphSub
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernClass_whitneySum_of_lt
import Submission.Work.Whitney.chernRelation_of_whitneyFormula

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.TangentClasses Work.LerayHirsch

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

/-! # The middle degrees of the Whitney sum formula

**Target.** `Work.Whitney.chernClass_whitneySum_middle`: for a pair of complex gluing-data bundles
of total rank `m₁ + m₂`, the Whitney sum formula

  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)`

holds in every degree `k ≤ m₁ + m₂ - 2`, *given* the full formula for every pair of strictly smaller
total rank (over paracompact Hausdorff bases).

**Proof.**  Two steps.

* The **low degrees** `k ≤ max m₁ m₂ - 1` (`wfBelow_lt` below) are pure descent: peel the larger
  summand over its punctured total space, where `π^*` is injective in degree `2k`
  (`Work.Thom.bijective_proj_zeroComplementA`) and where the peeled bundle has become
  `Q ⊕ π^*F` of total rank `m₁ + m₂ - 1 < m₁ + m₂`; the induction hypothesis then applies over that
  punctured space — which is why `Work.Whitney.puncturedParacompact` is needed
  (`ParacompactSpace ↥(zeroComplement (realification A))`, the only missing instance).
* The **middle degrees** `max m₁ m₂ ≤ k ≤ m₁ + m₂ - 2` are the "pairing argument": pull the identity
  back along `π : P(Z₁) → B`, which is injective in *every* degree (Leray–Hirsch,
  `Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull`, unconditional here because
  `Work.Kunneth.kunnethCP` is proved).  Over `P(Z₁)` one has `π^*Z₁ ≅ ℓ ⊕ Q`, so
  `π^*(Z₁ ⊕ Z₂) ≅ ℓ ⊕ (Q ⊕ π^*Z₂)` and the identity is the associativity of the convolution of
  Chern series: the pair `(Q, π^*Z₂)` has total rank `m₁ + m₂ - 1` (induction hypothesis), the pairs
  `(ℓ, Q)` and `(1, m₁ - 1)`, `(Q, π^*Z₂)` have total rank `< m₁ + m₂` (induction hypothesis), and
  the remaining case `(ℓ, Q ⊕ π^*Z₂)` — of total rank `m₁ + m₂` but in degree `k ≤ m₁ + m₂ - 2` — is
  handled by the *low degree* result proved in the first step. -/

/-- **The Whitney sum formula below rank `N`** (over paracompact Hausdorff bases): for every pair
of complex gluing-data bundles of total rank `< N`, `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)` in
*every* degree `k`.  This is the shape of the induction hypothesis of
`Work.Whitney.chernClass_whitneySum_middle`. -/
def WFBelow (N : ℕ) : Prop :=
  ∀ {m₁ m₂ : ℕ}, m₁ + m₂ < N →
    ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (W₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
      (W₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (j : ℕ),
      Work.Thom.chernClass (m₁ + m₂) j (Work.Whitney.whitneySum W₁ W₂)
        = Work.Whitney.chernProductSum W₁ W₂ j

/-- The punctured total space of a realification is Hausdorff
(`Work.Tubular.PuncturedDiscPair.t2Space_totalSpace` for the total space, then the subtype
instance). -/
private theorem t2Space_zeroComplement_aux {m : ℕ} {B : Type} [TopologicalSpace B] [T2Space B]
    {ι : Type} (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    T2Space ↥(Work.Thom.zeroComplement (Work.Thom.realification A)) :=
  @instT2SpaceSubtype (Work.Thom.realification A).TotalSpace _
    (fun p => p ∈ Work.Thom.zeroComplement (Work.Thom.realification A))
    (Work.Tubular.PuncturedDiscPair.t2Space_totalSpace (Work.Thom.realification A))

/-- **The peeling step of the Whitney sum formula, in the paracompact form.**  If the formula holds
for every pair of total rank `< N`, then it holds in ranks `(r+1, s)` (total rank `r+1+s ≤ N`) in
degree `k ≤ r`: this is exactly the range in which the descent over the punctured total space of the
first summand is injective (`Work.Thom.bijective_proj_zeroComplementA`), and the intermediate pair
`(Q_A, π^*B)` has total rank `r + s < N`. -/
theorem wfBelow_peelStep {N r s k : ℕ} (IH : WFBelow N) (hN : r + s < N) (hk : k ≤ r)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type}
      [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (r + 1))) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂) :
    Work.Thom.chernClass (r + 1 + s) k (whitneySum A B)
      = chernProductSum A B k := by
  haveI : ParacompactSpace ↥(Work.Thom.zeroComplement (Work.Thom.realification A)) :=
    Work.Whitney.puncturedParacompact (Work.Thom.realification A)
  haveI : T2Space ↥(Work.Thom.zeroComplement (Work.Thom.realification A)) :=
    t2Space_zeroComplement_aux A
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (Work.Whitney.punctProjE A) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification A)
      (Work.Thom.finrank_real_euclidean_complex (r + 1))
      (Work.Thom.thomClassRank (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) A) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (whitneySum A B) (Work.Whitney.punctProjE A),
    chernProductSum_CohMap A B (Work.Whitney.punctProjE A)]
  rw [chernClass_whitneySum_pullback_eq (E := A) (F := B) (m₁ := r) (m₂ := s)]
  rw [IH (by omega) (Work.Thom.tautQuotient (m := r) A)
    (Work.Thom.bundleComap B (Work.Whitney.punctProjE A)) k]
  exact Work.LerayHirsch.chernProductSum_congr_first
    (Work.Thom.tautQuotient (m := r) A) (Work.Thom.bundleComap A (Work.Whitney.punctProjE A))
    (Work.Thom.bundleComap B (Work.Whitney.punctProjE A)) k
    (fun i => (chernClass_bundleComap_proj_eq_tautQuotient (j := i) A).symm)

/-- **The peeling step of the Whitney sum formula, second slot, in the paracompact form.** -/
theorem wfBelow_peelStep_snd {N r s k : ℕ} (IH : WFBelow N) (hN : r + s < N) (hk : k ≤ s)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type}
      [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin r)) ι₁)
    (B : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (r + (s + 1)) k (whitneySum A B)
      = chernProductSum A B k := by
  haveI : ParacompactSpace ↥(Work.Thom.zeroComplement (Work.Thom.realification B)) :=
    Work.Whitney.puncturedParacompact (Work.Thom.realification B)
  haveI : T2Space ↥(Work.Thom.zeroComplement (Work.Thom.realification B)) :=
    t2Space_zeroComplement_aux B
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (Work.Whitney.punctProjE B) ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification B)
      (Work.Thom.finrank_real_euclidean_complex (s + 1))
      (Work.Thom.thomClassRank (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) B) (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (whitneySum A B) (Work.Whitney.punctProjE B),
    chernProductSum_CohMap A B (Work.Whitney.punctProjE B)]
  rw [chernClass_whitneySum_pullback_eq_snd (E := A) (F := B) (r := r) (s := s)]
  rw [IH (by omega) (Work.Thom.bundleComap A (Work.Whitney.punctProjE B))
    (Work.Thom.tautQuotient (m := s) B) k]
  exact chernProductSum_congr_second (Work.Thom.bundleComap A (Work.Whitney.punctProjE B))
    (Work.Thom.tautQuotient (m := s) B) (Work.Thom.bundleComap B (Work.Whitney.punctProjE B)) k
    (fun i => (chernClass_bundleComap_proj_eq_tautQuotient (j := i) B).symm)

/-- **The low-degree part of the Whitney sum formula, in the paracompact form**: for
`k ≤ max m₁ m₂ - 1` the formula in ranks `(m₁, m₂)` follows from the formula for every pair of
strictly smaller total rank (this is `Work.Whitney.chernClass_whitneySum_of_lt` with the induction
hypothesis restricted to paracompact Hausdorff bases, which is the form in which it is available). -/
theorem wfBelow_lt {N m₁ m₂ k : ℕ} (IH : WFBelow N) (hN : m₁ + m₂ ≤ N)
    (hk : k ≤ max m₁ m₂ - 1)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type}
      [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) k (whitneySum Z₁ Z₂) = chernProductSum Z₁ Z₂ k := by
  rcases m₁ with _ | r
  · exact Work.LerayHirsch.whitneySumFormula_rank_zero m₂ Z₁ Z₂ k
  rcases m₂ with _ | s
  · have hk' : k ≤ r := by omega
    exact wfBelow_peelStep (N := N) IH (by omega) hk' Z₁ Z₂
  · have hk' : k ≤ max r s := by omega
    rcases le_max_iff.mp hk' with hr | hs
    · exact wfBelow_peelStep (N := N) IH (by omega) hr Z₁ Z₂
    · exact wfBelow_peelStep_snd (N := N) IH (by omega) hs Z₁ Z₂

theorem chernClass_whitneySum_middle {m₁ m₂ k : ℕ}
    (IH : ∀ {m₁' m₂' : ℕ}, m₁' + m₂' < m₁ + m₂ →
      ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
        {ι₁' ι₂' : Type} [Fintype ι₁'] [Fintype ι₂']
        (W₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁')) ι₁')
        (W₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂') (j : ℕ),
        Work.Thom.chernClass (m₁' + m₂') j (Work.Whitney.whitneySum W₁ W₂)
          = Work.Whitney.chernProductSum W₁ W₂ j)
    (hk : k + 2 ≤ m₁ + m₂)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) k (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.chernProductSum Z₁ Z₂ k := by
  have hIH : WFBelow (m₁ + m₂) := IH
  by_cases hlt : k ≤ max m₁ m₂ - 1
  · exact wfBelow_lt hIH le_rfl hlt Z₁ Z₂
  · -- the middle range: `max m₁ m₂ ≤ k ≤ m₁ + m₂ - 2`
    have hmax : max m₁ m₂ ≤ k := by omega
    have h₁ : m₁ ≤ k := le_trans (le_max_left m₁ m₂) hmax
    have h₂ : m₂ ≤ k := le_trans (le_max_right m₁ m₂) hmax
    have hm₁ : 2 ≤ m₁ := by omega
    have hm₂ : 2 ≤ m₂ := by omega
    obtain ⟨p, rfl⟩ : ∃ p, m₁ = p + 1 := ⟨m₁ - 1, by omega⟩
    -- the projectivisation of `Z₁` is paracompact Hausdorff
    haveI : ParacompactSpace (ProjSpace Z₁) := paracompactSpace_projSpace Z₁
    haveI : T2Space (ProjSpace Z₁) := t2Space_projSpace Z₁
    obtain ⟨Q, ⟨e⟩⟩ := splitsOverProj_of_paracompact (m' := p) Z₁
    -- pull back to the projectivisation, where `π^*` is injective in every degree
    refine (CohMap_projMap_injective_of_LerayHirschFull (m := p + 1) (by omega) Z₁
      (lerayHirschFull_of_kunnethCP Work.Kunneth.kunnethCP Z₁) (2 * k)) ?_
    rw [← Work.Thom.chernClass_comap, whitneySum_bundleComap, chernProductSum_CohMap]
    set W : VectorBundleCore ℂ (ProjSpace Z₁) (EuclideanSpace ℂ (Fin m₂)) ι₂ :=
      Work.Thom.bundleComap Z₂ (projMap Z₁) with hW
    -- step 1: replace `π^*Z₁` by `ℓ ⊕ Q`
    have hstep1 : Work.Thom.chernClass ((p + 1) + m₂) k
          (whitneySum (Work.Thom.bundleComap Z₁ (projMap Z₁)) W)
        = Work.Thom.chernClass ((1 + p) + m₂) k
          (whitneySum (whitneySum (tautLine Z₁) Q) W) := by
      obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_first
        (Z₁ := Work.Thom.bundleComap Z₁ (projMap Z₁))
        (Z₁' := whitneySum (tautLine Z₁) Q) (Z₂ := W) e
      exact chernClass_BundleIso_of_eq (by omega : (p + 1) + m₂ = (1 + p) + m₂) _ _ e' k
    rw [hstep1]
    -- step 2: reassociate
    have hstep2 : Work.Thom.chernClass ((1 + p) + m₂) k
          (whitneySum (whitneySum (tautLine Z₁) Q) W)
        = Work.Thom.chernClass (1 + (p + m₂)) k
          (whitneySum (tautLine Z₁) (whitneySum Q W)) := by
      obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_assoc (tautLine Z₁) Q W
      exact chernClass_BundleIso_of_eq (by omega : (1 + p) + m₂ = 1 + (p + m₂)) _ _ e' k
    rw [hstep2]
    -- step 3: the `(1, p + m₂)` case in degree `k ≤ p + m₂ - 1`, i.e. `wfBelow_lt`
    have hk3 : k ≤ max 1 (p + m₂) - 1 := by omega
    have hstep3 : Work.Thom.chernClass (1 + (p + m₂)) k
          (whitneySum (tautLine Z₁) (whitneySum Q W))
        = chernProductSum (tautLine Z₁) (whitneySum Q W) k :=
      wfBelow_lt (N := (p + 1) + m₂) hIH (by omega) hk3 (tautLine Z₁) (whitneySum Q W)
    rw [hstep3]
    -- step 4: associativity of the convolution
    have hstep4 : chernProductSum (tautLine Z₁) (whitneySum Q W) k
        = chernProductSum (whitneySum (tautLine Z₁) Q) W k := by
      have hQWs : chernSeries (whitneySum Q W)
          = convSeries (chernSeries Q) (chernSeries W) :=
        chernSeries_whitneySum_eq_convSeries Q W
          (fun j => hIH (by omega) Q W j)
      have hlQ : convSeries (chernSeries (tautLine Z₁)) (chernSeries Q)
          = chernSeries (whitneySum (tautLine Z₁) Q) :=
        (chernSeries_whitneySum_eq_convSeries (tautLine Z₁) Q
          (fun j => hIH (by omega) (tautLine Z₁) Q j)).symm
      rw [chernProductSum_eq_convSeries, hQWs, ← convSeries_assoc, hlQ,
        ← chernProductSum_eq_convSeries]
    rw [hstep4]
    -- step 5: `whitneySum ℓ Q ≅ π^*Z₁`
    refine (Work.LerayHirsch.chernProductSum_congr_first (whitneySum (tautLine Z₁) Q)
      (Work.Thom.bundleComap Z₁ (projMap Z₁)) W k ?_)
    intro i
    exact chernClass_BundleIso_of_eq (by omega : 1 + p = p + 1)
      (whitneySum (tautLine Z₁) Q) (Work.Thom.bundleComap Z₁ (projMap Z₁)) e.symm i

end

end Work.Whitney
