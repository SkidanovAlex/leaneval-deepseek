import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.Series
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernClass_whitneySum_stability
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Whitney sum formula from Leray–Hirsch, splitting and the line-bundle case

This is the assembly statement of the Leray–Hirsch chapter: the Leray–Hirsch theorem for the
projectivisation (`∀ Z, LerayHirschFull Z`), the geometric splitting `∀ Z, SplitsOverProj Z` and
the Whitney formula for a line-bundle summand (`∀ N, WhitneySumFormula 1 N`) together imply the
**Whitney sum formula in all ranks and degrees**:

  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)`.

The proof is the classical induction on the rank of the first summand, and the three inputs above
enter in the three steps of the induction step:

* **pull back to the projectivisation** `π : P(Z₁) → B`.  By
  `Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull` the map `π^*` is injective on
  cohomology, so it suffices to prove the identity after pulling back; by the naturality of the
  Chern classes (`Work.Thom.chernClass_comap`) and of the right-hand side
  (`Work.Whitney.chernProductSum_CohMap`) this is the identity for `π^*Z₁` and `π^*Z₂` over
  `P(Z₁)`;
* **split off the tautological line**: `SplitsOverProj Z₁` gives `π^*Z₁ ≅ ℓ ⊕ Q` with `ℓ` of rank
  one, so `π^*Z₁ ⊕ π^*Z₂ ≅ (ℓ ⊕ Q) ⊕ π^*Z₂ ≅ ℓ ⊕ (Q ⊕ π^*Z₂)`
  (`Work.LerayHirsch.nonempty_bundleIso_whitneySum_first`,
  `Work.LerayHirsch.nonempty_bundleIso_whitneySum_assoc`,
  `Work.Thom.chernClass_BundleIso`), and the line-bundle case
  `∀ N, WhitneySumFormula 1 N` computes `c_k(ℓ ⊕ (Q ⊕ π^*Z₂)) = Σ_{i+j=k} c_i(ℓ) c_j(Q ⊕ π^*Z₂)`;
* **induct on the rank of `Q`**: expanding `c_j(Q ⊕ π^*Z₂)` by the induction hypothesis, the two
  sides of the formula are the two groupings of the *triple* convolution
  `Σ_{i+j+l=k} c_i(ℓ) c_j(Q) c_l(π^*Z₂)`, whose equality is the associativity of the convolution
  (`Work.LerayHirsch.convSeries_assoc`) together with the expansion of `c_i(ℓ ⊕ Q)`
  (`∀ p, WhitneySumFormula 1 p`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The unit law of the graded product in its first variable -/

/-- **The left unit law of the graded product**: `1 ⌣ y = y`, with the degree bookkeeping
`2*(0+k) = 2*k`. -/
theorem cohTransport_cupChern_one_left (k : ℕ) (y : Coh ℤ (2 * k) B) :
    cohTransport (by omega : 2 * (0 + k) = 2 * k)
        (Work.Whitney.cupChern 0 k (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) y) = y := by
  have h1 : Work.Whitney.cupChern 0 k (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) y
      = cohTransport (by omega : 2 * k = 2 * (0 + k)) y := by
    rw [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_one_left, eqRec_eq_cohTransport,
      Work.Whitney.cohTransport_trans]
  rw [h1, Work.Whitney.cohTransport_trans]
  exact (cohTransport_congr_proof _ (rfl : 2 * k = 2 * k)).trans (cohTransport_rfl y)

/-! ## Congruence of the right-hand side in its first argument -/

/-- The right-hand side of the Whitney formula only depends on the Chern classes of its first
argument. -/
theorem chernProductSum_congr_first {m₁ m₁' m₂ : ℕ} {ι₁ ι₁' ι₂ : Type} [Fintype ι₁]
    [Fintype ι₁'] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₁' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁')) ι₁')
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ)
    (h : ∀ i, chernClass m₁ i Z₁ = chernClass m₁' i Z₁') :
    Work.Whitney.chernProductSum Z₁ Z₂ k = Work.Whitney.chernProductSum Z₁' Z₂ k := by
  rw [Work.Whitney.chernProductSum, Work.Whitney.chernProductSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hik : i ≤ k
  · rw [dif_pos hik, dif_pos hik]
    congr 1
    rw [Work.Whitney.chernSummand_def, Work.Whitney.chernSummand_def, h i]
  · rw [dif_neg hik, dif_neg hik]

/-! ## The rank-`0` base case -/

/-- **The right-hand side collapses when the first bundle has rank zero**: `c_i(Z₁) = 0` for
`i ≥ 1` and `c_0(Z₁) = 1`, so only the `i = 0` summand survives, and it is `c_k(Z₂)`. -/
theorem chernProductSum_rank_zero_first {m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ) :
    Work.Whitney.chernProductSum Z₁ Z₂ k = chernClass m₂ k Z₂ := by
  have hzero : (if _h : (0 : ℕ) ≤ k then
        cohTransport (by omega : 2 * (0 + (k - 0)) = 2 * k)
          (Work.Whitney.cupChern 0 (k - 0) (chernClass 0 0 Z₁) (chernClass m₂ (k - 0) Z₂))
      else 0) = chernClass m₂ k Z₂ := by
    rw [dif_pos (Nat.zero_le k), chernClass_zero_eq_oneH]
    rw [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_one_left, eqRec_eq_cohTransport,
      Work.Whitney.cohTransport_trans, Work.Whitney.cohTransport_trans]
    exact (cohTransport_congr_proof _ (rfl : 2 * k = 2 * k)).trans (cohTransport_rfl _)
  rw [Work.Whitney.chernProductSum]
  refine (Finset.sum_eq_single 0 ?_ ?_).trans hzero
  · intro a ha ha0
    rw [dif_pos (by have := Finset.mem_range.mp ha; omega), Work.Whitney.chernSummand_def,
      chernClass_rank_zero_of_ne Z₁ ha0, cupChern_zero_left, Work.Thom.cohTransport_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0

/-- **The Whitney sum formula for a rank-`0` first summand.** -/
theorem whitneySumFormula_rank_zero (m₂ : ℕ) : WhitneySumFormula 0 m₂ := by
  intro B _ ι₁ ι₂ _ _ Z₁ Z₂ k
  obtain ⟨e₁⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm (Z₁ := Z₁) (Z₂ := Z₂)
  obtain ⟨e₂⟩ := Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton (𝕜 := ℂ) (B := B)
    (F₁ := EuclideanSpace ℂ (Fin m₂)) (F₂ := EuclideanSpace ℂ (Fin 0))
    (F := EuclideanSpace ℂ (Fin (m₂ + 0))) (Work.Whitney.sumFibreC m₂ 0) Z₂ Z₁
  exact (Work.Whitney.chernClass_BundleIso_of_eq (by omega : 0 + m₂ = m₂ + 0) _ _ e₁ k).trans
    ((Work.Whitney.chernClass_BundleIso_of_eq (by omega : m₂ + 0 = m₂) _ _ e₂ k).trans
      (chernProductSum_rank_zero_first Z₁ Z₂ k).symm)

/-! ## `WhitneySumFormula` as an identity of Chern series -/

/-- **The Whitney formula means that the Chern series of the sum is the convolution of the Chern
series of the summands.** -/
theorem chernSeries_whitneySum_eq_convSeries {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (h : ∀ k, chernClass (m₁ + m₂) k (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.chernProductSum Z₁ Z₂ k) :
    chernSeries (Work.Whitney.whitneySum Z₁ Z₂) = convSeries (chernSeries Z₁) (chernSeries Z₂) := by
  funext k
  exact (h k).trans (chernProductSum_eq_convSeries Z₁ Z₂ k)

/-! ## The induction step -/

/-- **The induction step**: the Whitney formula in rank `p` implies it in rank `p + 1`. -/
theorem whitneySumFormula_succ (p : ℕ)
    (hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z)
    (hSplit : ∀ {m' : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m' + 1))) ι), SplitsOverProj Z)
    (hLine : ∀ N : ℕ, WhitneySumFormula 1 N)
    (IH : ∀ m₂, WhitneySumFormula p m₂) :
    ∀ m₂, WhitneySumFormula (p + 1) m₂ := by
  intro m₂ B _ ι₁ ι₂ _ _ Z₁ Z₂ k
  obtain ⟨Q, ⟨e⟩⟩ := hSplit (m' := p) Z₁
  -- pull back to the projectivisation
  refine (CohMap_projMap_injective_of_LerayHirschFull (m := p + 1) (by omega) Z₁ (hLH Z₁)
    (2 * k)) ?_
  rw [← Work.Thom.chernClass_comap, Work.Whitney.whitneySum_bundleComap,
    Work.Whitney.chernProductSum_CohMap]
  -- now over `ProjSpace Z₁`
  set W : VectorBundleCore ℂ (ProjSpace Z₁) (EuclideanSpace ℂ (Fin m₂)) ι₂ :=
    Work.Thom.bundleComap Z₂ (projMap Z₁) with hW
  -- step 1: replace `π^*Z₁` by `ℓ ⊕ Q`
  have hstep1 : chernClass ((p + 1) + m₂) k
        (Work.Whitney.whitneySum (Work.Thom.bundleComap Z₁ (projMap Z₁)) W)
      = chernClass ((1 + p) + m₂) k
        (Work.Whitney.whitneySum (Work.Whitney.whitneySum (tautLine Z₁) Q) W) := by
    obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_first (Z₁ := Work.Thom.bundleComap Z₁ (projMap Z₁))
      (Z₁' := Work.Whitney.whitneySum (tautLine Z₁) Q) (Z₂ := W) e
    exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : (p + 1) + m₂ = (1 + p) + m₂) _ _ e' k
  rw [hstep1]
  -- step 2: reassociate
  have hstep2 : chernClass ((1 + p) + m₂) k
        (Work.Whitney.whitneySum (Work.Whitney.whitneySum (tautLine Z₁) Q) W)
      = chernClass (1 + (p + m₂)) k
        (Work.Whitney.whitneySum (tautLine Z₁) (Work.Whitney.whitneySum Q W)) := by
    obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_assoc (tautLine Z₁) Q W
    exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : (1 + p) + m₂ = 1 + (p + m₂)) _ _ e' k
  rw [hstep2]
  -- step 3: the line-bundle case
  have hstep3 : chernClass (1 + (p + m₂)) k
        (Work.Whitney.whitneySum (tautLine Z₁) (Work.Whitney.whitneySum Q W))
      = Work.Whitney.chernProductSum (tautLine Z₁) (Work.Whitney.whitneySum Q W) k :=
    hLine (p + m₂) (tautLine Z₁) (Work.Whitney.whitneySum Q W) k
  rw [hstep3]
  -- step 4: the algebraic step (associativity of the convolution)
  have hstep4 : Work.Whitney.chernProductSum (tautLine Z₁) (Work.Whitney.whitneySum Q W) k
      = Work.Whitney.chernProductSum (Work.Whitney.whitneySum (tautLine Z₁) Q) W k := by
    have hQWs : chernSeries (Work.Whitney.whitneySum Q W)
        = convSeries (chernSeries Q) (chernSeries W) :=
      chernSeries_whitneySum_eq_convSeries Q W (fun j => IH m₂ Q W j)
    have hlQ : convSeries (chernSeries (tautLine Z₁)) (chernSeries Q)
        = chernSeries (Work.Whitney.whitneySum (tautLine Z₁) Q) :=
      (chernSeries_whitneySum_eq_convSeries (tautLine Z₁) Q
        (fun j => hLine p (tautLine Z₁) Q j)).symm
    rw [chernProductSum_eq_convSeries, hQWs, ← convSeries_assoc, hlQ,
      ← chernProductSum_eq_convSeries]
  rw [hstep4]
  -- step 5: `whitneySum ℓ Q ≅ π^*Z₁`
  refine (chernProductSum_congr_first (Work.Whitney.whitneySum (tautLine Z₁) Q)
    (Work.Thom.bundleComap Z₁ (projMap Z₁)) W k ?_)
  intro i
  exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : 1 + p = p + 1)
    (Work.Whitney.whitneySum (tautLine Z₁) Q) (Work.Thom.bundleComap Z₁ (projMap Z₁)) e.symm i

/-! ## The assembly statement -/

/-- **The Whitney sum formula from Leray–Hirsch, the splitting principle and the line-bundle
case.** -/
theorem whitneySumFormulaOfLerayHirsch : Work.LerayHirsch.WhitneySumFormulaFromLerayHirsch := by
  intro hLH hSplit hLine m₁
  induction m₁ using Nat.strong_induction_on with
  | _ m ih =>
    intro m₂
    rcases m with _ | _ | p
    · exact whitneySumFormula_rank_zero m₂
    · exact hLine m₂
    · exact whitneySumFormula_succ (p + 1) hLH hSplit hLine (ih (p + 1) (by omega)) m₂

end

end Work.LerayHirsch
