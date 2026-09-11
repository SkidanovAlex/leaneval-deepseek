import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsTPrime
import Submission.ProfileSum
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiDeep2
import Submission.MultiFrag1
import Submission.MultiFrag2
import Submission.MultiPre
import Submission.MultiMass
import Submission.MultiZ
import Submission.MultiAdd
import Submission.MultiMLM

/-!
# multi'-w assembly (paper Theorem multi'-w): no (eNμ)-cover ⟹ Esup ≥ 10^{-11}.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep

variable {X : Type*} [Fintype X]

namespace MSys

/-- weightM as a plain sum over x (valid when all levels of S' are ≤ τ) -/
lemma weightM_eq_sum_x (N0 : MSys X) (S' W : X → ℕ) (hS' : S' ∈ N0.F)
    (hB : N0.LevelBounded) :
    N0.weightM S' W = ∑ x : X, (min (W x) (S' x) : ℝ) * wlev (N0.lv S' x) := by
  classical
  have hτ : ∀ x : X, N0.lv S' x ≤ N0.τ := hB S' hS'
  unfold weightM countAt
  calc
    (∑ j ∈ Finset.range (N0.τ + 1), ((∑ x : X, if N0.lv S' x = j then min (W x) (S' x) else 0 : ℕ) : ℝ) * wlev j)
        = (∑ j ∈ Finset.range (N0.τ + 1), ∑ x : X, ((if N0.lv S' x = j then min (W x) (S' x) else 0 : ℕ) : ℝ) * wlev j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Nat.cast_sum]
          rw [Finset.sum_mul]
    _ = ∑ x : X, (min (W x) (S' x) : ℝ) * wlev (N0.lv S' x) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          have hsum : (∑ j ∈ Finset.range (N0.τ + 1),
              ((if N0.lv S' x = j then min (W x) (S' x) else 0 : ℕ) : ℝ) * wlev j)
              = (min (W x) (S' x) : ℝ) * wlev (N0.lv S' x) := by
            calc
              (∑ j ∈ Finset.range (N0.τ + 1), ((if N0.lv S' x = j then min (W x) (S' x) else 0 : ℕ) : ℝ) * wlev j)
                  = (∑ j ∈ Finset.range (N0.τ + 1), if N0.lv S' x = j then (min (W x) (S' x) : ℝ) * wlev j else 0) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    by_cases hl : N0.lv S' x = j <;> simp [hl]
              _ = (min (W x) (S' x) : ℝ) * wlev (N0.lv S' x) := by
                    rw [Finset.sum_ite_eq]
                    have hmem : N0.lv S' x ∈ Finset.range (N0.τ + 1) := by simpa using hτ x
                    simp [hmem]
          simpa using hsum

/-- a member's lamSum is at most the sup over the family -/
lemma le_supLam {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} (m : X → ℕ)
    {S : X → ℕ} (hS : S ∈ Λ) : lamSum lam S m ≤ supLam Λ lam m := by
  classical
  unfold supLam
  by_cases h : (Λ.image (fun S : X → ℕ => lamSum lam S m)).Nonempty
  · simp [h]
    exact Finset.le_max' (Λ.image (fun S : X → ℕ => lamSum lam S m)) (lamSum lam S m)
      (Finset.mem_image.mpr ⟨S, hS, rfl⟩)
  · exfalso
    exact h ⟨lamSum lam S m, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩

/-- the processed value is at most the original sup (domination from preprocessing) -/
lemma procValM_le_lamSup (N0 : MSys X) (F : Finset (X → ℕ))
    (lam : (X → ℕ) → X → ℝ)
    (hdom : ∀ S' ∈ N0.F, ∃ S ∈ F, subM S' S ∧ ∀ x, 0 < S' x → lam S x ≥ wlev (N0.lv S' x))
    (hlam0 : ∀ S ∈ F, ∀ x, 0 ≤ lam S x) (hB : N0.LevelBounded) (W : X → ℕ) :
    N0.procValM W ≤ supLam F lam W := by
  classical
  unfold procValM
  refine mSup_le_of_forall (v := fun S' : X → ℕ => N0.weightM S' W) N0 (c := supLam F lam W) ?_ ?_
  · intro S' hS'
    rcases hdom S' hS' with ⟨S, hSF, hS'S, hdomx⟩
    have hle1 : N0.weightM S' W ≤ lamSum lam S W := by
      calc
        N0.weightM S' W = ∑ x : X, (min (W x) (S' x) : ℝ) * wlev (N0.lv S' x) :=
          N0.weightM_eq_sum_x S' W hS' hB
        _ ≤ ∑ x : X, (min (W x) (S' x) : ℝ) * lam S x := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases hpos : 0 < S' x
              · have hle : wlev (N0.lv S' x) ≤ lam S x := hdomx x hpos
                have hmin0 : (0 : ℝ) ≤ (min (W x) (S' x) : ℝ) := by positivity
                exact mul_le_mul_of_nonneg_left hle hmin0
              · have hSx0 : S' x = 0 := by omega
                simp [hSx0]
        _ ≤ lamSum lam S W := by
              unfold lamSum
              apply Finset.sum_le_sum
              intro x hx
              have hmin : min (W x) (S' x) ≤ W x := min_le_left _ _
              have hlam0x : 0 ≤ lam S x := hlam0 S hSF x
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) hlam0x
    exact le_trans hle1 (le_supLam (Λ := F) W hSF)
  · exact supLam_nonneg (Λ := F) (lam := lam) (m := W) hlam0

/-- if a processed family is mSmall then the original is: transfer of the no-cover assumption -/
lemma mSmall_trim_of_mSmall {F G : Set (X → ℕ)} (c : ℝ) (p : X → ℝ)
    (htrim : ∀ S ∈ F, ∃ S' ∈ G, subM S' S)
    (hG : mSmall c p G) : mSmall c p F := by
  classical
  rcases hG with ⟨𝓖, hcov, hcost⟩
  refine ⟨𝓖, ?_, hcost⟩
  intro S hS
  rcases htrim S hS with ⟨S', hS'G, hS'S⟩
  rcases hcov S' hS'G with ⟨U, hU, hUS'⟩
  exact ⟨U, hU, subM_trans hUS' hS'S⟩

/-- deep: no-cover for the processed family gives every cover by min-fragments cost > 1/2 -/
lemma cover_cost_gt_half_of_not_mSmall (N0 : MSys X) (W : X → ℕ) (c : ℝ) (p : X → ℝ)
    (hB : N0.LevelBounded) (hnot : ¬ mSmall c p (N0.F : Set (X → ℕ))) :
    (2 : ℝ)⁻¹ < N0.coverCostM c p W hB := by
  classical
  by_contra hle
  apply hnot
  refine ⟨N0.coverFinsetM W hB, N0.coverFinsetM_cover W hB, ?_⟩
  unfold coverCostM at hle
  exact le_of_not_gt hle


/-- good multisets of exact size M -/
noncomputable def goodMsetsM (N0 : MSys X) (M : ℕ) : Finset (X → ℕ) :=
  (msizeExact (X := X) M).filter (fun W : X → ℕ => N0.GoodM ((10 : ℝ) ^ 10)⁻¹ W)

/-- expected processed value over multisets of size M -/
noncomputable def Eproc (M : ℕ) (μ : X → ℝ) (N0 : MSys X) : ℝ :=
  ∑ W ∈ msizeExact (X := X) M, mass (X := X) M μ W * N0.procValM W

/-- expected sup dominates expected processed value (pointwise domination) -/
lemma Esup_ge_Eproc (N0 : MSys X) (F : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (M : ℕ) (μ : X → ℝ) (hμ0 : ∀ x : X, 0 ≤ μ x)
    (hdom : ∀ S' ∈ N0.F, ∃ S ∈ F, subM S' S ∧ ∀ x, 0 < S' x → lam S x ≥ wlev (N0.lv S' x))
    (hlam0 : ∀ S ∈ F, ∀ x, 0 ≤ lam S x) (hB : N0.LevelBounded) :
    Eproc M μ N0 ≤ Esup (X := X) M μ F lam := by
  classical
  unfold Eproc Esup
  apply Finset.sum_le_sum
  intro W hW
  have hm0 : 0 ≤ mass (X := X) M μ W := mass_nonneg' hμ0 M W
  have hle := procValM_le_lamSup N0 F lam hdom hlam0 hB W
  exact mul_le_mul_of_nonneg_left hle hm0

/-- total mass of size-M multisets is 1 when μ is a probability -/
lemma mass_total_eq_one (M : ℕ) (μ : X → ℝ) (hμ1 : (∑ x : X, μ x) = 1) :
    (∑ W ∈ msizeExact (X := X) M, mass (X := X) M μ W) = 1 := by
  rw [mass_sum_eq_pow]
  simp [hμ1]

/-- Eproc ≥ θ·(1 − Σ_{bad} mass) -/
lemma Eproc_ge_theta_good (M : ℕ) (μ : X → ℝ) (N0 : MSys X)
    (hμ0 : ∀ x : X, 0 ≤ μ x)
    (hproc0 : ∀ W, 0 ≤ N0.procValM W) :
    ((10 : ℝ) ^ 10)⁻¹ * (∑ W ∈ goodMsetsM N0 M, mass (X := X) M μ W)
      ≤ Eproc M μ N0 := by
  classical
  unfold Eproc goodMsetsM
  calc
    ((10 : ℝ) ^ 10)⁻¹ * (∑ W ∈ (msizeExact (X := X) M).filter (fun W => N0.GoodM ((10 : ℝ) ^ 10)⁻¹ W),
        mass (X := X) M μ W)
        ≤ ∑ W ∈ (msizeExact (X := X) M).filter (fun W => N0.GoodM ((10 : ℝ) ^ 10)⁻¹ W),
            mass (X := X) M μ W * N0.procValM W := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro W hW
          have hg : N0.GoodM ((10 : ℝ) ^ 10)⁻¹ W := (Finset.mem_filter.mp hW).2
          unfold GoodM at hg
          have hm0 : 0 ≤ mass (X := X) M μ W := mass_nonneg' hμ0 M W
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hg hm0
    _ ≤ (∑ W ∈ msizeExact (X := X) M, mass (X := X) M μ W * N0.procValM W) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro W hW
            exact (Finset.mem_filter.mp hW).1
          · intro W hW hin
            have hp0 : 0 ≤ N0.procValM W := hproc0 W
            exact mul_nonneg (mass_nonneg' hμ0 M W) hp0
    _ = Eproc M μ N0 := by rfl

/-- procValM is nonnegative -/
lemma procValM_nonneg (N0 : MSys X) (W : X → ℕ) : 0 ≤ N0.procValM W := by
  unfold procValM
  exact mSup_nonneg N0 (fun S : X → ℕ => N0.weightM S W) (by
    intro S hS
    exact N0.weightM_nonneg S W)

/-- expected sup over the ORIGINAL family (multi'-w; assembly of the deep machinery) -/
theorem multi'_w (N : ℕ) (μ : X → ℝ) (F : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ S ∈ F, ∀ x : X, 0 ≤ lam S x)
    (htot1 : ∀ S ∈ F, 1 ≤ lamSum lam S S)
    (hnot : ¬ mSmall (eN N) μ (F : Set (X → ℕ))) :
    ((10 : ℝ) ^ 11)⁻¹ ≤ Esup (X := X) (Kbig * N) μ F lam := by
  classical
  let Fs : Set (X → ℕ) := F
  have hFin : Set.Finite Fs := by
    exact F.finite_toSet
  rcases MSys.theorem_preprocessM Fs lam hFin (by intro S hS x; exact hlam0 S (by simpa [Fs] using hS) x)
    (by intro S hS; simpa [Fs, mwtot, lamSum] using htot1 S (by simpa [Fs] using hS)) with ⟨N0, hFB, hTot, hLeg, htrim, hdom⟩
  have hnotN : ¬ mSmall (eN N) μ (N0.F : Set (X → ℕ)) := by
    intro hN
    exact hnot (mSmall_trim_of_mSmall (c := eN N) (p := μ) (F := Fs) (G := N0.F) (by
      intro S hS
      exact htrim S (by simpa [Fs] using hS)) hN)
  have hμle : (∑ x : X, μ x) ≤ 1 := by rw [hμ1]
  have hML := theorem_MLM N μ N0 hμ0 hμle hFB hTot hLeg
  -- hML : Σ over badMsetsM mass·coverCostEN ≤ 1/10
  have hbadsum : (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) ≤ (1 / 5 : ℝ) := by
    have hhalf : (1 / 2 : ℝ) * (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W)
        ≤ (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W * N0.coverCostM (eN N) μ W hFB) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro W hW
      have hgt := cover_cost_gt_half_of_not_mSmall N0 W (eN N) μ hFB hnotN
      have hgt' : (1 / 2 : ℝ) < N0.coverCostM (eN N) μ W hFB := by
        have hc : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
        rwa [hc] at hgt
      have hm0 : 0 ≤ mass (X := X) (Kbig * N) μ W := mass_nonneg' hμ0 (Kbig * N) W
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_of_lt hgt') hm0
    have hML' : (∑ W ∈ badMsetsM N0 (Kbig * N),
        mass (X := X) (Kbig * N) μ W * N0.coverCostM (eN N) μ W hFB) ≤ (1 / 10 : ℝ) := by
      simpa [coverCostEN] using hML
    linarith
  -- total mass over size M is 1
  have htotmass : (∑ W ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ W) = 1 :=
    mass_total_eq_one (Kbig * N) μ hμ1
  have hgoodmass : (4 / 5 : ℝ) ≤
      ∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W := by
    have hgood : (msizeExact (X := X) (Kbig * N)).filter
          (fun W : X → ℕ => ¬ N0.BadM ((10 : ℝ) ^ 10)⁻¹ W)
        = goodMsetsM N0 (Kbig * N) := by
      ext W
      rw [goodMsetsM]
      rw [Finset.mem_filter]
      rw [Finset.mem_filter]
      unfold BadM GoodM
      constructor
      · intro h
        exact ⟨h.1, le_of_not_gt h.2⟩
      · intro h
        exact ⟨h.1, not_lt_of_ge h.2⟩
    have hsplit : (∑ W ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ W)
        = (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W)
          + (∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := by
      have h1 : (∑ W ∈ (msizeExact (X := X) (Kbig * N)).filter
            (fun W : X → ℕ => N0.BadM ((10 : ℝ) ^ 10)⁻¹ W), mass (X := X) (Kbig * N) μ W)
          = (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := rfl
      have h2 : (∑ W ∈ (msizeExact (X := X) (Kbig * N)).filter
            (fun W : X → ℕ => ¬ N0.BadM ((10 : ℝ) ^ 10)⁻¹ W), mass (X := X) (Kbig * N) μ W)
          = (∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := by
        rw [hgood]
      calc
        (∑ W ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ W)
            = (∑ W ∈ (msizeExact (X := X) (Kbig * N)).filter
                  (fun W : X → ℕ => N0.BadM ((10 : ℝ) ^ 10)⁻¹ W), mass (X := X) (Kbig * N) μ W)
              + (∑ W ∈ (msizeExact (X := X) (Kbig * N)).filter
                  (fun W : X → ℕ => ¬ N0.BadM ((10 : ℝ) ^ 10)⁻¹ W), mass (X := X) (Kbig * N) μ W) := by
                  rw [Finset.sum_filter_add_sum_filter_not]
        _ = (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W)
            + (∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := by rw [h1, h2]
    have hsum : (1 : ℝ) = (∑ W ∈ badMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W)
          + (∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := by
      rw [← hsplit]
      exact htotmass.symm
    linarith
  have hge := Eproc_ge_theta_good (Kbig * N) μ N0 hμ0 (procValM_nonneg N0)
  have hthetamul : ((10 : ℝ) ^ 10)⁻¹ * (4 / 5 : ℝ) ≤
      ((10 : ℝ) ^ 10)⁻¹ * (∑ W ∈ goodMsetsM N0 (Kbig * N), mass (X := X) (Kbig * N) μ W) := by
    exact mul_le_mul_of_nonneg_left hgoodmass (by positivity)
  have hEproc : ((10 : ℝ) ^ 10)⁻¹ * (4 / 5 : ℝ) ≤ Eproc (X := X) (Kbig * N) μ N0 :=
    le_trans hthetamul hge
  have hE10 : ((10 : ℝ) ^ 11)⁻¹ ≤ Eproc (X := X) (Kbig * N) μ N0 := by
    have hpow : ((10 : ℝ) ^ 10)⁻¹ * (4 / 5 : ℝ) = ((10 : ℝ) ^ 11)⁻¹ * 8 := by
      have h10 : (10 : ℝ) ^ 11 = (10 : ℝ) ^ 10 * 10 := by
        rw [pow_succ']
        ring
      rw [h10]
      field_simp [show (10 : ℝ) ^ 10 ≠ 0 by positivity]
      ring
    have h8 : ((10 : ℝ) ^ 11)⁻¹ ≤ ((10 : ℝ) ^ 11)⁻¹ * 8 := by
      have h8' : (1 : ℝ) ≤ 8 := by norm_num
      have hc0 : 0 ≤ ((10 : ℝ) ^ 11)⁻¹ := by positivity
      simpa using (mul_le_mul_of_nonneg_left h8' hc0)
    have h8'' : ((10 : ℝ) ^ 11)⁻¹ * 8 ≤ Eproc (X := X) (Kbig * N) μ N0 := by
      simpa [hpow] using hEproc
    exact le_trans h8 h8''
  have hEproc_le_Esup : Eproc (X := X) (Kbig * N) μ N0 ≤ Esup (X := X) (Kbig * N) μ F lam :=
    Esup_ge_Eproc N0 F lam (Kbig * N) μ hμ0 (by
      intro S' hS'
      rcases hdom S' hS' with ⟨S, hSF, h1, h2⟩
      exact ⟨S, by simpa [Fs] using hSF, h1, h2⟩) hlam0 hFB
  exact le_trans hE10 hEproc_le_Esup

end MSys


end Multi
end Submission
