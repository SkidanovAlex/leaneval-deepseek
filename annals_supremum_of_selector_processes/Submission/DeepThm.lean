import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsT
import Submission.ObsTPrime
import Submission.Nice
import Submission.ML
import Submission.Binom
import Submission.Binom2

/-!
# Theorem 5.7'' (nice version): assembly from Lemma ML.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace DeepThm

open Frame
open ML
open Sel
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-- the number of w-subsets of X equals (n choose w) -/
lemma levelFinset_card (w : ℕ) (hw : w ≤ Fintype.card X) :
    (Binom.levelFinset X w).card = (Fintype.card X).choose w := by
  classical
  exact Binom.levelFinset_card (X := X) w hw

/-- the w-subsets form a nonempty Finset when w ≤ n -/
lemma levelFinset_nonempty (w : ℕ) (hw : w ≤ Fintype.card X) :
    (Binom.levelFinset X w).Nonempty := by
  classical
  exact Binom.levelFinset_nonempty (X := X) w hw

/-- avgOver = (Σ over w-subsets)/(their number) -/
lemma avgOver_eq (v : Set X → ℝ) (w : ℕ) (hw : w ≤ Fintype.card X) :
    Sys.avgOver v w = (∑ W ∈ Binom.levelFinset X w, v W) /
      (Binom.levelFinset X w).card := by
  classical
  unfold Sys.avgOver
  have hs : (Finset.univ.filter (fun W : Set X => W.ncard = w)).Nonempty := by
    exact Binom.levelFinset_nonempty (X := X) w hw
  have hs' : ((Finset.univ.filter (fun W : Set X => W.ncard = w)).card : ℝ) ≠ 0 := by
    have hc : (Finset.univ.filter (fun W : Set X => W.ncard = w)).card =
        (Fintype.card X).choose w := Binom.levelFinset_card (X := X) w hw
    rw [hc]
    exact_mod_cast (ne_of_gt (Nat.choose_pos hw))
  simp [hs, hs', Binom.levelFinset]

/-- not-p-small ⟹ ∅ ∉ F (under total-weight bound) -/
lemma not_pSmall_empty_mem (N : Sys X) (p : ℝ) (hTot : N.TotBound)
    (hnot : ¬ pSmall p N.F) :
    (∅ : Set X) ∉ N.F := by
  intro hmem
  have htot : ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight (∅ : Set X) := hTot ∅ hmem
  have hz : N.totalWeight (∅ : Set X) = 0 := by
    classical
    simp [Sys.totalWeight, Sys.weight]
  rw [hz] at htot
  norm_num at htot

/-- not-p-small ⟹ (1/2) < n·p -/
lemma not_pSmall_np (N : Sys X) (n : ℕ) (p : ℝ) (hn : Fintype.card X = n)
    (hTot : N.TotBound) (hnot : ¬ pSmall p N.F) :
    (2 : ℝ)⁻¹ < (n : ℝ) * p := by
  have hnmem : (∅ : Set X) ∉ N.F := not_pSmall_empty_mem N p hTot hnot
  have h := pSmall.not_of_np (p := p) (𝓕 := N.F) hnot hnmem
  simpa [hn] using h

/-- not-p-small ⟹ F is nonempty -/
lemma not_pSmall_nonempty (N : Sys X) (p : ℝ) (hnot : ¬ pSmall p N.F) : N.F.Nonempty := by
  classical
  by_contra h
  have hF : N.F = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    exact h
  exact hnot (by simpa [hF] using (pSmall.empty : pSmall p (∅ : Set (Set X))))

/-- N.weight is nonnegative -/
lemma weight_nonneg (N : Sys X) (S A : Set X) : 0 ≤ N.weight S A := by
  unfold Sys.weight
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (by exact_mod_cast Nat.zero_le ((A ∩ N.levelSet S j).ncard)) (wlev_nonneg j)

/-- procVal(X) ≥ 10^{-8} -/
lemma procVal_univ_ge (N : Sys X) (p : ℝ) (hTot : N.TotBound) (hnot : ¬ pSmall p N.F) :
    ((10 : ℝ) ^ 8)⁻¹ ≤ N.procVal Set.univ := by
  classical
  rcases not_pSmall_nonempty N p hnot with ⟨S, hS⟩
  have htot : ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight S := hTot S hS
  have hEq : Set.univ ∩ S = S := by ext x; simp
  have hle : N.totalWeight S ≤ N.procVal Set.univ := by
    unfold Sys.totalWeight Sys.procVal
    have h' := le_famSup (v := fun T : Set X => N.weight T (Set.univ ∩ T)) hS
    simpa [hEq] using h'
  exact le_trans htot hle

lemma cover_cost_gt (N : Sys X) (W : Set X) (hB : N.LevelBounded) (p : ℝ)
    (hnot : ¬ pSmall p N.F) :
    (2 : ℝ)⁻¹ < totalCost p (N.coverFinset W hB) := by
  by_contra hle
  have hcover : ∀ S ∈ N.F, ∃ U ∈ N.coverFinset W hB, U ⊆ S := N.coverFinset_cover W hB
  have hpSmall : pSmall p N.F := by
    refine ⟨N.coverFinset W hB, ?_, ?_⟩
    · intro S hS
      rcases hcover S hS with ⟨U, hU, hUS⟩
      exact ⟨U, hU, hUS⟩
    · exact le_of_not_gt hle
  exact hnot hpSmall

/-- procVal ≥ 10^{-10} on good W -/
lemma good_val (N : Sys X) (W : Set X) (hgood : ¬ N.Bad ((10 : ℝ) ^ 10)⁻¹ W) :
    ((10 : ℝ) ^ 10)⁻¹ ≤ N.procVal W := by
  unfold Sys.Bad at hgood
  exact le_of_not_gt hgood

/-- the bad w-subsets are contained in the level w-subsets -/
lemma badSubsets_subset_level (N : Sys X) (w : ℕ) :
    badSubsets N w ⊆ Binom.levelFinset X w := by
  intro W hW
  simp [badSubsets, Binom.levelFinset] at hW ⊢
  exact hW.1

/-- total over w-subsets = bad part + good part; good part ≥ (#good)·θ -/
lemma sum_ge (N : Sys X) (v : Set X → ℝ) (w : ℕ) (θ : ℝ)
    (hgood : ∀ W ∈ Binom.levelFinset X w, ¬ N.Bad θ W → θ ≤ v W)
    (hbadnonneg : ∀ W ∈ Binom.levelFinset X w, N.Bad θ W → 0 ≤ v W) :
    (((Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W)).card : ℝ) * θ ≤
      ∑ W ∈ Binom.levelFinset X w, v W := by
  classical
  have hsplit : (∑ W ∈ Binom.levelFinset X w, v W) =
      (∑ W ∈ (Binom.levelFinset X w).filter (fun W => N.Bad θ W), v W) +
        (∑ W ∈ (Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W), v W) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Binom.levelFinset X w)
      (p := fun W => N.Bad θ W) (f := fun W => v W)]
  have h1 : 0 ≤ ∑ W ∈ (Binom.levelFinset X w).filter (fun W => N.Bad θ W), v W := by
    exact Finset.sum_nonneg (by intro W hW; exact hbadnonneg W (Finset.mem_filter.mp hW).1 (Finset.mem_filter.mp hW).2)
  have h2 : (((Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W)).card : ℝ) * θ ≤
      ∑ W ∈ (Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W), v W := by
    have hsum : (∑ W ∈ (Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W), θ) ≤
        ∑ W ∈ (Binom.levelFinset X w).filter (fun W => ¬ N.Bad θ W), v W := by
      exact Finset.sum_le_sum (by intro W hW; exact hgood W (Finset.mem_filter.mp hW).1 (Finset.mem_filter.mp hW).2)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    simpa [mul_comm] using hsum
  nlinarith

/-- if w = |X| then the only w-subset is univ -/
lemma levelFinset_self (X : Type*) [Fintype X] :
    (Binom.levelFinset X (Fintype.card X)) = {Set.univ} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · simp [Binom.levelFinset]
  · intro W hW
    have hc : W.ncard = Fintype.card X := by simpa [Binom.levelFinset] using hW
    have hcardW : W.toFinset.card = (Finset.univ : Finset X).card := by
      rw [ncard_eq_toFinset_card'] at hc
      simpa using hc
    have hEqF : W.toFinset = (Finset.univ : Finset X) := by
      exact Finset.eq_of_subset_of_card_le (by intro x hx; simp) (le_of_eq hcardW.symm)
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have : x ∈ (W.toFinset : Set X) := by
      rw [hEqF]
      simp
    simpa using this

/-- sum over a singleton Finset -/
lemma sum_singleton {α : Type*} (f : α → ℝ) (T : α) :
    (∑ W ∈ ({T} : Finset α), f W) = f T := by
  simp

theorem nice57 (p : ℝ) (J : ℕ) (N : Sys X)
    (hJ : 10 ^ 20 ≤ J) (hp0 : 0 < p) (hp1 : p < 1)
    (hB : N.LevelBounded) (hTot : N.TotBound) (hLeg : N.FLegal)
    (hnot : ¬ pSmall p N.F) :
    ((10 : ℝ) ^ 11)⁻¹ ≤ Sys.avgOver (fun W : Set X => N.procVal W)
      (Sys.wSize J (Fintype.card X) p) := by
  classical
  set n : ℕ := Fintype.card X with hn
  set w0 : ℕ := Sys.wSize J n p with hw0
  have hw0le : w0 ≤ n := by
    rw [hw0]
    unfold Sys.wSize
    exact min_le_left n ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat
  have hw0leX : w0 ≤ Fintype.card X := by simpa [n] using hw0le
  have hC : ((Binom.levelFinset X w0).card : ℝ) = (n.choose w0 : ℝ) := by
    have hc : (Binom.levelFinset X w0).card = n.choose w0 := by
      calc
        (Binom.levelFinset X w0).card = (Fintype.card X).choose w0 := levelFinset_card w0 hw0leX
        _ = n.choose w0 := by rw [← hn]
    exact_mod_cast hc
  have hnp : (2 : ℝ)⁻¹ ≤ (n : ℝ) * p := by
    exact le_of_lt (not_pSmall_np N n p hn hTot hnot)
  let θ : ℝ := ((10 : ℝ) ^ 10)⁻¹
  by_cases hwn : w0 < n
  · -- main case w0 < n
    have hw' : w0 = ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat := by
      have : ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat ≤ n := by
        by_contra h
        have hlt : n < ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat := lt_of_not_ge h
        have hw0eq : w0 = n := by
          rw [hw0]
          unfold Sys.wSize
          exact min_eq_left (le_of_lt hlt)
        omega
      rw [hw0]
      unfold Sys.wSize
      exact min_eq_right this
    have hML := ML.theorem_ML p J N w0 n hJ hp0 hp1 hn hw' hnp hwn hB hTot hLeg
    -- E = (Σ_all)/C
    have hE : Sys.avgOver (fun W : Set X => N.procVal W) (Sys.wSize J (Fintype.card X) p)
        = (∑ W ∈ Binom.levelFinset X w0, N.procVal W) / ((Binom.levelFinset X w0).card) := by
      have hsz : Sys.wSize J (Fintype.card X) p = w0 := by
        rw [← hn]
      rw [hsz]
      rw [avgOver_eq (fun W : Set X => N.procVal W) w0]
      exact le_trans hw0le (le_of_eq hn)
    have hML2 : (∑ W ∈ badSubsets N w0, totalCost p (N.coverFinset W hB)) ≤
        (1 / 10 : ℝ) * ((Binom.levelFinset X w0).card) := by
      rw [← hC] at hML
      simpa [mul_comm] using hML
    have hgoodsum : (((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card : ℝ) * θ ≤
        ∑ W ∈ Binom.levelFinset X w0, N.procVal W := by
      refine sum_ge N (fun W => N.procVal W) w0 θ ?_ ?_
      · intro W hW hgood
        exact good_val N W hgood
      · intro W hW hb
        unfold Sys.procVal
        exact famSup_nonneg (fun S hS => weight_nonneg N S (W ∩ S))
    have hbads_le : ((badSubsets N w0).card : ℝ) * (2 : ℝ)⁻¹ ≤
        (∑ W ∈ badSubsets N w0, totalCost p (N.coverFinset W hB)) := by
      have hle : (∑ W ∈ badSubsets N w0, (2 : ℝ)⁻¹) ≤
          ∑ W ∈ badSubsets N w0, totalCost p (N.coverFinset W hB) := by
        exact Finset.sum_le_sum (by intro W hW; exact le_of_lt (cover_cost_gt N W hB p hnot))
      calc
        ((badSubsets N w0).card : ℝ) * (2 : ℝ)⁻¹
            = ∑ W ∈ badSubsets N w0, (2 : ℝ)⁻¹ := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ W ∈ badSubsets N w0, totalCost p (N.coverFinset W hB) := hle
    have hbadR : ((badSubsets N w0).card : ℝ) ≤ (2 / 10 : ℝ) * ((Binom.levelFinset X w0).card) := by
      have h1 : ((badSubsets N w0).card : ℝ) * (2 : ℝ)⁻¹ ≤ (1 / 10 : ℝ) * ((Binom.levelFinset X w0).card) :=
        le_trans hbads_le hML2
      nlinarith
    have hcardeq : (Binom.levelFinset X w0).card = (badSubsets N w0).card +
        ((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card := by
      have hbad : badSubsets N w0 = (Binom.levelFinset X w0).filter (fun W => N.Bad θ W) := by
        apply Finset.ext
        intro W
        simp [badSubsets, Binom.levelFinset, θ]
      rw [hbad]
      exact (Finset.card_filter_add_card_filter_not (p := fun W : Set X => N.Bad θ W)
        (s := Binom.levelFinset X w0)).symm
    -- E ≥ ((8/10)·θ) ≥ 10^{-11}
    have hE2 : θ * (8 / 10 : ℝ) ≤
        (∑ W ∈ Binom.levelFinset X w0, N.procVal W) / ((Binom.levelFinset X w0).card) := by
      have hgoodR : ((8 / 10 : ℝ) * ((Binom.levelFinset X w0).card : ℝ)) * θ ≤
          ∑ W ∈ Binom.levelFinset X w0, N.procVal W := by
        have hgoodcard : (((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card : ℝ) ≥
            (8 / 10 : ℝ) * ((Binom.levelFinset X w0).card) := by
          have hcR : ((badSubsets N w0).card : ℝ) +
              (((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card : ℝ)
              = (Binom.levelFinset X w0).card := by
            exact_mod_cast hcardeq.symm
          calc
            (8 / 10 : ℝ) * ((Binom.levelFinset X w0).card : ℝ)
                ≤ ((Binom.levelFinset X w0).card : ℝ) - ((badSubsets N w0).card : ℝ) := by
                  nlinarith [hbadR]
            _ ≤ (((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card : ℝ) := by
                  linarith [hcR]
        have hθ : 0 ≤ θ := by unfold θ; positivity
        calc
          ((8 / 10 : ℝ) * ((Binom.levelFinset X w0).card : ℝ)) * θ
              ≤ ((((Binom.levelFinset X w0).filter (fun W => ¬ N.Bad θ W)).card : ℝ) * θ) := by
                exact mul_le_mul_of_nonneg_right hgoodcard hθ
          _ ≤ ∑ W ∈ Binom.levelFinset X w0, N.procVal W := hgoodsum
      have hCpos : 0 < (Binom.levelFinset X w0).card := by
        rw [levelFinset_card w0 hw0leX]
        exact Nat.choose_pos hw0leX
      have hCposR : (0 : ℝ) < ((Binom.levelFinset X w0).card : ℝ) := by exact_mod_cast hCpos
      rw [le_div_iff₀ hCposR]
      nlinarith [hgoodR]
    have hfinal : ((10 : ℝ) ^ 11)⁻¹ ≤ θ * (8 / 10 : ℝ) := by
      unfold θ
      norm_num
    rw [hE]
    exact le_trans hfinal hE2
  · -- corner: w0 = n
    have hwn2 : w0 = n := by omega
    have hsz : Sys.wSize J (Fintype.card X) p = Fintype.card X := by
      rw [← hn]
      rw [← hw0]
      exact hwn2
    have hE : Sys.avgOver (fun W : Set X => N.procVal W) (Sys.wSize J (Fintype.card X) p)
        = N.procVal Set.univ := by
      rw [hsz]
      rw [avgOver_eq (fun W : Set X => N.procVal W) (Fintype.card X) le_rfl]
      rw [levelFinset_self X]
      simp
    have hp8 : ((10 : ℝ) ^ 8)⁻¹ ≤ N.procVal Set.univ := procVal_univ_ge N p hTot hnot
    rw [hE]
    have h11 : ((10 : ℝ) ^ 11)⁻¹ ≤ ((10 : ℝ) ^ 8)⁻¹ := by norm_num
    exact le_trans h11 hp8
end DeepThm
end Submission
