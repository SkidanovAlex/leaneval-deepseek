import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsT
import Submission.ObsTPrime
import Submission.Nice
import Submission.ProfileSum

set_option autoImplicit false
set_option maxHeartbeats 800000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace ML

open Frame
open Sel
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-- subsets of size w which are bad -/
noncomputable def badSubsets (N : Sys X) (w : ℕ) : Finset (Set X) :=
  Finset.univ.filter (fun W : Set X => W.ncard = w ∧ N.Bad ((10 : ℝ) ^ 10)⁻¹ W)

/-- Proposition obs.T' (Park--Pham), stated in `Submission.ObsTPrime.theorem_obsTp`. -/
theorem obsTp {X : Type*} [Fintype X] (N : Sys X) (S W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight T)
    (hbad : N.Bad ((10 : ℝ) ^ 10)⁻¹ W) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ (U.ncard : ℝ) :=
  ObsTPrime.theorem_obsTp N S W U b hS hB hTot hbad hmin hfr

/-! ## STEP 0: facts about minimum fragments of BAD pairs -/

namespace Step0

/-- θ = 10^{-10} (badness threshold). -/
noncomputable abbrev θ : ℝ := ((10 : ℝ) ^ 10)⁻¹

variable {N : Sys X} {S W U : Set X} {b : ℕ}

/-- If f vanishes for all j ≤ b then summing over 0..τ is the same as over b+1..τ. -/
lemma sum_range_eq_sum_Icc_of_lt {f : ℕ → ℝ} {b τ : ℕ} (hf : ∀ j ≤ b, f j = 0) :
    (∑ j ∈ Finset.range (τ + 1), f j) = (∑ j ∈ Finset.Icc (b + 1) τ, f j) := by
  classical
  calc
    (∑ j ∈ Finset.range (τ + 1), f j)
        = (∑ j ∈ Finset.range (τ + 1), (if b < j then f j else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : b < j
          · simp [h]
          · have hjb : j ≤ b := by omega
            simp [h, hf j hjb]
    _ = (∑ j ∈ (Finset.range (τ + 1)).filter (fun j => b < j), f j) := by
          rw [Finset.sum_filter]
    _ = (∑ j ∈ Finset.Icc (b + 1) τ, f j) := by
          have hset : (Finset.range (τ + 1)).filter (fun j => b < j) = Finset.Icc (b + 1) τ := by
            ext j
            simp
            omega
          rw [hset]

/-- upper bound t ≤ n_b from obs.T (Nice) -/
lemma t_le_nb (hS : S ∈ N.F) (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    (U.ncard : ℝ) ≤ (N.prefixCount S b : ℝ) :=
  Nice.obsT_le N S W U b hS hB hmin hfr

/-- lower bound (9/10) n_b ≤ t from obs.T' (ObsTPrime; dev axiom) -/
lemma nb_le_t (hS : S ∈ N.F) (hB : N.LevelBounded)
    (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight T)
    (hbad : N.Bad θ W) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ (U.ncard : ℝ) := by
  simpa [θ] using obsTp N S W U b hS hB hTot hbad hmin hfr

/-- prefixCount = 0 forces every level count ≤ b to vanish. -/
lemma sCount_eq_zero_of_prefix (hpre : N.prefixCount S b = 0) :
    ∀ j, j ≤ b → N.sCount S j = 0 := by
  intro j hj
  have hmem : j ∈ Finset.range (b + 1) := by simpa using hj
  have hsum : (∑ j ∈ Finset.range (b + 1), N.sCount S j) = 0 := by
    simpa [Sys.prefixCount] using hpre
  have hall : ∀ j ∈ Finset.range (b + 1), N.sCount S j = 0 :=
    Finset.sum_eq_zero_iff.mp hsum
  exact hall j hmem

/-- a level set with zero count is empty -/
lemma levelSet_eq_empty_of_sCount_zero (T : Set X) (j : ℕ) (h : N.sCount T j = 0) :
    N.levelSet T j = ∅ := by
  unfold Sys.sCount at h
  exact (Set.ncard_eq_zero (s := N.levelSet T j)).mp h

/-- all level sets (in the witness) up to b are empty when the prefix is 0. -/
lemma levelSet_empty_of_prefix_zero {S' : Set X} (hpre : N.prefixCount S b = 0)
    (hprof : N.ProfileEq S S' b) : ∀ j, j ≤ b → N.levelSet S' j = ∅ := by
  intro j hj
  have hcnt : N.sCount S j = 0 := sCount_eq_zero_of_prefix hpre j hj
  have hcnt' : N.sCount S' j = 0 := by
    rw [← hprof j hj]
    exact hcnt
  exact levelSet_eq_empty_of_sCount_zero S' j hcnt'

/-- If all level sets ≤ b are empty then the total weight of S' sits entirely above level b. -/
lemma weight_eq_weightAbove_of_empty {S' : Set X}
    (hempty : ∀ j, j ≤ b → N.levelSet S' j = ∅) :
    N.totalWeight S' = N.weightAbove S' S' b := by
  classical
  unfold Sys.totalWeight Sys.weight Sys.weightAbove
  have hf : ∀ j ≤ b, ((S' ∩ N.levelSet S' j).ncard : ℝ) * wlev j = 0 := by
    intro j hj
    have hem : N.levelSet S' j = ∅ := hempty j hj
    simp [hem]
  exact sum_range_eq_sum_Icc_of_lt hf

/-- weightAbove (levels > b) of A is ≤ the total weight of A ∩ S'. -/
lemma weightAbove_le_weight {S' : Set X} (A : Set X) :
    N.weightAbove S' A b ≤ N.weight S' (A ∩ S') := by
  classical
  unfold Sys.weight Sys.weightAbove
  let h : ℕ → ℝ := fun j => (((A ∩ S') ∩ N.levelSet S' j).ncard : ℝ) * wlev j
  have hset : ∀ j, A ∩ N.levelSet S' j = (A ∩ S') ∩ N.levelSet S' j := by
    intro j
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, hx.2.1⟩, hx.2⟩
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
  have hEq : ∀ j ∈ Finset.Icc (b + 1) N.τ,
      ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j = h j := by
    intro j hj
    unfold h
    rw [hset j]
  calc
    (∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, h j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hEq j hj
    _ ≤ (∑ j ∈ Finset.range (N.τ + 1), h j) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro j hj
            simp at hj ⊢
            omega
          · intro j hj hnot
            unfold h
            have h0 : 0 ≤ (((A ∩ S') ∩ N.levelSet S' j).ncard : ℝ) := by
              exact_mod_cast (Nat.zero_le (((A ∩ S') ∩ N.levelSet S' j).ncard))
            exact mul_nonneg h0 (wlev_nonneg j)

/-- MinIndex ≤ τ for a fragment-bearing pair. -/
lemma minIndex_le_tau (hS : S ∈ N.F) (hB : N.LevelBounded) :
    N.MinIndex S W hS hB ≤ N.τ := by
  exact N.minIndex_min S W hS hB (S \ W) S (N.sdiff_isFragment S W hS hB)

/-- t ≥ 1 for a minimum fragment of a bad pair -/
lemma t_pos (hS : S ∈ N.F) (hB : N.LevelBounded)
    (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight T)
    (hbad : N.Bad θ W) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') : 1 ≤ U.ncard := by
  by_contra hnot
  have ht0 : U.ncard = 0 := by omega
  have hprof : N.ProfileEq S S' b := hfr.1.2
  have hS'F : S' ∈ N.F := hfr.1.1
  have hb0 : (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ 0 := by
    have hb1 := nb_le_t hS hB hTot hbad hmin hfr
    simpa [ht0] using hb1
  have hpre0 : N.prefixCount S b = 0 := by
    have hx0 : 0 ≤ (N.prefixCount S b : ℝ) := by positivity
    have hx : (N.prefixCount S b : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast (le_antisymm hx hx0)
  have hfr2 := hfr.2.2.2.2
  have hpre0' : ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)) = 0 := by simp [hpre0, ht0]
  have hwS' : N.weightAbove S' S' b = N.totalWeight S' := by
    exact (weight_eq_weightAbove_of_empty
      (levelSet_empty_of_prefix_zero hpre0 hprof)).symm
  have hwtot : ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight S' := hTot S' hS'F
  have hR : (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) ≤ N.weightAbove S' (W ∪ U) b := hfr2
  have hlowW : ((10 : ℝ) ^ 10)⁻¹ ≤ N.weightAbove S' (W ∪ U) b := by
    have hten : ((10 : ℝ) ^ 10)⁻¹ ≤ (100 : ℝ)⁻¹ * N.totalWeight S' := by
      have hmul := mul_le_mul_of_nonneg_left hwtot (by norm_num : 0 ≤ (100 : ℝ)⁻¹)
      have hEq : (100 : ℝ)⁻¹ * ((10 : ℝ) ^ 8)⁻¹ = ((10 : ℝ) ^ 10)⁻¹ := by
        norm_num [pow_succ]
      nlinarith
    have hmain : (100 : ℝ)⁻¹ * N.totalWeight S' ≤ N.weightAbove S' (W ∪ U) b := by
      calc
        (100 : ℝ)⁻¹ * N.totalWeight S' = (100 : ℝ)⁻¹ * N.weightAbove S' S' b := by rw [hwS']
        _ = (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) := by
              rw [hpre0']
              ring
        _ ≤ N.weightAbove S' (W ∪ U) b := hR
    exact le_trans hten hmain
  have hUempty : U = ∅ := (Set.ncard_eq_zero (s := U)).mp ht0
  have hWU : W ∪ U = W := by simp [hUempty]
  have hlowW' : ((10 : ℝ) ^ 10)⁻¹ ≤ N.weightAbove S' W b := by
    simpa [hWU] using hlowW
  have hwinter : N.weightAbove S' W b ≤ N.weight S' (W ∩ S') := weightAbove_le_weight W
  have hleProc : N.weight S' (W ∩ S') ≤ N.procVal W := by
    unfold Sys.procVal
    exact le_famSup (v := fun T : Set X => N.weight T (W ∩ T)) hS'F
  have hbad' : N.procVal W < ((10 : ℝ) ^ 10)⁻¹ := by simpa [Sys.Bad, θ] using hbad
  nlinarith [hlowW', hwinter, hleProc, hbad']

/-- removing the top level from a sum over Icc when its term vanishes -/
lemma sum_Icc_succ_of_zero {a τ : ℕ} {f : ℕ → ℝ} (ha : a ≤ τ) (hf : f a = 0) :
    (∑ j ∈ Finset.Icc a τ, f j) = (∑ j ∈ Finset.Icc (a + 1) τ, f j) := by
  classical
  calc
    (∑ j ∈ Finset.Icc a τ, f j)
        = (∑ j ∈ Finset.Icc a τ, if a < j then f j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : a < j
          · simp [h]
          · have hja : j = a := by
              have hj1 : a ≤ j := (Finset.mem_Icc.mp hj).1
              omega
            simp [h, hja, hf]
    _ = (∑ j ∈ (Finset.Icc a τ).filter (fun j => a < j), f j) := by rw [Finset.sum_filter]
    _ = (∑ j ∈ Finset.Icc (a + 1) τ, f j) := by
          have hset : (Finset.Icc a τ).filter (fun j => a < j) = Finset.Icc (a + 1) τ := by
            ext j
            simp
            omega
          rw [hset]

/-- weightAbove at level b-1 equals weightAbove at level b when the level-b set of S' is empty -/
lemma weightAbove_pred_eq {S' : Set X} (hS'F : S' ∈ N.F) (hb1 : 1 ≤ b) (hbτ : b ≤ N.τ)
    (hlev : N.levelSet S' b = ∅) (A : Set X) :
    N.weightAbove S' A (b - 1) = N.weightAbove S' A b := by
  classical
  unfold Sys.weightAbove
  let f : ℕ → ℝ := fun j => ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j
  have hf0 : f b = 0 := by
    unfold f
    simp [hlev]
  have hb_eq : b - 1 + 1 = b := by omega
  calc
    (∑ j ∈ Finset.Icc (b - 1 + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc (b - 1 + 1) N.τ, f j) := by simp [f]
    _ = (∑ j ∈ Finset.Icc b N.τ, f j) := by rw [hb_eq]
    _ = (∑ j ∈ Finset.Icc (b + 1) N.τ, f j) := sum_Icc_succ_of_zero (a := b) hbτ hf0
    _ = (∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by simp [f]

/-- prefixCount at b-1 equals prefixCount at b when s_b = 0 -/
lemma prefixCount_pred_eq (hb1 : 1 ≤ b) (hsb0 : N.sCount S b = 0) :
    N.prefixCount S (b - 1) = N.prefixCount S b := by
  classical
  have hb_eq : b - 1 + 1 = b := by omega
  unfold Sys.prefixCount
  have h1 : (∑ j ∈ Finset.range (b - 1 + 1), N.sCount S j) = ∑ j ∈ Finset.range b, N.sCount S j := by
    rw [hb_eq]
  have h2 : (∑ j ∈ Finset.range (b + 1), N.sCount S j) =
      (∑ j ∈ Finset.range b, N.sCount S j) + N.sCount S b := by
    rw [Finset.sum_range_succ]
  rw [h1, h2, hsb0]
  simp

/-- s_b ≠ 0 -/
lemma sb_ne_zero (hS : S ∈ N.F) (hB : N.LevelBounded)
    (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight T)
    (hbad : N.Bad θ W) (hmin : N.MinFragmentAt S W U b hS hB) :
    N.sCount S b ≠ 0 := by
  intro hsb0
  rcases hmin.2.1 with ⟨S', hfr⟩
  by_cases hb0 : b = 0
  · subst b
    have hnb0 : N.prefixCount S 0 = 0 := by
      unfold Sys.prefixCount
      simp [hsb0]
    have ht1 : (1 : ℝ) ≤ (U.ncard : ℝ) := by
      exact_mod_cast (t_pos hS hB hTot hbad hmin hfr)
    have htn : (U.ncard : ℝ) ≤ (N.prefixCount S 0 : ℝ) := by
      simpa using (t_le_nb hS hB hmin hfr : (U.ncard : ℝ) ≤ (N.prefixCount S 0 : ℝ))
    have hpre0 : (N.prefixCount S 0 : ℝ) = 0 := by exact_mod_cast hnb0
    nlinarith
  · -- b ≥ 1: build a fragment at index b-1, contradicting minimality of b
    have hb1 : 1 ≤ b := by omega
    have hbtau : b ≤ N.τ := by
      have hmi := N.minIndex_min S W hS hB (S \ W) S (N.sdiff_isFragment S W hS hB)
      rwa [← hmin.1] at hmi
    have hprof : N.ProfileEq S S' b := hfr.1.2
    have hS'F : S' ∈ N.F := hfr.1.1
    have hsb' : N.sCount S' b = 0 := by
      have hp := hprof b (by omega)
      exact hp.symm.trans hsb0
    have hlev : N.levelSet S' b = ∅ := levelSet_eq_empty_of_sCount_zero S' b hsb'
    let c : ℕ := b - 1
    have hcle : c ≤ b := by omega
    have hprof_c : ∀ j, j ≤ c → N.sCount S j = N.sCount S' j := by
      intro j hj
      exact hprof j (le_trans hj hcle)
    have hfr_c : N.IsFragment S W U c S' := by
      constructor
      · constructor
        · exact hS'F
        · intro j hj
          exact hprof_c j hj
      · constructor
        · exact hfr.2.1
        · constructor
          · exact hfr.2.2.1
          · constructor
            · intro j hj x hx
              exact hfr.2.2.2.1 j (le_trans hj hcle) hx
            · -- fragment2 at index c
              have hwA : N.weightAbove S' (W ∪ U) c = N.weightAbove S' (W ∪ U) b := by
                exact weightAbove_pred_eq hS'F hb1 hbtau hlev (W ∪ U)
              have hwS : N.weightAbove S' S' c = N.weightAbove S' S' b := by
                exact weightAbove_pred_eq hS'F hb1 hbtau hlev S'
              have hpc : N.prefixCount S c = N.prefixCount S b := by
                exact prefixCount_pred_eq hb1 hsb0
              have htn : (U.ncard : ℝ) ≤ (N.prefixCount S b : ℝ) := t_le_nb hS hB hmin hfr
              have hD : 0 ≤ ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)) := by nlinarith
              have hwlev : wlev b ≤ wlev c := wlev_le_of_le (by omega : c ≤ b)
              have hRle : (100 : ℝ)⁻¹ * (N.weightAbove S' S' c - wlev c * ((N.prefixCount S c : ℝ) - (U.ncard : ℝ))) ≤
                  (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) := by
                rw [hwS, hpc]
                have hm : wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)) ≤
                    wlev c * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)) :=
                  mul_le_mul_of_nonneg_right hwlev hD
                nlinarith
              calc
                N.weightAbove S' (W ∪ U) c
                    = N.weightAbove S' (W ∪ U) b := hwA
                _ ≥ (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) := hfr.2.2.2.2
                _ ≥ (100 : ℝ)⁻¹ * (N.weightAbove S' S' c - wlev c * ((N.prefixCount S c : ℝ) - (U.ncard : ℝ))) := hRle
    have hU' : N.HasFragmentAt S W U c := ⟨S', hfr_c⟩
    have hminle : N.MinIndex S W hS hB ≤ c := N.minIndex_min S W hS hB U S' hfr_c
    have hminb : b = N.MinIndex S W hS hB := hmin.1
    have : b ≤ c := by rw [hminb]; exact hminle
    omega

end Step0

/-! ## Pair framework: (W, U) with W bad of size w and U in the cover -/

/-- Generic: a sum over a finset equals the sum over the g-fibers. -/
lemma sum_fiberwise {α β : Type*} {M : Type*} [AddCommMonoid M] (s : Finset α)
    (g : α → β) (w : α → M) :
    (∑ x ∈ s, w x) = ∑ k ∈ s.image g, ∑ x ∈ s.filter (fun x => g x = k), w x := by
  classical
  let T : Finset β := s.image g
  let F : β → Finset α := fun k => s.filter (fun x => g x = k)
  have hcover : s = T.biUnion F := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_biUnion.mpr ⟨g x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · intro hx
      rcases (Finset.mem_biUnion.mp hx) with ⟨k, hkT, hxF⟩
      exact (Finset.mem_filter.mp hxF).1
  have hdisj : (T : Set β).Pairwise (fun k k' => Disjoint (F k) (F k')) := by
    intro k hk k' hk' hkk'
    rw [Finset.disjoint_left]
    intro x hx hx'
    apply hkk'
    have h1 : g x = k := (Finset.mem_filter.mp hx).2
    have h2 : g x = k' := (Finset.mem_filter.mp hx').2
    rw [← h1, ← h2]
  calc
    (∑ x ∈ s, w x) = ∑ x ∈ T.biUnion F, w x := by rw [hcover]
    _ = ∑ k ∈ T, ∑ x ∈ F k, w x := Finset.sum_biUnion hdisj
    _ = ∑ k ∈ s.image g, ∑ x ∈ s.filter (fun x => g x = k), w x := rfl

/-- all (W,U) with W ∈ badSubsets, U ∈ coverFinset W -/
lemma toFinset_card_eq_ncard (s : Set X) : s.toFinset.card = s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext x
  simp

noncomputable def pairSet (N : Sys X) (w : ℕ) (hB : N.LevelBounded) : Finset (Set X × Set X) :=
  ((badSubsets N w).product (Finset.univ : Finset (Set X))).filter
    (fun x : Set X × Set X => x.2 ∈ N.coverFinset x.1 hB)

/-- membership in the cover gives a member of F with that minFrag -/
lemma cover_mem_exists (N : Sys X) (W U : Set X) (hB : N.LevelBounded)
    (hU : U ∈ N.coverFinset W hB) :
    ∃ S : Set X, S ∈ N.F ∧ N.minFragW W S hB = U := by
  classical
  unfold Sys.coverFinset at hU
  rcases (Finset.mem_image.mp hU) with ⟨S, hSF, hS⟩
  exact ⟨S, (Set.mem_toFinset.mp hSF), hS⟩

/-- chosen member of F realizing U as minFrag of W -/
noncomputable def witness (N : Sys X) (hB : N.LevelBounded) (W U : Set X) : Set X := by
  classical
  exact if h : U ∈ N.coverFinset W hB then Classical.choose (cover_mem_exists N W U hB h) else ∅

lemma witness_mem (N : Sys X) (hB : N.LevelBounded) (W U : Set X)
    (hU : U ∈ N.coverFinset W hB) : witness N hB W U ∈ N.F := by
  classical
  unfold witness
  rw [dif_pos hU]
  exact (Classical.choose_spec (cover_mem_exists N W U hB hU)).1

lemma witness_spec (N : Sys X) (hB : N.LevelBounded) (W U : Set X)
    (hU : U ∈ N.coverFinset W hB) : N.minFragW W (witness N hB W U) hB = U := by
  classical
  unfold witness
  rw [dif_pos hU]
  exact (Classical.choose_spec (cover_mem_exists N W U hB hU)).2

/-- LHS equals the pair sum over pairSet -/
lemma lhs_eq_pairSum (N : Sys X) (w : ℕ) (hB : N.LevelBounded) (p : ℝ) :
    (∑ W ∈ badSubsets N w, totalCost p (N.coverFinset W hB)) =
      ∑ x ∈ pairSet N w hB, p ^ x.2.ncard := by
  classical
  unfold pairSet
  have hA : (∑ W ∈ badSubsets N w, totalCost p (N.coverFinset W hB)) =
      (∑ W ∈ badSubsets N w, ∑ U ∈ (Finset.univ : Finset (Set X)),
        (if U ∈ N.coverFinset W hB then p ^ U.ncard else 0)) := by
    apply Finset.sum_congr rfl
    intro W hW
    unfold totalCost
    calc
      (∑ U ∈ N.coverFinset W hB, p ^ U.ncard)
          = (∑ U ∈ (Finset.univ : Finset (Set X)).filter (fun U : Set X => U ∈ N.coverFinset W hB), p ^ U.ncard) := by
            congr 1
            ext U
            simp
      _ = (∑ U ∈ (Finset.univ : Finset (Set X)), (if U ∈ N.coverFinset W hB then p ^ U.ncard else 0)) := by
            rw [Finset.sum_filter]
  have hB1 : (∑ W ∈ badSubsets N w, ∑ U ∈ (Finset.univ : Finset (Set X)),
        (if U ∈ N.coverFinset W hB then p ^ U.ncard else 0)) =
      (∑ x ∈ (badSubsets N w).product (Finset.univ : Finset (Set X)),
        (if x.2 ∈ N.coverFinset x.1 hB then p ^ x.2.ncard else 0)) := by
    exact (Finset.sum_product (s := badSubsets N w) (t := (Finset.univ : Finset (Set X)))
      (f := fun x : Set X × Set X => if x.2 ∈ N.coverFinset x.1 hB then p ^ x.2.ncard else 0)).symm
  have hC : (∑ x ∈ ((badSubsets N w).product (Finset.univ : Finset (Set X))).filter
        (fun x : Set X × Set X => x.2 ∈ N.coverFinset x.1 hB), p ^ x.2.ncard) =
      (∑ x ∈ (badSubsets N w).product (Finset.univ : Finset (Set X)),
        (if x.2 ∈ N.coverFinset x.1 hB then p ^ x.2.ncard else 0)) := by
    rw [Finset.sum_filter]
  rw [hA, hB1]
  exact hC.symm

/-- key of a pair: (b, profile) with profile zero above b -/
noncomputable def bOf (N : Sys X) (hB : N.LevelBounded) (x : Set X × Set X) : ℕ := by
  classical
  exact if h : x.2 ∈ N.coverFinset x.1 hB then
    N.MinIndex (witness N hB x.1 x.2) x.1 (witness_mem N hB x.1 x.2 h) hB else 0

/-- zero-padded level-count function of the pair's witness -/
noncomputable def sOf (N : Sys X) (hB : N.LevelBounded) (x : Set X × Set X) : ℕ → ℕ :=
  fun j => if j ≤ bOf N hB x then N.sCount (witness N hB x.1 x.2) j else 0

/-- the full group key: (b, s) -/
noncomputable def groupKey (N : Sys X) (hB : N.LevelBounded) (x : Set X × Set X) :
    ℕ × (ℕ → ℕ) := (bOf N hB x, sOf N hB x)

/-- fibers of groupKey inside pairSet -/
noncomputable def fiber (N : Sys X) (w : ℕ) (hB : N.LevelBounded)
    (k : ℕ × (ℕ → ℕ)) : Finset (Set X × Set X) :=
  (pairSet N w hB).filter (fun x => groupKey N hB x = k)

/-- n_b = sum of the counts up to the key's level -/
noncomputable def keyTotal (k : ℕ × (ℕ → ℕ)) : ℕ := ∑ j ∈ Finset.range (k.1 + 1), k.2 j

/-- total sum of p^{|U|} over all pairs -/
noncomputable def pairWeightSum (N : Sys X) (w : ℕ) (hB : N.LevelBounded) (p : ℝ) : ℝ :=
  ∑ x ∈ pairSet N w hB, p ^ x.2.ncard

/-! ## Pair facts (STEP 0 applied to pairs) -/

section PairFacts

variable (N : Sys X) (w : ℕ) (hB : N.LevelBounded)

lemma mem_pairSet_iff (x : Set X × Set X) :
    x ∈ pairSet N w hB ↔ x.1 ∈ badSubsets N w ∧ x.2 ∈ N.coverFinset x.1 hB := by
  unfold pairSet
  simp [Finset.mem_filter, Finset.mem_product]

lemma pairSet_mem_bad {x : Set X × Set X} (hx : x ∈ pairSet N w hB) : x.1 ∈ badSubsets N w :=
  (mem_pairSet_iff N w hB x).mp hx |>.1

lemma pairSet_mem_cover {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    x.2 ∈ N.coverFinset x.1 hB :=
  (mem_pairSet_iff N w hB x).mp hx |>.2

lemma badSubsets_card {W : Set X} (hW : W ∈ badSubsets N w) : W.ncard = w := by
  unfold badSubsets at hW
  exact (Finset.mem_filter.mp hW).2.1

lemma badSubsets_bad {W : Set X} (hW : W ∈ badSubsets N w) : N.Bad ((10 : ℝ) ^ 10)⁻¹ W := by
  unfold badSubsets at hW
  exact (Finset.mem_filter.mp hW).2.2

/-- For a pair, its U is the minFrag of its chosen witness. -/
lemma pair_minFrag {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    N.minFrag (witness N hB x.1 x.2) x.1 (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB = x.2 := by
  have hs := witness_spec N hB x.1 x.2 (pairSet_mem_cover N w hB hx)
  unfold Sys.minFragW at hs
  rw [dif_pos (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx))] at hs
  exact hs

/-- MinFragmentAt for the pair. -/
lemma pair_minFragmentAt {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    N.MinFragmentAt (witness N hB x.1 x.2) x.1 x.2 (bOf N hB x)
      (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB := by
  classical
  have hs := pair_minFrag N w hB hx
  have hmi := N.minFrag_spec (witness N hB x.1 x.2) x.1
    (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB
  -- hmi : MinFragmentAt S W (minFrag S W hS hB) (MinIndex S W hS hB) hS hB
  unfold bOf
  rw [dif_pos (pairSet_mem_cover N w hB hx)]
  -- now need MinFragmentAt S W U (MinIndex S W hS hB) hS hB with U = minFrag...
  simpa [hs] using hmi

/-- witness of the pair's minimum fragment. -/
lemma pair_hasFragment {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    ∃ S' : Set X, N.IsFragment (witness N hB x.1 x.2) x.1 x.2 (bOf N hB x) S' := by
  have hmi := pair_minFragmentAt N w hB hx
  exact hmi.2.1

/-- t ≤ n_b for a pair -/
lemma pair_t_le_nb {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    (x.2.ncard : ℝ) ≤ (N.prefixCount (witness N hB x.1 x.2) (bOf N hB x) : ℝ) := by
  rcases pair_hasFragment N w hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N w hB hx
  exact Step0.t_le_nb (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB hmi hfr

/-- (9/10)·n_b ≤ t for a pair (bad) -/
lemma pair_nb_le_t {x : Set X × Set X} (hx : x ∈ pairSet N w hB)
    (hTot : N.TotBound) :
    (9 / 10 : ℝ) * (N.prefixCount (witness N hB x.1 x.2) (bOf N hB x) : ℝ) ≤ (x.2.ncard : ℝ) := by
  rcases pair_hasFragment N w hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N w hB hx
  have hbad := badSubsets_bad N w (pairSet_mem_bad N w hB hx)
  exact Step0.nb_le_t (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB hTot hbad hmi hfr

/-- t ≥ 1 -/
lemma pair_t_pos {x : Set X × Set X} (hx : x ∈ pairSet N w hB) (hTot : N.TotBound) :
    1 ≤ x.2.ncard := by
  rcases pair_hasFragment N w hB hx with ⟨S', hfr⟩
  have hmi := pair_minFragmentAt N w hB hx
  have hbad := badSubsets_bad N w (pairSet_mem_bad N w hB hx)
  exact Step0.t_pos (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB hTot hbad hmi hfr

/-- the profile (counts) of the pair's witness at its own top level is nonzero -/
lemma pair_sb_ne_zero {x : Set X × Set X} (hx : x ∈ pairSet N w hB) (hTot : N.TotBound) :
    N.sCount (witness N hB x.1 x.2) (bOf N hB x) ≠ 0 := by
  have hmi := pair_minFragmentAt N w hB hx
  have hbad := badSubsets_bad N w (pairSet_mem_bad N w hB hx)
  exact Step0.sb_ne_zero (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) hB hTot hbad hmi

/-- n_b ≥ 1 for a pair -/
lemma pair_nb_pos {x : Set X × Set X} (hx : x ∈ pairSet N w hB) (hTot : N.TotBound) :
    1 ≤ N.prefixCount (witness N hB x.1 x.2) (bOf N hB x) := by
  have htn := pair_t_le_nb N w hB hx
  have ht1 : (1 : ℝ) ≤ (x.2.ncard : ℝ) := by exact_mod_cast pair_t_pos N w hB hx hTot
  have : (1 : ℝ) ≤ (N.prefixCount (witness N hB x.1 x.2) (bOf N hB x) : ℝ) := le_trans ht1 htn
  exact_mod_cast this

/-- b ≤ τ for a pair -/
lemma pair_b_le_tau {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    bOf N hB x ≤ N.τ := by
  classical
  unfold bOf
  rw [dif_pos (pairSet_mem_cover N w hB hx)]
  exact Step0.minIndex_le_tau (N := N) (S := witness N hB x.1 x.2) (W := x.1)
    (hS := witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) (hB := hB)

/-- profile values of a pair's witness are legal at levels ≤ τ (from FLegal) -/
lemma pair_legal (hLeg : N.FLegal) {x : Set X × Set X} (hx : x ∈ pairSet N w hB)
    {j : ℕ} (hj : j ≤ N.τ) :
    Sys.LegalEntry (N.sCount (witness N hB x.1 x.2) j) j := by
  unfold Sys.FLegal at hLeg
  exact hLeg (witness N hB x.1 x.2) (witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)) j hj

end PairFacts

/-! ## Per-pair structural facts and the common-feasibility (obs.T) lemma -/

section Struct

variable (N : Sys X) (w : ℕ) (hB : N.LevelBounded)

/-- witness of a pair -/
noncomputable def pw (x : Set X × Set X) : Set X := witness N hB x.1 x.2

lemma pw_mem {x : Set X × Set X} (hx : x ∈ pairSet N w hB) : pw N hB x ∈ N.F :=
  witness_mem N hB x.1 x.2 (pairSet_mem_cover N w hB hx)

/-- the pair's U is disjoint from its W -/
lemma pair_disjoint {x : Set X × Set X} (hx : x ∈ pairSet N w hB) : Disjoint x.2 x.1 := by
  have hmi := pair_minFragmentAt N w hB hx
  rcases hmi.2.1 with ⟨S', hfr⟩
  exact hfr.2.2.1

/-- the pair's U is contained in its witness S -/
lemma pair_U_subset_S {x : Set X × Set X} (hx : x ∈ pairSet N w hB) : x.2 ⊆ pw N hB x := by
  have hmi := pair_minFragmentAt N w hB hx
  rcases hmi.2.1 with ⟨S', hfr⟩
  exact hfr.2.1

/-- |W| = w for pairs -/
lemma pair_W_card {x : Set X × Set X} (hx : x ∈ pairSet N w hB) : x.1.ncard = w :=
  badSubsets_card N w (pairSet_mem_bad N w hB hx)

/-- obs.T for any (Z,b,s,t)-feasible witness: U ⊆ unionBelow Sh b -/
lemma unionBelow_contains_of_feasible (S W U Sh : Set X) (b : ℕ)
    (hS : S ∈ N.F)
    (hmin : N.MinFragmentAt S W U b hS hB)
    (hShF : Sh ∈ N.F)
    (hprof : ∀ j, j ≤ b → N.sCount Sh j = N.sCount S j)
    (hfeas1 : ∀ j, j ≤ b → N.levelSet Sh j ⊆ W ∪ U)
    (hfeas2 : N.weightAbove Sh (W ∪ U) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAbove Sh Sh b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)))) :
    U ⊆ N.unionBelow Sh b := by
  classical
  have hUsubS : U ⊆ S := by
    rcases hmin.2.1 with ⟨S₀, hfr₀⟩
    exact hfr₀.2.1
  have hdisj : Disjoint U W := by
    rcases hmin.2.1 with ⟨S₀, hfr₀⟩
    exact hfr₀.2.2.1
  have hfr : N.IsFragment S W U b Sh := by
    constructor
    · constructor
      · exact hShF
      · intro j hj
        exact (hprof j hj).symm
    · constructor
      · exact hUsubS
      · constructor
        · exact hdisj
        · constructor
          · exact hfeas1
          · exact hfeas2
  have hT := ObsT.theorem_obsT N S W U b hS hB hmin hfr
  intro u hu
  have hnotW : u ∉ W := (Set.disjoint_left.mp hdisj) hu
  have : u ∈ N.unionBelow Sh b \ W := by
    rw [hT]
    exact hu
  exact this.1

/-- |unionBelow Sh b| = prefixCount S b when Sh shares counts with S up to b -/
lemma card_unionBelow_of_profile (Sh S : Set X) (b : ℕ)
    (hprof : ∀ j, j ≤ b → N.sCount Sh j = N.sCount S j) :
    (N.unionBelow Sh b).ncard = N.prefixCount S b := by
  calc
    (N.unionBelow Sh b).ncard = N.prefixCount Sh b := (N.prefixCount_eq_card_below Sh b).symm
    _ = N.prefixCount S b := by
          unfold Sys.prefixCount
          apply Finset.sum_congr rfl
          intro j hj
          have hjb : j ≤ b := by simpa using hj
          exact hprof j hjb

/-- any pair with key (b,s) has sCount of its witness equal to the key profile on j ≤ b -/
lemma groupKey_profile (x : Set X × Set X) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N w hB)
    (hk : groupKey N hB x = k) : ∀ j, j ≤ k.1 → N.sCount (pw N hB x) j = k.2 j := by
  intro j hj
  have hb : bOf N hB x = k.1 := by simpa [groupKey] using (congrArg Prod.fst hk)
  have hs : sOf N hB x j = k.2 j := by
    simpa [groupKey] using (congrArg (fun q : ℕ × (ℕ → ℕ) => q.2 j) hk)
  have hb2 : j ≤ bOf N hB x := by
    rw [hb]
    exact hj
  have hif : N.sCount (witness N hB x.1 x.2) j = k.2 j := by
    have : (if j ≤ bOf N hB x then N.sCount (witness N hB x.1 x.2) j else 0) = k.2 j := by
      simpa [sOf] using hs
    rwa [if_pos hb2] at this
  simpa [pw] using hif

end Struct

/-! ## The slice counting core -/

section SliceCore

variable (N : Sys X) (w : ℕ) (hB : N.LevelBounded)

/-- the fragment witness S' of a pair (junk outside pairSet) -/
noncomputable def fragWitnessOf (x : Set X × Set X) : Set X := by
  classical
  exact if hx : x ∈ pairSet N w hB then
    Classical.choose (pair_hasFragment N w hB hx) else ∅

lemma fragWitness_mem {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    fragWitnessOf N w hB x ∈ N.F := by
  classical
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N w hB hx)
  exact hfr.1.1

lemma fragWitness_profile {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    ∀ j, j ≤ bOf N hB x → N.sCount (fragWitnessOf N w hB x) j = N.sCount (pw N hB x) j := by
  classical
  intro j hj
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N w hB hx)
  exact (hfr.1.2 j hj).symm

lemma fragWitness_frag1 {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    ∀ j, j ≤ bOf N hB x → N.levelSet (fragWitnessOf N w hB x) j ⊆ x.1 ∪ x.2 := by
  classical
  intro j hj
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N w hB hx)
  exact hfr.2.2.2.1 j hj

lemma fragWitness_frag2 {x : Set X × Set X} (hx : x ∈ pairSet N w hB) :
    N.weightAbove (fragWitnessOf N w hB x) (x.1 ∪ x.2) (bOf N hB x) ≥ (100 : ℝ)⁻¹ *
      (N.weightAbove (fragWitnessOf N w hB x) (fragWitnessOf N w hB x) (bOf N hB x) -
        wlev (bOf N hB x) *
          ((N.prefixCount (pw N hB x) (bOf N hB x) : ℝ) - (x.2.ncard : ℝ))) := by
  classical
  unfold fragWitnessOf
  rw [dif_pos hx]
  have hfr := Classical.choose_spec (pair_hasFragment N w hB hx)
  simpa [pw] using hfr.2.2.2.2

/-- group keys equal implies the levels agree -/
lemma groupKey_b_eq (x : Set X × Set X) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N w hB)
    (hk : groupKey N hB x = k) : bOf N hB x = k.1 := by
  simpa [groupKey] using (congrArg Prod.fst hk)

/-- keyTotal equals the prefix count of the pair's witness at its own level -/
lemma keyTotal_eq_prefix (x : Set X × Set X) (k : ℕ × (ℕ → ℕ)) (hx : x ∈ pairSet N w hB)
    (hk : groupKey N hB x = k) : keyTotal k = N.prefixCount (pw N hB x) (bOf N hB x) := by
  have hb : bOf N hB x = k.1 := groupKey_b_eq N w hB x k hx hk
  unfold keyTotal
  unfold Sys.prefixCount
  rw [hb]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j ≤ k.1 := by simpa using hj
  exact (groupKey_profile N w hB x k hx hk j hjb).symm

/-- the U of a pair lies in unionBelow of the fragment witness of ANY pair with the same key and the same Z -/
lemma U_subset_unionBelow_of_common (x y : Set X × Set X) (hx : x ∈ pairSet N w hB)
    (hy : y ∈ pairSet N w hB) (hkx : groupKey N hB x = groupKey N hB y)
    (hZ : x.1 ∪ x.2 = y.1 ∪ y.2) (ht : x.2.ncard = y.2.ncard) :
    x.2 ⊆ N.unionBelow (fragWitnessOf N w hB y) (bOf N hB y) := by
  classical
  let k : ℕ × (ℕ → ℕ) := groupKey N hB y
  have hky : groupKey N hB y = k := rfl
  have hkx' : groupKey N hB x = k := by simpa [k] using hkx
  have hbxy : bOf N hB x = bOf N hB y := by
    have h1 := groupKey_b_eq N w hB y k hy hky
    have h2 := groupKey_b_eq N w hB x k hx hkx'
    rw [h1, h2]
  let Sh : Set X := fragWitnessOf N w hB y
  let Sx : Set X := pw N hB x
  let Sy : Set X := pw N hB y
  have hSyF : Sy ∈ N.F := pw_mem N w hB hy
  have hSxF : Sx ∈ N.F := pw_mem N w hB hx
  have hShF : Sh ∈ N.F := fragWitness_mem N w hB hy
  have hminx0 : N.MinFragmentAt Sx x.1 x.2 (bOf N hB x) hSxF hB := by
    dsimp [Sx]
    exact pair_minFragmentAt N w hB hx
  have hminx : N.MinFragmentAt Sx x.1 x.2 (bOf N hB y) hSxF hB := by
    simpa [hbxy] using hminx0
  have hprof : ∀ j, j ≤ bOf N hB y → N.sCount Sh j = N.sCount Sx j := by
    intro j hj
    have h1 : N.sCount Sh j = N.sCount Sy j := fragWitness_profile N w hB hy j hj
    have h2 : N.sCount Sy j = N.sCount Sx j := by
      have hb' : bOf N hB y = k.1 := groupKey_b_eq N w hB y k hy hky
      have hj' : j ≤ k.1 := by
        rw [← hb']
        exact hj
      have a1 := groupKey_profile N w hB x k hx hkx' j hj'
      have a2 := groupKey_profile N w hB y k hy hky j hj'
      unfold Sy Sx
      exact a2.trans a1.symm
    exact h1.trans h2
  have hfeas1 : ∀ j, j ≤ bOf N hB y → N.levelSet Sh j ⊆ x.1 ∪ x.2 := by
    intro j hj
    have hf := fragWitness_frag1 N w hB hy j hj
    intro u hu
    have huZ : u ∈ y.1 ∪ y.2 := hf hu
    rw [hZ]
    exact huZ
  have hfeas2 : N.weightAbove Sh (x.1 ∪ x.2) (bOf N hB y) ≥ (100 : ℝ)⁻¹ *
      (N.weightAbove Sh Sh (bOf N hB y) - wlev (bOf N hB y) *
        ((N.prefixCount Sx (bOf N hB y) : ℝ) - (x.2.ncard : ℝ))) := by
    have hf := fragWitness_frag2 N w hB hy
    have hf' : N.weightAbove Sh (y.1 ∪ y.2) (bOf N hB y) ≥ (100 : ℝ)⁻¹ *
        (N.weightAbove Sh Sh (bOf N hB y) - wlev (bOf N hB y) *
          ((N.prefixCount Sy (bOf N hB y) : ℝ) - (y.2.ncard : ℝ))) := by
      simpa [Sh, Sy, pw] using hf
    have hpreN : N.prefixCount Sy (bOf N hB y) = N.prefixCount Sx (bOf N hB y) := by
      unfold Sys.prefixCount
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ bOf N hB y := by simpa using hj
      have hb' : bOf N hB y = k.1 := groupKey_b_eq N w hB y k hy hky
      have hj' : j ≤ k.1 := by
        rw [← hb']
        exact hjb
      have h1 := groupKey_profile N w hB x k hx hkx' j hj'
      have h2 := groupKey_profile N w hB y k hy hky j hj'
      unfold Sy Sx
      exact h2.trans h1.symm
    have hpreR : (N.prefixCount Sy (bOf N hB y) : ℝ) = (N.prefixCount Sx (bOf N hB y) : ℝ) := by
      exact_mod_cast hpreN
    have htR : (y.2.ncard : ℝ) = (x.2.ncard : ℝ) := by exact_mod_cast ht.symm
    rw [hpreR, htR] at hf'
    rw [← hZ] at hf'
    simpa [Sh] using hf'
  have hmain := unionBelow_contains_of_feasible N hB Sx x.1 x.2 Sh (bOf N hB y) hSxF
    (by simpa [Sx] using hminx) hShF hprof hfeas1 hfeas2
  simpa [Sh, Sx] using hmain

/-- cardinality of unionBelow of a pair's fragment witness equals keyTotal -/
lemma unionBelow_card_of_key (x : Set X × Set X) (k : ℕ × (ℕ → ℕ))
    (hx : x ∈ pairSet N w hB) (hk : groupKey N hB x = k) :
    (N.unionBelow (fragWitnessOf N w hB x) (bOf N hB x)).ncard = keyTotal k := by
  classical
  have h1 : (N.unionBelow (fragWitnessOf N w hB x) (bOf N hB x)).ncard =
      N.prefixCount (fragWitnessOf N w hB x) (bOf N hB x) :=
    (N.prefixCount_eq_card_below (fragWitnessOf N w hB x) (bOf N hB x)).symm
  calc
    (N.unionBelow (fragWitnessOf N w hB x) (bOf N hB x)).ncard
        = N.prefixCount (fragWitnessOf N w hB x) (bOf N hB x) := h1
    _ = N.prefixCount (pw N hB x) (bOf N hB x) := by
          unfold Sys.prefixCount
          apply Finset.sum_congr rfl
          intro j hj
          exact fragWitness_profile N w hB hx j (by simpa using hj)
    _ = keyTotal k := (keyTotal_eq_prefix N w hB x k hx hk).symm

/-- if a ∪ b = Z with b disjoint from a then a = Z \ b -/
lemma sdiff_eq_of_union_eq {a b Z : Set X} (hZ : a ∪ b = Z) (hab : Disjoint b a) :
    a = Z \ b := by
  ext u
  constructor
  · intro hu
    constructor
    · have : u ∈ Z := by
        rw [← hZ]
        exact Or.inl hu
      exact this
    · exact (Set.disjoint_left.mp hab.symm) hu
  · intro hu
    rcases hu with ⟨huZ, hub⟩
    have : u ∈ a ∪ b := by
      rw [hZ]
      exact huZ
    rcases this with hua | hub'
    · exact hua
    · exact False.elim (hub hub')

/-- the number of pairs in the slice with a fixed Z is at most 2^{keyTotal k} -/
lemma slice_Z_card_le {k : ℕ × (ℕ → ℕ)} {t : ℕ} {Z : Set X}
    (x0 : Set X × Set X) (hx0S : x0 ∈ (pairSet N w hB).filter
      (fun x => groupKey N hB x = k ∧ x.2.ncard = t)) (hx0Z : x0.1 ∪ x0.2 = Z) :
    (((pairSet N w hB).filter (fun x => groupKey N hB x = k ∧ x.2.ncard = t)).filter
      (fun x => x.1 ∪ x.2 = Z)).card ≤ 2 ^ keyTotal k := by
  classical
  let S : Finset (Set X × Set X) := (pairSet N w hB).filter
    (fun x => groupKey N hB x = k ∧ x.2.ncard = t)
  let fb : Finset (Set X × Set X) := S.filter (fun x => x.1 ∪ x.2 = Z)
  have hx0pair : x0 ∈ pairSet N w hB := (Finset.mem_filter.mp hx0S).1
  have hx0key : groupKey N hB x0 = k := (Finset.mem_filter.mp hx0S).2.1
  have hx0t : x0.2.ncard = t := (Finset.mem_filter.mp hx0S).2.2
  let V0 : Set X := N.unionBelow (fragWitnessOf N w hB x0) (bOf N hB x0)
  have hVcard : V0.ncard = keyTotal k := by
    dsimp [V0]
    exact unionBelow_card_of_key N w hB x0 k hx0pair hx0key
  let tgt : Finset (Finset X) := (V0.toFinset).powerset
  have hmap : ∀ x ∈ fb, x.2.toFinset ∈ tgt := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hxZ : x.1 ∪ x.2 = Z := (Finset.mem_filter.mp hx).2
    have hxpair : x ∈ pairSet N w hB := (Finset.mem_filter.mp hxS).1
    have hxkey : groupKey N hB x = k := (Finset.mem_filter.mp hxS).2.1
    have hxt : x.2.ncard = t := (Finset.mem_filter.mp hxS).2.2
    have hsub : x.2 ⊆ V0 := by
      have hmain := U_subset_unionBelow_of_common N w hB x x0 hxpair hx0pair
        (by rw [hxkey, hx0key]) (by rw [hxZ, hx0Z]) (by rw [hxt, hx0t])
      dsimp [V0]
      simpa using hmain
    dsimp [tgt]
    rw [Finset.mem_powerset]
    intro u hu
    have hu' : u ∈ x.2 := by simpa using hu
    have huV : u ∈ V0 := hsub hu'
    exact (by simpa using huV : u ∈ V0.toFinset)
  have hinj : Set.InjOn (fun x : Set X × Set X => x.2.toFinset) (↑fb : Set (Set X × Set X)) := by
    intro x hx y hy hxy
    have hx2 : x.2 = y.2 := (Set.toFinset_inj.mp hxy)
    have hxSx : x ∈ S := (Finset.mem_filter.mp hx).1
    have hxZ : x.1 ∪ x.2 = Z := (Finset.mem_filter.mp hx).2
    have hxpair : x ∈ pairSet N w hB := (Finset.mem_filter.mp hxSx).1
    have hySy : y ∈ S := (Finset.mem_filter.mp hy).1
    have hyZ : y.1 ∪ y.2 = Z := (Finset.mem_filter.mp hy).2
    have hypair : y ∈ pairSet N w hB := (Finset.mem_filter.mp hySy).1
    have hxdisj : Disjoint x.2 x.1 := pair_disjoint N w hB hxpair
    have hydisj : Disjoint y.2 y.1 := pair_disjoint N w hB hypair
    have hx1 : x.1 = Z \ x.2 := sdiff_eq_of_union_eq hxZ hxdisj
    have hy1 : y.1 = Z \ y.2 := sdiff_eq_of_union_eq hyZ hydisj
    have hx1' : x.1 = Z \ y.2 := by rwa [hx2] at hx1
    exact Prod.ext (hx1'.trans hy1.symm) hx2
  have hcard : fb.card ≤ tgt.card :=
    Finset.card_le_card_of_injOn (fun x : Set X × Set X => x.2.toFinset) hmap hinj
  have htg : tgt.card = 2 ^ keyTotal k := by
    dsimp [tgt]
    rw [Finset.card_powerset]
    rw [toFinset_card_eq_ncard V0, hVcard]
  have hc' : fb.card ≤ 2 ^ keyTotal k := by
    calc
      fb.card ≤ tgt.card := hcard
      _ = 2 ^ keyTotal k := htg
  simpa [S, fb] using hc'

/-- the cardinality of the slice is bounded -/
lemma slice_card_le (k : ℕ × (ℕ → ℕ)) (t : ℕ) :
    ((pairSet N w hB).filter (fun x => groupKey N hB x = k ∧ x.2.ncard = t)).card ≤
      (Fintype.card X).choose (w + t) * 2 ^ keyTotal k := by
  classical
  let S : Finset (Set X × Set X) := (pairSet N w hB).filter
    (fun x => groupKey N hB x = k ∧ x.2.ncard = t)
  let ZF : Finset (Set X) := S.image (fun x => x.1 ∪ x.2)
  have hS : S.card = ∑ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card := by
    calc
      S.card = (∑ x ∈ S, (1 : ℕ)) := Finset.card_eq_sum_ones S
      _ = ∑ Z ∈ S.image (fun x => x.1 ∪ x.2),
            ∑ x ∈ S.filter (fun x => x.1 ∪ x.2 = Z), 1 := by
            exact sum_fiberwise S (fun x : Set X × Set X => x.1 ∪ x.2) (fun _ => (1 : ℕ))
      _ = ∑ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card := by
            apply Finset.sum_congr rfl
            intro Z hZ
            rw [Finset.card_eq_sum_ones]
  have hfib : ∀ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card ≤ 2 ^ keyTotal k := by
    intro Z hZ
    rcases (Finset.mem_image.mp hZ) with ⟨x0, hx0S, hx0Z⟩
    have hx0S' : x0 ∈ (pairSet N w hB).filter (fun x => groupKey N hB x = k ∧ x.2.ncard = t) := by
      simpa [S] using hx0S
    have hb := slice_Z_card_le N w hB (k := k) (t := t) (Z := Z) x0 hx0S' hx0Z
    simpa [S] using hb
  have hsum : (∑ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card) ≤
      ZF.card * 2 ^ keyTotal k := by
    calc
      (∑ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card)
          ≤ ∑ Z ∈ ZF, 2 ^ keyTotal k := Finset.sum_le_sum (fun Z hZ => hfib Z hZ)
      _ = ZF.card * 2 ^ keyTotal k := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hZcard : ZF.card ≤ (Fintype.card X).choose (w + t) := by
    let P : Finset (Finset X) := (Finset.univ : Finset X).powersetCard (w + t)
    have hmap : ∀ Z ∈ ZF, Z.toFinset ∈ P := by
      intro Z hZ
      rcases (Finset.mem_image.mp hZ) with ⟨x, hxS, hxZ⟩
      have hxpair : x ∈ pairSet N w hB := (Finset.mem_filter.mp hxS).1
      have hxt : x.2.ncard = t := (Finset.mem_filter.mp hxS).2.2
      have hw' : x.1.ncard = w := pair_W_card N w hB hxpair
      have hdisj : Disjoint x.2 x.1 := pair_disjoint N w hB hxpair
      dsimp [P]
      rw [Finset.mem_powersetCard]
      constructor
      · intro u hu
        simp
      · have hn : Z.ncard = w + t := by
          have hc : (x.1 ∪ x.2).ncard = x.1.ncard + x.2.ncard := Set.ncard_union_eq hdisj.symm
          rw [← hxZ]
          rw [hc, hw', hxt]
        rw [toFinset_card_eq_ncard Z, hn]
    have hinj : Set.InjOn (fun Z : Set X => Z.toFinset) (↑ZF : Set (Set X)) := by
      intro Z hZ Z' hZ' hZZ'
      exact (Set.toFinset_inj.mp hZZ')
    have hc1 : ZF.card ≤ P.card :=
      Finset.card_le_card_of_injOn (fun Z : Set X => Z.toFinset) hmap hinj
    have hP : P.card = (Fintype.card X).choose (w + t) := by
      dsimp [P]
      rw [Finset.card_powersetCard]
      simp
    calc
      ZF.card ≤ P.card := hc1
      _ = (Fintype.card X).choose (w + t) := hP
  calc
    S.card = ∑ Z ∈ ZF, (S.filter (fun x => x.1 ∪ x.2 = Z)).card := hS
    _ ≤ ZF.card * 2 ^ keyTotal k := hsum
    _ ≤ (Fintype.card X).choose (w + t) * 2 ^ keyTotal k := by
          exact Nat.mul_le_mul_right _ hZcard
end SliceCore

-----/-! ## The real inequality chain (binomial ratio, J-decay, sigma) -/

section Chain

/-- C(n, w+t) ≤ C(n,w)·(n/(w+1))^t -/
lemma choose_ratio_le (n w t : ℕ) (hw : w ≤ n) :
    ((n.choose (w + t) : ℝ)) ≤ (n.choose w : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) ^ t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      change ((n.choose (w + t + 1) : ℝ)) ≤ (n.choose w : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) ^ (t + 1)
      by_cases hle : w + t + 1 ≤ n
      · have hk : w + t < n := by omega
        have hrecN := Nat.choose_succ_right_eq n (w + t)
        have hrec : (n.choose (w + t + 1) : ℝ) =
            (n.choose (w + t) : ℝ) * (((n - (w + t) : ℕ) : ℝ) / (w + t + 1 : ℕ)) := by
          have hc : ((n.choose (w + t + 1) : ℕ) : ℝ) * ((w + t + 1 : ℕ) : ℝ) =
              ((n.choose (w + t) : ℕ) : ℝ) * ((n - (w + t) : ℕ) : ℝ) := by
            exact_mod_cast hrecN
          field_simp [show (0 : ℝ) < ((w + t + 1 : ℕ) : ℝ) by positivity]
          linarith
        have hnum : ((n - (w + t) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le _ _)
        have hden : ((w + 1 : ℕ) : ℝ) ≤ ((w + t + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : w + 1 ≤ w + t + 1)
        have hfact : (((n - (w + t) : ℕ) : ℝ) / (w + t + 1 : ℕ)) ≤
            ((n : ℝ) / (w + 1 : ℕ)) := by
          have hp1 : 0 < ((w + t + 1 : ℕ) : ℝ) := by positivity
          have hp2 : 0 < ((w + 1 : ℕ) : ℝ) := by positivity
          have hmul : ((n - (w + t) : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ≤ (n : ℝ) * ((w + t + 1 : ℕ) : ℝ) := by
            calc
              ((n - (w + t) : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ)
                  ≤ (n : ℝ) * ((w + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hnum (by positivity)
              _ ≤ (n : ℝ) * ((w + t + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (n : ℝ))
          rw [div_le_div_iff₀ hp1 hp2]
          exact hmul
        calc
          (n.choose (w + t + 1) : ℝ)
              = (n.choose (w + t) : ℝ) * (((n - (w + t) : ℕ) : ℝ) / (w + t + 1 : ℕ)) := hrec
          _ ≤ (n.choose (w + t) : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left hfact (by positivity)
          _ ≤ (n.choose w : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) ^ (t + 1) := by
                have hnon : 0 ≤ ((n : ℝ) / (w + 1 : ℕ)) := by positivity
                calc
                  (n.choose (w + t) : ℝ) * ((n : ℝ) / (w + 1 : ℕ))
                      ≤ ((n.choose w : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) ^ t) * ((n : ℝ) / (w + 1 : ℕ)) :=
                        mul_le_mul_of_nonneg_right ih hnon
                  _ = (n.choose w : ℝ) * ((n : ℝ) / (w + 1 : ℕ)) ^ (t + 1) := by ring
      · have htoo : n < w + t + 1 := by omega
        have hzero : n.choose (w + t + 1) = 0 := Nat.choose_eq_zero_of_lt htoo
        rw [hzero]
        norm_num
        positivity

/-- C(n, w+t)·p^t ≤ C(n,w)·(1/J)^t given (w+1) ≥ J·n·p -/
lemma choose_J_pow (n w t : ℕ) (J : ℕ) (p : ℝ) (hw : w ≤ n) (hp0 : 0 ≤ p)
    (hnp : (2 : ℝ)⁻¹ ≤ (n : ℝ) * p)
    (hJw : ((w : ℕ) : ℝ) + 1 ≥ (J : ℝ) * (n : ℝ) * p) (hJ : 1 ≤ J) :
    ((n.choose (w + t) : ℝ)) * p ^ t ≤ (n.choose w : ℝ) * (((J : ℝ))⁻¹) ^ t := by
  have hratio := choose_ratio_le n w t hw
  have hA : ((n.choose (w + t) : ℝ)) * p ^ t ≤
      ((n.choose w : ℝ) * (((n : ℝ) / (w + 1 : ℕ)) ^ t)) * p ^ t := by
    exact mul_le_mul_of_nonneg_right hratio (pow_nonneg hp0 t)
  have hb1 : (n : ℝ) * p / ((w + 1 : ℕ) : ℝ) ≤ ((J : ℝ))⁻¹ := by
    have hJ' : 0 < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
    have hden : 0 < ((w + 1 : ℕ) : ℝ) := by positivity
    have hw' : (J : ℝ) * (n : ℝ) * p ≤ ((w + 1 : ℕ) : ℝ) := by
      simpa using hJw
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ hden hJ']
    nlinarith [hw']
  have hreg : ((n.choose w : ℝ) * (((n : ℝ) / (w + 1 : ℕ)) ^ t)) * p ^ t =
      (n.choose w : ℝ) * (((n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) ^ t) := by
    have hpp : ((n : ℝ) / (w + 1 : ℕ)) ^ t * p ^ t =
        (((n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) ^ t) := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc
      ((n.choose w : ℝ) * (((n : ℝ) / (w + 1 : ℕ)) ^ t)) * p ^ t
          = (n.choose w : ℝ) * (((n : ℝ) / (w + 1 : ℕ)) ^ t * p ^ t) := by ring
      _ = (n.choose w : ℝ) * (((n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) ^ t) := by rw [hpp]
  have hbpow : (((n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) ^ t) ≤ (((J : ℝ))⁻¹) ^ t :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) hb1 t
  calc
    ((n.choose (w + t) : ℝ)) * p ^ t
        ≤ ((n.choose w : ℝ) * (((n : ℝ) / (w + 1 : ℕ)) ^ t)) * p ^ t := hA
    _ = (n.choose w : ℝ) * (((n : ℝ) * p / ((w + 1 : ℕ) : ℝ)) ^ t) := hreg
    _ ≤ (n.choose w : ℝ) * (((J : ℝ))⁻¹) ^ t := by
          exact mul_le_mul_of_nonneg_left hbpow (by positivity)

/-- σ = sqrt(1/J) -/
noncomputable def sigmaJ (J : ℕ) : ℝ := Real.sqrt ((J : ℝ))⁻¹

/-- ζ := 4σ -/
noncomputable def zetaJ (J : ℕ) : ℝ := 4 * sigmaJ J

/-- (a^n)^2 = (a^2)^n -/
lemma pow_sq (a : ℝ) (n : ℕ) : (a ^ n) ^ 2 = (a ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : a ^ (n + 1) = a ^ n * a := pow_succ a n
      calc
        (a ^ (n + 1)) ^ 2 = (a ^ n * a) ^ 2 := by rw [hs]
        _ = (a ^ n) ^ 2 * a ^ 2 := by ring
        _ = (a ^ 2) ^ n * a ^ 2 := by rw [ih]
        _ = (a ^ 2) ^ (n + 1) := by rw [← pow_succ]

/-- for t ≥ (9/10)·n_b (i.e. n_b ≤ 2t), (1/J)^t ≤ σ^{n_b} -/
lemma inv_pow_le_sqrt_pow (J n t : ℕ) (hJ1 : 1 ≤ J) (h2t : n ≤ 2 * t) :
    (((J : ℝ))⁻¹) ^ t ≤ (sigmaJ J) ^ n := by
  let sg : ℝ := sigmaJ J
  have hnon : 0 ≤ ((J : ℝ))⁻¹ := by positivity
  have hnon2 : 0 ≤ sg := by dsimp [sg]; exact Real.sqrt_nonneg _
  have hσ2 : sg ^ 2 = ((J : ℝ))⁻¹ := by
    dsimp [sg, sigmaJ]
    exact Real.sq_sqrt hnon
  have hs1 : ((J : ℝ))⁻¹ ≤ 1 := by
    have hJ' : 0 < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
    have hJ1' : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
    rw [inv_eq_one_div]
    rw [div_le_iff₀ hJ']
    nlinarith
  have ha : 0 ≤ ((J : ℝ))⁻¹ ^ t := pow_nonneg hnon t
  have hb : 0 ≤ sg ^ n := pow_nonneg hnon2 n
  have h1 : (((J : ℝ))⁻¹ ^ t) ^ 2 = ((J : ℝ))⁻¹ ^ (2 * t) := by
    exact (pow_sq ((J : ℝ))⁻¹ t).trans (pow_mul ((J : ℝ))⁻¹ 2 t).symm
  have h2 : (sg ^ n) ^ 2 = ((J : ℝ))⁻¹ ^ n := by
    rw [← hσ2]
    exact pow_sq sg n
  have hsq : (((J : ℝ))⁻¹ ^ t) ^ 2 ≤ (sg ^ n) ^ 2 := by
    rw [h1, h2]
    exact pow_le_pow_of_le_one hnon hs1 (by omega : n ≤ 2 * t)
  have habs : |((J : ℝ))⁻¹ ^ t| ≤ |sg ^ n| := by
    exact sq_le_sq.mp hsq
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at habs
  simpa [sigmaJ, sg] using habs

/-- (n+1) ≤ 2^n as reals -/
lemma add_one_le_two_pow_real (m : ℕ) : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
  have h : m + 1 ≤ 2 ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hstep : (m + 1) + 1 ≤ 2 * (m + 1) := by omega
        have hle2 : 2 * (m + 1) ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        calc
          (m + 1) + 1 ≤ 2 * (m + 1) := hstep
          _ ≤ 2 * 2 ^ m := hle2
          _ = 2 ^ (m + 1) := by
                rw [pow_succ]
                ring
  exact_mod_cast h


/-- (4σ)^2 = 16/J -/
lemma zetaJ_sq (J : ℕ) : (zetaJ J) ^ 2 = 16 * ((J : ℝ))⁻¹ := by
  dsimp [zetaJ, sigmaJ]
  calc
    (4 * Real.sqrt ((J : ℝ))⁻¹) ^ 2 = 16 * (Real.sqrt ((J : ℝ))⁻¹) ^ 2 := by ring
    _ = 16 * ((J : ℝ))⁻¹ := by rw [Real.sq_sqrt (by positivity : 0 ≤ ((J : ℝ))⁻¹)]

/-- ζ ≥ 0 -/
lemma zetaJ_nonneg (J : ℕ) : 0 ≤ zetaJ J := by
  dsimp [zetaJ, sigmaJ]
  have : 0 ≤ Real.sqrt ((J : ℝ))⁻¹ := Real.sqrt_nonneg _
  nlinarith

/-- ζ ≤ 10^{-9} when J ≥ 10^{20} -/
lemma zetaJ_le (J : ℕ) (hJ : 10 ^ 20 ≤ J) : zetaJ J ≤ ((10 : ℝ) ^ 9)⁻¹ := by
  have hz0 : 0 ≤ zetaJ J := zetaJ_nonneg J
  have hb0 : 0 ≤ ((10 : ℝ) ^ 9)⁻¹ := by positivity
  have hJ1 : ((10 : ℝ) ^ 20) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJp : 0 < (J : ℝ) := by
    have : (0 : ℝ) < (10 : ℝ) ^ 20 := by positivity
    exact lt_of_lt_of_le this hJ1
  have hsq : (zetaJ J) ^ 2 ≤ (((10 : ℝ) ^ 9)⁻¹) ^ 2 := by
    rw [zetaJ_sq]
    have hpow : ((10 : ℝ) ^ 9)⁻¹ ^ 2 = ((10 : ℝ) ^ 18)⁻¹ := by norm_num [← pow_mul]
    rw [hpow]
    have h18 : ((10 : ℝ) ^ 18) ≠ 0 := by positivity
    have hJbig' : (16 : ℝ) * (10 : ℝ) ^ 18 ≤ (J : ℝ) := by
      have hJbig : (16 : ℝ) * (10 : ℝ) ^ 18 ≤ (10 : ℝ) ^ 20 := by norm_num
      exact le_trans hJbig hJ1
    field_simp [hJp.ne', h18]
    exact hJbig'
  rw [sq_le_sq] at hsq
  rwa [abs_of_nonneg hz0, abs_of_nonneg hb0] at hsq


/-- w = ⌊x⌋.toNat with x ≥ 0 implies w + 1 ≥ x -/
lemma floor_toNat_add_one (x : ℝ) (hx : 0 ≤ x) : ((⌊x⌋.toNat : ℝ)) + 1 ≥ x := by
  have hf0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hto : (⌊x⌋.toNat : ℝ) = (⌊x⌋ : ℝ) := by
    rw [← Int.cast_natCast (⌊x⌋.toNat)]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hf0 : (⌊x⌋.toNat : ℤ) = ⌊x⌋)
  have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  rw [hto]
  linarith

end Chain

/-! ## Fiber bound and total -/

/-- the set of admissible t for a fiber key (independent of N) -/
noncomputable def fiberTs (k : ℕ × (ℕ → ℕ)) : Finset ℕ :=
  (Finset.range (keyTotal k + 1)).filter (fun t : ℕ => (9 / 10 : ℝ) * (keyTotal k : ℝ) ≤ (t : ℝ))

section FiberBound

variable (N : Sys X) (w : ℕ) (hB : N.LevelBounded)

/-- every pair in the fiber has its t in fiberTs k -/
lemma fiber_mem_Ts {k : ℕ × (ℕ → ℕ)} {x : Set X × Set X} (hx : x ∈ fiber N w hB k)
    (hTot : N.TotBound) : x.2.ncard ∈ fiberTs k := by
  classical
  have hx1 : x ∈ pairSet N w hB ∧ groupKey N hB x = k := by
    simpa [fiber] using hx
  have hxpair : x ∈ pairSet N w hB := hx1.1
  have hxkey : groupKey N hB x = k := hx1.2
  have hnb : keyTotal k = N.prefixCount (pw N hB x) (bOf N hB x) := by
    rw [← hxkey]
    exact keyTotal_eq_prefix N w hB x (groupKey N hB x) hxpair rfl
  have htl : (x.2.ncard : ℝ) ≤ (N.prefixCount (pw N hB x) (bOf N hB x) : ℝ) :=
    pair_t_le_nb N w hB hxpair
  have htge : (9 / 10 : ℝ) * (N.prefixCount (pw N hB x) (bOf N hB x) : ℝ) ≤ (x.2.ncard : ℝ) :=
    pair_nb_le_t N w hB hxpair hTot
  unfold fiberTs
  have htln : x.2.ncard ≤ keyTotal k := by
    rw [hnb]
    exact_mod_cast htl
  have htgn : (9 / 10 : ℝ) * (keyTotal k : ℝ) ≤ (x.2.ncard : ℝ) := by
    rwa [← hnb] at htge
  exact Finset.mem_filter.mpr ⟨by simpa using htln, htgn⟩

/-- cardinality bound of the t-slice of the fiber -/
lemma fiber_slice_card {k : ℕ × (ℕ → ℕ)} {t : ℕ} :
    ((fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t)).card ≤
      (Fintype.card X).choose (w + t) * 2 ^ keyTotal k := by
  classical
  have h1 := slice_card_le N w hB k t
  have hrel : ((fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t)).card =
      ((pairSet N w hB).filter (fun x => groupKey N hB x = k ∧ x.2.ncard = t)).card := by
    congr 1
    ext x
    simp [fiber, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [hrel]
  exact h1

/-- slice of the fiber contributes at most C(n,w+t)·2^{nb}·p^t -/
lemma fiber_slice_sum {p : ℝ} (hp0 : 0 ≤ p) {k : ℕ × (ℕ → ℕ)} {t : ℕ} :
    (∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard) ≤
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ keyTotal k * p ^ t := by
  classical
  have hcard := fiber_slice_card N w hB (k := k) (t := t)
  have hsum : (∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard) =
      ((fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t)).card * p ^ t := by
    calc
      (∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard)
          = ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ t := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
      _ = ((fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t)).card * p ^ t := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hc' : (((fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t)).card : ℝ) ≤
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ keyTotal k := by
    exact_mod_cast hcard
  rw [hsum]
  exact mul_le_mul_of_nonneg_right hc' (pow_nonneg hp0 t)

/-- per-fiber bound: Σ_{x in fiber k} p^{|U|} ≤ C(n,w)·ζ^{nb} -/
lemma fiber_sum_le (p : ℝ) (J : ℕ) (hTot : N.TotBound) (hp0 : 0 ≤ p)
    (hwle : w ≤ Fintype.card X)
    (hnp : (2 : ℝ)⁻¹ ≤ (Fintype.card X : ℝ) * p)
    (hJw : ((w : ℕ) : ℝ) + 1 ≥ (J : ℝ) * (Fintype.card X : ℝ) * p) (hJ1 : 1 ≤ J)
    (k : ℕ × (ℕ → ℕ)) :
    (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) ≤
      ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ keyTotal k := by
  classical
  let nb : ℕ := keyTotal k
  have hpart : (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) ≤
      ∑ t ∈ fiberTs k,
        ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard := by
    have e1 : (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) =
        ∑ x ∈ fiber N w hB k,
          (∑ t ∈ fiberTs k, if t = x.2.ncard then p ^ x.2.ncard else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have htin : x.2.ncard ∈ fiberTs k := fiber_mem_Ts N w hB hx hTot
      have hsum := Finset.sum_ite_eq' (fiberTs k) (x.2.ncard) (fun t : ℕ => p ^ x.2.ncard)
      simpa [htin] using hsum.symm
    have e2 : (∑ x ∈ fiber N w hB k,
          (∑ t ∈ fiberTs k, if t = x.2.ncard then p ^ x.2.ncard else 0)) =
        ∑ t ∈ fiberTs k,
          ∑ x ∈ fiber N w hB k, (if t = x.2.ncard then p ^ x.2.ncard else 0) := by
      exact Finset.sum_comm (s := fiber N w hB k) (t := fiberTs k)
        (f := fun (x : Set X × Set X) (t : ℕ) => if t = x.2.ncard then p ^ x.2.ncard else 0)
    have e3 : (∑ t ∈ fiberTs k,
          ∑ x ∈ fiber N w hB k, (if t = x.2.ncard then p ^ x.2.ncard else 0)) =
        ∑ t ∈ fiberTs k,
          ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard := by
      apply Finset.sum_congr rfl
      intro t ht
      have hfs : (fiber N w hB k).filter (fun x : Set X × Set X => t = x.2.ncard) =
          (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t) := by
        ext x
        simp [eq_comm]
      calc
        (∑ x ∈ fiber N w hB k, (if t = x.2.ncard then p ^ x.2.ncard else 0))
            = ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => t = x.2.ncard), p ^ x.2.ncard := by
              rw [Finset.sum_filter]
        _ = ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard := by
              rw [hfs]
    rw [e1, e2, e3]
  have hslice : ∀ t ∈ fiberTs k,
      (∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard) ≤
        ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t := by
    intro t ht
    have hs := fiber_slice_sum N w hB (p := p) hp0 (k := k) (t := t)
    simpa [nb] using hs
  have hch : ∀ t ∈ fiberTs k,
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t ≤
        ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (((J : ℝ))⁻¹) ^ t := by
    intro t ht
    have hc := choose_J_pow (Fintype.card X) w t J p hwle hp0 hnp hJw hJ1
    have hnon : 0 ≤ (2 : ℝ) ^ nb := by positivity
    calc
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t
          = (((Fintype.card X).choose (w + t) : ℝ) * p ^ t) * (2 : ℝ) ^ nb := by ring
      _ ≤ (((Fintype.card X).choose w : ℝ) * (((J : ℝ))⁻¹) ^ t) * (2 : ℝ) ^ nb := by
            exact mul_le_mul_of_nonneg_right hc hnon
      _ = ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (((J : ℝ))⁻¹) ^ t := by ring
  have hdec : ∀ t ∈ fiberTs k,
      (((J : ℝ))⁻¹) ^ t ≤ (sigmaJ J) ^ nb := by
    intro t ht
    have htge : (9 / 10 : ℝ) * (nb : ℝ) ≤ (t : ℝ) := by
      simpa [nb, fiberTs] using (Finset.mem_filter.mp ht).2
    have hnat : 9 * nb ≤ 10 * t := by
      have h' : (9 : ℝ) * (nb : ℝ) ≤ (10 : ℝ) * (t : ℝ) := by nlinarith
      exact_mod_cast h'
    have h2t : nb ≤ 2 * t := by omega
    exact inv_pow_le_sqrt_pow J nb t hJ1 h2t
  have hterm : ∀ t ∈ fiberTs k,
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t ≤
        ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb := by
    intro t ht
    have hnonC : 0 ≤ ((Fintype.card X).choose w : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hnon2 : 0 ≤ (2 : ℝ) ^ nb := by positivity
    calc
      ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t
          ≤ ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (((J : ℝ))⁻¹) ^ t := hch t ht
      _ ≤ ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb := by
            exact mul_le_mul_of_nonneg_left (hdec t ht) (mul_nonneg hnonC hnon2)
  have hmain : (∑ t ∈ fiberTs k,
        ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard) ≤
      ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ nb := by
    have h1 : (∑ t ∈ fiberTs k,
          ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard) ≤
        ∑ t ∈ fiberTs k,
          ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t :=
      Finset.sum_le_sum (fun t ht => hslice t ht)
    have h2 : (∑ t ∈ fiberTs k,
          ((Fintype.card X).choose (w + t) : ℝ) * (2 : ℝ) ^ nb * p ^ t) ≤
        ∑ t ∈ fiberTs k,
          ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb :=
      Finset.sum_le_sum (fun t ht => hterm t ht)
    have h3 : (∑ t ∈ fiberTs k,
          ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb) ≤
        ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ nb := by
      have hnonC : 0 ≤ ((Fintype.card X).choose w : ℝ) := by exact_mod_cast (Nat.zero_le _)
      have hnon2 : 0 ≤ (2 : ℝ) ^ nb := by positivity
      have hnonσ : 0 ≤ (sigmaJ J) ^ nb := by
        have : 0 ≤ sigmaJ J := by dsimp [sigmaJ]; exact Real.sqrt_nonneg _
        exact pow_nonneg this nb
      have hc1 : (fiberTs k).card ≤ nb + 1 := by
        have hss : fiberTs k ⊆ Finset.range (nb + 1) := by
          intro t ht
          exact (Finset.mem_filter.mp ht).1
        simpa [nb] using (Finset.card_le_card (s := fiberTs k) (t := Finset.range (nb + 1)) hss)
      have hc1' : ((fiberTs k).card : ℝ) ≤ ((nb : ℕ) : ℝ) + 1 := by exact_mod_cast hc1
      have hn21 : ((nb : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ nb := by
        simpa using (add_one_le_two_pow_real nb)
      let const : ℝ := ((Fintype.card X).choose w : ℝ) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb
      have hsc : (∑ t ∈ fiberTs k, const) ≤ (((nb : ℕ) : ℝ) + 1) * const := by
        have hnonC2 : 0 ≤ const := by
          dsimp [const]
          positivity
        calc
          (∑ t ∈ fiberTs k, const) = (fiberTs k).card * const := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (((nb : ℕ) : ℝ) + 1) * const := by
                exact mul_le_mul_of_nonneg_right hc1' hnonC2
      have hfinal : (((nb : ℕ) : ℝ) + 1) * const ≤ ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ nb := by
        have hle1 : (((nb : ℕ) : ℝ) + 1) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb ≤
            (2 : ℝ) ^ nb * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb := by
          calc
            (((nb : ℕ) : ℝ) + 1) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb
                = (((nb : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ nb * (sigmaJ J) ^ nb) := by ring
            _ ≤ (2 : ℝ) ^ nb * ((2 : ℝ) ^ nb * (sigmaJ J) ^ nb) := by
                  exact mul_le_mul_of_nonneg_right hn21 (by positivity : 0 ≤ (2 : ℝ) ^ nb * (sigmaJ J) ^ nb)
            _ = (2 : ℝ) ^ nb * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb := by ring
        have hz : (2 : ℝ) ^ nb * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb = (zetaJ J) ^ nb := by
          dsimp [zetaJ]
          rw [← mul_pow, ← mul_pow]
          ring
        calc
          (((nb : ℕ) : ℝ) + 1) * const
              = ((Fintype.card X).choose w : ℝ) * ((((nb : ℕ) : ℝ) + 1) * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb) := by
                dsimp [const]
                ring
          _ ≤ ((Fintype.card X).choose w : ℝ) * ((2 : ℝ) ^ nb * (2 : ℝ) ^ nb * (sigmaJ J) ^ nb) := by
                exact mul_le_mul_of_nonneg_left hle1 hnonC
          _ = ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ nb := by rw [hz]
      exact le_trans hsc hfinal
    exact le_trans h1 (le_trans h2 h3)
  calc
    (∑ x ∈ fiber N w hB k, p ^ x.2.ncard)
        ≤ ∑ t ∈ fiberTs k,
            ∑ x ∈ (fiber N w hB k).filter (fun x : Set X × Set X => x.2.ncard = t), p ^ x.2.ncard := hpart
    _ ≤ ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ nb := hmain
    _ ≤ ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ keyTotal k := by
          simpa [nb]

end FiberBound

/-! ## Total over keys -/

section Total

variable (N : Sys X) (w : ℕ) (hB : N.LevelBounded)

/-- the set of group keys occurring -/
noncomputable def keySet : Finset (ℕ × (ℕ → ℕ)) :=
  (pairSet N w hB).image (fun x => groupKey N hB x)

/-- pairWeightSum equals the sum over keys of the fiber sums -/
lemma pairWeightSum_eq_keySum (p : ℝ) :
    pairWeightSum N w hB p = ∑ k ∈ keySet N w hB, (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) := by
  classical
  unfold pairWeightSum
  have hkeymem (x : Set X × Set X) (hx : x ∈ pairSet N w hB) : groupKey N hB x ∈ keySet N w hB := by
    unfold keySet
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have e1 : (∑ x ∈ pairSet N w hB, p ^ x.2.ncard) =
      ∑ x ∈ pairSet N w hB,
        (∑ k ∈ keySet N w hB, if k = groupKey N hB x then p ^ x.2.ncard else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hm := Finset.sum_ite_eq' (keySet N w hB) (groupKey N hB x) (fun k : ℕ × (ℕ → ℕ) => p ^ x.2.ncard)
    have : (∑ k ∈ keySet N w hB, if k = groupKey N hB x then p ^ x.2.ncard else 0) = p ^ x.2.ncard := by
      simpa [hkeymem x hx] using hm
    exact this.symm
  have e2 : (∑ x ∈ pairSet N w hB,
        (∑ k ∈ keySet N w hB, if k = groupKey N hB x then p ^ x.2.ncard else 0)) =
      ∑ k ∈ keySet N w hB,
        ∑ x ∈ pairSet N w hB, (if k = groupKey N hB x then p ^ x.2.ncard else 0) := by
    exact Finset.sum_comm (s := pairSet N w hB) (t := keySet N w hB)
      (f := fun (x : Set X × Set X) (k : ℕ × (ℕ → ℕ)) => if k = groupKey N hB x then p ^ x.2.ncard else 0)
  have e3 : (∑ k ∈ keySet N w hB,
        ∑ x ∈ pairSet N w hB, (if k = groupKey N hB x then p ^ x.2.ncard else 0)) =
      ∑ k ∈ keySet N w hB, (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hfs : (pairSet N w hB).filter (fun x : Set X × Set X => k = groupKey N hB x) =
        fiber N w hB k := by
      ext x
      simp [fiber, eq_comm]
    calc
      (∑ x ∈ pairSet N w hB, (if k = groupKey N hB x then p ^ x.2.ncard else 0))
          = ∑ x ∈ (pairSet N w hB).filter (fun x : Set X × Set X => k = groupKey N hB x), p ^ x.2.ncard := by
            rw [Finset.sum_filter]
      _ = ∑ x ∈ fiber N w hB k, p ^ x.2.ncard := by rw [hfs]
  rw [e1, e2, e3]

/-- pairWeightSum ≤ C(n,w)·Σ_k ζ^{keyTotal k} -/
lemma pairWeightSum_le (p : ℝ) (J : ℕ) (hTot : N.TotBound) (hp0 : 0 ≤ p)
    (hwle : w ≤ Fintype.card X)
    (hnp : (2 : ℝ)⁻¹ ≤ (Fintype.card X : ℝ) * p)
    (hJw : ((w : ℕ) : ℝ) + 1 ≥ (J : ℝ) * (Fintype.card X : ℝ) * p) (hJ1 : 1 ≤ J) :
    pairWeightSum N w hB p ≤
      ((Fintype.card X).choose w : ℝ) * ∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k := by
  classical
  have hpart := pairWeightSum_eq_keySum N w hB p
  have hfib : ∀ k ∈ keySet N w hB,
      (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) ≤
        ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ keyTotal k := by
    intro k hk
    exact fiber_sum_le N w hB p J hTot hp0 hwle hnp hJw hJ1 k
  calc
    pairWeightSum N w hB p
        = ∑ k ∈ keySet N w hB, (∑ x ∈ fiber N w hB k, p ^ x.2.ncard) := hpart
    _ ≤ ∑ k ∈ keySet N w hB,
          ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ keyTotal k :=
          Finset.sum_le_sum (fun k hk => hfib k hk)
    _ = ((Fintype.card X).choose w : ℝ) * ∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k := by
          calc
            (∑ k ∈ keySet N w hB, ((Fintype.card X).choose w : ℝ) * (zetaJ J) ^ keyTotal k)
                = (∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k * ((Fintype.card X).choose w : ℝ)) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
            _ = (∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k) * ((Fintype.card X).choose w : ℝ) := by
                  rw [Finset.sum_mul]
            _ = ((Fintype.card X).choose w : ℝ) * (∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k) := by ring

/-- each key in keySet is realised by a pair -/
lemma keySet_realized {k : ℕ × (ℕ → ℕ)} (hk : k ∈ keySet N w hB) :
    ∃ x : Set X × Set X, x ∈ pairSet N w hB ∧ groupKey N hB x = k := by
  classical
  unfold keySet at hk
  exact (Finset.mem_image.mp hk)

/-- level of a key is at most τ -/
lemma keySet_level {k : ℕ × (ℕ → ℕ)} (hk : k ∈ keySet N w hB) : k.1 ≤ N.τ := by
  classical
  rcases keySet_realized N w hB hk with ⟨x, hx, hk'⟩
  have hb : bOf N hB x = k.1 := by
    rw [← hk']
    rfl
  have hle := pair_b_le_tau N w hB hx
  rw [hb] at hle
  exact hle

/-- entries of a key are legal -/
lemma keySet_legal {k : ℕ × (ℕ → ℕ)} (hk : k ∈ keySet N w hB) (hLeg : N.FLegal) :
    ∀ j, j ≤ k.1 → Sys.LegalEntry (k.2 j) j := by
  classical
  intro j hj
  rcases keySet_realized N w hB hk with ⟨x, hx, hk'⟩
  have hprof : ∀ j, j ≤ k.1 → N.sCount (pw N hB x) j = k.2 j := by
    intro j hj
    have hg := groupKey_profile N w hB x k hx hk'
    exact hg j hj
  have hb : bOf N hB x = k.1 := by rw [← hk']; rfl
  have hj' : j ≤ N.τ := le_trans hj (keySet_level N w hB hk)
  have hleg := pair_legal N w hB hLeg hx hj'
  -- hleg : LegalEntry (sCount (witness x) j) j; need for sCount (pw x) j = k.2 j
  rwa [← hprof j hj]

/-- top entry of a key is nonzero -/
lemma keySet_top {k : ℕ × (ℕ → ℕ)} (hk : k ∈ keySet N w hB) (hTot : N.TotBound) :
    k.2 k.1 ≠ 0 := by
  classical
  rcases keySet_realized N w hB hk with ⟨x, hx, hk'⟩
  have hb : bOf N hB x = k.1 := by rw [← hk']; rfl
  have hsb := pair_sb_ne_zero N w hB hx hTot
  -- k.2 k.1 = sCount (pw x) (bOf x)
  have hk2 : k.2 k.1 = N.sCount (pw N hB x) (bOf N hB x) := by
    have hprof := groupKey_profile N w hB x k hx hk'
    have hz := hprof k.1 (by omega)
    -- hz : sCount (pw x) k.1 = k.2 k.1 ; want k.2 k.1 = sCount (pw x)(bOf x)
    rw [← hb] at hz
    rw [← hb]
    exact hz.symm
  rwa [hk2]

/-- entries of a key vanish above its level -/
lemma keySet_zero_above {k : ℕ × (ℕ → ℕ)} (hk : k ∈ keySet N w hB) :
    ∀ j, k.1 < j → k.2 j = 0 := by
  classical
  intro j hj
  rcases keySet_realized N w hB hk with ⟨x, hx, hk'⟩
  have hb : bOf N hB x = k.1 := by rw [← hk']; rfl
  -- k.2 j = sOf x j; for j > bOf x, sOf x j = 0
  have hs : sOf N hB x j = k.2 j := by
    have hg := congrArg (fun q : ℕ × (ℕ → ℕ) => q.2 j) hk'
    simpa [groupKey] using hg
  unfold sOf at hs
  have hgt : ¬ j ≤ bOf N hB x := by omega
  rw [if_neg hgt] at hs
  exact hs.symm

end Total

theorem theorem_ML (p : ℝ) (J : ℕ) (N : Sys X) (w n : ℕ)
    (hJ : 10 ^ 20 ≤ J) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : Fintype.card X = n) (hw : w = ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat)
    (hnp : (2 : ℝ)⁻¹ ≤ (n : ℝ) * p) (hwn : w < n)
    (hB : N.LevelBounded) (hTot : N.TotBound) (hLeg : N.FLegal) :
    (∑ W ∈ badSubsets N w, totalCost p (N.coverFinset W hB)) ≤
      (1 / 10 : ℝ) * (n.choose w : ℝ) := by
  classical
  have hnp0 : 0 ≤ p := le_of_lt hp0
  have hJge1 : 1 ≤ J := by omega
  have hwle : w ≤ Fintype.card X := by
    have : w < Fintype.card X := by simpa [hn] using hwn
    omega
  have hncard : Fintype.card X = n := hn
  have hnp' : (2 : ℝ)⁻¹ ≤ (Fintype.card X : ℝ) * p := by simpa [hn] using hnp
  have hx0 : 0 ≤ (J : ℝ) * (Fintype.card X : ℝ) * p := by positivity
  have hwfloor : w = ⌊(J : ℝ) * (Fintype.card X : ℝ) * p⌋.toNat := by simpa [hn] using hw
  have hJw : ((w : ℕ) : ℝ) + 1 ≥ (J : ℝ) * (Fintype.card X : ℝ) * p := by
    have hf := floor_toNat_add_one ((J : ℝ) * (Fintype.card X : ℝ) * p) hx0
    have hw' : ((⌊(J : ℝ) * (Fintype.card X : ℝ) * p⌋.toNat : ℝ)) = ((w : ℕ) : ℝ) := by
      rw [hwfloor]
    rw [hw'] at hf
    exact hf
  -- 1. LHS = pairWeightSum
  have h1 : (∑ W ∈ badSubsets N w, totalCost p (N.coverFinset W hB)) = pairWeightSum N w hB p := by
    exact lhs_eq_pairSum N w hB p
  -- 2. pairWeightSum ≤ C(n,w)·Σ ζ^{keyTotal}
  have h2 := pairWeightSum_le N w hB p J hTot hnp0 hwle hnp' hJw hJge1
  -- 3. Σ over keys ≤ 1/10 via the profile-sum bound
  have hprof : (∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k) ≤ (10 : ℝ)⁻¹ := by
    exact ProfileSum.profile_sum_bound (zetaJ J) (zetaJ_nonneg J) (zetaJ_le J hJ) (N.τ)
      (keySet N w hB)
      (fun k hk => keySet_level N w hB (k := k) hk)
      (fun k hk => keySet_legal N w hB (k := k) hk hLeg)
      (fun k hk => keySet_top N w hB (k := k) hk hTot)
      (fun k hk => keySet_zero_above N w hB (k := k) hk)
  -- 4. C(n,w)·(1/10) ≤ (1/10)·(n.choose w) after replacing card by n
  have hA : (∑ W ∈ badSubsets N w, totalCost p (N.coverFinset W hB)) ≤
      ((Fintype.card X).choose w : ℝ) * ∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k := by
    rw [h1]
    exact h2
  have hB : ((Fintype.card X).choose w : ℝ) * ∑ k ∈ keySet N w hB, (zetaJ J) ^ keyTotal k ≤
      ((Fintype.card X).choose w : ℝ) * ((10 : ℝ)⁻¹) := by
    exact mul_le_mul_of_nonneg_left hprof (by positivity)
  have hC : ((Fintype.card X).choose w : ℝ) * ((10 : ℝ)⁻¹) ≤ (1 / 10 : ℝ) * (n.choose w : ℝ) := by
    rw [hncard]
    rw [mul_comm]
    have hinv : (10 : ℝ)⁻¹ = (1 / 10 : ℝ) := by norm_num
    rw [hinv]
  exact le_trans (le_trans hA hB) hC

end ML
end Submission
