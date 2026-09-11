import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Bridge
import Submission.Binom
import Submission.BinomMed

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission
open _root_.SupremumOfSelectorProcesses
namespace Binom2
open Frame
open Sel.Deep
open Sel.Deep.Sys

noncomputable section
variable {X : Type*} [Fintype X]

/-- binomial sum of g -/
noncomputable def binomSum (p : ℝ) (g : Set X → ℝ) : ℝ := Binom.binomSum p g
/-- sum over subsets of size N -/
noncomputable def sizeSum (g : Set X → ℝ) (N : ℕ) : ℝ := Binom.sizeSum g N
/-- average over subsets of size N -/
noncomputable def sizeAvg (g : Set X → ℝ) (N : ℕ) : ℝ := Binom.sizeAvg g N

/-- subsets of `X` of ncard exactly `k` -/
noncomputable def levelFinset (X : Type*) [Fintype X] (k : ℕ) : Finset (Set X) :=
  Finset.univ.filter (fun T : Set X => T.ncard = k)

lemma level_mem (T : Set X) (k : ℕ) : T ∈ levelFinset X k ↔ T.ncard = k := by
  simp [levelFinset]

lemma level_subset_univ (k : ℕ) : levelFinset X k ⊆ (Finset.univ : Finset (Set X)) := by
  intro T hT
  exact Finset.mem_univ T

lemma ncard_le_univ (T : Set X) : T.ncard ≤ Fintype.card X := by
  have h := Set.ncard_le_ncard (Set.subset_univ T) (Set.toFinite Set.univ)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h

lemma mem_level_of_le (T : Set X) (k : ℕ) (hT : T ∈ levelFinset X k) : k ≤ Fintype.card X := by
  rw [level_mem] at hT
  exact le_trans (le_of_eq hT.symm) (ncard_le_univ T)

-- counting: number of subsets of size k is C(n,k)

lemma toFinset_card_ncard (T : Set X) : T.toFinset.card = T.ncard := by
  rw [Set.ncard_eq_toFinset_card]
  rw [Set.Finite.toFinset_eq_toFinset]

lemma coe_ncard (s : Finset X) : (↑s : Set X).ncard = s.card := by
  rw [Set.ncard_eq_toFinset_card]
  rw [Set.Finite.toFinset_eq_toFinset]
  simp

lemma levelFinset_card (k : ℕ) (hk : k ≤ Fintype.card X) :
    (levelFinset X k).card = (Fintype.card X).choose k := by
  classical
  let t : Finset (Finset X) :=
    (Finset.univ : Finset (Finset X)).filter (fun s : Finset X => s.card = k)
  have ht : t = Finset.powersetCard k (Finset.univ : Finset X) := by
    ext s
    simp [t, Finset.mem_powersetCard]
  have hcard : t.card = (Fintype.card X).choose k := by
    rw [ht]
    rw [Finset.card_powersetCard]
    rw [Finset.card_univ]
  -- biject levelFinset k to t via T ↦ T.toFinset
  rw [← hcard]
  apply Finset.card_bij (fun T (_ : T ∈ levelFinset X k) => T.toFinset)
  · intro T hT
    have hc : T.toFinset.card = k := by
      rw [toFinset_card_ncard]
      exact (level_mem T k).mp hT
    simpa [t] using hc
  · intro T hT U hU hEq
    ext x
    calc
      x ∈ T ↔ x ∈ (T.toFinset : Set X) := by simp
      _ ↔ x ∈ (U.toFinset : Set X) := by rw [hEq]
      _ ↔ x ∈ U := by simp
  · intro s hs
    have hs' : s ∈ t := hs
    have hsc : s.card = k := by simpa [t] using hs'
    refine ⟨(↑s : Set X), ?_, ?_⟩
    · rw [level_mem]
      rw [coe_ncard]
      exact hsc
    · ext x
      simp

lemma levelFinset_card_pos (k : ℕ) (hk : k ≤ Fintype.card X) :
    0 < (levelFinset X k).card := by
  rw [levelFinset_card k hk]
  exact Nat.choose_pos hk

lemma levelFinset_nonempty (k : ℕ) (hk : k ≤ Fintype.card X) :
    (levelFinset X k).Nonempty := by
  exact Finset.card_pos.mp (levelFinset_card_pos k hk)

lemma sizeAvg_eq (g : Set X → ℝ) (k : ℕ) (hk : k ≤ Fintype.card X) :
    sizeAvg g k = (sizeSum g k) / ((levelFinset X k).card : ℝ) := by
  classical
  unfold sizeAvg sizeSum Binom.sizeAvg Binom.sizeSum
  rw [dif_pos]
  · rfl
  · exact levelFinset_nonempty k hk

lemma sizeSum_eq_avg_mul (g : Set X → ℝ) (k : ℕ) (hk : k ≤ Fintype.card X) :
    sizeSum g k = sizeAvg g k * ((levelFinset X k).card : ℝ) := by
  rw [sizeAvg_eq g k hk]
  have hc : ((levelFinset X k).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (levelFinset_card_pos k hk))
  field_simp [hc]

lemma sizeAvg_nonneg (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T) (k : ℕ)
    (hk : k ≤ Fintype.card X) : 0 ≤ sizeAvg g k := by
  rw [sizeAvg_eq g k hk]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun T hT => hg T)
  · exact_mod_cast le_of_lt (levelFinset_card_pos k hk)

lemma sizeSum_nonneg (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T) (k : ℕ) :
    0 ≤ Binom.sizeSum g k := by
  classical
  unfold Binom.sizeSum
  exact Finset.sum_nonneg (fun T hT => hg T)

/-- binomSum decomposes into levels (sets of size exactly k). -/
lemma binomSum_eq_sum_levels (p : ℝ) (g : Set X → ℝ) :
    binomSum p g =
      ∑ k ∈ Finset.range (Fintype.card X + 1),
        (Binom.sizeSum g k) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
  classical
  unfold binomSum Binom.binomSum
  calc
    (∑ T : Set X, g T * p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard))
      = ∑ T : Set X,
          ∑ k ∈ Finset.range (Fintype.card X + 1),
            (if T.ncard = k then g T * p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard) else 0) := by
        apply Finset.sum_congr rfl
        intro T hT
        have hTmem : T.ncard ∈ Finset.range (Fintype.card X + 1) := by
          rw [Finset.mem_range]
          have hTle : T.ncard ≤ Fintype.card X := ncard_le_univ T
          omega
        rw [Finset.sum_ite_eq]
        simp [hTmem]
    _ = ∑ k ∈ Finset.range (Fintype.card X + 1),
          ∑ T : Set X,
            (if T.ncard = k then g T * p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (Fintype.card X + 1),
          ∑ T ∈ levelFinset X k,
            g T * p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.sum_filter]
        rfl
    _ = ∑ k ∈ Finset.range (Fintype.card X + 1),
          ∑ T ∈ levelFinset X k, g T * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro T hT
        have hTk : T.ncard = k := (level_mem T k).mp hT
        rw [hTk]
    _ = ∑ k ∈ Finset.range (Fintype.card X + 1),
          (Binom.sizeSum g k) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (∑ T ∈ levelFinset X k, g T * p ^ k * (1 - p) ^ (Fintype.card X - k))
              = (∑ T ∈ levelFinset X k, g T) * (p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro T hT
                ring
          _ = (Binom.sizeSum g k) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
                simp [Binom.sizeSum, levelFinset]
                ring

/-- number of elements of X outside S -/
lemma card_compl_eq (S : Set X) : (Fintype.card X - S.ncard : ℕ) = ((univ : Finset X).filter (fun x : X => x ∉ S)).card := by
  classical
  calc
    (Fintype.card X - S.ncard : ℕ) = (Set.univ \ S : Set X).ncard := by
      rw [Set.ncard_sdiff (Set.subset_univ S) (Set.toFinite S)]
      simp [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ = ((Set.univ \ S : Set X).toFinset).card := by
      simp [Set.ncard_eq_toFinset_card]
    _ = ((univ : Finset X).filter (fun x : X => x ∉ S)).card := by
      congr 1
      ext x
      simp

lemma sum_notmem_const (S : Set X) (c : ℝ) :
    (∑ x : X, if x ∈ S then 0 else c) = (Fintype.card X - S.ncard : ℝ) * c := by
  classical
  calc
    (∑ x : X, if x ∈ S then 0 else c)
        = ∑ x : X, if x ∉ S then c else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : x ∈ S <;> simp [h]
    _ = ∑ x ∈ (univ : Finset X).filter (fun x : X => x ∉ S), c := by
          rw [← Finset.sum_filter]
    _ = ((univ : Finset X).filter (fun x : X => x ∉ S)).card * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card X - S.ncard : ℝ) * c := by
          congr 1
          rw [← Nat.cast_sub (ncard_le_univ S)]
          exact_mod_cast (card_compl_eq S).symm

lemma sum_mem_const (S : Set X) (c : ℝ) :
    (∑ x : X, if x ∈ S then c else 0) = (S.ncard : ℝ) * c := by
  classical
  calc
    (∑ x : X, if x ∈ S then c else 0)
        = ∑ x ∈ (univ : Finset X).filter (fun x : X => x ∈ S), c := by
          rw [← Finset.sum_filter]
    _ = ((univ : Finset X).filter (fun x : X => x ∈ S)).card * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (S.ncard : ℝ) * c := by
          have h2 : (univ : Finset X).filter (fun x : X => x ∈ S) = S.toFinset := by
            ext x
            simp
          rw [h2, toFinset_card_ncard]
lemma sum_x_inj (g : Set X → ℝ) (hmono : Monotone g) (x : X) (k : ℕ) :
    (∑ T ∈ (levelFinset X k).filter (fun T : Set X => x ∉ T), g T)
      ≤ (∑ S ∈ (levelFinset X (k + 1)).filter (fun S : Set X => x ∈ S), g S) := by
  classical
  let A : Finset (Set X) := (levelFinset X k).filter (fun T : Set X => x ∉ T)
  let B : Finset (Set X) := (levelFinset X (k + 1)).filter (fun S : Set X => x ∈ S)
  calc
    (∑ T ∈ A, g T)
      ≤ ∑ T ∈ A, g (insert x T) := by
          exact Finset.sum_le_sum (fun T hT => hmono (Set.subset_insert x T))
    _ = (∑ S ∈ B, g S) := by
          refine Finset.sum_bij (s := A) (t := B)
            (f := fun T : Set X => g (insert x T)) (g := fun S : Set X => g S)
            (fun T hT => insert x T) ?_ ?_ ?_ ?_
          · intro T hT
            have hT' := (Finset.mem_filter.mp hT)
            have hTk : T.ncard = k := (level_mem T k).mp hT'.1
            have hxT : x ∉ T := hT'.2
            have hcard : (insert x T : Set X).ncard = k + 1 := by
              rw [Set.ncard_insert_of_notMem hxT (Set.toFinite T)]
              omega
            simp [B, Finset.mem_filter, level_mem, hcard]
          · intro T hT U hU hEq
            have hxT : x ∉ T := (Finset.mem_filter.mp hT).2
            have hxU : x ∉ U := (Finset.mem_filter.mp hU).2
            calc
              T = ((insert x T : Set X) \ {x}) := by ext y; by_cases hy : y = x <;> simp [hxT, hy]
              _ = ((insert x U : Set X) \ {x}) := by rw [hEq]
              _ = U := by ext y; by_cases hy : y = x <;> simp [hxU, hy]
          · intro S hS
            have hS' := (Finset.mem_filter.mp hS)
            have hSk : S.ncard = k + 1 := (level_mem S (k + 1)).mp hS'.1
            have hxS : x ∈ S := hS'.2
            refine ⟨S \ {x}, ?_, ?_⟩
            · have hxSx : x ∉ S \ {x} := by simp
              have hcard : (S \ {x} : Set X).ncard = k := by
                have h1 := Set.ncard_sdiff_singleton_of_mem (s := S) (a := x) hxS
                omega
              simp [A, Finset.mem_filter, level_mem, hcard, hxSx]
            · ext y
              by_cases hy : y = x <;> simp [hy, hxS]
          · intro T hT
            rfl

lemma level_step_mul (g : Set X → ℝ) (hmono : Monotone g) (k : ℕ)
    (hk : k + 1 ≤ Fintype.card X) :
    ((Fintype.card X : ℝ) - (k : ℝ)) * Binom.sizeSum g k ≤
      ((k + 1 : ℕ) : ℝ) * Binom.sizeSum g (k + 1) := by
  classical
  calc
    ((Fintype.card X : ℝ) - (k : ℝ)) * Binom.sizeSum g k
      = ∑ T ∈ levelFinset X k, ((Fintype.card X : ℝ) - (k : ℝ)) * g T := by
          have h : Binom.sizeSum g k = ∑ T ∈ levelFinset X k, g T := by rfl
          rw [h]
          rw [Finset.mul_sum]
    _ = ∑ T ∈ levelFinset X k, ∑ x : X, (if x ∈ T then 0 else g T) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTk : T.ncard = k := (level_mem T k).mp hT
          calc
            ((Fintype.card X : ℝ) - (k : ℝ)) * g T
                = (Fintype.card X - T.ncard : ℝ) * g T := by
                  rw [← hTk]
            _ = ∑ x : X, (if x ∈ T then 0 else g T) := by
                rw [sum_notmem_const]
    _ = ∑ x : X, ∑ T ∈ levelFinset X k, (if x ∈ T then 0 else g T) := by
          rw [Finset.sum_comm]
    _ = ∑ x : X, ∑ T ∈ (levelFinset X k).filter (fun T : Set X => x ∉ T), g T := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            (∑ T ∈ levelFinset X k, if x ∈ T then 0 else g T)
                = ∑ T ∈ levelFinset X k, if x ∉ T then g T else 0 := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    by_cases h : x ∈ T <;> simp [h]
            _ = ∑ T ∈ (levelFinset X k).filter (fun T : Set X => x ∉ T), g T := by
                    rw [Finset.sum_filter]
    _ ≤ ∑ x : X, ∑ S ∈ (levelFinset X (k + 1)).filter (fun S : Set X => x ∈ S), g S := by
          exact Finset.sum_le_sum (fun x hx => sum_x_inj g hmono x k)
    _ = ∑ x : X, ∑ S ∈ levelFinset X (k + 1), (if x ∈ S then g S else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_filter]
    _ = ∑ S ∈ levelFinset X (k + 1), ∑ x : X, (if x ∈ S then g S else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ S ∈ levelFinset X (k + 1), (S.ncard : ℝ) * g S := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [sum_mem_const]
    _ = ∑ S ∈ levelFinset X (k + 1), ((k + 1 : ℕ) : ℝ) * g S := by
          apply Finset.sum_congr rfl
          intro S hS
          have hSk : S.ncard = k + 1 := (level_mem S (k + 1)).mp hS
          rw [hSk]
    _ = ((k + 1 : ℕ) : ℝ) * Binom.sizeSum g (k + 1) := by
          have h : Binom.sizeSum g (k + 1) = ∑ S ∈ levelFinset X (k + 1), g S := by rfl
          rw [h]
          rw [← Finset.mul_sum]

lemma choose_succ_mul_real (k : ℕ) (hk : k + 1 ≤ Fintype.card X) :
    ((Fintype.card X).choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      ((Fintype.card X).choose k : ℝ) * ((Fintype.card X : ℝ) - (k : ℝ)) := by
  have h := Nat.choose_succ_right_eq (Fintype.card X) k
  have hk0 : k ≤ Fintype.card X := by omega
  have hc : ((Fintype.card X).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      ((Fintype.card X).choose k : ℝ) * ((Fintype.card X - k : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_add, Nat.cast_one] at hc
  rw [Nat.cast_sub hk0] at hc
  simpa using hc

lemma sizeAvg_mono_step (g : Set X → ℝ) (hmono : Monotone g) (k : ℕ)
    (hk : k + 1 ≤ Fintype.card X) : sizeAvg g k ≤ sizeAvg g (k + 1) := by
  have hk0 : k ≤ Fintype.card X := by omega
  let a : ℝ := (Fintype.card X : ℝ) - (k : ℝ)
  let b : ℝ := (k + 1 : ℝ)
  let Sk : ℝ := Binom.sizeSum g k
  let S1 : ℝ := Binom.sizeSum g (k + 1)
  let ck : ℝ := ((Fintype.card X).choose k : ℝ)
  let c1 : ℝ := ((Fintype.card X).choose (k + 1) : ℝ)
  have hstep : a * Sk ≤ b * S1 := by
    simpa [a, b, Sk, S1] using level_step_mul g hmono k hk
  have hid : b * c1 = a * ck := by
    dsimp [a, b, ck, c1]
    rw [mul_comm]
    rw [choose_succ_mul_real k hk]
    rw [mul_comm]
  have hapos : 0 < a := by
    unfold a
    have hklt : (k : ℝ) < (Fintype.card X : ℝ) := by
      exact_mod_cast (by omega : k < Fintype.card X)
    nlinarith
  have hbpos : 0 < b := by unfold b; positivity
  have hckpos : 0 < ck := by
    unfold ck
    exact_mod_cast Nat.choose_pos hk0
  have hc1pos : 0 < c1 := by
    unfold c1
    exact_mod_cast Nat.choose_pos hk
  rw [sizeAvg_eq g k hk0, sizeAvg_eq g (k + 1) hk]
  have hcnt : ((levelFinset X k).card : ℝ) = ck := by
    unfold ck
    rw [levelFinset_card k hk0]
  have hcnt1 : ((levelFinset X (k + 1)).card : ℝ) = c1 := by
    unfold c1
    rw [levelFinset_card (k + 1) hk]
  rw [hcnt, hcnt1]
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hac : a * ck ≠ 0 := mul_ne_zero (ne_of_gt hapos) (ne_of_gt hckpos)
  have hc1ne : c1 ≠ 0 := ne_of_gt hc1pos
  have hfrac : b / (a * ck) = 1 / c1 := by
    field_simp [hbne, hac, hc1ne]
    nlinarith [hid]
  calc
    Sk / ck = (a * Sk) / (a * ck) := by
          field_simp [ne_of_gt hapos, ne_of_gt hckpos]
    _ ≤ (b * S1) / (a * ck) := by
          have hnonneg : 0 ≤ a * ck := by positivity
          exact div_le_div_of_nonneg_right hstep hnonneg
    _ = S1 * (b / (a * ck)) := by
          field_simp [ne_of_gt hapos, ne_of_gt hckpos]
    _ = S1 / c1 := by
          rw [hfrac]
          ring

lemma sizeAvg_le_of_le (g : Set X → ℝ) (hmono : Monotone g) (N k : ℕ)
    (hNk : N ≤ k) (hk : k ≤ Fintype.card X) : sizeAvg g N ≤ sizeAvg g k := by
  induction k with
  | zero =>
      have hN0 : N = 0 := Nat.eq_zero_of_le_zero hNk
      rw [hN0]
  | succ k ih =>
      by_cases hNk' : N ≤ k
      · exact le_trans (ih hNk' (by omega)) (sizeAvg_mono_step g hmono k hk)
      · have hN : N = k + 1 := by omega
        rw [hN]

lemma toNat_floor_le_real (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) :
    ((Int.floor ((n : ℝ) * p)).toNat : ℝ) ≤ (n : ℝ) * p := by
  have h1 : ((Int.floor ((n : ℝ) * p) : ℤ) : ℝ) ≤ (n : ℝ) * p := Int.floor_le _
  have hnonneg : 0 ≤ Int.floor ((n : ℝ) * p) := by
    exact Int.floor_nonneg.mpr (mul_nonneg (by exact_mod_cast Nat.zero_le n) hp0)
  calc
    ((Int.floor ((n : ℝ) * p)).toNat : ℝ) = (Int.floor ((n : ℝ) * p) : ℤ) := by
          exact_mod_cast (Int.toNat_of_nonneg hnonneg)
    _ ≤ (n : ℝ) * p := h1

lemma toNat_floor_le_n (n : ℕ) (p : ℝ) (hp1 : p ≤ 1) :
    (Int.floor ((n : ℝ) * p)).toNat ≤ n := by
  rw [Int.toNat_le]
  have h1 : ((Int.floor ((n : ℝ) * p) : ℤ) : ℝ) ≤ (n : ℝ) * p := Int.floor_le _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h2 : (n : ℝ) * p ≤ (n : ℝ) := by
    rw [mul_comm]
    exact mul_le_of_le_one_left hn0 hp1
  have hle : ((Int.floor ((n : ℝ) * p) : ℤ) : ℝ) ≤ (n : ℝ) := le_trans h1 h2
  exact_mod_cast hle

lemma term_eq_avg_w (p : ℝ) (g : Set X → ℝ) (k : ℕ) (hk : k ≤ Fintype.card X) :
    Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k) =
      sizeAvg g k * (((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
  classical
  have hcnt : ((levelFinset X k).card : ℝ) = ((Fintype.card X).choose k : ℝ) := by
    exact_mod_cast levelFinset_card k hk
  calc
    Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k)
        = (sizeSum g k) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by rfl
    _ = (sizeAvg g k * ((levelFinset X k).card : ℝ)) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
            rw [sizeSum_eq_avg_mul g k hk]
    _ = sizeAvg g k * (((levelFinset X k).card : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by ring
    _ = sizeAvg g k * (((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
            rw [hcnt]

lemma binomSum_ge_Icc (p : ℝ) (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.Icc N (Fintype.card X),
        Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k)) ≤ binomSum p g := by
  rw [binomSum_eq_sum_levels]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_range]
    have hk2 : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
    omega
  · intro k hk hk2
    have hk3 : k ≤ Fintype.card X := by
      rw [Finset.mem_range] at hk
      omega
    exact mul_nonneg (mul_nonneg (sizeSum_nonneg g hg k) (pow_nonneg hp0 k))
      (pow_nonneg (sub_nonneg.mpr hp1) (Fintype.card X - k))

theorem binom_ge_uniform (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (N : ℕ)
    (hN : N = ⌊(Fintype.card X : ℝ) * p⌋.toNat)
    (g : Set X → ℝ) (hg : ∀ T : Set X, 0 ≤ g T) (hmono : Monotone g) :
    (1 / 2 : ℝ) * sizeAvg g N ≤ binomSum p g := by
  classical
  have hp0le : 0 ≤ p := le_of_lt hp0
  have hp1le : p ≤ 1 := le_of_lt hp1
  have hNle : (N : ℝ) ≤ (Fintype.card X : ℝ) * p := by
    rw [hN]
    exact toNat_floor_le_real (Fintype.card X) p hp0le
  have hNn : N ≤ Fintype.card X := by
    rw [hN]
    exact toNat_floor_le_n (Fintype.card X) p hp1le
  let w : ℕ → ℝ := fun k => ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)
  have hw_nonneg (k : ℕ) : 0 ≤ w k := by
    dsimp [w]
    positivity
  have hsum : (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.Icc N (Fintype.card X), w k := by
    simpa [w] using (BinomMed.median_lower (Fintype.card X) N p hp0 hp1 hNle)
  have havg : 0 ≤ sizeAvg g N := sizeAvg_nonneg g hg N hNn
  calc
    (1 / 2 : ℝ) * sizeAvg g N
        ≤ (∑ k ∈ Finset.Icc N (Fintype.card X), w k) * sizeAvg g N := by
            exact mul_le_mul_of_nonneg_right hsum havg
    _ ≤ binomSum p g := by
            calc
              (∑ k ∈ Finset.Icc N (Fintype.card X), w k) * sizeAvg g N
                  ≤ ∑ k ∈ Finset.Icc N (Fintype.card X), w k * sizeAvg g k := by
                      rw [Finset.sum_mul]
                      apply Finset.sum_le_sum
                      intro k hk
                      have hNk : N ≤ k := (Finset.mem_Icc.mp hk).1
                      have hkn : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
                      exact mul_le_mul_of_nonneg_left
                        (sizeAvg_le_of_le g hmono N k hNk hkn) (hw_nonneg k)
              _ = ∑ k ∈ Finset.Icc N (Fintype.card X),
                    Binom.sizeSum g k * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      have hkn : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
                      rw [mul_comm]
                      simpa [w] using (term_eq_avg_w p g k hkn).symm
              _ ≤ binomSum p g := binomSum_ge_Icc p g hg hp0le hp1le N


end
end Binom2
end Submission
