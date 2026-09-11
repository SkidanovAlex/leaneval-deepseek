import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep

/-!
# Preprocessing (Park--Pham 2024, §2.2 Observations "reduction1" and "obs2").
PROVE `Submission.Pre.theorem_preprocess` below (no unfinished proofs).  Add helpers as needed.

## Goal
Turn arbitrary *weighted* selector data into "nice" layered data, losing only constants.

INPUT: finite X; F : Set (Set X) a family; lam : Set X → X → ℝ weights with
  hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i
  hnonnegtot : ∀ S ∈ F, 1 ≤ Sys.wtot lam S        (Σ_{i∈S} lam S i ≥ 1)

OUTPUT: a layered system N : Sys X (fields τ : ℕ, lv : Set X → X → ℕ, F : Set (Set X)) with:
  (a) N.FBounded            (∀ S ∈ N.F, ∀ i ∈ S, N.lv S i ≤ N.τ)
  (b) N.TotBound            (∀ S ∈ N.F, (10^8)⁻¹ ≤ N.totalWeight S)   [≥ 100^{-4}]
  (c) N.FLegal              (∀ S ∈ N.F, ∀ j ≤ N.τ, s_j := sCount N S j satisfies
       s_j = 0 ∨ (s_j is a power of 100 ∧ legalLower j ≤ (s_j:ℝ) ∧ (s_j:ℝ) < 2·100^j))
  (d) every original member has a trim: ∀ S ∈ F, ∃ S' ∈ N.F, S' ⊆ S
  (e) weight domination from each trim back to its original:
      ∀ S' ∈ N.F, ∃ S ∈ F, S' ⊆ S ∧ ∀ i ∈ S', lam0 S i ≥ wlev (N.lv S' i)

## The construction (see the paper; q := 100, wlev j = 100^{-j})
For each S ∈ F with Σλ ≥ 1:
 1. CAP: λ' i := min (lam S i) 1  for i ∈ S (0 outside S).  Note Σ λ' ≥ 1
    (prove: Σ min(λ,1) ≥ 1 whenever Σλ ≥ 1: either some λ_i ≥ 1, in which case the
    min-sum is ≥ ... ; or all λ_i < 1 and nothing changes).
 2. QUANTIZE: for i ∈ S set level j := ⌈log_{100}(1/λ' i)⌉ (any j ≥ 0 with
    100^{-j} ≤ λ' i < 100^{-(j-1)}, i.e. 100^{-j} ≤ λ' i and 100^{-j} ≥ λ' i / 100),
    so the new weight 100^{-j} satisfies λ' i / 100 ≤ 100^{-j} ≤ λ' i.  Total weight
    becomes ≥ (1/100)·Σλ' ≥ 1/100 = 10^{-2}.
 3. DROP high levels: pick τ := ⌊log_{100}(Fintype.card X)⌋ + 2 (or any τ with
    n·100^{-(τ+1)} ≤ 100^{-2}, e.g. τ := Fintype.card X works: prove n·100^{-(n+1)} ≤ 100^{-2}),
    and remove every element whose level j > τ.  These cost ≤ n·100^{-(τ+1)} ≤ 100^{-2},
    leaving total weight ≥ 10^{-2} - 10^{-2} = 0 -- CAREFUL: you need to keep ≥ 100^{-4};
    so instead of (1/100)·Σλ' ≥ 1/100 use that after quantizing and dropping, total is still
    ≥ 10^{-2} - 10^{-2}: adjust constants: better follow the paper: first cap (≥ 1), then
    quantize loses factor 100 (total ≥ 10^{-2}), then dropping levels > τ with τ :=
    ⌊log_{100} n⌋ + 2 loses ≤ n·100^{-(τ+1)} ≤ 100^{-2}, leaving ≥ 10^{-2} - 100^{-2} ≥ 10^{-3}·-ish;
    then obs2-style trimming (below) loses another ≤ factor 100 and small amounts, leaving
    ≥ 100^{-4} = 10^{-8}.
 4. OBS2 TRIM (make the profile legal): for each remaining S and each level j, keep a subset
    of the level-j elements of S so that the number s_j kept is a power of 100 with
    s_j ≥ max(1, 100^j/(100^4·(j+1)^2)) (when the level is used) -- concretely:
    - if fewer than 100^j/(100^4·(j+1)^2) elements remain at level j, drop the whole level
      (total loss ≤ Σ_j (100^j/(100^4 (j+1)^2))·100^{-j} < 100^{-3}, leaving ≥ 10^{-2}-10^{-2}-...;
      choose your constants carefully so the final total stays ≥ 10^{-8}),
    - otherwise round s_j down to the largest power of 100 at most s_j (losing at most a
      factor 100 of that level's weight; total weight stays ≥ 1/100 of what it was).
    Also enforce s_j < 2·100^j: if a level has ≥ 2·100^j elements keep only 100^j... (largest
    power of 100 strictly below 2·100^j): you may drop elements to get s_j < 2·100^j first
    (keep ≤ 100^j ≤ 2·100^j elements per level, losing ≤ 1/2 of the weight? -- adjust; the
    upper bound s_j < 2·100^j is used only mildly, feel free to instead guarantee
    s_j ≤ 100^j ≤ 2·100^j by truncating each level to at most 100^j elements, which loses
    at most... if s_j > 100^j keep 100^j of them: since weight of the kept part ≥ weight of
    the dropped part? not necessarily; but 100^{-j}·100^j = 1 ≥ (1/2)·s_j·100^{-j} when
    s_j ≤ 2·100^j, so first truncate to ≤ 2·100^j, then round down to a power of 100 which
    is ≤ 100^j < 2·100^j: total losses ≤ factor 4-ish: verify the final total ≥ 100^{-4}).

All the numeric constants are yours to manage: the ONLY hard requirements are the conclusions
(a)-(e) above.  (e) must hold for the ORIGINAL lam: after cap/quantize we have
100^{-lv i} ≤ min(lam S i, 1) ≤ lam S i for kept elements i, and trimming only removes
elements, so (e) holds with the original S.

For each S ∈ F the output is one layered member S' := (kept set with levels); different S's are
processed independently (S' need not be distinct across S).  Since N.F is a Set of subsets, and
levels are given by a function N.lv defined on ALL subsets (junk value for subsets not in N.F),
define N.lv S' i := (the level assigned to i when S was processed) if S' is one of the outputs,
and e.g. 0 otherwise -- you must ensure (a) N.lv S' i ≤ N.τ and (e) hold for the outputs; for
N.F members that are NOT outputs of any S... -- simplest: define N.F to be exactly the image of
the construction (the set of outputs), and define N.lv via a choice function so that on each
output S' it returns the assigned level function (N.lv S' i := assigned level for i ∈ S', and 0
for i ∉ S' -- but then i ∈ S' needs lv ≤ τ which holds by construction; also levelSet S' j =
{i ∈ S' | assigned level = j} is what you want).

Hint: build the whole construction as an explicit function on the finite data, or use
Classical.choose freely (it is allowed).  Work only in this file; import Submission.Deep for
Sys, wlev, TotBound, FLegal, FBounded, LegalEntry, IsQPower, legalLower, sCount, weight,
totalWeight.  The final declaration must be `theorem_preprocess` exactly as below (you may add
hypotheses only if they are provable from the given ones; you may add conclusions only if they
follow).
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Pre

open Frame
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]



open Sel.Deep
open Sel.Deep.Sys

lemma q_one_lt_nat : 1 < (q : ℕ) := by norm_num [q]
lemma q_two_le_nat : 2 ≤ (q : ℕ) := by norm_num [q]

lemma q_pow_add_one_le (j : ℕ) : j + 1 ≤ (q : ℕ) ^ j := by
  induction j with
  | zero => norm_num [q]
  | succ j ih =>
      calc
        (j + 1) + 1 ≤ 2 * (j + 1) := by omega
        _ ≤ 2 * (q : ℕ) ^ j := by exact Nat.mul_le_mul_left 2 ih
        _ = (q : ℕ) ^ j * 2 := by rw [mul_comm]
        _ ≤ (q : ℕ) ^ j * (q : ℕ) := by exact Nat.mul_le_mul_left ((q : ℕ) ^ j) q_two_le_nat
        _ = (q : ℕ) ^ (j + 1) := by rw [pow_succ]

lemma q_pow_gt_self (M : ℕ) : M < (q : ℕ) ^ (M + 1) := by
  have h := q_pow_add_one_le (M + 1)
  omega

lemma q_nat_pow_lt {a b : ℕ} (h : a < b) : (q : ℕ) ^ a < (q : ℕ) ^ b := by
  exact (Nat.pow_lt_pow_iff_right q_one_lt_nat).2 h

lemma q_nat_pow_le {a b : ℕ} (h : a ≤ b) : (q : ℕ) ^ a ≤ (q : ℕ) ^ b := by
  have h1 : 1 ≤ (q : ℕ) := by exact le_of_lt q_one_lt_nat
  exact pow_le_pow_right₀ h1 h

lemma q_nat_pow_le_iff {a b : ℕ} : (q : ℕ) ^ a ≤ (q : ℕ) ^ b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hb
    have hlt : b < a := lt_of_not_ge hb
    have hpow : (q : ℕ) ^ b < (q : ℕ) ^ a := q_nat_pow_lt hlt
    exact (not_lt_of_ge h) hpow
  · exact q_nat_pow_le

noncomputable def logq (M : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨M, q_pow_gt_self M⟩ : ∃ k : ℕ, M < (q : ℕ) ^ (k + 1))

lemma logq_spec (M : ℕ) : M < (q : ℕ) ^ (logq M + 1) := by
  classical
  have hex : ∃ k : ℕ, M < (q : ℕ) ^ (k + 1) := ⟨M, q_pow_gt_self M⟩
  exact Nat.find_spec hex

lemma logq_le_pow {M : ℕ} (hM : 1 ≤ M) : (q : ℕ) ^ logq M ≤ M := by
  classical
  by_cases hz : logq M = 0
  · rw [hz]
    norm_num [q]
    exact hM
  · have hpos : 1 ≤ logq M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hgt : ¬ M < (q : ℕ) ^ ((logq M - 1) + 1) := by
      intro hp
      have hmin := Nat.find_min' (m := logq M - 1)
        (⟨M, q_pow_gt_self M⟩ : ∃ k : ℕ, M < (q : ℕ) ^ (k + 1)) hp
      have hc : logq M ≤ logq M - 1 := by
        change Nat.find (⟨M, q_pow_gt_self M⟩ : ∃ k : ℕ, M < (q : ℕ) ^ (k + 1)) ≤ logq M - 1
        exact hmin
      omega
    have hsub : logq M - 1 + 1 = logq M := Nat.sub_add_cancel hpos
    have hn : ¬ M < (q : ℕ) ^ logq M := by simpa [hsub] using hgt
    exact le_of_not_gt hn

lemma logq_max {M k : ℕ} (hM : 1 ≤ M) (hk : (q : ℕ) ^ k ≤ M) : k ≤ logq M := by
  classical
  have hlt : (q : ℕ) ^ k < (q : ℕ) ^ (logq M + 1) := lt_of_le_of_lt hk (logq_spec M)
  have hklt : k < logq M + 1 := (Nat.pow_lt_pow_iff_right q_one_lt_nat).1 hlt
  omega

lemma logq_pow_real_le {M : ℕ} (hM : 1 ≤ M) :
    (M : ℝ) / (q : ℝ) ≤ ((q : ℕ) ^ logq M : ℝ) := by
  have hspec := logq_spec M
  have hpow : (q : ℕ) ^ (logq M + 1) = (q : ℕ) ^ logq M * (q : ℕ) := by
    rw [pow_succ]
  have hreal : (M : ℝ) < (((q : ℕ) ^ logq M * (q : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [hpow] using hspec)
  have hq : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  have hreal' : (M : ℝ) < (q : ℝ) ^ logq M * (q : ℝ) := by
    simpa [Nat.cast_pow, Nat.cast_mul] using hreal
  have hdiv : (M : ℝ) / (q : ℝ) < (q : ℝ) ^ logq M := by
    exact (div_lt_iff₀ hq).2 (by simpa [mul_comm] using hreal')
  exact le_of_lt hdiv

lemma q_real_pow_pos (j : ℕ) : 0 < (q : ℝ) ^ j := by positivity
lemma q_real_pow_ne_zero (j : ℕ) : (q : ℝ) ^ j ≠ 0 := ne_of_gt (q_real_pow_pos j)
lemma q_real_one_lt : (1 : ℝ) < (q : ℝ) := by norm_num [q]
lemma q_real_pow_lt {a b : ℕ} (h : a < b) : (q : ℝ) ^ a < (q : ℝ) ^ b := by
  exact pow_lt_pow_right₀ q_real_one_lt h
lemma q_real_pow_le {a b : ℕ} (h : a ≤ b) : (q : ℝ) ^ a ≤ (q : ℝ) ^ b := by
  exact pow_le_pow_right₀ (le_of_lt q_real_one_lt) h

lemma legalLower_nonneg (j : ℕ) : 0 ≤ legalLower j := by
  unfold legalLower
  positivity

lemma legalLower_pos (j : ℕ) : 0 < legalLower j := by
  unfold legalLower
  positivity

lemma legalLower_le_qpow (j : ℕ) : legalLower j ≤ (q : ℝ) ^ j := by
  unfold legalLower
  apply max_le
  · have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ j := by
      have hq0 : (1 : ℝ) ≤ (q : ℝ) := by norm_num [q]
      exact pow_le_pow_right₀ hq0 (Nat.zero_le j)
    exact hq1
  · have hpos1 : 0 < ((q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2)) := by positivity
    have hden : (1 : ℝ) ≤ (q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2) := by
      have hq4 : (1 : ℝ) ≤ (q : ℝ) ^ 4 := by norm_num [q]
      have hsq : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
        have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by nlinarith
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 2
        simpa using hp
      exact le_trans hq4 (le_mul_of_one_le_right (by positivity) hsq)
    have hqj : 0 < (q : ℝ) ^ j := q_real_pow_pos j
    calc
      (q : ℝ) ^ j / ((q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2)) ≤ (q : ℝ) ^ j := by
        rw [div_le_iff₀ hpos1]
        have : (q : ℝ) ^ j * 1 ≤ (q : ℝ) ^ j * ((q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hden (le_of_lt hqj)
        simpa using this

noncomputable def needExp (j : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨j, by
    have h1 : legalLower j ≤ (q : ℝ) ^ j := legalLower_le_qpow j
    exact ⟨le_rfl, h1⟩⟩ : ∃ e : ℕ, e ≤ j ∧ legalLower j ≤ (q : ℝ) ^ e)

lemma needExp_le (j : ℕ) : needExp j ≤ j := by
  classical
  exact (Nat.find_spec (⟨j, by
    have h1 : legalLower j ≤ (q : ℝ) ^ j := legalLower_le_qpow j
    exact ⟨le_rfl, h1⟩⟩ : ∃ e : ℕ, e ≤ j ∧ legalLower j ≤ (q : ℝ) ^ e)).1

lemma needExp_spec (j : ℕ) : legalLower j ≤ (q : ℝ) ^ needExp j := by
  classical
  exact (Nat.find_spec (⟨j, by
    have h1 : legalLower j ≤ (q : ℝ) ^ j := legalLower_le_qpow j
    exact ⟨le_rfl, h1⟩⟩ : ∃ e : ℕ, e ≤ j ∧ legalLower j ≤ (q : ℝ) ^ e)).2

lemma needExp_min {j e : ℕ} (he : e ≤ j) (hp : legalLower j ≤ (q : ℝ) ^ e) : needExp j ≤ e := by
  classical
  exact Nat.find_min' (m := e) (⟨j, by
    have h1 : legalLower j ≤ (q : ℝ) ^ j := legalLower_le_qpow j
    exact ⟨le_rfl, h1⟩⟩ : ∃ e : ℕ, e ≤ j ∧ legalLower j ≤ (q : ℝ) ^ e) ⟨he, hp⟩

lemma needExp_qpow_le (j : ℕ) : ((q : ℕ) ^ needExp j : ℝ) ≤ (100 : ℝ) * legalLower j := by
  by_cases hz : needExp j = 0
  · rw [hz]
    norm_num [q]
    have : (1 : ℝ) ≤ 100 * legalLower j := by
      have h1 : (1 : ℝ) ≤ legalLower j := by
        unfold legalLower
        exact le_max_left (1 : ℝ) (((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * (((j : ℝ) + 1) ^ 2)))
      nlinarith
    simpa using this
  · have hpos : 1 ≤ needExp j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hn : ¬ legalLower j ≤ (q : ℝ) ^ (needExp j - 1) := by
      intro hp
      have hmin := needExp_min (le_trans (Nat.sub_le _ _) (needExp_le j)) hp
      omega
    have hgt : legalLower j > (q : ℝ) ^ (needExp j - 1) := lt_of_not_ge hn
    calc
      ((q : ℕ) ^ needExp j : ℝ) = (q : ℝ) ^ needExp j := by norm_num [Nat.cast_pow]
      _ = (q : ℝ) ^ (needExp j - 1) * (q : ℝ) := by
        have hsub : needExp j - 1 + 1 = needExp j := Nat.sub_add_cancel hpos
        conv_lhs => rw [← hsub]
        rw [pow_succ]
      _ ≤ legalLower j * (q : ℝ) := by nlinarith [hgt, q_real_pow_pos (needExp j - 1)]
      _ = (100 : ℝ) * legalLower j := by
        rw [show (q : ℝ) = (100 : ℝ) by norm_num [q]]
        ring

/-- qlev -/
noncomputable def qlev (m : ℕ) (v : ℝ) : ℕ := by
  classical
  exact if h : ∃ j, j ≤ m ∧ 1 ≤ v * (q : ℝ) ^ j then Nat.find h else m + 1

lemma qlev_spec {m : ℕ} {v : ℝ} (hv : 0 < v) (hb : 1 ≤ v * (q : ℝ) ^ m) :
    qlev m v ≤ m ∧ 1 ≤ v * (q : ℝ) ^ (qlev m v) := by
  classical
  unfold qlev
  by_cases h : ∃ j, j ≤ m ∧ 1 ≤ v * (q : ℝ) ^ j
  · rw [dif_pos h]
    exact Nat.find_spec h
  · exfalso
    apply h
    exact ⟨m, le_rfl, hb⟩

lemma qlev_min {m : ℕ} {v : ℝ} (hv : 0 < v) (hb : 1 ≤ v * (q : ℝ) ^ m) {j : ℕ}
    (hj : j ≤ m) (hjp : 1 ≤ v * (q : ℝ) ^ j) : qlev m v ≤ j := by
  classical
  unfold qlev
  by_cases h : ∃ j, j ≤ m ∧ 1 ≤ v * (q : ℝ) ^ j
  · rw [dif_pos h]
    exact Nat.find_min' (m := j) h ⟨hj, hjp⟩
  · exfalso
    apply h
    exact ⟨m, le_rfl, hb⟩

lemma qlev_eq_succ {m : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hnb : ¬ 1 ≤ v * (q : ℝ) ^ m) :
    qlev m v = m + 1 := by
  classical
  unfold qlev
  by_cases h : ∃ j, j ≤ m ∧ 1 ≤ v * (q : ℝ) ^ j
  · exfalso
    apply hnb
    rcases h with ⟨j, hj, h1⟩
    exact le_trans h1 (mul_le_mul_of_nonneg_left (q_real_pow_le hj) hv0)
  · rw [dif_neg h]

/-- qlev ≤ m from the membership bound -/
lemma qlev_le_bound {m : ℕ} {v : ℝ} (hb : 1 ≤ v * (q : ℝ) ^ m) : qlev m v ≤ m := by
  classical
  unfold qlev
  by_cases h : ∃ j, j ≤ m ∧ 1 ≤ v * (q : ℝ) ^ j
  · rw [dif_pos h]
    exact (Nat.find_spec h).1
  · exfalso
    apply h
    exact ⟨m, le_rfl, hb⟩

lemma qlev_wlev_le {m : ℕ} {v : ℝ} (hv : 0 < v) (hb : 1 ≤ v * (q : ℝ) ^ m) :
    wlev (qlev m v) ≤ v := by
  have h := (qlev_spec hv hb).2
  have hpos : 0 < (q : ℝ) ^ qlev m v := q_real_pow_pos _
  have hd : (1 : ℝ) / (q : ℝ) ^ qlev m v ≤ v := (div_le_iff₀ hpos).2 h
  simpa [wlev] using hd

lemma qlev_wlev_ge {m : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hb : 1 ≤ v * (q : ℝ) ^ m) :
    v / (q : ℝ) ≤ wlev (qlev m v) := by
  classical
  have hspec := qlev_spec hv hb
  by_cases hz : qlev m v = 0
  · rw [hz]
    simp [wlev]
    have hq : (0 : ℝ) < (q : ℝ) := by norm_num [q]
    nlinarith [hv1, hq]
  · have hj0pos : 1 ≤ qlev m v := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    have hnp : ¬ 1 ≤ v * (q : ℝ) ^ (qlev m v - 1) := by
      intro hp
      have hmin := qlev_min hv hb (j := qlev m v - 1) (by omega) hp
      omega
    have hvq : v * (q : ℝ) ^ (qlev m v - 1) < 1 := lt_of_not_ge hnp
    have hsub : qlev m v - 1 + 1 = qlev m v := Nat.sub_add_cancel hj0pos
    have he : (q : ℝ) ^ qlev m v = (q : ℝ) ^ (qlev m v - 1) * (q : ℝ) := by
      conv_lhs => rw [← hsub]
      rw [pow_succ]
    have hle : v * (q : ℝ) ^ qlev m v ≤ (q : ℝ) := by
      rw [he]
      rw [← mul_assoc]
      calc
        v * (q : ℝ) ^ (qlev m v - 1) * (q : ℝ) ≤ 1 * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt hvq) (by positivity)
        _ = (q : ℝ) := by ring
    rw [wlev]
    have hq : (q : ℝ) ≠ 0 := q_ne_zero
    have hq0 : (q : ℝ) ^ qlev m v ≠ 0 := q_real_pow_ne_zero _
    field_simp [hq, hq0]
    nlinarith [hle]

/-! ## auxiliary arithmetic lemmas -/

/-- min(x,1) + min(y,1) ≥ min(x+y,1) for x,y ≥ 0 -/
lemma min_add_le_min_add_min {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min (x + y) 1 ≤ min x 1 + min y 1 := by
  by_cases hxy : x + y ≤ 1
  · have hx1 : x ≤ 1 := by linarith
    have hy1 : y ≤ 1 := by linarith
    rw [min_eq_left hx1, min_eq_left hy1, min_eq_left hxy]
  · have hgt : 1 ≤ x + y := by linarith
    rw [min_eq_right hgt]
    by_cases hx1 : 1 ≤ x
    · rw [min_eq_right hx1]
      have hmy : (0 : ℝ) ≤ min y 1 := le_min hy (by norm_num)
      linarith
    · have hxl : x ≤ 1 := le_of_lt (lt_of_not_ge hx1)
      rw [min_eq_left hxl]
      by_cases hy1 : 1 ≤ y
      · rw [min_eq_right hy1]
        linarith
      · have hyl : y ≤ 1 := le_of_lt (lt_of_not_ge hy1)
        rw [min_eq_left hyl]
        linarith

/-- Σ_j min(a_j,1) ≥ min(Σ a_j, 1) for nonneg a_j -/
lemma sum_min_one_ge_min_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    min (∑ i ∈ s, a i) 1 ≤ ∑ i ∈ s, min (a i) 1 := by
  classical
  let P : Finset ι → Prop := fun t =>
    (∀ i ∈ t, 0 ≤ a i) → min (∑ i ∈ t, a i) 1 ≤ ∑ i ∈ t, min (a i) 1
  have hall : ∀ t, P t := by
    intro t
    refine Finset.induction_on t ?base ?step
    · intro h
      simp
    · intro i s his ih2
      intro ha'
      have hai : 0 ≤ a i := ha' i (by simp)
      have hys : 0 ≤ (∑ x ∈ s, a x) := by
        exact Finset.sum_nonneg (fun x hx => ha' x (by simp [hx]))
      have hih : min (∑ x ∈ s, a x) 1 ≤ ∑ x ∈ s, min (a x) 1 :=
        ih2 (fun x hx => ha' x (by simp [hx]))
      rw [Finset.sum_insert his]
      rw [Finset.sum_insert his]
      calc
        min (a i + (∑ x ∈ s, a x)) 1 ≤ min (a i) 1 + min (∑ x ∈ s, a x) 1 :=
          min_add_le_min_add_min hai hys
        _ ≤ min (a i) 1 + (∑ x ∈ s, min (a x) 1) := by
          have h' : min (a i) 1 + min (∑ x ∈ s, a x) 1 ≤ min (a i) 1 + (∑ x ∈ s, min (a x) 1) :=
            add_le_add_right hih (min (a i) 1)
          simpa [add_comm, add_left_comm, add_assoc] using h' 
  exact hall s ha

/-- min(a,1) is monotone -/
lemma min_one_mono {a b : ℝ} (h : a ≤ b) : min a 1 ≤ min b 1 := by
  exact min_le_min h le_rfl

/-- min distributes: min(a·c)(b·c) = (min a b)·c for c ≥ 0 -/
lemma min_mul_of_nonneg {a b c : ℝ} (hc : 0 ≤ c) : min (a * c) (b * c) = min a b * c := by
  by_cases h : a ≤ b
  · have h' : a * c ≤ b * c := mul_le_mul_of_nonneg_right h hc
    rw [min_eq_left h, min_eq_left h']
  · have hb : b ≤ a := le_of_lt (lt_of_not_ge h)
    have hb' : b * c ≤ a * c := mul_le_mul_of_nonneg_right hb hc
    rw [min_eq_right hb, min_eq_right hb']

/-- Σ_{i ∈ A} min(f_i,1) ≥ 1 if Σ f_i ≥ 1 and 0 ≤ f -/
lemma sum_min_one_ge_one {ι : Type*} (A : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ A, 0 ≤ f i) (hge : 1 ≤ ∑ i ∈ A, f i) : 1 ≤ ∑ i ∈ A, min (f i) 1 := by
  by_cases hbig : ∃ i ∈ A, 1 ≤ f i
  · rcases hbig with ⟨i, hiA, hfi⟩
    have hsplit : A = insert i (A.erase i) := by
      rw [Finset.insert_erase hiA]
    rw [hsplit]
    rw [Finset.sum_insert (by simp)]
    calc
      (1 : ℝ) ≤ min (f i) 1 := by
        rw [min_eq_right hfi]
      _ ≤ min (f i) 1 + (∑ x ∈ A.erase i, min (f x) 1) := by
        exact le_add_of_nonneg_right (Finset.sum_nonneg (by
          intro x hx
          have hx0 : 0 ≤ f x := hf x (Finset.mem_of_mem_erase hx)
          exact le_min hx0 (by norm_num)))
  · have hsmall : ∀ i ∈ A, f i < 1 := by
      intro i hi
      exact lt_of_not_ge (by intro h; exact hbig ⟨i, hi, h⟩)
    have hmin : ∀ i ∈ A, min (f i) 1 = f i := by
      intro i hi
      exact min_eq_left (le_of_lt (hsmall i hi))
    rw [Finset.sum_congr rfl (by intro i hi; exact hmin i hi)]
    exact hge

/-- (n : ℝ) ≤ (q : ℝ)^(n-1) for n ≥ 1 -/
lemma nat_le_qpow_sub_one {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ≤ (q : ℝ) ^ (n - 1) := by
  have hnat : n ≤ (q : ℕ) ^ (n - 1) := by
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst hn0
          norm_num [q]
        · have ih' : n ≤ (q : ℕ) ^ (n - 1) := ih (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
          calc
            n + 1 ≤ (q : ℕ) ^ (n - 1) + 1 := by omega
            _ ≤ 2 * (q : ℕ) ^ (n - 1) := by omega
            _ ≤ (q : ℕ) * (q : ℕ) ^ (n - 1) := by
              exact Nat.mul_le_mul_right ((q : ℕ) ^ (n - 1)) q_two_le_nat
            _ = (q : ℕ) ^ n := by
              rw [← pow_succ']
              congr 1
              omega
  exact_mod_cast hnat

/-- n·q^{-n} ≤ 1/100 for n ≥ 1 -/
lemma nat_mul_wlev_le (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * wlev n ≤ (1 : ℝ) / (q : ℝ) := by
  have h := nat_le_qpow_sub_one hn
  have hw0 : 0 ≤ wlev n := wlev_nonneg n
  calc
    (n : ℝ) * wlev n ≤ ((q : ℝ) ^ (n - 1)) * wlev n := mul_le_mul_of_nonneg_right h hw0
    _ = (1 : ℝ) / (q : ℝ) := by
      have hq : (q : ℝ) ≠ 0 := q_ne_zero
      have hn1 : (n - 1) + 1 = n := by omega
      have hpow : (q : ℝ) ^ n = (q : ℝ) ^ (n - 1) * (q : ℝ) := by
        conv_lhs => rw [← hn1]
        rw [pow_succ]
      unfold wlev
      rw [hpow]
      field_simp [hq]

/-- Σ_{k ∈ range n} (1/2)^k ≤ 2 -/
lemma sum_half_pow_le_two (n : ℕ) : (∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k) ≤ 2 := by
  have hgeom := geom_sum_eq (x := ((1 : ℝ) / 2)) (by norm_num) n
  calc
    (∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k) = (((1 : ℝ) / 2) ^ n - 1) / ((1 : ℝ) / 2 - 1) := hgeom
    _ = 2 - 2 * ((1 : ℝ) / 2) ^ n := by
      field_simp
      ring
    _ ≤ 2 := by
      have hnon : 0 ≤ 2 * ((1 : ℝ) / 2) ^ n := by positivity
      linarith


/-! ## drop-loss and profile bounds -/

/-- legalLower j = 1 for j ≤ 4 -/
lemma legalLower_eq_one_of_le4 {j : ℕ} (hj : j ≤ 4) : legalLower j = 1 := by
  unfold legalLower
  have hX : ((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) ≤ 1 := by
    have hqj4 : (q : ℝ) ^ j ≤ (q : ℝ) ^ 4 := q_real_pow_le (by omega)
    have hsq : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
      have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by nlinarith
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 2
      simpa using hp
    have hpos : 0 < (q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2) := by positivity
    have hle : (q : ℝ) ^ j ≤ (q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2) :=
      le_trans hqj4 (by
        simpa using (mul_le_mul_of_nonneg_left hsq (le_of_lt (q_real_pow_pos 4))))
    exact (div_le_iff₀ hpos).2 (by simpa using hle)
  exact max_eq_left hX

/-- needExp j = 0 for j ≤ 4 -/
lemma needExp_zero_of_le4 {j : ℕ} (hj : j ≤ 4) : needExp j = 0 := by
  apply le_antisymm
  · have h0j : 0 ≤ j := Nat.zero_le j
    have h01 : legalLower j ≤ (q : ℝ) ^ 0 := by
      simp [legalLower_eq_one_of_le4 hj]
    exact needExp_min h0j h01
  · exact Nat.zero_le (needExp j)

/-- legalLower j * wlev j ≤ wlev j + 1/(q^4 (j+1)^2) -/
lemma legalLower_mul_wlev_le (j : ℕ) :
    legalLower j * wlev j ≤ wlev j + (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) := by
  unfold legalLower wlev
  have hX : (0 : ℝ) ≤ ((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) := by positivity
  have hmax : max 1 (((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))) ≤
      1 + ((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) := by
    exact max_le (by linarith) (by linarith)
  have hqj : (q : ℝ) ^ j ≠ 0 := q_real_pow_ne_zero j
  calc
    max 1 (((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))) * ((q : ℝ) ^ j)⁻¹
        ≤ (1 + ((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))) * ((q : ℝ) ^ j)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hmax (by positivity)
    _ = ((q : ℝ) ^ j)⁻¹ + (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) := by
          have hprod : ((q : ℝ) ^ j) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) * ((q : ℝ) ^ j)⁻¹ =
              (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2)) := by
            field_simp [hqj]
          rw [add_mul, one_mul]
          rw [hprod]

/-- wlev(a + t) = wlev a · (q⁻¹)^t -/
lemma wlev_add (a t : ℕ) : wlev (a + t) = wlev a * ((q : ℝ)⁻¹) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        wlev (a + (t + 1)) = wlev ((a + t) + 1) := by rw [← Nat.add_assoc]
        _ = (q : ℝ)⁻¹ * wlev (a + t) := wlev_succ (a + t)
        _ = (q : ℝ)⁻¹ * (wlev a * ((q : ℝ)⁻¹) ^ t) := by rw [ih]
        _ = wlev a * ((q : ℝ)⁻¹) ^ (t + 1) := by
          rw [pow_succ]
          ring

/-- decay wlev j ≤ wlev 5 * (1/2)^{j-5} for j ≥ 5 -/
lemma wlev_decay {j : ℕ} (hj : 5 ≤ j) : wlev j ≤ wlev 5 * ((1 : ℝ) / 2) ^ (j - 5) := by
  have hw : wlev j = wlev 5 * ((q : ℝ)⁻¹) ^ (j - 5) := by
    calc
      wlev j = wlev (5 + (j - 5)) := by congr 1; omega
      _ = wlev 5 * ((q : ℝ)⁻¹) ^ (j - 5) := wlev_add 5 (j - 5)
  rw [hw]
  have hqinv : (q : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by norm_num [q]
  have hpow : ((q : ℝ)⁻¹) ^ (j - 5) ≤ ((1 : ℝ) / 2) ^ (j - 5) := by
    exact pow_le_pow_left₀ (by norm_num) hqinv (j - 5)
  exact mul_le_mul_of_nonneg_left hpow (wlev_nonneg 5)

/-- wlev j ≤ 2·(wlev j − wlev (j+1)) -/
lemma two_sub_wlev (j : ℕ) : wlev j ≤ 2 * (wlev j - wlev (j + 1)) := by
  have hsucc : wlev (j + 1) = (q : ℝ)⁻¹ * wlev j := wlev_succ j
  have hw : 0 ≤ wlev j := wlev_nonneg j
  have hq : (0 : ℝ) ≤ 2 * (1 - (q : ℝ)⁻¹) - 1 := by norm_num [q]
  rw [hsucc]
  have h : 0 ≤ 2 * (wlev j - (q : ℝ)⁻¹ * wlev j) - wlev j := by
    have hh : 2 * (wlev j - (q : ℝ)⁻¹ * wlev j) - wlev j =
        (2 * (1 - (q : ℝ)⁻¹) - 1) * wlev j := by ring
    rw [hh]
    exact mul_nonneg hq hw
  linarith

/-- Σ_{j ∈ Icc 5 T} wlev j ≤ 2·wlev 5 -/
lemma sum_wlev_high_le (T : ℕ) : (∑ j ∈ Finset.Icc 5 T, wlev j) ≤ 2 * wlev 5 := by
  classical
  by_cases hT : 5 ≤ T
  · have htele : (∑ j ∈ Finset.Icc 5 T, (wlev (j + 1) - wlev j)) = wlev (T + 1) - wlev 5 :=
      Finset.sum_Icc_sub hT (fun j : ℕ => wlev j)
    have hneg : (∑ j ∈ Finset.Icc 5 T, (wlev j - wlev (j + 1))) = wlev 5 - wlev (T + 1) := by
      calc
        (∑ j ∈ Finset.Icc 5 T, (wlev j - wlev (j + 1)))
            = ∑ j ∈ Finset.Icc 5 T, -(wlev (j + 1) - wlev j) := by
              apply Finset.sum_congr rfl; intro j hj; ring
        _ = -(∑ j ∈ Finset.Icc 5 T, (wlev (j + 1) - wlev j)) := by rw [Finset.sum_neg_distrib]
        _ = wlev 5 - wlev (T + 1) := by rw [htele]; ring
    calc
      (∑ j ∈ Finset.Icc 5 T, wlev j) ≤ ∑ j ∈ Finset.Icc 5 T, 2 * (wlev j - wlev (j + 1)) := by
        exact Finset.sum_le_sum (fun j hj => two_sub_wlev j)
      _ = 2 * (∑ j ∈ Finset.Icc 5 T, (wlev j - wlev (j + 1))) := by rw [Finset.mul_sum]
      _ = 2 * (wlev 5 - wlev (T + 1)) := by rw [hneg]
      _ ≤ 2 * wlev 5 := by
        have hw : 0 ≤ wlev (T + 1) := wlev_nonneg (T + 1)
        nlinarith
  · have hI : Finset.Icc 5 T = (∅ : Finset ℕ) := by
      ext j
      simp
      omega
    have hsum0 : (∑ j ∈ Finset.Icc 5 T, wlev j) = 0 := by
      rw [hI]
      simp
    rw [hsum0]
    exact mul_nonneg (by norm_num) (wlev_nonneg 5)

/-- Σ_{j ∈ Icc 5 T} 1/((j+1)·j) ≤ 1/5 -/
lemma sum_inv_prod_high_le (T : ℕ) :
    (∑ j ∈ Finset.Icc 5 T, (1 : ℝ) / (((j : ℝ) + 1) * (j : ℝ))) ≤ (1 : ℝ) / 5 := by
  classical
  by_cases hT : 5 ≤ T
  · have htel : (∑ j ∈ Finset.Icc 5 T, ((1 : ℝ) / ((j : ℝ) + 1) - (1 : ℝ) / (j : ℝ))) =
      (1 : ℝ) / ((T : ℝ) + 1) - 1 / (5 : ℝ) := by
      have hsum := Finset.sum_Icc_sub hT (fun i : ℕ => (1 : ℝ) / (i : ℝ))
      simpa [Nat.cast_add, Nat.cast_one] using hsum
    calc
      (∑ j ∈ Finset.Icc 5 T, (1 : ℝ) / (((j : ℝ) + 1) * (j : ℝ)))
          = ∑ j ∈ Finset.Icc 5 T, ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / ((j : ℝ) + 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjp : (j : ℝ) ≠ 0 := by
              have hj5 : 5 ≤ j := (Finset.mem_Icc.mp hj).1
              exact_mod_cast (by omega : j ≠ 0)
            have hjp1 : ((j : ℝ) + 1) ≠ 0 := by positivity
            field_simp [hjp, hjp1]
            ring
      _ = ∑ j ∈ Finset.Icc 5 T, -((1 : ℝ) / ((j : ℝ) + 1) - (1 : ℝ) / (j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = - (∑ j ∈ Finset.Icc 5 T, ((1 : ℝ) / ((j : ℝ) + 1) - (1 : ℝ) / (j : ℝ))) := by
            rw [Finset.sum_neg_distrib]
      _ = - ((1 : ℝ) / ((T : ℝ) + 1) - 1 / (5 : ℝ)) := by rw [htel]
      _ ≤ (1 : ℝ) / 5 := by
            have hle : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
            linarith
  · have hI : Finset.Icc 5 T = (∅ : Finset ℕ) := by
      ext j
      simp
      omega
    simp [hI]

/-- Σ_{j ∈ Icc 5 T} 1/(j+1)^2 ≤ 1/5 -/
lemma sum_inv_sq_high_le (T : ℕ) :
    (∑ j ∈ Finset.Icc 5 T, (1 : ℝ) / ((j + 1 : ℝ) ^ 2)) ≤ (1 : ℝ) / 5 := by
  calc
    (∑ j ∈ Finset.Icc 5 T, (1 : ℝ) / ((j + 1 : ℝ) ^ 2))
        ≤ ∑ j ∈ Finset.Icc 5 T, (1 : ℝ) / (((j : ℝ) + 1) * (j : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj5 : 5 ≤ j := (Finset.mem_Icc.mp hj).1
          have hjp : (0 : ℝ) < (j : ℝ) := by
            exact_mod_cast (by omega : 0 < j)
          have hden : ((j : ℝ) + 1) * (j : ℝ) ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith : (j : ℝ) ≤ (j : ℝ) + 1) (by positivity)
          have hy : 0 < ((j : ℝ) + 1) * (j : ℝ) := by positivity
          have hv := one_div_le_one_div_of_le hy hden
          -- hv : 1 / ((j+1)*(j+1)) ≤ 1 / (((j+1)*j))
          simpa [sq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hv
    _ ≤ (1 : ℝ) / 5 := sum_inv_prod_high_le T




/-! ## per-S construction -/

/-- capped weight min(λ,1) -/
noncomputable def capv (lam : Set X → X → ℝ) (S : Set X) (i : X) : ℝ := min (lam S i) 1

/-- quantized level of i (w.r.t. the capped weight) -/
noncomputable def lvl (lam : Set X → X → ℝ) (S : Set X) (i : X) : ℕ := qlev (Fintype.card X) (capv lam S i)

/-- elements of S that can be kept: 1 ≤ capv·q^{τ} -/
noncomputable def keepElts (lam : Set X → X → ℝ) (S : Set X) : Finset X := by
  classical
  exact (S.toFinset).filter (fun i => 1 ≤ capv lam S i * (q : ℝ) ^ (Fintype.card X))

/-- level-j class -/
noncomputable def cls (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : Finset X := by
  classical
  exact (keepElts lam S).filter (fun i => lvl lam S i = j)

/-- whether level j is "kept" for class size c -/
def keptLvlN (j c : ℕ) : Prop := (q : ℕ) ^ needExp j ≤ c

/-- number kept at level j with class size c -/
noncomputable def keepNum (j c : ℕ) : ℕ :=
  if keptLvlN j c then (q : ℕ) ^ logq (min c ((q : ℕ) ^ j)) else 0

/-- (min a b : ℕ) casts to real min -/
lemma min_nat_cast {a b : ℕ} : (((min a b : ℕ) : ℝ) = min (a : ℝ) (b : ℝ)) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h : (a : ℝ) ≤ (b : ℝ))]
  · have hb : b ≤ a := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hb, min_eq_right (by exact_mod_cast hb : (b : ℝ) ≤ (a : ℝ))]

lemma keepNum_eq_keep {j c : ℕ} (h : keptLvlN j c) :
    keepNum j c = (q : ℕ) ^ logq (min c ((q : ℕ) ^ j)) := by
  unfold keepNum
  rw [if_pos h]

lemma keepNum_eq_zero {j c : ℕ} (h : ¬ keptLvlN j c) : keepNum j c = 0 := by
  unfold keepNum
  rw [if_neg h]

/-- if kept then c ≥ 1 -/
lemma keptLvlN_ge_one {j c : ℕ} (h : keptLvlN j c) : 1 ≤ c := by
  have h1 : (1 : ℕ) ≤ (q : ℕ) ^ needExp j := by
    have : (q : ℕ) ^ 0 ≤ (q : ℕ) ^ needExp j := q_nat_pow_le (Nat.zero_le (needExp j))
    simpa using this
  exact le_trans h1 h

/-- if kept then min c q^j ≥ 1 -/
lemma kept_min_one {j c : ℕ} (h : keptLvlN j c) : 1 ≤ min c ((q : ℕ) ^ j) := by
  have hc : 1 ≤ c := keptLvlN_ge_one h
  have hq : 1 ≤ (q : ℕ) ^ j := by
    have : (q : ℕ) ^ 0 ≤ (q : ℕ) ^ j := q_nat_pow_le (Nat.zero_le j)
    simpa using this
  exact le_min hc hq

/-- keepNum ≤ c -/
lemma keepNum_le_card {j c : ℕ} : keepNum j c ≤ c := by
  by_cases h : keptLvlN j c
  · rw [keepNum_eq_keep h]
    calc
      (q : ℕ) ^ logq (min c ((q : ℕ) ^ j)) ≤ min c ((q : ℕ) ^ j) := logq_le_pow (kept_min_one h)
      _ ≤ c := min_le_left _ _
  · rw [keepNum_eq_zero h]
    exact Nat.zero_le c

/-- keepNum ≤ q^j -/
lemma keepNum_le_qpow {j c : ℕ} : keepNum j c ≤ (q : ℕ) ^ j := by
  by_cases h : keptLvlN j c
  · rw [keepNum_eq_keep h]
    calc
      (q : ℕ) ^ logq (min c ((q : ℕ) ^ j)) ≤ min c ((q : ℕ) ^ j) := logq_le_pow (kept_min_one h)
      _ ≤ (q : ℕ) ^ j := min_le_right _ _
  · rw [keepNum_eq_zero h]
    exact Nat.zero_le ((q : ℕ) ^ j)

/-- keepNum is 0 or a power of 100 -/
lemma keepNum_zero_or_qpow {j c : ℕ} : keepNum j c = 0 ∨ ∃ k : ℕ, keepNum j c = (q : ℕ) ^ k := by
  by_cases h : keptLvlN j c
  · right
    refine ⟨logq (min c ((q : ℕ) ^ j)), ?_⟩
    rw [keepNum_eq_keep h]
  · left
    exact keepNum_eq_zero h

/-- kept: keepNum ≥ q^{needExp j} -/
lemma keepNum_ge_need {j c : ℕ} (h : keptLvlN j c) : (q : ℕ) ^ needExp j ≤ keepNum j c := by
  rw [keepNum_eq_keep h]
  have hle1 : (q : ℕ) ^ needExp j ≤ c := h
  have hle2 : (q : ℕ) ^ needExp j ≤ (q : ℕ) ^ j := q_nat_pow_le (needExp_le j)
  have hM : (q : ℕ) ^ needExp j ≤ min c ((q : ℕ) ^ j) := le_min hle1 hle2
  exact q_nat_pow_le (logq_max (kept_min_one h) hM)

/-- legalLower ≤ keepNum (real) when kept -/
lemma keepNum_lower {j c : ℕ} (h : keptLvlN j c) :
    legalLower j ≤ (keepNum j c : ℝ) := by
  have hq : ((q : ℕ) ^ needExp j : ℝ) ≤ (keepNum j c : ℝ) := by exact_mod_cast keepNum_ge_need h
  have hc := needExp_spec j
  have hc' : legalLower j ≤ ((q : ℕ) ^ needExp j : ℝ) := by
    simpa [Nat.cast_pow] using hc
  exact le_trans hc' hq

/-- keepNum < 2·q^j (real) -/
lemma keepNum_upper {j c : ℕ} : (keepNum j c : ℝ) < 2 * (q : ℝ) ^ j := by
  have h1 : (keepNum j c : ℝ) ≤ ((q : ℕ) ^ j : ℝ) := by exact_mod_cast keepNum_le_qpow
  calc
    (keepNum j c : ℝ) ≤ (q : ℝ) ^ j := by simpa [Nat.cast_pow] using h1
    _ < 2 * (q : ℝ) ^ j := by
      have hpos : 0 < (q : ℝ) ^ j := q_real_pow_pos j
      nlinarith

/-- kept: per-level weight lower bound -/
lemma keepNum_weight {j c : ℕ} (h : keptLvlN j c) :
    min ((c : ℝ) * wlev j) 1 / (q : ℝ) ≤ (keepNum j c : ℝ) * wlev j := by
  have hM1 : 1 ≤ min c ((q : ℕ) ^ j) := kept_min_one h
  have hlg := logq_pow_real_le hM1
  have hkn : (((min c ((q : ℕ) ^ j) : ℕ) : ℝ) / (q : ℝ)) ≤ (keepNum j c : ℝ) := by
    rw [keepNum_eq_keep h]
    simpa using hlg
  have hw0 : 0 ≤ wlev j := wlev_nonneg j
  have h2 : ((((min c ((q : ℕ) ^ j) : ℕ) : ℝ) / (q : ℝ)) * wlev j) ≤
      (keepNum j c : ℝ) * wlev j := mul_le_mul_of_nonneg_right hkn hw0
  have hMid : min ((c : ℝ) * wlev j) 1 = (((min c ((q : ℕ) ^ j) : ℕ) : ℝ) * wlev j) := by
    have hmul : min (((c : ℝ)) * wlev j) (((((q : ℕ) ^ j : ℕ) : ℝ)) * wlev j) =
        (((min c ((q : ℕ) ^ j) : ℕ) : ℝ)) * wlev j := by
      -- min (a w) (b w) = (min a b) w  with a := (c:ℝ), b := ((q:ℕ)^j : ℝ)
      rw [min_mul_of_nonneg hw0]
      congr 1
      -- min over reals of casts equals cast of min over naturals
      exact min_nat_cast.symm
    have hqj : (((q : ℕ) ^ j : ℕ) : ℝ) * wlev j = 1 := by
      unfold wlev
      have hq : (q : ℝ) ≠ 0 := q_ne_zero
      rw [Nat.cast_pow]
      field_simp [hq]
    calc
      min ((c : ℝ) * wlev j) 1 = min ((c : ℝ) * wlev j) ((((q : ℕ) ^ j : ℕ) : ℝ) * wlev j) := by
        rw [hqj]
      _ = (((min c ((q : ℕ) ^ j) : ℕ) : ℝ)) * wlev j := hmul
  calc
    min ((c : ℝ) * wlev j) 1 / (q : ℝ) = ((((min c ((q : ℕ) ^ j) : ℕ) : ℝ)) * wlev j) / (q : ℝ) := by
      rw [hMid]
    _ = ((((min c ((q : ℕ) ^ j) : ℕ) : ℝ) / (q : ℝ)) * wlev j) := by
      have hq : (q : ℝ) ≠ 0 := q_ne_zero
      field_simp [hq]
    _ ≤ (keepNum j c : ℝ) * wlev j := h2


/-- class size of level j -/
noncomputable def cS (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : ℕ := (cls lam S j).card

/-- kept elements at level j -/
noncomputable def keepFin (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : Finset X := by
  classical
  exact Classical.choose (Finset.exists_subset_card_eq
    (keepNum_le_card (j := j) (c := cS lam S j)))

lemma keepFin_spec (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) :
    keepFin lam S j ⊆ cls lam S j ∧ (keepFin lam S j).card = keepNum j (cS lam S j) := by
  classical
  unfold keepFin
  exact Classical.choose_spec (Finset.exists_subset_card_eq
    (keepNum_le_card (j := j) (c := cS lam S j)))

lemma keepFin_subset_cls (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) :
    keepFin lam S j ⊆ cls lam S j := (keepFin_spec lam S j).1

lemma keepFin_card (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) :
    (keepFin lam S j).card = keepNum j (cS lam S j) := (keepFin_spec lam S j).2

lemma mem_cls_iff (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) {i : X} :
    i ∈ cls lam S j ↔ i ∈ keepElts lam S ∧ lvl lam S i = j := by
  classical
  unfold cls
  simp

lemma keepElts_subset_S (lam : Set X → X → ℝ) (S : Set X) : keepElts lam S ⊆ S.toFinset := by
  classical
  intro i hi
  exact (Finset.mem_filter.mp hi).1

lemma cls_subset_keepElts (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : cls lam S j ⊆ keepElts lam S := by
  intro i hi
  exact (mem_cls_iff lam S j).1 hi |>.1

lemma keepFin_subset_keepElts (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) :
    keepFin lam S j ⊆ keepElts lam S := fun i hi => cls_subset_keepElts lam S j (keepFin_subset_cls lam S j hi)

/-- elements of keepFin have the class level -/
lemma level_of_keepFin (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) {i : X} (hi : i ∈ keepFin lam S j) :
    lvl lam S i = j := (mem_cls_iff lam S j).1 (keepFin_subset_cls lam S j hi) |>.2

/-- the trimmed finset -/
noncomputable def trimF (lam : Set X → X → ℝ) (S : Set X) : Finset X := by
  classical
  exact (Finset.range (Fintype.card X + 1)).biUnion (fun j => keepFin lam S j)

/-- trimF ⊆ S -/
lemma trimF_subset_S (lam : Set X → X → ℝ) (S : Set X) : (trimF lam S : Set X) ⊆ S := by
  classical
  intro i hi
  rcases (Finset.mem_biUnion.mp hi) with ⟨j, hj, hij⟩
  have h1 : i ∈ keepElts lam S := keepFin_subset_keepElts lam S j hij
  have hE : i ∈ S.toFinset := keepElts_subset_S lam S h1
  exact (by simpa using hE : i ∈ S)

/-- members of trimF have level ≤ card X -/
lemma level_le_Tau_of_mem_trimF (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hi : i ∈ (trimF lam S : Set X)) : lvl lam S i ≤ Fintype.card X := by
  classical
  rcases (Finset.mem_biUnion.mp hi) with ⟨j, hj, hij⟩
  have hl : lvl lam S i = j := level_of_keepFin lam S j hij
  rw [hl]
  have : j < Fintype.card X + 1 := Finset.mem_range.mp hj
  omega

/-- level of keepElts members is ≤ card X -/
lemma lvl_le_Tau_of_mem_keepElts (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hi : i ∈ keepElts lam S) : lvl lam S i ≤ Fintype.card X := by
  classical
  unfold keepElts at hi
  have hb : 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := by
    simpa using (Finset.mem_filter.mp hi).2
  unfold lvl
  exact qlev_le_bound hb

/-- level sets of trimF -/
lemma levelSet_trimF (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) :
    ((trimF lam S : Set X) ∩ {i | lvl lam S i = j}) = (keepFin lam S j : Set X) := by
  classical
  ext i
  constructor
  · intro hi
    have hiT : i ∈ (trimF lam S : Set X) := hi.1
    have hij : lvl lam S i = j := hi.2
    rcases (Finset.mem_biUnion.mp hiT) with ⟨k, hk, hik⟩
    have hkl : lvl lam S i = k := level_of_keepFin lam S k hik
    have hkj : k = j := by rw [← hkl, hij]
    simpa [hkj] using hik
  · intro hi
    have hiF : i ∈ keepFin lam S j := by simpa using hi
    have hl : lvl lam S i = j := level_of_keepFin lam S j hiF
    have hk : ∃ k ∈ Finset.range (Fintype.card X + 1), i ∈ keepFin lam S k := by
      refine ⟨j, ?_, hiF⟩
      have hj : j ≤ Fintype.card X := by
        have hke : i ∈ keepElts lam S := keepFin_subset_keepElts lam S j hiF
        have hle := lvl_le_Tau_of_mem_keepElts lam S hke
        rwa [hl] at hle
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    constructor
    · exact Finset.mem_biUnion.mpr hk
    · exact hl


/-! ## per-S weight analysis -/

/-- sum over level fibers -/
lemma sum_fiber (A : Finset X) (g : X → ℕ) (w : ℕ → ℝ) (m : ℕ)
    (hm : ∀ i ∈ A, g i ≤ m) :
    (∑ j ∈ Finset.range (m+1), ((A.filter (fun i => g i = j)).card : ℝ) * w j)
      = ∑ i ∈ A, w (g i) := by
  classical
  have hsplit : (∑ j ∈ Finset.range (m+1), ((A.filter (fun i => g i = j)).card : ℝ) * w j)
      = (∑ j ∈ Finset.range (m+1), (A.filter (fun i => g i = j)).sum (fun _ => w j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hwj : (∑ j ∈ Finset.range (m+1), (A.filter (fun i => g i = j)).sum (fun _ => w j))
      = (∑ j ∈ Finset.range (m+1), (A.filter (fun i => g i = j)).sum (fun i => w (g i))) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have hgj : g i = j := (Finset.mem_filter.mp hi).2
    rw [hgj]
  have hdisj : ((Finset.range (m+1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => A.filter (fun i => g i = j)) := by
    intro j hj k hk hjk
    change Disjoint (A.filter (fun i => g i = j)) (A.filter (fun i => g i = k))
    rw [Finset.disjoint_left]
    intro i hi hik
    have hgj : g i = j := (Finset.mem_filter.mp hi).2
    have hgk : g i = k := (Finset.mem_filter.mp hik).2
    exact hjk (by rw [← hgj, hgk])
  have hunion : (Finset.range (m+1)).biUnion (fun j => A.filter (fun i => g i = j)) = A := by
    ext i
    constructor
    · intro hi
      rcases (Finset.mem_biUnion.mp hi) with ⟨j, hj, hij⟩
      exact (Finset.mem_filter.mp hij).1
    · intro hi
      refine (Finset.mem_biUnion.mpr) ⟨g i, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm i hi))
      · exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  calc
    (∑ j ∈ Finset.range (m+1), ((A.filter (fun i => g i = j)).card : ℝ) * w j)
        = (∑ j ∈ Finset.range (m+1), (A.filter (fun i => g i = j)).sum (fun _ => w j)) := hsplit
    _ = (∑ j ∈ Finset.range (m+1), (A.filter (fun i => g i = j)).sum (fun i => w (g i))) := hwj
    _ = ∑ i ∈ (Finset.range (m+1)).biUnion (fun j => A.filter (fun i => g i = j)), w (g i) := by
        rw [Finset.sum_biUnion hdisj]
    _ = ∑ i ∈ A, w (g i) := by rw [hunion]

/-- capv ≥ 0 -/
lemma capv_nonneg (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hnon : ∀ i ∈ S, 0 ≤ lam S i) (hiS : i ∈ S) : 0 ≤ capv lam S i := by
  unfold capv
  exact le_min (hnon i hiS) (by norm_num)

/-- capv ≤ 1 -/
lemma capv_le_one (lam : Set X → X → ℝ) (S : Set X) (i : X) : capv lam S i ≤ 1 := by
  unfold capv
  exact min_le_right (lam S i) (1 : ℝ)

/-- membership in keepElts -/
lemma mem_keepElts_iff (lam : Set X → X → ℝ) (S : Set X) (i : X) :
    i ∈ keepElts lam S ↔ i ∈ S ∧ 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := by
  classical
  unfold keepElts
  simp

/-- keepElts members have positive capv -/
lemma capv_pos_of_keep (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hi : i ∈ keepElts lam S) : 0 < capv lam S i := by
  have hb : 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := (mem_keepElts_iff lam S i).1 hi |>.2
  have hq : 0 < (q : ℝ) ^ Fintype.card X := q_real_pow_pos (Fintype.card X)
  -- 1 ≤ v·q^n and q^n > 0 ⟹ v ≥ q^{-n} > 0
  have hv : capv lam S i ≥ (1 : ℝ) / (q : ℝ) ^ Fintype.card X := by
    exact (div_le_iff₀ hq).2 hb
  have hpos : 0 < (1 : ℝ) / (q : ℝ) ^ Fintype.card X := by positivity
  linarith

/-- level weight ≤ capv -/
lemma wlev_lvl_le_capv (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hi : i ∈ keepElts lam S) : wlev (lvl lam S i) ≤ capv lam S i := by
  have hb : 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := (mem_keepElts_iff lam S i).1 hi |>.2
  have hv : 0 < capv lam S i := capv_pos_of_keep lam S hi
  have h := qlev_wlev_le (m := Fintype.card X) hv hb
  simpa [lvl] using h

/-- capv/100 ≤ level weight -/
lemma capv_div_q_le_wlev_lvl (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hi : i ∈ keepElts lam S) : capv lam S i / (q : ℝ) ≤ wlev (lvl lam S i) := by
  have hb : 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := (mem_keepElts_iff lam S i).1 hi |>.2
  have hv : 0 < capv lam S i := capv_pos_of_keep lam S hi
  have hv1 : capv lam S i ≤ 1 := capv_le_one lam S i
  have h := qlev_wlev_ge (m := Fintype.card X) hv hv1 hb
  simpa [lvl] using h


/-- generalize nat_mul_wlev_le to all n -/
lemma nat_mul_wlev_le_all (n : ℕ) : (n : ℝ) * wlev n ≤ (1 : ℝ) / (q : ℝ) := by
  by_cases hn : 1 ≤ n
  · exact nat_mul_wlev_le n hn
  · have hn0 : n = 0 := by omega
    subst n
    simp [wlev]

/-- dropped elements have tiny capv: capv < q^{-Tau} -/
lemma capv_lt_wlev_of_not_keep (lam : Set X → X → ℝ) (S : Set X) {i : X}
    (hiS : i ∈ S) (hnot : ¬ 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X) :
    capv lam S i < wlev (Fintype.card X) := by
  have hlt : capv lam S i * (q : ℝ) ^ Fintype.card X < 1 := lt_of_not_ge hnot
  have hqpos : 0 < (q : ℝ) ^ Fintype.card X := q_real_pow_pos _
  have hv : capv lam S i < (1 : ℝ) / (q : ℝ) ^ Fintype.card X := by
    exact (lt_div_iff₀ hqpos).2 hlt
  simpa [wlev] using hv

/-- drop sum bound -/
lemma drop_sum_le (lam : Set X → X → ℝ) (S : Set X)
    (hSnon : ∀ i ∈ S, 0 ≤ lam S i) :
    (∑ i ∈ S.toFinset, capv lam S i) - (∑ i ∈ keepElts lam S, capv lam S i) ≤ (1 : ℝ) / (q : ℝ) := by
  classical
  let drop : Finset X := S.toFinset \ keepElts lam S
  have hsub : keepElts lam S ⊆ S.toFinset := keepElts_subset_S lam S
  have hsum : (∑ i ∈ drop, capv lam S i) + (∑ i ∈ keepElts lam S, capv lam S i) =
      ∑ i ∈ S.toFinset, capv lam S i := by
    simpa [drop] using (Finset.sum_sdiff hsub (s₁ := keepElts lam S) (s₂ := S.toFinset)
      (f := fun i => capv lam S i))
  have hle : (∑ i ∈ drop, capv lam S i) ≤ (1 : ℝ) / (q : ℝ) := by
    have hterm : ∀ i ∈ drop, capv lam S i ≤ wlev (Fintype.card X) := by
      intro i hid
      have hiE : i ∈ S.toFinset := (Finset.mem_sdiff.mp hid).1
      have hin : i ∉ keepElts lam S := (Finset.mem_sdiff.mp hid).2
      have hiS : i ∈ S := by simpa using hiE
      have hv0 : 0 ≤ capv lam S i := capv_nonneg lam S hSnon hiS
      have hnot : ¬ 1 ≤ capv lam S i * (q : ℝ) ^ Fintype.card X := by
        intro hb
        apply hin
        exact (mem_keepElts_iff lam S i).2 ⟨hiS, hb⟩
      exact le_of_lt (capv_lt_wlev_of_not_keep lam S hiS hnot)
    have hsumle : (∑ i ∈ drop, capv lam S i) ≤ ∑ i ∈ drop, (fun _ : X => wlev (Fintype.card X)) i := by
      exact Finset.sum_le_sum (fun i hid => hterm i hid)
    calc
      (∑ i ∈ drop, capv lam S i) ≤ ∑ i ∈ drop, wlev (Fintype.card X) := hsumle
      _ = (drop.card : ℝ) * wlev (Fintype.card X) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((S.toFinset.card : ℕ) : ℝ) * wlev (Fintype.card X) := by
        have hcard : drop.card ≤ S.toFinset.card := Finset.card_le_card (by
          -- drop ⊆ S.toFinset: sdiff subset
          intro x hx; exact (Finset.mem_sdiff.mp hx).1)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (wlev_nonneg (Fintype.card X))
      _ ≤ ((Fintype.card X : ℕ) : ℝ) * wlev (Fintype.card X) := by
        have hcard : S.toFinset.card ≤ Fintype.card X := by
          exact Finset.card_le_card (Finset.subset_univ S.toFinset)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (wlev_nonneg (Fintype.card X))
      _ = (Fintype.card X : ℝ) * wlev (Fintype.card X) := by simp
      _ ≤ (1 : ℝ) / (q : ℝ) := nat_mul_wlev_le_all (Fintype.card X)
  nlinarith [hsum, hle]

/-- Σ over keepElts of capv ≥ 1 − 1/100 -/
lemma keepElts_sum_ge (lam : Set X → X → ℝ) (S : Set X)
    (hSnon : ∀ i ∈ S, 0 ≤ lam S i)
    (hSge : 1 ≤ Sys.wtot lam S) :
    (1 : ℝ) - (1 : ℝ) / (q : ℝ) ≤ ∑ i ∈ keepElts lam S, capv lam S i := by
  have hcap : 1 ≤ ∑ i ∈ S.toFinset, capv lam S i := by
    have h1 := sum_min_one_ge_one (S.toFinset) (fun i : X => lam S i)
      (fun i hi => hSnon i (by simpa using hi)) hSge
    simpa [capv] using h1
  have hdrop := drop_sum_le lam S hSnon
  nlinarith


/-- sum over levels of class-weight (fiber = elementwise sum over keepElts) -/
lemma classSum_eq (lam : Set X → X → ℝ) (S : Set X) :
    (∑ j ∈ Finset.range (Fintype.card X + 1), (cS lam S j : ℝ) * wlev j)
      = ∑ i ∈ keepElts lam S, wlev (lvl lam S i) := by
  classical
  have hm : ∀ i ∈ keepElts lam S, lvl lam S i ≤ Fintype.card X :=
    fun i hi => lvl_le_Tau_of_mem_keepElts lam S hi
  have hf := sum_fiber (keepElts lam S) (fun i => lvl lam S i) wlev (Fintype.card X) hm
  calc
    (∑ j ∈ Finset.range (Fintype.card X + 1), (cS lam S j : ℝ) * wlev j)
        = ∑ j ∈ Finset.range (Fintype.card X + 1),
            ((((keepElts lam S).filter (fun i => lvl lam S i = j)).card : ℕ) : ℝ) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [cS, cls]
    _ = ∑ i ∈ keepElts lam S, wlev (lvl lam S i) := hf

/-- class-size total weight ≥ (1 - 1/100)/100 -/
lemma classSum_ge (lam : Set X → X → ℝ) (S : Set X)
    (hSnon : ∀ i ∈ S, 0 ≤ lam S i)
    (hSge : 1 ≤ Sys.wtot lam S) :
    ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤
      ∑ j ∈ Finset.range (Fintype.card X + 1), (cS lam S j : ℝ) * wlev j := by
  classical
  have hfib := classSum_eq lam S
  -- per element capv ≤ q·wlev(lvl), summed over keepElts: A ≤ q·B
  have hqpos : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  have hel : (∑ i ∈ keepElts lam S, capv lam S i) ≤ (q : ℝ) *
      ∑ i ∈ keepElts lam S, wlev (lvl lam S i) := by
    have hle : (∑ i ∈ keepElts lam S, capv lam S i) ≤
        ∑ i ∈ keepElts lam S, (q : ℝ) * wlev (lvl lam S i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hge := capv_div_q_le_wlev_lvl lam S hi
      simpa [mul_comm] using (div_le_iff₀ hqpos).1 hge
    calc
      (∑ i ∈ keepElts lam S, capv lam S i) ≤ ∑ i ∈ keepElts lam S, (q : ℝ) * wlev (lvl lam S i) := hle
      _ = (q : ℝ) * ∑ i ∈ keepElts lam S, wlev (lvl lam S i) := by
        rw [← Finset.mul_sum]
  have hA : (1 : ℝ) - (1 : ℝ) / (q : ℝ) ≤ ∑ i ∈ keepElts lam S, capv lam S i :=
    keepElts_sum_ge lam S hSnon hSge
  have hqB : (1 : ℝ) - (1 : ℝ) / (q : ℝ) ≤
      (∑ i ∈ keepElts lam S, wlev (lvl lam S i)) * (q : ℝ) := by
    calc
      (1 : ℝ) - (1 : ℝ) / (q : ℝ) ≤ ∑ i ∈ keepElts lam S, capv lam S i := hA
      _ ≤ (∑ i ∈ keepElts lam S, wlev (lvl lam S i)) * (q : ℝ) := by
        simpa [mul_comm] using hel
  have hB : ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤
      ∑ i ∈ keepElts lam S, wlev (lvl lam S i) := by
    exact (div_le_iff₀ hqpos).2 hqB
  rw [hfib]
  exact hB


/-- kept number at level j for S -/
noncomputable def sL (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : ℕ := keepNum j (cS lam S j)

/-- kept decision at level j for S -/
def keptL (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : Prop := keptLvlN j (cS lam S j)

/-- level weight -/
noncomputable def wL (lam : Set X → X → ℝ) (S : Set X) (j : ℕ) : ℝ := (cS lam S j : ℝ) * wlev j

/-- the drop-loss upper bound constant -/
noncomputable def D2b (X : Type*) [Fintype X] : ℝ :=
  (200 : ℝ) * wlev 5 + (20 : ℝ) / ((q : ℝ) ^ 4)

/-- low levels ≤ 4 are never dropped with positive content -/
lemma wL_zero_of_notkeep_le4 (lam : Set X → X → ℝ) (S : Set X) {j : ℕ}
    (hnot : ¬ keptL lam S j) (hj : j ≤ 4) : wL lam S j = 0 := by
  have hne : needExp j = 0 := needExp_zero_of_le4 hj
  have hc : cS lam S j = 0 := by
    by_contra hc0
    have h1 : 1 ≤ cS lam S j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc0)
    have hq : (q : ℕ) ^ needExp j = 1 := by rw [hne]; norm_num
    have hk : keptL lam S j := by
      unfold keptL keptLvlN
      rw [hq]
      exact h1
    exact hnot hk
  unfold wL
  rw [hc]
  simp

/-- sL = 0 when not kept -/
lemma sL_zero_of_notkeep (lam : Set X → X → ℝ) (S : Set X) {j : ℕ}
    (hnot : ¬ keptL lam S j) : sL lam S j = 0 := by
  unfold keptL at hnot
  unfold sL
  exact keepNum_eq_zero hnot

/-- drop loss (whole dropped levels) ≤ D2b -/
lemma dropLoss_le (lam : Set X → X → ℝ) (S : Set X) :
    (∑ j ∈ (Finset.range (Fintype.card X + 1)).filter (fun j => ¬ keptL lam S j),
        wL lam S j) ≤ D2b X := by
  classical
  let tau : ℕ := Fintype.card X
  let rng : Finset ℕ := Finset.range (tau + 1)
  let notF : Finset ℕ := rng.filter (fun j => ¬ keptL lam S j)
  let high : Finset ℕ := rng.filter (fun j => 5 ≤ j)
  let highNot : Finset ℕ := rng.filter (fun j => 5 ≤ j ∧ ¬ keptL lam S j)
  have hD : (∑ j ∈ notF, wL lam S j) = ∑ j ∈ highNot, wL lam S j := by
    calc
      (∑ j ∈ notF, wL lam S j) = ∑ j ∈ notF.filter (fun j => 5 ≤ j), wL lam S j := by
        symm
        apply Finset.sum_subset
        · intro j hj
          exact (Finset.mem_filter.mp hj).1
        · intro j hj hn
          have hnot : ¬ keptL lam S j := (Finset.mem_filter.mp hj).2
          have hn5 : ¬ 5 ≤ j := by
            intro h5
            apply hn
            exact Finset.mem_filter.mpr ⟨hj, h5⟩
          exact wL_zero_of_notkeep_le4 lam S hnot (by omega)
      _ = ∑ j ∈ highNot, wL lam S j := by
        have hset : notF.filter (fun j => 5 ≤ j) = highNot := by
          ext j
          simp [notF, highNot, rng]
          tauto
        rw [hset]
  have hterm : ∀ j ∈ highNot,
      wL lam S j ≤ (100 : ℝ) * legalLower j * wlev j := by
    intro j hj
    have hnot : ¬ keptL lam S j := (Finset.mem_filter.mp hj).2.2
    have hle' : ¬ (q : ℕ) ^ needExp j ≤ cS lam S j := by
      simpa [keptL, keptLvlN] using hnot
    have hc : (cS lam S j : ℕ) ≤ (q : ℕ) ^ needExp j :=
      Nat.le_of_lt (lt_of_not_ge hle')
    have h1 : (cS lam S j : ℝ) * wlev j ≤ ((q : ℕ) ^ needExp j : ℝ) * wlev j := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (wlev_nonneg j)
    have h2 : ((q : ℕ) ^ needExp j : ℝ) * wlev j ≤ (100 : ℝ) * legalLower j * wlev j := by
      have hq := needExp_qpow_le j
      exact mul_le_mul_of_nonneg_right hq (wlev_nonneg j)
    unfold wL
    exact le_trans h1 h2
  have hD2 : (∑ j ∈ highNot, wL lam S j) ≤ ∑ j ∈ highNot, (100 : ℝ) * legalLower j * wlev j := by
    exact Finset.sum_le_sum (fun j hj => hterm j hj)
  have hsubset : highNot ⊆ high := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩
  have hD3 : (∑ j ∈ highNot, (100 : ℝ) * legalLower j * wlev j) ≤
      ∑ j ∈ high, (100 : ℝ) * legalLower j * wlev j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro j hj hx
    exact mul_nonneg (mul_nonneg (by norm_num) (legalLower_nonneg j)) (wlev_nonneg j)
  have hD4 : (∑ j ∈ high, (100 : ℝ) * legalLower j * wlev j) ≤
      ∑ j ∈ Finset.Icc 5 tau, (100 : ℝ) * legalLower j * wlev j := by
    have hEq : high = Finset.Icc 5 tau := by
      ext j
      simp [high, rng, Finset.mem_Icc, Nat.succ_le_iff]
      tauto
    rw [hEq]
  have hD5 : (∑ j ∈ Finset.Icc 5 tau, (100 : ℝ) * legalLower j * wlev j) ≤ D2b X := by
    let inv : ℕ → ℝ := fun j => (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))
    have hterm0 : ∀ j ∈ Finset.Icc 5 tau,
        (100 : ℝ) * legalLower j * wlev j ≤ (100 : ℝ) * wlev j + (100 : ℝ) * inv j := by
      intro j hj
      have h0 := legalLower_mul_wlev_le j
      have hml : (100 : ℝ) * (legalLower j * wlev j) ≤
          (100 : ℝ) * (wlev j + (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left h0 (by norm_num)
      have hL : (100 : ℝ) * legalLower j * wlev j = (100 : ℝ) * (legalLower j * wlev j) := by ring
      have hR : (100 : ℝ) * wlev j + (100 : ℝ) * inv j =
          (100 : ℝ) * (wlev j + inv j) := by ring
      rw [hL, hR]
      simpa [inv] using hml
    have hinv1 : ∀ j ∈ Finset.Icc 5 tau,
        inv j = (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / ((j + 1 : ℝ) ^ 2)) := by
      intro j hj
      have hq4 : (q : ℝ) ^ 4 ≠ 0 := q_real_pow_ne_zero 4
      have hsq : ((j + 1 : ℝ) ^ 2) ≠ 0 := by positivity
      unfold inv
      field_simp [hq4, hsq]
    calc
      (∑ j ∈ Finset.Icc 5 tau, (100 : ℝ) * legalLower j * wlev j)
          ≤ ∑ j ∈ Finset.Icc 5 tau, ((100 : ℝ) * wlev j + (100 : ℝ) * inv j) := by
            exact Finset.sum_le_sum (fun j hj => hterm0 j hj)
      _ = (100 : ℝ) * (∑ j ∈ Finset.Icc 5 tau, wlev j) +
          (100 : ℝ) * (∑ j ∈ Finset.Icc 5 tau, inv j) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · rw [← Finset.mul_sum]
      _ ≤ (100 : ℝ) * (2 * wlev 5) + (100 : ℝ) * ((1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5)) := by
            have h1 := sum_wlev_high_le tau
            have h1m : (100 : ℝ) * (∑ j ∈ Finset.Icc 5 tau, wlev j) ≤ (100 : ℝ) * (2 * wlev 5) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
            have h2sum : (∑ j ∈ Finset.Icc 5 tau, inv j) ≤ (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5) := by
              calc
                (∑ j ∈ Finset.Icc 5 tau, inv j)
                    = ∑ j ∈ Finset.Icc 5 tau, (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / ((j + 1 : ℝ) ^ 2)) := by
                      exact Finset.sum_congr rfl (fun j hj => hinv1 j hj)
                _ = (1 : ℝ) / ((q : ℝ) ^ 4) * (∑ j ∈ Finset.Icc 5 tau, 1 / ((j + 1 : ℝ) ^ 2)) := by
                      rw [Finset.mul_sum]
                _ ≤ (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5) := by
                      have hs := sum_inv_sq_high_le tau
                      exact mul_le_mul_of_nonneg_left hs (by positivity)
            have h2m : (100 : ℝ) * (∑ j ∈ Finset.Icc 5 tau, inv j) ≤
                (100 : ℝ) * ((1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5)) :=
              mul_le_mul_of_nonneg_left h2sum (by norm_num)
            nlinarith
      _ = D2b X := by
            unfold D2b
            norm_num [wlev, q]
  calc
    (∑ j ∈ (Finset.range (Fintype.card X + 1)).filter (fun j => ¬ keptL lam S j), wL lam S j)
        = ∑ j ∈ notF, wL lam S j := rfl
    _ = ∑ j ∈ highNot, wL lam S j := hD
    _ ≤ ∑ j ∈ highNot, (100 : ℝ) * legalLower j * wlev j := hD2
    _ ≤ ∑ j ∈ high, (100 : ℝ) * legalLower j * wlev j := hD3
    _ ≤ ∑ j ∈ Finset.Icc 5 tau, (100 : ℝ) * legalLower j * wlev j := hD4
    _ ≤ D2b X := hD5


/-- main per-S weight bound: Σ_j (sL j)·wlev j ≥ 10^{-8} -/
lemma perS_weight (lam : Set X → X → ℝ) (S : Set X)
    (hSnon : ∀ i ∈ S, 0 ≤ lam S i)
    (hSge : 1 ≤ Sys.wtot lam S) :
    ((10 : ℝ) ^ 8)⁻¹ ≤
      ∑ j ∈ Finset.range (Fintype.card X + 1), (sL lam S j : ℝ) * wlev j := by
  classical
  let tau : ℕ := Fintype.card X
  let keptR : Finset ℕ := (Finset.range (tau + 1)).filter (fun j => keptL lam S j)
  have hq : (q : ℝ) ≠ 0 := q_ne_zero
  have hqinv : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hqinvpos : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  -- hT: total class weight ≥ Tlow
  have hT : ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤
      ∑ j ∈ Finset.range (Fintype.card X + 1), (cS lam S j : ℝ) * wlev j :=
    classSum_ge lam S hSnon hSge
  -- K (all levels) equals K over kept levels
  have hKwSk : (∑ j ∈ Finset.range (tau + 1), (sL lam S j : ℝ) * wlev j) =
      ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := by
    have h1 : (∑ j ∈ Finset.range (tau + 1), (sL lam S j : ℝ) * wlev j)
        = ∑ j ∈ Finset.range (tau + 1),
            (if keptL lam S j then (sL lam S j : ℝ) * wlev j else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hk : keptL lam S j
      · simp [hk]
      · have hs : sL lam S j = 0 := sL_zero_of_notkeep lam S hk
        simp [hs, hk]
    calc
      (∑ j ∈ Finset.range (tau + 1), (sL lam S j : ℝ) * wlev j)
          = ∑ j ∈ Finset.range (tau + 1),
              (if keptL lam S j then (sL lam S j : ℝ) * wlev j else 0) := h1
      _ = ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := by
          rw [Finset.sum_filter]
  -- per-level kept weight inequality
  have hlevel : (∑ j ∈ keptR, min ((cS lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹) ≤
      ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := by
    apply Finset.sum_le_sum
    intro j hj
    have hk : keptL lam S j := (Finset.mem_filter.mp hj).2
    have hw := keepNum_weight (j := j) (c := cS lam S j) (by simpa [keptL] using hk)
    -- hw: min(cS·wlev,1)/q ≤ (keepNum j (cS):ℝ)·wlev; (q:ℝ)⁻¹ form:
    have hw' : min ((cS lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ ≤ (sL lam S j : ℝ) * wlev j := by
      -- convert division by q into multiplication by q⁻¹
      have hd : min ((cS lam S j : ℝ) * wlev j) 1 / (q : ℝ) * (q : ℝ) = min ((cS lam S j : ℝ) * wlev j) 1 := by
        field_simp [hq]
      -- hw : min(...)/q ≤ sL·wlev  (division); multiply?? need same form: 
      simpa [sL, div_eq_mul_inv] using hw
    exact hw'
  -- Mk·q⁻¹ = Σ min·q⁻¹
  have hMk : (∑ j ∈ keptR, min ((cS lam S j : ℝ) * wlev j) 1) * (q : ℝ)⁻¹ ≤
      ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := by
    rw [Finset.sum_mul]
    exact hlevel
  -- min-sum: min(Wk,1) ≤ Σ min
  have hmin1 : min (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) 1 ≤
      ∑ j ∈ keptR, min ((cS lam S j : ℝ) * wlev j) 1 := by
    apply sum_min_one_ge_min_sum (keptR) (fun j => (cS lam S j : ℝ) * wlev j)
    intro j hj
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (cS lam S j))) (wlev_nonneg j)
  have hminWk : min (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ ≤
      ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := by
    calc
      min (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹
          ≤ (∑ j ∈ keptR, min ((cS lam S j : ℝ) * wlev j) 1) * (q : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hmin1 hqinv
      _ ≤ ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := hMk
  -- Wk ≥ Tlow − D2b
  let D : ℝ := ∑ j ∈ (Finset.range (tau + 1)).filter (fun j => ¬ keptL lam S j),
      (cS lam S j : ℝ) * wlev j
  have hpart : (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) + D =
      ∑ j ∈ Finset.range (tau + 1), (cS lam S j : ℝ) * wlev j := by
    have hp := Finset.sum_filter_add_sum_filter_not (Finset.range (tau + 1))
      (fun j => keptL lam S j) (fun j => (cS lam S j : ℝ) * wlev j)
    -- hp : Σ_{filter kept} + Σ_{filter ¬kept} = Σ_{range}: but the ¬-filter predicate is (¬ keptL)
    unfold keptR D
    simpa using hp
  have hDle : D ≤ D2b X := by
    unfold D
    exact dropLoss_le lam S
  have hWk : ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) - D2b X ≤
      ∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j := by
    have hWkeq : (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) =
        (∑ j ∈ Finset.range (tau + 1), (cS lam S j : ℝ) * wlev j) - D := by
      rw [← hpart]
      ring
    rw [hWkeq]
    nlinarith [hT, hDle]
  have hminBig : ((10 : ℝ) ^ 6)⁻¹ ≤ min (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) 1 := by
    have hnum : ((10 : ℝ) ^ 6)⁻¹ ≤ ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) - D2b X := by
      unfold D2b
      norm_num [wlev, q]
    have hWk6 : ((10 : ℝ) ^ 6)⁻¹ ≤ ∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j :=
      le_trans hnum hWk
    exact le_min hWk6 (by norm_num)
  have hconcl : ((10 : ℝ) ^ 8)⁻¹ ≤ (∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j) := by
    calc
      ((10 : ℝ) ^ 8)⁻¹ ≤ ((10 : ℝ) ^ 6)⁻¹ * (q : ℝ)⁻¹ := by norm_num [q]
      _ ≤ min (∑ j ∈ keptR, (cS lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hminBig hqinv
      _ ≤ ∑ j ∈ keptR, (sL lam S j : ℝ) * wlev j := hminWk
  -- convert keptR-sum back to range-sum
  rw [hKwSk]
  exact hconcl


/-- keepNum entries are legal -/
lemma LegalEntry_keepNum {j c : ℕ} : Sys.LegalEntry (keepNum j c) j := by
  by_cases h : keptLvlN j c
  · right
    refine ⟨⟨logq (min c ((q : ℕ) ^ j)), keepNum_eq_keep h⟩, ?_, ?_⟩
    · exact keepNum_lower h
    · exact keepNum_upper (j := j) (c := c)
  · left
    exact keepNum_eq_zero h

/-- sL entries are legal on levels ≤ card X -/
lemma perS_legal (lam : Set X → X → ℝ) (S : Set X) :
    ∀ j, j ≤ Fintype.card X → Sys.LegalEntry (sL lam S j) j := by
  intro j hj
  unfold sL
  exact LegalEntry_keepNum (j := j) (c := cS lam S j)

/-- domination: level weight ≤ original weight -/
lemma perS_dom (lam : Set X → X → ℝ) (S : Set X) :
    ∀ i ∈ (trimF lam S : Set X), wlev (lvl lam S i) ≤ lam S i := by
  intro i hi
  have hke : i ∈ keepElts lam S := by
    classical
    rcases (Finset.mem_biUnion.mp hi) with ⟨j, hj, hij⟩
    exact keepFin_subset_keepElts lam S j hij
  exact le_trans (wlev_lvl_le_capv lam S hke) (by unfold capv; exact min_le_left (lam S i) (1 : ℝ))

/-- bundled per-S properties -/
theorem perS_spec (lam : Set X → X → ℝ) (S : Set X)
    (hSnon : ∀ i ∈ S, 0 ≤ lam S i)
    (hSge : 1 ≤ Sys.wtot lam S) :
    (trimF lam S : Set X) ⊆ S ∧
    (∀ i ∈ (trimF lam S : Set X), lvl lam S i ≤ Fintype.card X) ∧
    (((10 : ℝ) ^ 8)⁻¹ ≤
      ∑ j ∈ Finset.range (Fintype.card X + 1), (sL lam S j : ℝ) * wlev j) ∧
    (∀ j, j ≤ Fintype.card X → Sys.LegalEntry (sL lam S j) j) ∧
    (∀ i ∈ (trimF lam S : Set X), wlev (lvl lam S i) ≤ lam S i) := by
  exact ⟨trimF_subset_S lam S, (fun i hi => level_le_Tau_of_mem_trimF lam S hi),
    perS_weight lam S hSnon hSge, perS_legal lam S, perS_dom lam S⟩


/-! ## System assembly -/

/-- trimmed set (as a Set) -/
noncomputable def trimSet (lam : Set X → X → ℝ) (S : Set X) : Set X := (trimF lam S : Set X)

/-- a chosen preimage of a trimmed set -/
noncomputable def preS (lam : Set X → X → ℝ) (F : Set (Set X)) (T : Set X) : Set X := by
  classical
  exact if h : ∃ S ∈ F, trimSet lam S = T then Classical.choose h else ∅

/-- the output family -/
noncomputable def theF (lam : Set X → X → ℝ) (F : Set (Set X)) : Set (Set X) :=
  {T : Set X | ∃ S ∈ F, trimSet lam S = T}

/-- the output system -/
noncomputable def theSys (lam : Set X → X → ℝ) (F : Set (Set X)) : Sys X :=
  { τ := Fintype.card X
    lv := fun T i => qlev (Fintype.card X) (capv lam (preS lam F T) i)
    F := theF lam F }

/-- preS is a genuine preimage on the output family -/
lemma preS_spec (lam : Set X → X → ℝ) (F : Set (Set X)) {T : Set X}
    (hT : T ∈ theF lam F) : preS lam F T ∈ F ∧ trimSet lam (preS lam F T) = T := by
  classical
  have hT' : ∃ S ∈ F, trimSet lam S = T := by simpa [theF] using hT
  unfold preS
  rw [dif_pos hT']
  exact Classical.choose_spec hT'

/-- (Finset : Set).ncard = card -/
lemma coe_finset_ncard (t : Finset X) : ((t : Set X).ncard) = t.card := by
  classical
  rw [ncard_eq_toFinset_card' (t : Set X)]
  congr 1
  ext x
  simp

/-- level sets of theSys members -/
lemma theSys_levelSet (lam : Set X → X → ℝ) (F : Set (Set X)) {T : Set X}
    (hT : T ∈ theF lam F) (j : ℕ) :
    Sys.levelSet (theSys lam F) T j = (keepFin lam (preS lam F T) j : Set X) := by
  classical
  have hpre := preS_spec lam F hT
  ext i
  constructor
  · intro hi
    have hiT : i ∈ T := hi.1
    have hij : qlev (Fintype.card X) (capv lam (preS lam F T) i) = j := hi.2
    have hiF : i ∈ (trimF lam (preS lam F T) : Set X) := by
      change i ∈ trimSet lam (preS lam F T)
      rw [hpre.2]
      exact hiT
    have hij' : lvl lam (preS lam F T) i = j := by
      change qlev (Fintype.card X) (capv lam (preS lam F T) i) = j
      exact hij
    have hlf := levelSet_trimF lam (preS lam F T) j
    have hmem : i ∈ ((trimF lam (preS lam F T) : Set X) ∩ {x | lvl lam (preS lam F T) x = j}) :=
      ⟨hiF, hij'⟩
    rw [← hlf]
    exact hmem
  · intro hi
    have hj : j ≤ Fintype.card X := by
      have hke : i ∈ keepElts lam (preS lam F T) := keepFin_subset_keepElts lam (preS lam F T) j hi
      have hle := lvl_le_Tau_of_mem_keepElts lam (preS lam F T) hke
      have hl : lvl lam (preS lam F T) i = j := level_of_keepFin lam (preS lam F T) j hi
      rwa [hl] at hle
    have hbj := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hi⟩
    have hiF : i ∈ (trimF lam (preS lam F T) : Set X) := Finset.mem_coe.mpr hbj
    constructor
    · rw [← hpre.2]
      simpa [trimSet] using hiF
    · have hl : lvl lam (preS lam F T) i = j := level_of_keepFin lam (preS lam F T) j hi
      change qlev (Fintype.card X) (capv lam (preS lam F T) i) = j
      simpa [lvl] using hl

/-- sCount of a member -/
lemma theSys_sCount (lam : Set X → X → ℝ) (F : Set (Set X)) {T : Set X}
    (hT : T ∈ theF lam F) (j : ℕ) :
    Sys.sCount (theSys lam F) T j = sL lam (preS lam F T) j := by
  classical
  unfold Sys.sCount
  rw [theSys_levelSet lam F hT j]
  unfold sL
  rw [coe_finset_ncard]
  exact keepFin_card lam (preS lam F T) j

/-- total weight of a member = Σ_j (sL j)·wlev j -/
lemma theSys_totalWeight (lam : Set X → X → ℝ) (F : Set (Set X)) {T : Set X}
    (hT : T ∈ theF lam F) :
    Sys.totalWeight (theSys lam F) T =
      ∑ j ∈ Finset.range (Fintype.card X + 1), (sL lam (preS lam F T) j : ℝ) * wlev j := by
  classical
  unfold Sys.totalWeight Sys.weight
  have hlevel : ∀ j, T ∩ Sys.levelSet (theSys lam F) T j = Sys.levelSet (theSys lam F) T j := by
    intro j
    ext x
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hx.1, hx⟩
  calc
    (∑ j ∈ Finset.range ((theSys lam F).τ + 1),
        (((T ∩ Sys.levelSet (theSys lam F) T j).ncard : ℕ) : ℝ) * wlev j)
        = ∑ j ∈ Finset.range ((theSys lam F).τ + 1),
            (((Sys.levelSet (theSys lam F) T j).ncard : ℕ) : ℝ) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hc : (((T ∩ Sys.levelSet (theSys lam F) T j).ncard : ℕ) : ℝ) =
              (((Sys.levelSet (theSys lam F) T j).ncard : ℕ) : ℝ) := by
            rw [hlevel j]
          rw [hc]
    _ = ∑ j ∈ Finset.range (Fintype.card X + 1), (sL lam (preS lam F T) j : ℝ) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hsc := theSys_sCount lam F hT j
          have hc : (((Sys.levelSet (theSys lam F) T j).ncard : ℕ) : ℝ) =
              ((sL lam (preS lam F T) j) : ℝ) := by
            change ((Sys.sCount (theSys lam F) T j) : ℝ) = (sL lam (preS lam F T) j : ℝ)
            exact_mod_cast hsc
          rw [hc]

/-- FBounded of theSys -/
lemma theSys_fbounded (lam : Set X → X → ℝ) (F : Set (Set X))
    (hnon : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hge : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) :
    (theSys lam F).FBounded := by
  classical
  unfold Sys.FBounded
  intro T hT i hiT
  have hpre := preS_spec lam F hT
  have hSge : 1 ≤ Sys.wtot lam (preS lam F T) := hge (preS lam F T) hpre.1
  have hSnon : ∀ i ∈ (preS lam F T), 0 ≤ lam (preS lam F T) i := hnon (preS lam F T) hpre.1
  have hiF : i ∈ (trimF lam (preS lam F T) : Set X) := by
    change i ∈ trimSet lam (preS lam F T)
    rw [hpre.2]
    exact hiT
  have hb := (perS_spec lam (preS lam F T) hSnon hSge).2.1 i hiF
  change qlev (Fintype.card X) (capv lam (preS lam F T) i) ≤ Fintype.card X
  simpa [lvl] using hb

/-- TotBound of theSys -/
lemma theSys_totbound (lam : Set X → X → ℝ) (F : Set (Set X))
    (hnon : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hge : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) :
    (theSys lam F).TotBound := by
  classical
  unfold Sys.TotBound
  intro T hT
  have hpre := preS_spec lam F hT
  have hSge : 1 ≤ Sys.wtot lam (preS lam F T) := hge (preS lam F T) hpre.1
  have hSnon : ∀ i ∈ (preS lam F T), 0 ≤ lam (preS lam F T) i := hnon (preS lam F T) hpre.1
  have hw := (perS_spec lam (preS lam F T) hSnon hSge).2.2.1
  have ht := theSys_totalWeight lam F hT
  rw [ht]
  simpa using hw

/-- FLegal of theSys -/
lemma theSys_flegal (lam : Set X → X → ℝ) (F : Set (Set X))
    (hnon : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hge : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) :
    (theSys lam F).FLegal := by
  classical
  unfold Sys.FLegal Sys.LegalProfile
  intro T hT j hj
  have hsc := theSys_sCount lam F hT j
  have hleg := perS_legal lam (preS lam F T) j hj
  change Sys.LegalEntry (Sys.sCount (theSys lam F) T j) j
  rw [hsc]
  exact hleg

/-- (d): every original member has a trim -/
lemma theSys_cover (lam : Set X → X → ℝ) (F : Set (Set X))
    (hnon : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hge : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) :
    ∀ S ∈ F, ∃ T ∈ (theSys lam F).F, T ⊆ S := by
  classical
  intro S hS
  refine ⟨trimSet lam S, ?_, ?_⟩
  · simpa [theF] using ⟨S, hS, rfl⟩
  · have hSnon : ∀ i ∈ S, 0 ≤ lam S i := hnon S hS
    have hSge : 1 ≤ Sys.wtot lam S := hge S hS
    exact (perS_spec lam S hSnon hSge).1

/-- (e): domination from each trim back to its original -/
lemma theSys_dom (lam : Set X → X → ℝ) (F : Set (Set X))
    (hnon : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hge : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) :
    ∀ T ∈ (theSys lam F).F, ∃ S ∈ F, T ⊆ S ∧ ∀ i ∈ T, lam S i ≥ wlev ((theSys lam F).lv T i) := by
  classical
  intro T hT
  have hpre := preS_spec lam F hT
  let S0 : Set X := preS lam F T
  have hSnon : ∀ i ∈ S0, 0 ≤ lam S0 i := by
    intro i hi
    exact hnon S0 hpre.1 i hi
  have hSge : 1 ≤ Sys.wtot lam S0 := hge S0 hpre.1
  have hspec := perS_spec lam S0 hSnon hSge
  refine ⟨S0, hpre.1, ?_⟩
  constructor
  · intro i hi
    have hiF : i ∈ (trimF lam S0 : Set X) := by
      change i ∈ trimSet lam (preS lam F T)
      rw [hpre.2]
      exact hi
    exact hspec.1 hiF
  · intro i hiT
    have hiF : i ∈ (trimF lam S0 : Set X) := by
      change i ∈ trimSet lam (preS lam F T)
      rw [hpre.2]
      exact hiT
    have hdom := hspec.2.2.2.2 i hiF
    change lam S0 i ≥ wlev ((theSys lam F).lv T i)
    have hlvl : (theSys lam F).lv T i = lvl lam S0 i := by
      change qlev (Fintype.card X) (capv lam (preS lam F T) i) =
        qlev (Fintype.card X) (capv lam (preS lam F T) i)
      rfl
    rw [hlvl]
    exact hdom



theorem theorem_preprocess (F : Set (Set X)) (lam0 : Set X → X → ℝ)
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam0 S i)
    (hnonnegtot : ∀ S ∈ F, 1 ≤ Sys.wtot lam0 S) :
    ∃ N : Sys X, N.FBounded ∧ N.TotBound ∧ N.FLegal ∧
      (∀ S ∈ F, ∃ S' ∈ N.F, S' ⊆ S) ∧
      (∀ S' ∈ N.F, ∃ S ∈ F, S' ⊆ S ∧ ∀ i ∈ S', lam0 S i ≥ wlev (N.lv S' i)) := by
  classical
  let N : Sys X := theSys lam0 F
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · exact theSys_fbounded lam0 F hnonneg hnonnegtot
  · exact theSys_totbound lam0 F hnonneg hnonnegtot
  · exact theSys_flegal lam0 F hnonneg hnonnegtot
  · exact theSys_cover lam0 F hnonneg hnonnegtot
  · exact theSys_dom lam0 F hnonneg hnonnegtot

end Pre
end Submission
