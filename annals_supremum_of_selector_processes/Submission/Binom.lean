import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Bridge
import Submission.BinomMed

/-!
# Binomial / uniform-subset concentration facts (pure finite sums), for the 5.7'' -> 5.7' step.
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Binom

open Frame
open Sel.Deep
open Sel.Deep.Sys

/-- binomial sum of g over subsets: Σ_T g(T) p^{|T|} (1-p)^{n-|T|} -/
noncomputable def binomSum {X : Type*} [Fintype X] (p : ℝ) (g : Set X → ℝ) : ℝ := by
  classical
  exact ∑ T : Set X, g T * p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard)

/-- sum of g over the subsets of size exactly N -/
noncomputable def sizeSum {X : Type*} [Fintype X] (g : Set X → ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ T ∈ Finset.univ.filter (fun T : Set X => T.ncard = N), g T

/-- average of g over subsets of size exactly N (0 if there are none) -/
noncomputable def sizeAvg {X : Type*} [Fintype X] (g : Set X → ℝ) (N : ℕ) : ℝ := by
  classical
  let s : Finset (Set X) := Finset.univ.filter (fun T : Set X => T.ncard = N)
  exact if h : s.Nonempty then (∑ T ∈ s, g T) / (s.card : ℝ) else 0

/-! ## Set-level vs 1-D binomial facts -/

variable {X : Type*} [Fintype X]

/-- subsets of `X` of ncard exactly `k` -/
noncomputable def levelFinset (X : Type*) [Fintype X] (k : ℕ) : Finset (Set X) :=
  Finset.univ.filter (fun T : Set X => T.ncard = k)

lemma level_mem (T : Set X) (k : ℕ) : T ∈ levelFinset X k ↔ T.ncard = k := by
  simp [levelFinset]

lemma ncard_le_univ (T : Set X) : T.ncard ≤ Fintype.card X := by
  have h := Set.ncard_le_ncard (Set.subset_univ T) (Set.toFinite Set.univ)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h

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

/-- every subset lies in exactly one level, so summing over levels equals summing over subsets -/
lemma sum_univ_eq_sum_levels (f : Set X → ℝ) :
    (∑ T : Set X, f T) =
      ∑ k ∈ Finset.Icc 0 (Fintype.card X), ∑ T ∈ levelFinset X k, f T := by
  classical
  have h1 : (∑ T : Set X, f T) =
      ∑ T : Set X, (∑ k ∈ Finset.Icc 0 (Fintype.card X),
        if T.ncard = k then f T else 0) := by
    apply Finset.sum_congr rfl
    intro T hT
    have hmem : T.ncard ∈ Finset.Icc 0 (Fintype.card X) := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le _, ncard_le_univ T⟩
    rw [Finset.sum_ite_eq]
    simp [hmem]
  rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  simp [levelFinset]

/-- the sum over subsets of size exactly k of (p q powers) equals C(n,k) p^k (1-p)^{n-k} -/
lemma level_mass_eq (p : ℝ) (k : ℕ) (hk : k ≤ Fintype.card X) :
    (∑ T ∈ levelFinset X k, p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard)) =
      ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
  classical
  calc
    (∑ T ∈ levelFinset X k, p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard))
        = ∑ T ∈ levelFinset X k, p ^ k * (1 - p) ^ (Fintype.card X - k) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTk : T.ncard = k := (level_mem T k).mp hT
          rw [hTk]
    _ = (levelFinset X k).card * (p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
          rw [levelFinset_card k hk]
          ring

/-- collapsing an indicator inside a sum over Icc 0 n to a sum over Icc N n -/
lemma sum_Icc_indicator (N : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 0 (Fintype.card X), (if N ≤ k then (1 : ℝ) else 0) * a k) =
      ∑ k ∈ Finset.Icc N (Fintype.card X), a k := by
  classical
  have hstep : (∑ k ∈ Finset.Icc 0 (Fintype.card X), (if N ≤ k then (1 : ℝ) else 0) * a k)
      = ∑ k ∈ Finset.Icc 0 (Fintype.card X), (if N ≤ k then a k else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : N ≤ k <;> simp [h]
  rw [hstep]
  rw [← Finset.sum_filter]
  have hset : (Finset.Icc 0 (Fintype.card X)).filter (fun k : ℕ => N ≤ k) =
      Finset.Icc N (Fintype.card X) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset]

/-- The indicator tail mass over subsets with ncard ≥ N equals the 1-D binomial tail. -/
lemma binomSum_ge_indicator_eq_tail (p : ℝ) (N : ℕ) :
    binomSum p (fun T : Set X => if N ≤ T.ncard then 1 else 0) =
      ∑ k ∈ Finset.Icc N (Fintype.card X),
        ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
  classical
  unfold binomSum
  calc
    (∑ T : Set X, (if N ≤ T.ncard then (1 : ℝ) else 0) *
        p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard))
    = ∑ k ∈ Finset.Icc 0 (Fintype.card X),
        ∑ T ∈ levelFinset X k,
          (if N ≤ T.ncard then (1 : ℝ) else 0) *
            p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard) := by
        rw [← sum_univ_eq_sum_levels
          (fun T : Set X => (if N ≤ T.ncard then (1 : ℝ) else 0) *
            p ^ T.ncard * (1 - p) ^ (Fintype.card X - T.ncard))]
    _ = ∑ k ∈ Finset.Icc 0 (Fintype.card X),
        ∑ T ∈ levelFinset X k,
          (if N ≤ k then (1 : ℝ) else 0) *
            p ^ k * (1 - p) ^ (Fintype.card X - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro T hT
        have hTk : T.ncard = k := (level_mem T k).mp hT
        rw [hTk]
    _ = ∑ k ∈ Finset.Icc 0 (Fintype.card X),
        (if N ≤ k then (1 : ℝ) else 0) *
          (((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k ≤ Fintype.card X := (Finset.mem_Icc.mp hk).2
        have hsum : (∑ T ∈ levelFinset X k,
              (if N ≤ k then (1 : ℝ) else 0) * p ^ k * (1 - p) ^ (Fintype.card X - k)) =
            (if N ≤ k then (1 : ℝ) else 0) *
              (((levelFinset X k).card : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
        calc
          (∑ T ∈ levelFinset X k,
              (if N ≤ k then (1 : ℝ) else 0) * p ^ k * (1 - p) ^ (Fintype.card X - k))
              = (if N ≤ k then (1 : ℝ) else 0) *
                  (((levelFinset X k).card : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := hsum
          _ = (if N ≤ k then (1 : ℝ) else 0) *
                  (((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)) := by
                  rw [levelFinset_card k hkle]
    _ = ∑ k ∈ Finset.Icc N (Fintype.card X),
        ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k) := by
        rw [sum_Icc_indicator N
          (fun k : ℕ => ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k))]

/-! ## THEOREM A: median lower bound for binomial -/

/-- The median of the binomial set distribution is at least the floor of the mean:
    the total mass of subsets with `ncard ≥ ⌊(n:ℝ) * p⌋` is at least `1/2`.
    (Follows from the 1-D binomial-tail fact `BinomMed.median_lower` via the level
    decomposition `binomSum_ge_indicator_eq_tail`.) -/
theorem binom_median_lower (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / 2 : ℝ) ≤ binomSum p (fun T : Set X =>
      if ⌊(Fintype.card X : ℝ) * p⌋.toNat ≤ T.ncard then 1 else 0) := by
  classical
  let n : ℕ := Fintype.card X
  let N : ℕ := ⌊(n : ℝ) * p⌋.toNat
  have hNle : (N : ℝ) ≤ (n : ℝ) * p := by
    dsimp [N]
    have hx : 0 ≤ (n : ℝ) * p := by positivity
    have hfnonneg : 0 ≤ ⌊(n : ℝ) * p⌋ := Int.floor_nonneg.mpr hx
    have htoNat : (⌊(n : ℝ) * p⌋.toNat : ℤ) = ⌊(n : ℝ) * p⌋ :=
      Int.toNat_of_nonneg hfnonneg
    have hcast : (⌊(n : ℝ) * p⌋.toNat : ℝ) = (⌊(n : ℝ) * p⌋ : ℝ) := by
      exact_mod_cast htoNat
    rw [hcast]
    exact Int.floor_le ((n : ℝ) * p)
  rw [binomSum_ge_indicator_eq_tail p N]
  change (1 / 2 : ℝ) ≤
    ∑ k ∈ Finset.Icc N (Fintype.card X),
      ((Fintype.card X).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card X - k)
  apply BinomMed.median_lower (Fintype.card X) N p hp0 hp1
  simpa [N] using hNle

end Binom
end Submission
