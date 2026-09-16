import Submission.ZagierHoffmanProof.StepL195
import Submission.Commons.Topology.Algebra.Valued.tsum_v_eq_one_of
import Mathlib.Topology.Algebra.Valued.ValuationTopology

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open WithZero Filter

/-!
# Step L196: ★★ `ζ_A(1) ≠ 0` — the first non-vanishing MZV and theorem_A's non-vacuity

The block decomposition `ζ_A(1) = ∑_d S_d(1)` (StepL52's `zeta_eq_tsum_block`) together with
the closed form `P_d(1) = (∏_{i<d}(X − X^{q^{i+1}}))⁻¹` of StepL195 exhibits `ζ_A(1)` as the
limit of partial sums

    s_n = ∑_{d<n} P_d(1) = 1 + (a sum of terms of valuation < 1).

Every `s_n` therefore has valuation exactly `1` (`Valuation.map_sum_lt` +
`Valuation.map_add_eq_of_lt_left`), and the set `{x | 1 ≤ v x}` is CLOSED (it is the
complement of the open ball `{x | v x < 1}`, `Valued.isOpen_ball`), so the limit `ζ_A(1)`
satisfies `1 ≤ v (ζ_A(1))`: in particular `ζ_A(1) ≠ 0`.
Consequences: `𝒵 F 1 ≠ ⊥` (theorem_A is NOT vacuous) and the `w = 1` instances of
Theorems B and D.  Theorems B/D in general remain ABP-gated.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The family of depth-one power sums `P_d(1)` is summable (from `summable_S`). -/
theorem summable_P_oneExp : Summable (fun d : ℕ => P F d oneExp) := by
  classical
  have hs := summable_S F (r := 1) (by norm_num) (single oneExp)
  refine hs.congr (fun d => ?_)
  rw [S_one_eq_P F d (by norm_num) (single oneExp)]
  rfl

/-- The valuation of a partial sum of the depth-one blocks is `1` (the `d = 0` block is `1`,
all other blocks have valuation `< 1`). -/
theorem val_partial_sum (n : ℕ) :
    Valued.v (∑ i ∈ Finset.range (n + 1), S F 1 (by norm_num) (single oneExp) i)
      = (1 : ℤᵐ⁰) := by
  classical
  have hf0 : S F 1 (by norm_num : 0 < 1) (single oneExp) 0 = (1 : RatFunc.CompletionAtInfty F) := by
    rw [S_one_eq_P F 0 (by norm_num) (single oneExp)]
    exact P_zero_oneExp F
  rw [Finset.sum_range_succ', hf0]
  have htail : Valued.v (∑ i ∈ Finset.range n, S F 1 (by norm_num) (single oneExp) (i + 1))
      < Valued.v (1 : RatFunc.CompletionAtInfty F) := by
    rw [map_one]
    refine Valuation.map_sum_lt (v := Valued.v) (g := (1 : ℤᵐ⁰)) one_ne_zero (fun i hi => ?_)
    rw [S_one_eq_P F (i + 1) (by norm_num) (single oneExp)]
    exact val_P_oneExp_lt_one F (i + 1) (by omega)
  rw [Valuation.map_add_eq_of_lt_right (v := Valued.v) htail, map_one]

/-- ★★ A general non-vanishing/valuation principle: if `f 0 = 1`, `f` is summable and every
other term has valuation `< 1`, then the sum has valuation EXACTLY `1` (hence is nonzero).
The lower bound comes from the closed set `{x | 1 ≤ v x}` (every partial sum is in it),
the upper bound from the closed unit ball `{x | v x ≤ 1}`. -/
theorem val_tsum_eq_one_of (f : ℕ → RatFunc.CompletionAtInfty F) (hf0 : f 0 = 1)
    (hsumm : Summable f) (hlt : ∀ n : ℕ, 1 ≤ n → Valued.v (f n) < (1 : ℤᵐ⁰)) :
    Valued.v (∑' n, f n) = (1 : ℤᵐ⁰) :=
  Commons.Topology.Algebra.Valued.tsum_v_eq_one_of f hf0 hsumm hlt

/-- ★★★ `v (ζ_A(1)) = 1`, from the general `val_tsum_eq_one_of` applied to the block
decomposition `ζ_A(1) = Σ_d S_d(1)`. -/
theorem val_zeta_one : Valued.v (ζ_A F (single oneExp)) = (1 : ℤᵐ⁰) := by
  classical
  have hsumm := summable_S F (r := 1) (by norm_num) (single oneExp)
  have hf0 : S F 1 (by norm_num) (single oneExp) 0 = 1 := by
    rw [S_one_eq_P F 0 (by norm_num) (single oneExp)]
    exact P_zero_oneExp F
  have hlt : ∀ n : ℕ, 1 ≤ n →
      Valued.v (S F 1 (by norm_num) (single oneExp) n) < (1 : ℤᵐ⁰) := by
    intro n hn
    rw [S_one_eq_P F n (by norm_num) (single oneExp)]
    exact val_P_oneExp_lt_one F n hn
  have h := val_tsum_eq_one_of F (fun n => S F 1 (by norm_num) (single oneExp) n) hf0 hsumm hlt
  rw [zeta_eq_tsum_block F (by norm_num) (single oneExp)]
  exact h

/-- ★★ `ζ_A(1) ≠ 0`: the weight-one multiple zeta value does not vanish. -/
theorem zeta_one_ne_zero : ζ_A F (single oneExp) ≠ 0 := by
  intro hzero
  have h := val_zeta_one F
  rw [hzero] at h
  simp at h

/-- `ζ_A(1)` lies in `𝒵 F 1` (it is the weight-one MZV). -/
theorem zeta_one_mem_Z : ζ_A F (single oneExp) ∈ 𝒵 F 1 := by
  classical
  refine Submodule.subset_span ?_
  rw [Set.mem_iUnion]
  refine ⟨1, ?_⟩
  exact ⟨single oneExp, by simp [𝔖_w, weight, single, oneExp], rfl⟩

/-- ★★ theorem_A is NOT vacuous: `𝒵 F 1` contains the nonzero element `ζ_A(1)`. -/
theorem Z_one_ne_bot : 𝒵 F 1 ≠ (⊥ : Submodule (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  intro hbot
  have hmem := zeta_one_mem_Z F
  rw [hbot] at hmem
  exact zeta_one_ne_zero F (by simpa using hmem)

/-- ★ The closed form of `P_1(1)`: the inverse of `X − X^q`. -/
theorem P_one_oneExp : P F 1 oneExp
    = (((Afac F 1)⁻¹ : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  have h := P_oneExp_eq_prod F 1
  simpa using h

/-- ★ The valuation of `P_1(1)` is `exp (−q)`. -/
theorem val_P_one_oneExp : Valued.v (P F 1 oneExp) = WithZero.exp (-((Nat.card F : ℤ))) := by
  classical
  have hAfac1 : Afac F 1 ≠ 0 := by
    intro hzero
    have hd := intDegree_Afac F 1 (le_refl 1)
    rw [hzero, RatFunc.intDegree_zero] at hd
    have h1 : (0 : ℤ) < ((Nat.card F) ^ 1 : ℤ) := by
      have h := card_ge_two F
      calc (0 : ℤ) < (Nat.card F : ℤ) := by
            exact_mod_cast (by omega : 0 < Nat.card F)
        _ = ((Nat.card F) ^ 1 : ℤ) := by norm_num
    omega
  rw [P_one_oneExp F, inftyValued_v_ratFunc F _ (inv_ne_zero hAfac1),
    RatFunc.intDegree_inv, intDegree_Afac F 1 (le_refl 1)]
  norm_num

end ZagierHoffmanPositiveChar
