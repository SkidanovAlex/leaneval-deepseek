import Mathlib
import Submission.Work.Lattice.MaxNorm
import Submission.Commons.Analysis.InnerProductSpace.norm_le_sqrt_card_mul_of_abs_le

/-!
# The sup norm along the diagonal flow: top block, and comparison with the Euclidean norm

This module continues `Submission.Work.Lattice.MaxNorm` (the paper's max norm `cnorm` on
`⋀^k ℝᵈ` and the exact flow identity `cnorm_map_flow`) with the two tools that de Saxcé's §3
needs in order to pass between the max norm (used for the Grayson polygon, because "the
behaviour of that norm with respect to differentiation is particularly simple") and the
Euclidean norm (used for the covolume/successive-minima theory).

## 1. The top block index

For an arbitrary `k`-vector `w` (not necessarily a pure tensor) we define

    topBlockIndex ℓ w = the largest u ≤ k with blockElem w u ≠ 0

(and `0` when `w = 0`).  It satisfies `IsTopBlock ℓ w (topBlockIndex ℓ w)` whenever `w ≠ 0`,
and it is the exponent index which eventually dominates the sup norm of the flowed vector:
since `σ_u = -k/ℓ + u·(1/ℓ + 1/(d-ℓ))` is *strictly increasing* in `u`, the block `topBlockIndex`
is the unique eventual argmax.

## 2. `eventually_cnorm_map_flow_eq_top`

For `w ≠ 0` there is `T` such that for all `t ≥ T`

    cnorm (⋀^k a_t w) = exp (t·σ_{u₀}) · cnorm (blockElem w u₀),  u₀ = topBlockIndex ℓ w,

i.e. the sup norm of the flowed `k`-vector is *exactly* the top-block eigenvalue — no `k+1`
constant.  This pins down the paper's integers `ℓ_s`: for large `t` they are the *positions*
`j_s - dim (span V_{j_s} ⊓ L)` (via `Submission.TopBlockIndex.isTopBlock_iMulti`).

## 3. The two norms are comparable with the explicit constant `√(C(d,k))`

`cnorm_le_norm` and `norm_le_sqrt_card_mul_cnorm` give

    cnorm w ≤ ‖w‖ ≤ sqrt (Nat.choose d k) · cnorm w,

so `|log (max-covolume) - log (Euclidean covolume)| ≤ (1/2) log (Nat.choose d k)`: the
max-norm Grayson polygon of the paper and the Euclidean polygon of this repository differ by
a constant depending only on `d, k`, and so do their slopes.  Since all statements of §3 carry
an `O(1)`, the Euclidean polygon layer already on disk may be used in place of the paper's.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNorm
open Submission.FlowRate
open Submission.FlowRateAsymptotic

namespace Submission.MaxNormFlow

variable {d : ℕ}

/-! ### The top block index of an arbitrary `k`-vector -/

/-- The largest `u ≤ k` with nonvanishing block `u` (and `0` when `w = 0`). -/
noncomputable def topBlockIndex (ℓ : ℕ) {k : ℕ} (w : WK d k) : ℕ := by
  classical
  exact Nat.findGreatest (fun u => blockElem (d := d) (k := k) (ℓ := ℓ) w u ≠ 0) k

lemma topBlockIndex_le (ℓ : ℕ) {k : ℕ} (w : WK d k) :
    topBlockIndex (d := d) ℓ w ≤ k := by
  classical
  exact Nat.findGreatest_le k

lemma le_topBlockIndex (ℓ : ℕ) {k u : ℕ} (w : WK d k) (hu : u ≤ k)
    (h : blockElem (d := d) (k := k) (ℓ := ℓ) w u ≠ 0) :
    u ≤ topBlockIndex (d := d) ℓ w := by
  classical
  exact Nat.le_findGreatest hu h

lemma exists_blockElem_ne_zero_of_ne_zero {k ℓ : ℕ} (w : WK d k) (hw : w ≠ 0) :
    ∃ u ≤ k, blockElem (d := d) (k := k) (ℓ := ℓ) w u ≠ 0 := by
  by_contra h
  have hzero : ∀ u ≤ k, blockElem (d := d) (k := k) (ℓ := ℓ) w u = 0 := by
    intro u hu
    by_contra hne
    exact h ⟨u, hu, hne⟩
  have hsum : (Finset.range (k + 1)).sum
      (fun u => blockElem (d := d) (k := k) (ℓ := ℓ) w u) = 0 := by
    refine Finset.sum_eq_zero (fun u hu => ?_)
    exact hzero u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
  rw [sum_blockElem (d := d) (k := k) (ℓ := ℓ) w] at hsum
  exact hw hsum

lemma blockElem_topBlockIndex_ne_zero {k ℓ : ℕ} (w : WK d k) (hw : w ≠ 0) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w (topBlockIndex (d := d) ℓ w) ≠ 0 := by
  classical
  obtain ⟨u, hu, hne⟩ := exists_blockElem_ne_zero_of_ne_zero (d := d) (k := k) (ℓ := ℓ) w hw
  exact Nat.findGreatest_spec (P := fun v => blockElem (d := d) (k := k) (ℓ := ℓ) w v ≠ 0) hu hne

lemma blockElem_eq_zero_of_topBlockIndex_lt {k ℓ u : ℕ} (w : WK d k)
    (h : topBlockIndex (d := d) ℓ w < u) (huk : u ≤ k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w u = 0 := by
  classical
  by_contra hne
  exact absurd (le_topBlockIndex ℓ w huk hne) (not_le.mpr h)

/-- For `w ≠ 0` the top block index is the top nonvanishing block. -/
lemma isTopBlock_topBlockIndex {k ℓ : ℕ} (w : WK d k) (hw : w ≠ 0) :
    IsTopBlock (d := d) (ℓ := ℓ) w (topBlockIndex (d := d) ℓ w) :=
  ⟨blockElem_topBlockIndex_ne_zero (d := d) w hw,
    fun _ hu' hu'k => blockElem_eq_zero_of_topBlockIndex_lt (d := d) w hu' hu'k⟩

/-! ### Comparison of the sup norm with the Euclidean norm -/

/-- The sup norm is bounded by the Euclidean norm. -/
lemma cnorm_le_norm {k : ℕ} (hk : k ≤ d) (w : WK d k) :
    cnorm (d := d) hk w ≤ ‖w‖ := by
  refine cnorm_le_of_forall (d := d) hk w (fun I => ?_)
  have h1 : (wcoord (d := d) (k := k) w I) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [normSq_eq_sum_wcoord (d := d) (k := k) w]
    exact Finset.single_le_sum (fun J _ => sq_nonneg _) (Finset.mem_univ I)
  have h2 : |wcoord (d := d) (k := k) w I| ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [sq_abs]
    exact h1
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg w)).mp h2

/-- The cardinality of the index set of `k`-subsets is `Nat.choose d k`. -/
lemma card_IDX (d k : ℕ) : Fintype.card (IDX d k) = Nat.choose d k := by
  have h1 : Nat.card (IDX d k) = Nat.choose d k := by
    have h := Set.powersetCard.card (Fin d) k
    simpa using h
  rwa [Nat.card_eq_fintype_card] at h1

/-- The Euclidean norm is bounded by `√(C(d,k))` times the sup norm. -/
lemma norm_le_sqrt_card_mul_cnorm {k : ℕ} (hk : k ≤ d) (w : WK d k) :
    ‖w‖ ≤ Real.sqrt (Nat.choose d k) * cnorm (d := d) hk w := by
  have hM : 0 ≤ cnorm (d := d) hk w := cnorm_nonneg (d := d) hk w
  have hsum : (Finset.univ : Finset (IDX d k)).sum
      (fun I => (wcoord (d := d) (k := k) w I) ^ 2) ≤
        (Nat.choose d k : ℝ) * (cnorm (d := d) hk w) ^ 2 := by
    calc (Finset.univ : Finset (IDX d k)).sum
            (fun I => (wcoord (d := d) (k := k) w I) ^ 2)
        ≤ (Finset.univ : Finset (IDX d k)).sum
            (fun _ => (cnorm (d := d) hk w) ^ 2) := by
          refine Finset.sum_le_sum (fun I _ => ?_)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (le_cnorm (d := d) hk w I) 2
      _ = (Finset.univ : Finset (IDX d k)).card * (cnorm (d := d) hk w) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Nat.choose d k : ℝ) * (cnorm (d := d) hk w) ^ 2 := by
          rw [Finset.card_univ, card_IDX]
  have hsq : ‖w‖ ^ 2 ≤ (Real.sqrt (Nat.choose d k) * cnorm (d := d) hk w) ^ 2 := by
    rw [normSq_eq_sum_wcoord (d := d) (k := k) w]
    calc (Finset.univ : Finset (IDX d k)).sum
            (fun I => (wcoord (d := d) (k := k) w I) ^ 2)
        ≤ (Nat.choose d k : ℝ) * (cnorm (d := d) hk w) ^ 2 := hsum
      _ = (Real.sqrt (Nat.choose d k) * cnorm (d := d) hk w) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h3 : 0 ≤ Real.sqrt (Nat.choose d k) * cnorm (d := d) hk w :=
    mul_nonneg (Real.sqrt_nonneg _) hM
  have h4 : |‖w‖| ≤ |Real.sqrt (Nat.choose d k) * cnorm (d := d) hk w| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg h3] at h4

/-! ### The flow identity at the top block -/

/-- `σ` is monotone in the block index. -/
lemma sig_mono {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {u v : ℕ} (h : u ≤ v) :
    sig (d := d) k ℓ u ≤ sig (d := d) k ℓ v := by
  have hgap := sig_sub_sig (d := d) (k := k) (ℓ := ℓ) h
  have hpos : 0 ≤ (((v - u : ℕ)) : ℝ) * slope (d := d) ℓ :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (slope_pos (d := d) hℓ0 hℓd))
  linarith [hgap]

/-- **The sup norm of the flowed `k`-vector is eventually exactly the top-block eigenvalue.**
For `w ≠ 0` and all sufficiently large `t`,

    cnorm (⋀^k a_t w) = exp (t · σ_{u₀}) · cnorm (blockElem w u₀),   u₀ = topBlockIndex ℓ w. -/
theorem eventually_cnorm_map_flow_eq_top {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (hk : k ≤ d) (w : WK d k) (hw : w ≠ 0) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      cnorm (d := d) hk (exteriorPower.map k
          (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ)) w) =
        Real.exp (t * sig (d := d) k ℓ (topBlockIndex (d := d) ℓ w)) *
          cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w
            (topBlockIndex (d := d) ℓ w)) := by
  classical
  set u₀ := topBlockIndex (d := d) ℓ w with hu₀
  have hu₀k : u₀ ≤ k := topBlockIndex_le (d := d) ℓ w
  have hne : (Finset.range (k + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  have hmem : u₀ ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hu₀k)
  have hβpos : 0 < cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) :=
    cnorm_pos_of_ne_zero (d := d) hk _ (blockElem_topBlockIndex_ne_zero (d := d) (k := k) w hw)
  -- the eventual comparison of the lower blocks with the top block
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ u : ℕ, u < u₀ →
      Real.exp (t * sig (d := d) k ℓ u) *
          cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≤
        Real.exp (t * sig (d := d) k ℓ u₀) *
          cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) := by
    rcases Nat.eq_zero_or_pos u₀ with h0 | hpos
    · exact ⟨0, fun t _ u hu => absurd hu (by omega)⟩
    · have hc : sig (d := d) k ℓ (u₀ - 1) - sig (d := d) k ℓ u₀ < 0 := by
        have h1 : sig (d := d) k ℓ (u₀ - 1) < sig (d := d) k ℓ u₀ :=
          sig_strict hℓ0 hℓd (by omega) hu₀k
        linarith
      have hev : ∀ᶠ t : ℝ in Filter.atTop,
          Real.exp (t * (sig (d := d) k ℓ (u₀ - 1) - sig (d := d) k ℓ u₀)) * ‖w‖ ≤
            cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) :=
        Filter.Tendsto.eventually_le_const hβpos
          (tendsto_exp_mul_const_zero (D := ‖w‖) hc)
      obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
      refine ⟨max T₀ 0, fun t ht u hu => ?_⟩
      have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
      have hut : u ≤ u₀ - 1 := by omega
      have hsig : sig (d := d) k ℓ u ≤ sig (d := d) k ℓ (u₀ - 1) :=
        sig_mono hℓ0 hℓd hut
      have hexp : Real.exp (t * sig (d := d) k ℓ u) ≤
          Real.exp (t * sig (d := d) k ℓ (u₀ - 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsig ht0)
      have hcn : cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≤ ‖w‖ :=
        le_trans (cnorm_le_norm (d := d) hk _)
          (norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) w (le_of_lt (lt_of_lt_of_le hu hu₀k)))
      have hstep1 : Real.exp (t * sig (d := d) k ℓ u) *
            cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u) ≤
          Real.exp (t * sig (d := d) k ℓ (u₀ - 1)) * ‖w‖ :=
        mul_le_mul hexp hcn (cnorm_nonneg (d := d) hk _) (le_of_lt (Real.exp_pos _))
      have hid : Real.exp (t * sig (d := d) k ℓ (u₀ - 1)) * ‖w‖ =
          Real.exp (t * sig (d := d) k ℓ u₀) *
            (Real.exp (t * (sig (d := d) k ℓ (u₀ - 1) - sig (d := d) k ℓ u₀)) * ‖w‖) := by
        rw [show t * sig (d := d) k ℓ (u₀ - 1) =
            t * sig (d := d) k ℓ u₀ + t * (sig (d := d) k ℓ (u₀ - 1) - sig (d := d) k ℓ u₀)
            by ring, Real.exp_add, mul_assoc]
      have hstep2 : Real.exp (t * sig (d := d) k ℓ (u₀ - 1)) * ‖w‖ ≤
          Real.exp (t * sig (d := d) k ℓ u₀) *
            cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u₀) := by
        rw [hid]
        exact mul_le_mul_of_nonneg_left (hT₀ t (le_trans (le_max_left _ _) ht))
          (le_of_lt (Real.exp_pos _))
      exact le_trans hstep1 hstep2
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  rw [cnorm_map_flow (d := d) hℓ0 hℓd t hk w]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hne
      (fun u => Real.exp (t * sig (d := d) k ℓ u) *
        cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) (fun u hu => ?_)
    have huk : u ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    by_cases hue : u = u₀
    · rw [hue]
    · rcases lt_or_gt_of_ne hue with hlt | hgt
      · exact hT t (le_trans (le_max_left _ _) ht) u hlt
      · have hzero : blockElem (d := d) (k := k) (ℓ := ℓ) w u = 0 :=
          blockElem_eq_zero_of_topBlockIndex_lt (d := d) w hgt huk
        rw [hzero, cnorm_zero, mul_zero]
        exact mul_nonneg (le_of_lt (Real.exp_pos _)) (cnorm_nonneg (d := d) hk _)
  · exact Finset.le_sup'
      (fun u => Real.exp (t * sig (d := d) k ℓ u) *
        cnorm (d := d) hk (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) hmem

end Submission.MaxNormFlow
