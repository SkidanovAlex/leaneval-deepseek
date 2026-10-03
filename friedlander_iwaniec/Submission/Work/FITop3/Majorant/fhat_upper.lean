/-
# `Submission.Work.FITop3.Majorant.fhat_upper` — the upper half of the (7.7) normalisation

`Fhat Pa f = Σ_{⌊M/4⌋ ≤ u ≤ ⌈4M⌉} f u / √u` is the discrete form of the paper's mean value
(7.7) `f̂(0) = ∫_0^∞ f(u) u^{-1/2} du`.  Here we prove the upper bound `f̂(0) ≤ 4√M` of
`Majorant.fhat_bounds`, from `IsMajorant` and `M ≥ 16` alone.

The proof is the discrete version of `∫_{M/4}^{4M} du/√u = 3√M ≤ 4√M`, with the two
elementary facts that replace the integral:

* `Σ_{u ≤ D} u^{-1/2} ≤ 2√D` (telescoping: `u^{-1/2} ≤ 2(√u - √(u-1))`, since
  `2√u(√u - √(u-1)) = 2u - 2√u√(u-1) ≥ u - (u-1) = 1` by AM–GM);
* the support `f u ≠ 0 → M/4 ≤ u ≤ 4M` of `IsMajorant`, which cuts the sum at `⌊4M⌋` (the
  *ceiling* `⌈4M⌉` of the summation range would overshoot `4√M` when `4M ∉ ℤ`), and pushes the
  terms at `u ≤ 0` (where `√u = 0`) out of the range.

Nothing of the second-difference bound is needed for this half; the ramp estimates are used
only for the *lower* bound `√M/4 ≤ f̂(0)`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3

namespace Work.FITop3.Majorant

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The elementary sum bound `Σ_{u=1}^{N} u^{-1/2} ≤ 2√N` -/

/-- `Σ_{k<N} 1/√(k+1) ≤ 2√N`.  The termwise bound is `1/√(k+1) ≤ 2(√(k+1) - √k)`, which
telescopes. -/
lemma sqrt_inv_sum_range (N : ℕ) :
    ∑ k ∈ Finset.range N, (1:ℝ) / Real.sqrt ((k:ℝ) + 1) ≤ 2 * Real.sqrt (N:ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hgoal : ((Nat.succ n : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    rw [hgoal, Finset.sum_range_succ]
    have hstep : 1 / Real.sqrt ((n:ℝ) + 1) ≤ 2 * (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ)) := by
      have h1 : (Real.sqrt ((n:ℝ)+1))^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
      have h2 : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
      have hkey : 1 ≤ 2 * Real.sqrt ((n:ℝ)+1) * (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ)) := by
        nlinarith [sq_nonneg (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ))]
      have hpos : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ hpos]
      nlinarith [hkey]
    calc ∑ k ∈ Finset.range n, 1/Real.sqrt ((k:ℝ)+1) + 1/Real.sqrt ((n:ℝ) + 1)
        ≤ 2 * Real.sqrt (n:ℝ) + 2*(Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ)) := add_le_add ih hstep
      _ = 2 * Real.sqrt ((n:ℝ) + 1) := by ring

/-- Reindexing an `ℤ`-interval `[1,n]` as a `ℕ`-range: `u = 1 + k`, `k < n`. -/
lemma sum_Icc_one_int_eq_sum_range (h : ℤ → ℝ) (n : ℕ) :
    ∑ u ∈ Finset.Icc (1:ℤ) (n:ℤ), h u = ∑ k ∈ Finset.range n, h ((1:ℤ) + (k:ℤ)) := by
  have himg : Finset.Icc (1:ℤ) (n:ℤ)
      = (Finset.range n).image (fun k : ℕ => (1:ℤ) + (k:ℤ)) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hu
      refine ⟨(u-1).toNat, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image (g := fun k : ℕ => (1:ℤ) + (k:ℤ))]
  intro x _ y _ hxy
  change (1:ℤ) + (x:ℤ) = (1:ℤ) + (y:ℤ) at hxy
  omega

/-- `Σ_{1 ≤ u ≤ n} 1/√u ≤ 2√n`, the `ℤ`-indexed form of `sqrt_inv_sum_range`. -/
lemma sum_Icc_one_sqrt_le (n : ℕ) :
    ∑ u ∈ Finset.Icc (1:ℤ) (n:ℤ), (1:ℝ)/Real.sqrt (u:ℝ) ≤ 2 * Real.sqrt (n:ℝ) := by
  rw [sum_Icc_one_int_eq_sum_range (fun u => (1:ℝ)/Real.sqrt (u:ℝ)) n]
  have hcongr : ∀ k ∈ Finset.range n,
      (1:ℝ)/Real.sqrt (((1:ℤ)+(k:ℤ) : ℤ):ℝ) = (1:ℝ)/Real.sqrt ((k:ℝ)+1) := by
    intro k _
    have hcast : (((1:ℤ)+(k:ℤ) : ℤ):ℝ) = (k:ℝ)+1 := by push_cast; ring
    rw [hcast]
  rw [Finset.sum_congr rfl hcongr]
  exact sqrt_inv_sum_range n

/-! ## 2. `f̂(0) ≤ 4√M` -/

theorem fhat_upper (Pa : Work.FITop.Params) (f : ℤ → ℝ) (h : Work.FITop3.IsMajorant Pa f)
    (hM : 16 ≤ Pa.M) : Work.FITop3.Fhat Pa f ≤ 4 * Real.sqrt Pa.M := by
  unfold Work.FITop3.Fhat
  -- the summation range, and the cut `D = ⌊4M⌋` forced by the support of `f`
  set A : ℤ := ((⌊Pa.M / 4⌋₊ : ℕ) : ℤ) with hAdef
  set B : ℤ := ((⌈4 * Pa.M⌉₊ : ℕ) : ℤ) with hBdef
  set D : ℤ := ((⌊4 * Pa.M⌋₊ : ℕ) : ℤ) with hDdef
  -- step 1: on the support of `f`, `f u / √u ≤ 1/√u`; off it, the term is `0`
  have hstep1 : ∑ u ∈ Finset.Icc A B, f u / Real.sqrt (u : ℝ)
      ≤ ∑ u ∈ (Finset.Icc A B).filter (fun u => f u ≠ 0), (1:ℝ) / Real.sqrt (u : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro u _
    by_cases hf : f u = 0
    · rw [if_neg (by simp [hf]), hf]
      simp
    · rw [if_pos hf]
      have hsup := h.2.2.2.1 u hf
      have h4 : (4:ℝ) ≤ (u:ℝ) := le_trans (by linarith) hsup.1
      have hpos : 0 < Real.sqrt (u:ℝ) := Real.sqrt_pos.mpr (by linarith)
      exact div_le_div_of_nonneg_right (h.2.1 u) (le_of_lt hpos)
  -- step 2: the support of `f` sits inside `[1, ⌊4M⌋]`
  have hsubset : (Finset.Icc A B).filter (fun u => f u ≠ 0) ⊆ Finset.Icc (1:ℤ) D := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hlo, hhi⟩, hfne⟩ := hu
    obtain ⟨hsup1, hsup2⟩ := h.2.2.2.1 u hfne
    have h4 : (4:ℝ) ≤ (u:ℝ) := le_trans (by linarith) hsup1
    have h1 : (1:ℤ) ≤ u := by
      have : (4:ℤ) ≤ u := by exact_mod_cast h4
      omega
    have hu0 : (0:ℤ) ≤ u := le_trans (by norm_num) h1
    have htoNat : ((u.toNat : ℕ) : ℝ) = (u:ℝ) := by
      have hnat : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu0
      exact_mod_cast hnat
    have hle4M : ((u.toNat : ℕ) : ℝ) ≤ 4 * Pa.M := by rw [htoNat]; exact hsup2
    have hfloor : u.toNat ≤ ⌊4 * Pa.M⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hle4M
    have hDz : ((u.toNat : ℕ) : ℤ) ≤ D := by
      rw [hDdef]
      exact_mod_cast hfloor
    have h2 : u ≤ D := by
      have hnat : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu0
      rw [← hnat]
      exact hDz
    rw [Finset.mem_Icc]
    exact ⟨h1, h2⟩
  -- step 3: enlarge the summation set
  have hstep3 : ∑ u ∈ (Finset.Icc A B).filter (fun u => f u ≠ 0), (1:ℝ) / Real.sqrt (u : ℝ)
      ≤ ∑ u ∈ Finset.Icc (1:ℤ) D, (1:ℝ) / Real.sqrt (u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => div_nonneg zero_le_one (Real.sqrt_nonneg _))
  -- step 4: `Σ_{u ≤ ⌊4M⌋} 1/√u ≤ 2√⌊4M⌋ ≤ 2√(4M) = 4√M`
  have hstep4 : ∑ u ∈ Finset.Icc (1:ℤ) D, (1:ℝ) / Real.sqrt (u : ℝ) ≤ 4 * Real.sqrt Pa.M := by
    have h1 : ∑ u ∈ Finset.Icc (1:ℤ) (((⌊4 * Pa.M⌋₊ : ℕ) : ℤ)), (1:ℝ) / Real.sqrt (u : ℝ)
        ≤ 2 * Real.sqrt ((⌊4 * Pa.M⌋₊ : ℝ)) := sum_Icc_one_sqrt_le ⌊4 * Pa.M⌋₊
    rw [hDdef]
    have hfl : ((⌊4 * Pa.M⌋₊ : ℕ) : ℝ) ≤ 4 * Pa.M := Nat.floor_le (by positivity)
    have hsqrt : Real.sqrt ((⌊4 * Pa.M⌋₊ : ℝ)) ≤ 2 * Real.sqrt Pa.M := by
      refine le_trans (Real.sqrt_le_sqrt hfl) ?_
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      have h4 : Real.sqrt (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
    linarith
  linarith [hstep1, hstep3, hstep4]

end

end Work.FITop3.Majorant
