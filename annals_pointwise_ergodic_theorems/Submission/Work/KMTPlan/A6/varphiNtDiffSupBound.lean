import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff
import Submission.Work.KMTPlan.A6.RandSymbAux
import Submission.Work.KMTPlan.A6.lacGeomSumBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Finset
open scoped BigOperators NNReal

/-! ## The difference `φ_{N,t} − φ_N` at the bottom height

At the bottom height `k₁ = 0` the two bumps of `lacunaryBump_mult_bound_k0_diff` are

  `φ_{N,t}(ξ) = η(2^{Log N}ξ) e(Ntξ)`,  `φ_N(ξ) = η(2^{Log N}ξ)`,

so their difference is `η(2^{Log N}ξ)·(e(Ntξ) − 1)`: the factor `e(Ntξ) − 1` vanishes at `ξ = 0`
and is `O(N|ξ|)` on the (shrinking) support of `η(2^{Log N}·)`.  This is the structural fact
behind the whole bound. -/

/-- The difference of the bumps at the bottom height, in factored form. -/
private lemma varphiNt_sub_varphiN_eq (N : ℕ) (t ξ : ℝ) :
    Work.KMTAreas.A7.varphiNt N 0 t ξ - Work.KMTAreas.A7.varphiN N 0 ξ
      = Work.KMTContract.kmtEta
          (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * ξ)
          * (Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ) - 1) := by
  rw [Work.KMTAreas.A7.varphiNt_zero_sub_varphiN, Work.KMTAreas.A7.lacσ_eq]
  norm_num

/-- `e 0 = 1`. -/
private lemma ee_zero : Work.KMTAreas.A7.ee (0 : ℝ) = 1 := by
  simp [Work.KMTAreas.A7.ee]

/-- Pointwise bound for the difference: `‖φ_{N,t}(ξ) − φ_N(ξ)‖ ≤ 2π N|ξ|` for `t ∈ [1/2,1]`. -/
private lemma norm_varphiNt_sub_varphiN_le (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
    (N : ℕ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphiNt N 0 t ξ - Work.KMTAreas.A7.varphiN N 0 ξ‖
      ≤ 2 * Real.pi * ((N : ℝ) * |ξ|) := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have ht1 : t ≤ 1 := ht.2
  rw [varphiNt_sub_varphiN_eq]
  have hη : ‖Work.KMTContract.kmtEta
      (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * ξ)‖ ≤ 1 :=
    Work.KMTContract.norm_kmtEta_le _
  have hee : ‖Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ) - 1‖
      ≤ 2 * Real.pi * ((N : ℝ) * t * |ξ|) := by
    have h := Work.KMTPlan.A6.norm_ee_sub_le ((N : ℝ) * t * ξ) 0
    rw [sub_zero, ee_zero] at h
    have h2 : |(N : ℝ) * t * ξ| = (N : ℝ) * t * |ξ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg N), abs_of_nonneg ht0]
    rwa [h2] at h
  have hmul : ‖Work.KMTContract.kmtEta
        (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * ξ)
        * (Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ) - 1)‖
      ≤ 1 * (2 * Real.pi * ((N : ℝ) * t * |ξ|)) := by
    rw [norm_mul]
    exact mul_le_mul hη hee (norm_nonneg _) (by norm_num)
  have hNξ : 0 ≤ (N : ℝ) * |ξ| := by positivity
  have hmono : (N : ℝ) * t * |ξ| ≤ (N : ℝ) * |ξ| := by
    calc (N : ℝ) * t * |ξ| = t * ((N : ℝ) * |ξ|) := by ring
      _ ≤ 1 * ((N : ℝ) * |ξ|) := mul_le_mul_of_nonneg_right ht1 hNξ
      _ = (N : ℝ) * |ξ| := by ring
  calc ‖Work.KMTContract.kmtEta
        (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * ξ)
        * (Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ) - 1)‖
      ≤ 1 * (2 * Real.pi * ((N : ℝ) * t * |ξ|)) := hmul
    _ = 2 * Real.pi * ((N : ℝ) * t * |ξ|) := by ring
    _ ≤ 2 * Real.pi * ((N : ℝ) * |ξ|) := by
        have hπ : 0 < 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hmono hπ.le

/-- Where the difference does not vanish, the scale is comparable with `1/|ξ|`: `N|ξ| < 2`.

Indeed a nonzero difference forces `η(2^{Log N}ξ) ≠ 0`, i.e. `2^{Log N}|ξ| < 1`, while
`N < 2·2^{Log N}`. -/
private lemma floor_mul_abs_lt_two (N : ℕ) (t ξ : ℝ)
    (h : Work.KMTAreas.A7.varphiNt N 0 t ξ - Work.KMTAreas.A7.varphiN N 0 ξ ≠ 0) :
    (N : ℝ) * |ξ| < 2 := by
  rw [varphiNt_sub_varphiN_eq] at h
  set L : ℝ := ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) with hL
  have hη : Work.KMTContract.kmtEta ((2 : ℝ) ^ L * ξ) ≠ 0 := by
    intro hc
    exact h (by rw [hc, zero_mul])
  have hle : |(2 : ℝ) ^ L * ξ| ≤ 1 := by
    by_contra hcon
    push Not at hcon
    exact hη (Work.KMTContract.kmtEta_zero (le_of_lt hcon))
  have hp : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hle' : (2 : ℝ) ^ L * |ξ| ≤ 1 := by
    rw [abs_mul, abs_of_pos hp] at hle
    exact hle
  have hN : (N : ℝ) < 2 * (2 : ℝ) ^ L := by
    simpa only [hL] using (Work.KMTPlan.A6.lt_two_mul_pow_logN N)
  rcases eq_or_lt_of_le (abs_nonneg ξ) with h0 | hpos
  · rw [← h0, mul_zero]; norm_num
  · have h3 : (N : ℝ) * |ξ| < (2 * (2 : ℝ) ^ L) * |ξ| := mul_lt_mul_of_pos_right hN hpos
    have h4 : (2 * (2 : ℝ) ^ L) * |ξ| = 2 * ((2 : ℝ) ^ L * |ξ|) := by ring
    rw [h4] at h3
    linarith

/-- The signed sums of the *difference* `varphiNt N 0 t − varphiN 0 0 = varphiN N 0 (e(N t ·) − 1)`
are bounded by a constant depending only on `Λ`.  The subtraction removes the value at `ξ = 0`
(where the un-subtracted family has uniformly unbounded signed sums), so this is the
`hz-integralDiff`-type bound of `Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff`, here in the
signs-only form consumed by the A6 `mdlVanishingCase` route. -/
theorem varphiNtDiffSupBound (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := lacGeomSumBound Λ hΛ
  refine ⟨2 * Real.pi * C₀ + 1, by positivity, ?_⟩
  intro t ht a ha ha1 U ω ξ
  classical
  have hterm : ∀ n : ℕ, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ‖
      ≤ 2 * Real.pi * ((Nat.floor (a n) : ℝ) * |ξ|) :=
    fun n => norm_varphiNt_sub_varphiN_le t ht (Nat.floor (a n)) ξ
  have hsupp : ∀ n ∈ U.filter (fun n =>
      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0),
      (Nat.floor (a n) : ℝ) * |ξ| < 2 := by
    intro n hn
    exact floor_mul_abs_lt_two (Nat.floor (a n)) t ξ (Finset.mem_filter.mp hn).2
  calc ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)‖
      ≤ ∑ n ∈ U, ‖(if ω n then (1 : ℂ) else -1) *
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ U, ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul]
        by_cases h : ω n <;> simp [h]
    _ = ∑ n ∈ U.filter (fun n =>
          Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0),
          ‖Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ‖ :=
        (Finset.sum_filter_of_ne fun n _ hn => norm_ne_zero_iff.mp hn).symm
    _ ≤ ∑ n ∈ U.filter (fun n =>
          Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0),
          2 * Real.pi * ((Nat.floor (a n) : ℝ) * |ξ|) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = 2 * Real.pi * ∑ n ∈ U.filter (fun n =>
          Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0),
          (Nat.floor (a n) : ℝ) * |ξ| := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.pi * C₀ :=
        mul_le_mul_of_nonneg_left (hC₀ a ha ha1 |ξ| _ hsupp) (by positivity)
    _ ≤ 2 * Real.pi * C₀ + 1 := by linarith

end Work.KMTPlan.A6
