import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.blockVec_norm
import Submission.Work.TMComp.Duality.two_cos_phase

/-!
# Auxiliary definitions for the block-vector residual estimate

This file collects the small indicator definitions and elementary lemmas used by
`blockVec_residual`.  The block vector `blockVec u s N` puts `u n / N` on the
`N` phase modes `m ∈ [0, N)`; the estimate compares the suspension residual
`(suspA - E) (blockVec u s N)` with the almost Mathieu residual of `u`.

The point of the indicator `blkC` below is that, for the block vector,

`(blockVec u s N) (m, n) = blkC N m * (u n / N)`

for *every* `(m, n)`, so that all shifted coordinates `v (m, n ± 1)`, `v (m ± 1, n)`
become expressions in `blkC` evaluated at `m`, `m ± 1`.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Duality

/-! ## The block indicator -/

/-- Indicator of the block `[0, N)`, as a complex number. -/
def blkC (N : ℕ) (m : ℤ) : ℂ := if 0 ≤ m ∧ m < (N : ℤ) then 1 else 0

/-- Indicator of the block `[0, N)`, as a real number. -/
def blkR (N : ℕ) (m : ℤ) : ℝ := if 0 ≤ m ∧ m < (N : ℤ) then 1 else 0

theorem blkC_rel (N : ℕ) (m : ℤ) : blkC N m = ((blkR N m : ℝ) : ℂ) := by
  rw [blkC, blkR]; by_cases h : 0 ≤ m ∧ m < (N : ℤ) <;> simp [h]

theorem blkR_nonneg (N : ℕ) (m : ℤ) : 0 ≤ blkR N m := by
  rw [blkR]; split <;> norm_num

theorem blkR_le_one (N : ℕ) (m : ℤ) : blkR N m ≤ 1 := by
  rw [blkR]; split <;> norm_num

theorem blkR_eq_zero_or_one (N : ℕ) (m : ℤ) : blkR N m = 0 ∨ blkR N m = 1 := by
  rw [blkR]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem norm_blkC (N : ℕ) (m : ℤ) : ‖blkC N m‖ = blkR N m := by
  rw [blkC_rel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (blkR_nonneg N m)]

theorem norm_blkC_le_one (N : ℕ) (m : ℤ) : ‖blkC N m‖ ≤ 1 := by
  rw [norm_blkC]; exact blkR_le_one N m

/-- `blkC N m * z` is `z` on the block and `0` outside. -/
theorem blkC_mul (N : ℕ) (m : ℤ) (z : ℂ) :
    blkC N m * z = if 0 ≤ m ∧ m < (N : ℤ) then z else 0 := by
  rw [blkC]; split <;> simp_all

theorem blkC_zero_of_lt (N : ℕ) {m : ℤ} (h : m < 0) : blkC N m = 0 := by
  rw [blkC]; exact if_neg (by omega)

theorem blkC_zero_of_le (N : ℕ) {m : ℤ} (h : (N : ℤ) ≤ m) : blkC N m = 0 := by
  rw [blkC]; exact if_neg (by omega)

theorem blkC_one (N : ℕ) {m : ℤ} (h1 : 0 ≤ m) (h2 : m < (N : ℤ)) : blkC N m = 1 := by
  rw [blkC]; exact if_pos ⟨h1, h2⟩

theorem norm_blkC_sub_le_one (N : ℕ) (a b : ℤ) : ‖blkC N a - blkC N b‖ ≤ 1 := by
  rcases blkR_eq_zero_or_one N a with h | h <;> rcases blkR_eq_zero_or_one N b with h' | h'
  · rw [blkC_rel, blkC_rel, h, h']; norm_num
  · rw [blkC_rel, blkC_rel, h, h']; norm_num
  · rw [blkC_rel, blkC_rel, h, h']; norm_num
  · rw [blkC_rel, blkC_rel, h, h']; norm_num

/-- The two block-indicator differences that appear in the residual vanish off the four
exceptional phase modes `-1, 0, N-1, N`. -/
theorem blkC_diff_vanishing (N : ℕ) {m : ℤ} (h1 : m ≠ -1) (h2 : m ≠ 0)
    (h3 : m ≠ (N : ℤ) - 1) (h4 : m ≠ (N : ℤ)) :
    blkC N (m - 1) - blkC N m = 0 ∧ blkC N (m + 1) - blkC N m = 0 := by
  have hmc : blkC N m = if 0 ≤ m ∧ m < (N : ℤ) then 1 else 0 := rfl
  by_cases hm : 0 ≤ m ∧ m < (N : ℤ)
  · have hm1 : blkC N m = 1 := blkC_one N hm.1 hm.2
    have hpm : 0 ≤ m - 1 ∧ m - 1 < (N : ℤ) := ⟨by omega, by omega⟩
    have hpp : 0 ≤ m + 1 ∧ m + 1 < (N : ℤ) := ⟨by omega, by omega⟩
    simp [hm1, blkC_one N hpm.1 hpm.2, blkC_one N hpp.1 hpp.2]
  · have hm0 : blkC N m = 0 := by rw [hmc]; exact if_neg hm
    have hm' : m < 0 ∨ (N : ℤ) ≤ m := by
      by_contra h
      exact hm (by push_neg at h; exact ⟨h.1, h.2⟩)
    rcases hm' with hm' | hm'
    · have h1' : blkC N (m - 1) = 0 := blkC_zero_of_lt N (by omega)
      have h2' : blkC N (m + 1) = 0 := blkC_zero_of_lt N (by omega)
      simp [hm0, h1', h2']
    · have h1' : blkC N (m - 1) = 0 := blkC_zero_of_le N (by omega)
      have h2' : blkC N (m + 1) = 0 := blkC_zero_of_le N (by omega)
      simp [hm0, h1', h2']

/-! ## The support frame -/

/-- The site-indices on which the residual of the block vector can be nonzero:
the support of `u`, shifted by `± 1`. -/
def suppFrame (s : Finset ℤ) : Finset ℤ := s ∪ s.image (fun k => k + 1) ∪ s.image (fun k => k - 1)

/-- The phase-site frame carrying the residual `(suspA - E) (blockVec u s N)`. -/
def blockFrame (s : Finset ℤ) (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico (-1 : ℤ) ((N : ℤ) + 1) ×ˢ suppFrame s

theorem mem_suppFrame_of_mem (s : Finset ℤ) {n : ℤ} (h : n ∈ s) : n ∈ suppFrame s := by
  simp only [suppFrame, Finset.mem_union]
  exact Or.inl (Or.inl h)

theorem mem_suppFrame_add_one (s : Finset ℤ) {n : ℤ} (h : n ∈ s) : n + 1 ∈ suppFrame s := by
  simp only [suppFrame, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨n, h, rfl⟩))

theorem mem_suppFrame_sub_one (s : Finset ℤ) {n : ℤ} (h : n ∈ s) : n - 1 ∈ suppFrame s := by
  simp only [suppFrame, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨n, h, rfl⟩)

/-- The almost Mathieu residual of `u` is supported in `suppFrame s`. -/
theorem amoOp_sub_support (α lam E : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) :
    ∀ n : ℤ, n ∉ suppFrame s →
      ((amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u : ℤ → ℂ) n = 0 := by
  intro n hn
  have hn0 : n ∉ s := fun h => hn (mem_suppFrame_of_mem s h)
  have hn1 : n + 1 ∉ s := fun h => hn (by
    simpa only [add_sub_cancel_right] using mem_suppFrame_sub_one s h)
  have hn2 : n - 1 ∉ s := fun h => hn (by
    simpa only [sub_add_cancel] using mem_suppFrame_add_one s h)
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, amoOp_coord]
  simp only [smul_apply, one_apply_eq_self, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul,
    hs n hn0, hs (n + 1) hn1, hs (n - 1) hn2]
  ring

/-! ## Two elementary norm inequalities -/

/-- `‖x + y‖ ^ 2 ≤ 2 ‖x‖ ^ 2 + 2 ‖y‖ ^ 2`. -/
theorem norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) :=
    mul_self_le_mul_self (norm_nonneg _) h1
  have h2' : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by rw [pow_two, pow_two]; exact h2
  have h3 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  linarith


/-! ## The coordinate formula of the block vector and the residual -/

/-- Every coordinate of `blockVec u s N` factors as `blkC N m * (u n / N)`, provided `u`
vanishes off `s`. -/
theorem blockVec_apply (u : ℤ → ℂ) (s : Finset ℤ) (N : ℕ)
    (hs : ∀ n : ℤ, n ∉ s → u n = 0) (m n : ℤ) :
    blockVec u s N (m, n) = blkC N m * (u n / (N : ℂ)) := by
  rw [blockVec_coord, blkC]
  by_cases h : 0 ≤ m ∧ m < (N : ℤ)
  · by_cases h' : n ∈ s
    · rw [if_pos ⟨h.1, h.2, h'⟩, if_pos h]; ring
    · rw [if_neg (by tauto), if_pos h, hs n h']; ring
  · rw [if_neg (by tauto), if_neg h]; ring

theorem norm_div_natCast_sq (z : ℂ) (N : ℕ) :
    ‖z / (N : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (N : ℝ) ^ 2 := by
  rw [norm_div, Complex.norm_natCast, div_pow]

theorem norm_blkC_mul_sq (N : ℕ) (m : ℤ) (z : ℂ) :
    ‖blkC N m * z‖ ^ 2 = blkR N m * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_blkC]
  rcases blkR_eq_zero_or_one N m with h | h <;> simp [h]

/-- Pointwise coordinate formula for the suspension residual of the block vector: the
residual is the "bulk" term `blkC N m * ((amoOp - E) u) n / N` plus a boundary correction
supported on the four phase modes `-1, 0, N-1, N`. -/
theorem suspA_blockVec_coord (α lam E : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) (m n : ℤ) :
    ((suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) (blockVec (u : ℤ → ℂ) s N)) (m, n)
      = blkC N m * (((amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u : ℤ → ℂ) n / (N : ℂ))
        + ((u : ℤ → ℂ) n / (N : ℂ))
          * ((lam : ℂ) * ph α n * (blkC N (m - 1) - blkC N m)
             + (lam : ℂ) * ph α (-n) * (blkC N (m + 1) - blkC N m)) := by
  have hv : ∀ (m' n' : ℤ), (blockVec (u : ℤ → ℂ) s N) (m', n')
      = blkC N m' * ((u : ℤ → ℂ) n' / (N : ℂ)) := fun m' n' => blockVec_apply _ s N hs m' n'
  have hW : (((amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u : ℤ → ℂ) n)
      = (u : ℤ → ℂ) (n + 1) + (u : ℤ → ℂ) (n - 1)
        + ((2 * lam * Real.cos (2 * Real.pi * (0 + (n : ℝ) * α)) : ℝ) : ℂ) * (u : ℤ → ℂ) n
        - E * (u : ℤ → ℂ) n := by
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, amoOp_coord]
    simp only [smul_apply, one_apply_eq_self, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, suspA_coord]
  simp only [smul_apply, one_apply_eq_self, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
  rw [hv m (n + 1), hv m (n - 1), hv (m - 1) n, hv (m + 1) n, hv m n, hW,
    two_cos_phase α lam 0 n]
  simp only [neg_zero, phR_zero, mul_one]
  ring

/-- The residual of the block vector is supported in the frame `blockFrame s N`. -/
theorem blockVec_residual_support (α lam E : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → (u : ℤ → ℂ) n = 0) {N : ℕ} (hN : 0 < N) (p : ℤ × ℤ)
    (hp : p ∉ blockFrame s N) :
    ((suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) (blockVec (u : ℤ → ℂ) s N)) p = 0 := by
  obtain ⟨m, n⟩ := p
  have hp' : m ∉ Finset.Ico (-1 : ℤ) ((N : ℤ) + 1) ∨ n ∉ suppFrame s := by
    by_contra h
    push Not at h
    exact hp (by
      simp only [blockFrame, Finset.mem_product]
      exact ⟨by simpa only [Finset.mem_Ico] using h.1, h.2⟩)
  rw [suspA_blockVec_coord α lam E u s hs hN m n]
  rcases hp' with h | h
  · have hm : m < -1 ∨ (N : ℤ) + 1 ≤ m := by
      by_contra hc
      push Not at hc
      exact h (by simp only [Finset.mem_Ico]; omega)
    rcases hm with hm | hm
    · rw [blkC_zero_of_lt N (show m < 0 by omega), blkC_zero_of_lt N (show m - 1 < 0 by omega),
        blkC_zero_of_lt N (show m + 1 < 0 by omega)]
      ring
    · rw [blkC_zero_of_le N (show (N : ℤ) ≤ m by omega),
        blkC_zero_of_le N (show (N : ℤ) ≤ m - 1 by omega),
        blkC_zero_of_le N (show (N : ℤ) ≤ m + 1 by omega)]
      ring
  · have hW : (((amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) u : ℤ → ℂ) n) = 0 :=
      amoOp_sub_support α lam E u s hs n h
    have hu : (u : ℤ → ℂ) n = 0 := hs n (fun h' => h (mem_suppFrame_of_mem s h'))
    rw [hW, hu]
    ring


end Work.TMComp.Duality
