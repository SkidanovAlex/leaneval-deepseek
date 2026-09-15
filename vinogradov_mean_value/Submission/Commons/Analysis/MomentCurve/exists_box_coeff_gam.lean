import Mathlib
import Submission.Commons.Analysis.MomentCurve.transversality_det
import Submission.Commons.Algebra.BigOperators.sum_antidiagonal_pow_div_factorial

open scoped BigOperators

namespace Commons.Analysis.MomentCurve

/-!
# Inverting the box of moment-curve coefficient vectors

Given `l ≥ 1`, `δ ∈ (0,1]` and `u ∈ [-1,1]`, consider the `l × l` matrix
`A (u,δ) := (δ^{i+1} · gam l u (i+1) j)_{j,i}` whose columns are the scaled
derivative vectors `δ^{i+1} Γ^{(i+1)}(u)` of the moment curve.  We show that every
`z` with `|z j| ≤ c δ^l` lies in the image of the box `{|y i| ≤ 1}`, for a constant
`c > 0` depending only on `l`.

The point is that `A(u,δ) = D_δ · B(u)` with `B(u)` lower triangular with diagonal
`(j+1)!` and `D_δ = diag(δ^{i+1})`; after the substitution `Y_i := δ^{i+1} y_i` the
system becomes triangular with unit diagonal, whose inverse is the truncated
exponential `truncExp u`.
-/

/-- The lower-triangular Toeplitz matrix of the truncated exponential:
`(truncExp l u) j i = u ^ (j-i) / (j-i)!` for `i ≤ j`, and `0` otherwise. -/
noncomputable def truncExp (l : ℕ) (u : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  Matrix.of (fun j i =>
    if i.val ≤ j.val then u ^ (j.val - i.val) / ((j.val - i.val).factorial : ℝ) else 0)

lemma truncExp_apply (l : ℕ) (u : ℝ) (j i : Fin l) :
    truncExp l u j i =
      if i.val ≤ j.val then u ^ (j.val - i.val) / ((j.val - i.val).factorial : ℝ) else 0 :=
  rfl

/-- The convolution identity for the truncated exponential:
`∑_{k=0}^{d} u^(d-k)/(d-k)! · (-u)^k/k! = [d = 0]`. -/
lemma sum_range_exp_conv (d : ℕ) (u : ℝ) :
    (∑ k ∈ Finset.range (d + 1),
        u ^ (d - k) / ((d - k).factorial : ℝ) * ((-u) ^ k / (k.factorial : ℝ)))
      = if d = 0 then 1 else 0 := by
  have h1 : (∑ k ∈ Finset.range (d + 1),
        u ^ (d - k) / ((d - k).factorial : ℝ) * ((-u) ^ k / (k.factorial : ℝ)))
      = ∑ k ∈ Finset.range (d + 1),
          (-u) ^ k / (((k.factorial : ℕ)) : ℝ)
            * (u ^ (d - k) / (((d - k).factorial : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  rw [h1, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b : ℕ => (-u) ^ a / (((a.factorial : ℕ)) : ℝ)
          * (u ^ b / (((b.factorial : ℕ)) : ℝ))) d,
      Commons.Algebra.BigOperators.sum_antidiagonal_pow_div_factorial d (-u) u,
      neg_add_cancel]
  by_cases hd : d = 0
  · subst hd; norm_num
  · rw [zero_pow hd, if_neg hd]; simp

/-- The `(j,m)` entry of the product of the truncated exponential with its `-u` counterpart. -/
lemma toeplitz_range_sum (l a b : ℕ) (ha : a < l) (u : ℝ) :
    (∑ n ∈ Finset.range l,
      (if n ≤ a then u ^ (a - n) / ((a - n).factorial : ℝ) else 0) *
      (if b ≤ n then (-u) ^ (n - b) / ((n - b).factorial : ℝ) else 0))
      = if a = b then 1 else 0 := by
  by_cases hba : b ≤ a
  · have hsub : Finset.Ico b (a + 1) ⊆ Finset.range l := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      exact Finset.mem_range.mpr (by omega)
    have hzero : ∀ n ∈ Finset.range l, n ∉ Finset.Ico b (a + 1) →
        (if n ≤ a then u ^ (a - n) / ((a - n).factorial : ℝ) else 0) *
        (if b ≤ n then (-u) ^ (n - b) / ((n - b).factorial : ℝ) else 0) = 0 := by
      intro n _ hn
      rw [Finset.mem_Ico] at hn
      by_cases hnb : b ≤ n
      · have hna : ¬ n ≤ a := fun h => hn ⟨hnb, by omega⟩
        rw [if_neg hna, zero_mul]
      · rw [if_neg hnb, mul_zero]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range]
    have hlen : (a + 1) - b = (a - b) + 1 := by omega
    rw [hlen]
    have hterm : ∀ k ∈ Finset.range ((a - b) + 1),
        (if b + k ≤ a then u ^ (a - (b + k)) / ((a - (b + k)).factorial : ℝ) else 0) *
        (if b ≤ b + k then (-u) ^ (b + k - b) / ((b + k - b).factorial : ℝ) else 0)
        = u ^ (a - b - k) / ((a - b - k).factorial : ℝ)
            * ((-u) ^ k / (k.factorial : ℝ)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [if_pos (show b + k ≤ a by omega), if_pos (show b ≤ b + k by omega)]
      have e1 : a - (b + k) = a - b - k := by omega
      have e2 : b + k - b = k := by omega
      rw [e1, e2]
    rw [Finset.sum_congr rfl hterm, sum_range_exp_conv (a - b) u]
    have hab : a - b = 0 ↔ a = b := by omega
    by_cases h : a = b
    · rw [if_pos h, if_pos (hab.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hab.mp hh))]
  · have hlt : a < b := by omega
    have hzero : ∀ n ∈ Finset.range l,
        (if n ≤ a then u ^ (a - n) / ((a - n).factorial : ℝ) else 0) *
        (if b ≤ n then (-u) ^ (n - b) / ((n - b).factorial : ℝ) else 0) = 0 := by
      intro n _
      by_cases hn : n ≤ a
      · rw [if_pos hn, if_neg (show ¬ b ≤ n by omega), mul_zero]
      · rw [if_neg hn, zero_mul]
    rw [Finset.sum_eq_zero hzero, if_neg (by omega)]

/-- `truncExp` is the inverse of its `-u`-counterpart: `truncExp u * truncExp (-u) = 1`. -/
lemma truncExp_mul_neg (l : ℕ) (u : ℝ) : truncExp l u * truncExp l (-u) = 1 := by
  ext j m
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hconv : (∑ i : Fin l, truncExp l u j i * truncExp l (-u) i m)
      = ∑ i : Fin l,
          (if i.val ≤ j.val then u ^ (j.val - i.val) / ((j.val - i.val).factorial : ℝ) else 0) *
          (if m.val ≤ i.val then
            (-u) ^ (i.val - m.val) / ((i.val - m.val).factorial : ℝ) else 0) :=
    Finset.sum_congr rfl fun i _ => by rw [truncExp_apply, truncExp_apply]
  rw [hconv]
  rw [Fin.sum_univ_eq_sum_range (fun n =>
        (if n ≤ j.val then u ^ (j.val - n) / ((j.val - n).factorial : ℝ) else 0) *
        (if m.val ≤ n then (-u) ^ (n - m.val) / ((n - m.val).factorial : ℝ) else 0))]
  rw [toeplitz_range_sum l j.val m.val j.isLt u]
  by_cases hjm : j = m
  · subst hjm; simp
  · rw [if_neg hjm, if_neg (fun h => hjm (Fin.ext h))]

/-- The scale relation: `gam l u (i+1) j = (j+1)! · (truncExp l u) j i`. -/
lemma gam_eq_factorial_mul_truncExp (l : ℕ) (u : ℝ) (j i : Fin l) :
    gam l u (i.val + 1) j = ((j.val + 1).factorial : ℝ) * truncExp l u j i := by
  rw [gam_apply, truncExp_apply]
  by_cases hij : i.val ≤ j.val
  · rw [if_pos hij]
    have hfac : (((j.val + 1).descFactorial (i.val + 1) : ℕ) : ℝ)
        * (((j.val - i.val).factorial : ℕ) : ℝ) = (((j.val + 1).factorial : ℕ) : ℝ) := by
      have h := Nat.factorial_mul_descFactorial (n := j.val + 1) (k := i.val + 1) (by omega)
      rw [show j.val + 1 - (i.val + 1) = j.val - i.val by omega, mul_comm] at h
      exact_mod_cast h
    have hd : (((j.val - i.val).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hexp : j.val + 1 - (i.val + 1) = j.val - i.val := by omega
    have hD : (((j.val + 1).descFactorial (i.val + 1) : ℕ) : ℝ)
        = (((j.val + 1).factorial : ℕ) : ℝ) / (((j.val - i.val).factorial : ℕ) : ℝ) := by
      rw [eq_div_iff hd]
      exact hfac
    rw [hexp, hD]
    ring
  · rw [if_neg hij]
    have h0 : (j.val + 1).descFactorial (i.val + 1) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h0, Nat.cast_zero, zero_mul, mul_zero]

/-- Every entry of `truncExp` is bounded by `1` when `|u| ≤ 1`. -/
lemma abs_truncExp_le_one (l : ℕ) (u : ℝ) (hu : |u| ≤ 1) (j i : Fin l) :
    |truncExp l u j i| ≤ 1 := by
  rw [truncExp_apply]
  by_cases hij : i.val ≤ j.val
  · rw [if_pos hij, abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (((j.val - i.val).factorial : ℕ) : ℝ) from Nat.cast_nonneg _)]
    have hnum : |u| ^ (j.val - i.val) ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
    have hden : (1 : ℝ) ≤ (((j.val - i.val).factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos _))
    exact div_le_one_of_le₀ (le_trans hnum hden) (le_trans zero_le_one hden)
  · rw [if_neg hij, abs_zero]; norm_num

/-- Matrix-vector product expanded. -/
lemma mulVec_eq_sum {l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ) (v : Fin l → ℝ) (i : Fin l) :
    (M.mulVec v) i = ∑ j : Fin l, M i j * v j := by
  rw [Matrix.mulVec_apply]
  simp [dotProduct]

theorem exists_box_coeff_gam (l : ℕ) (hl : 1 ≤ l) :
    ∃ c : ℝ, 0 < c ∧ ∀ (δ u : ℝ), 0 < δ → δ ≤ 1 → |u| ≤ 1 → ∀ z : Fin l → ℝ,
      (∀ j : Fin l, |z j| ≤ c * δ ^ l) →
      ∃ y : Fin l → ℝ, (∀ i : Fin l, |y i| ≤ 1) ∧
        (∀ j : Fin l, (∑ i : Fin l, y i * (δ ^ (i.val + 1) * gam l u (i.val + 1) j)) = z j) := by
  refine ⟨1 / (2 * (l : ℝ)), by positivity, ?_⟩
  intro δ u hδ hδ1 hu z hz
  set w : Fin l → ℝ := fun j => z j / ((j.val + 1).factorial : ℝ) with hw
  set Y : Fin l → ℝ := (truncExp l (-u)).mulVec w with hY
  have hTY : (truncExp l u).mulVec Y = w := by
    rw [hY, Matrix.mulVec_mulVec, truncExp_mul_neg, Matrix.one_mulVec]
  have hwbound : ∀ j : Fin l, |w j| ≤ (1 / (2 * (l : ℝ))) * δ ^ l := by
    intro j
    have hfac0 : (0 : ℝ) < (((j.val + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hfac1 : (1 : ℝ) ≤ (((j.val + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos _))
    rw [hw, abs_div, abs_of_pos hfac0]
    calc |z j| / (((j.val + 1).factorial : ℕ) : ℝ)
        ≤ |z j| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hfac1
      _ = |z j| := div_one _
      _ ≤ (1 / (2 * (l : ℝ))) * δ ^ l := hz j
  have hYbound : ∀ i : Fin l,
      |Y i| ≤ (l : ℝ) * ((1 / (2 * (l : ℝ))) * δ ^ l) := by
    intro i
    rw [hY, mulVec_eq_sum]
    have hterm : ∀ j : Fin l,
        |truncExp l (-u) i j * w j| ≤ 1 * ((1 / (2 * (l : ℝ))) * δ ^ l) := by
      intro j
      rw [abs_mul]
      exact mul_le_mul (abs_truncExp_le_one l (-u) (by simpa using hu) i j) (hwbound j)
        (abs_nonneg _) zero_le_one
    calc |∑ j : Fin l, truncExp l (-u) i j * w j|
        ≤ ∑ j : Fin l, |truncExp l (-u) i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin l, 1 * ((1 / (2 * (l : ℝ))) * δ ^ l) := Finset.sum_le_sum fun j _ => hterm j
      _ = (l : ℝ) * ((1 / (2 * (l : ℝ))) * δ ^ l) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hlc : (l : ℝ) * (1 / (2 * (l : ℝ))) = 1 / 2 := by field_simp
  refine ⟨fun i => Y i / δ ^ (i.val + 1), ?_, ?_⟩
  · intro i
    have hδpow : (0 : ℝ) < δ ^ (i.val + 1) := pow_pos hδ _
    have hli : i.val + 1 ≤ l := by have := i.isLt; omega
    have hδle : δ ^ l ≤ δ ^ (i.val + 1) := pow_le_pow_of_le_one (le_of_lt hδ) hδ1 hli
    rw [abs_div, abs_of_pos hδpow]
    calc |Y i| / δ ^ (i.val + 1)
        ≤ ((l : ℝ) * ((1 / (2 * (l : ℝ))) * δ ^ l)) / δ ^ (i.val + 1) :=
          div_le_div_of_nonneg_right (hYbound i) (le_of_lt hδpow)
      _ = (l : ℝ) * (1 / (2 * (l : ℝ))) * (δ ^ l / δ ^ (i.val + 1)) := by ring
      _ ≤ (l : ℝ) * (1 / (2 * (l : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hδle (le_of_lt hδpow)) (by positivity)
      _ ≤ 1 := by rw [hlc]; norm_num
  · intro j
    have hfac0 : (((j.val + 1).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hstep : ∀ i : Fin l, (Y i / δ ^ (i.val + 1)) * (δ ^ (i.val + 1) * gam l u (i.val + 1) j)
        = Y i * gam l u (i.val + 1) j := by
      intro i
      have hδp : δ ^ (i.val + 1) ≠ 0 := ne_of_gt (pow_pos hδ _)
      field_simp
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    have hgam : ∀ i : Fin l,
        gam l u (i.val + 1) j = ((j.val + 1).factorial : ℝ) * truncExp l u j i :=
      fun i => gam_eq_factorial_mul_truncExp l u j i
    rw [Finset.sum_congr rfl fun i _ => by rw [hgam i]]
    rw [show (∑ i : Fin l, Y i * ((((j.val + 1).factorial : ℕ) : ℝ) * truncExp l u j i))
        = ((((j.val + 1).factorial : ℕ) : ℝ)) * ((truncExp l u).mulVec Y j) from by
      rw [mulVec_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring]
    rw [hTY]
    have hwj : w j = z j / (((j.val + 1).factorial : ℕ) : ℝ) := by rw [hw]
    rw [hwj, ← mul_div_assoc, mul_div_cancel_left₀ (z j) hfac0]

end Commons.Analysis.MomentCurve
