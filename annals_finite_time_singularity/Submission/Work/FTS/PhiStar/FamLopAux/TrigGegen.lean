import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.PhiStar.FamLopAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FamLopAux

/-
# The trigonometric form of the Gegenbauer polynomials

`famC k = (3/2)_k/k!` (extended by `0` to negative `k`) and
`famTrig n ψ = Σ_{j<n+1} famC j · famC (n-j) · cos ((2j-n) ψ)` are defined in
`Submission/Work/FTS/PhiStar/FamLopAux/Defs.lean`.  The claim is the classical trigonometric
form of the Gegenbauer polynomial `gC n = C_n^{(3/2)}`.

## Proof recipe (verified numerically to 40 digits)

Let `c k := famC k`, so that `c 0 = 1`, `c (k+1) = c k * ((k + 3/2)/(k+1))`, `c k ≠ 0` for
`k ≥ 0`, and `c k = 0` for `k < 0`.  Write `S n ψ := famTrig n ψ`.

1. **Base cases**: `S 0 ψ = 1`, `S 1 ψ = 3 * cos ψ`.
2. **Recurrence**: prove, for every `n : ℕ` and `ψ : ℝ`,
   `(n+2) * S (n+2) ψ = (2n+5) * cos ψ * S (n+1) ψ - (n+3) * S n ψ`.
   Ingredients (all with the convention `c (-1) = 0`, which is built into `famC`):
   * `cos ψ * cos ((2j-(n+1))ψ) = (cos ((2j-n)ψ) + cos ((2j-n-2)ψ))/2`
     (`Real.cos_add`/`Real.cos_sub`, and `cos` even);
   * reindexing: shifts of the summation range are handled by `Finset.sum_range_succ'`
     (`∑_{i<n+3} F i = ∑_{j<n+2} F (j+1) + F 0`) and `Finset.sum_range_succ`, with
     `F j := c (j-1) * c (n+2-j) * cos ((2j-n-2)ψ)` (write the indices as integers, e.g.
     `(n : ℤ) + 2 - (j : ℤ)`, so that no truncated natural subtraction appears); the only
     "boundary" terms that appear are multiples of `c (-1) = 0`;
   * the pointwise algebraic identity: for `j + l = n + 2` (in `ℕ`),
     `(n+2) * c j * c l = ((2n+5)/2) * (c (j-1) * c l + c j * c (l-1)) - (n+3) * c (j-1) * c (l-1)`.
     For `1 ≤ j ≤ n+1` divide by `c (j-1) * c (l-1) > 0` and use
     `c k / c (k-1) = (2k+1)/(2k) =: α_k`; the identity becomes
     `(j+l) * α_j * α_l - ((2j+2l+1)/2) * (α_j + α_l) + (j+l+1) = 0`, a rational identity
     (`field_simp; ring`).  The two remaining cases `j = 0` and `j = n+2` are handled directly
     (in both, one factor `c (-1)` vanishes and the identity reduces to
     `(k+2)c(k+2) = ((2k+5)/2)c(k+1)`, which is the defining ratio of `c`).
3. **Conclusion**: by induction on `n`, using the recurrence `gC_rec` of
   `Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode`
   (`((n:ℝ)+2) * gC (n+2) x = (2*(n:ℝ)+5) * x * gC (n+1) x - ((n:ℝ)+3) * gC n x`).
-/

set_option autoImplicit false

/-! ## Elementary properties of the coefficients `famC`

`famC k = (3/2)_k / k!` is the coefficient sequence of the binomial series
`(1 - z)^{-3/2}`; by definition it vanishes on the negative integers, which is exactly
what allows the summation ranges of `famTrig` to be shifted without boundary
corrections. -/

lemma famC_zero : famC (0 : ℤ) = 1 := by
  rw [famC]
  norm_num

lemma famC_eq_zero_of_neg {k : ℤ} (hk : k < 0) : famC k = 0 := by
  rw [famC]
  rw [if_neg]
  omega

lemma famC_pos {k : ℤ} (hk : 0 ≤ k) : 0 < famC k := by
  rw [famC, if_pos hk]
  apply div_pos
  · apply Finset.prod_pos
    intro i _
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · exact Nat.cast_pos.mpr (Nat.factorial_pos _)

lemma famC_ne_zero {k : ℤ} (hk : 0 ≤ k) : famC k ≠ 0 := ne_of_gt (famC_pos hk)

/-- The defining ratio of the coefficients: `c (m+1) = c m · (m + 3/2)/(m+1)`. -/
lemma famC_succ_ratio (m : ℕ) :
    famC ((m : ℤ) + 1) = famC (m : ℤ) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) := by
  have h1 : famC ((m : ℤ) + 1)
      = (∏ i ∈ Finset.range (m + 1), ((3 : ℝ) / 2 + i)) / ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
    rw [famC, if_pos (by omega)]
    norm_num
  have h2 : famC ((m : ℤ))
      = (∏ i ∈ Finset.range m, ((3 : ℝ) / 2 + i)) / ((Nat.factorial m : ℕ) : ℝ) := by
    rw [famC, if_pos (by omega)]
    norm_num
  rw [h1, h2, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `c 1 = 3/2`. -/
lemma famC_one : famC (1 : ℤ) = 3 / 2 := by
  have h := famC_succ_ratio 0
  have hone : famC ((((0 : ℕ)) : ℤ) + 1) = famC (1 : ℤ) := congrArg famC (by norm_num)
  have hz : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  rw [hone, hz] at h
  have hval : ((((0 : ℕ)) : ℝ) + 3 / 2) / ((((0 : ℕ)) : ℝ) + 1) = 3 / 2 := by norm_num
  rw [hval, one_mul] at h
  exact h

/-- The boundary instance of the algebraic identity: `2(n+2)c(n+2) = (2n+5)c(n+1)`. -/
lemma famC_boundary (n : ℕ) :
    2 * ((n : ℝ) + 2) * famC ((n : ℤ) + 2) = (2 * (n : ℝ) + 5) * famC ((n : ℤ) + 1) := by
  have hA : (n : ℤ) + 2 = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [hA, famC_succ_ratio (n + 1)]
  push_cast
  field_simp
  ring

/--
**The pointwise algebraic identity driving the recurrence of `famTrig`.**

For integer `j`, `l` with `j + l = n + 2` (and the convention `c k = 0` for `k < 0`),

`2(n+2)·c j·c l = (2n+5)·(c (j-1)·c l + c j·c (l-1)) - 2(n+3)·c (j-1)·c (l-1)`.

Only the case `1 ≤ j`, `1 ≤ l` needs the defining ratio of `c`; the boundary cases
`j ≤ 0` or `l ≤ 0` are handled by `c (-1) = 0`, and `j = 0` / `l = 0` by
`famC_boundary`. -/
lemma famC_ident (n : ℕ) (j l : ℤ) (h : j + l = (n : ℤ) + 2) :
    2 * ((n : ℝ) + 2) * famC j * famC l
      = (2 * (n : ℝ) + 5) * (famC (j - 1) * famC l + famC j * famC (l - 1))
        - 2 * ((n : ℝ) + 3) * (famC (j - 1) * famC (l - 1)) := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have h1 : famC j = 0 := famC_eq_zero_of_neg hj
    have h2 : famC (j - 1) = 0 := famC_eq_zero_of_neg (by omega)
    rw [h1, h2]
    ring
  · -- `j = 0`: then `l = n + 2`
    subst hj
    have hl : l = (n : ℤ) + 2 := by omega
    rw [hl]
    have h0 : famC (0 : ℤ) = 1 := famC_zero
    have hm1 : famC ((0 : ℤ) - 1) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [h0, hm1]
    have hl1 : famC (((n : ℤ) + 2) - 1) = famC ((n : ℤ) + 1) := by congr 1; ring
    rw [hl1]
    linarith [famC_boundary n]
  · rcases lt_trichotomy l 0 with hl | hl | hl
    · have h1 : famC l = 0 := famC_eq_zero_of_neg hl
      have h2 : famC (l - 1) = 0 := famC_eq_zero_of_neg (by omega)
      rw [h1, h2]
      ring
    · -- `l = 0`: then `j = n + 2`
      subst hl
      have hj' : j = (n : ℤ) + 2 := by omega
      rw [hj']
      have h0 : famC (0 : ℤ) = 1 := famC_zero
      have hm1 : famC ((0 : ℤ) - 1) = 0 := famC_eq_zero_of_neg (by norm_num)
      rw [h0, hm1]
      have hl1 : famC (((n : ℤ) + 2) - 1) = famC ((n : ℤ) + 1) := by congr 1; ring
      rw [hl1]
      linarith [famC_boundary n]
    · -- `1 ≤ j` and `1 ≤ l`: the defining ratios
      obtain ⟨m, hm⟩ : ∃ m : ℕ, j = (m : ℤ) + 1 :=
        ⟨(j - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, l = (k : ℤ) + 1 :=
        ⟨(l - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      have hjpred : famC (j - 1) = famC (m : ℤ) := by rw [hm]; congr 1; ring
      have hkpred : famC (l - 1) = famC (k : ℤ) := by rw [hk]; congr 1; ring
      rw [hjpred, hkpred]
      rw [hm, hk] at h ⊢
      have hn : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        have hz : (n : ℤ) = (m : ℤ) + (k : ℤ) := by omega
        exact_mod_cast hz
      rw [hn, famC_succ_ratio m, famC_succ_ratio k]
      have key : 2 * ((m : ℝ) + (k : ℝ) + 2) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1))
            * (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1))
          = (2 * ((m : ℝ) + (k : ℝ)) + 5)
              * ((((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) + (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1)))
            - 2 * ((m : ℝ) + (k : ℝ) + 3) := by
        field_simp
        ring
      linear_combination (famC (m : ℤ) * famC (k : ℤ)) * key

/-- The product-to-sum identity with an arbitrary prefactor. -/
lemma two_cos_mul_aux (A a b : ℝ) :
    2 * (Real.cos a * (A * Real.cos b)) = A * (Real.cos (a + b) + Real.cos (a - b)) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- The base case `n = 0`: `famTrig 0 ψ = 1`. -/
lemma famTrig_zero (ψ : ℝ) : famTrig 0 ψ = 1 := by
  have h0 : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  rw [famTrig, Finset.sum_range_one]
  rw [show (((0 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ) = (((0 : ℕ)) : ℤ) from by norm_num,
      show (((2 : ℝ) * (((0 : ℕ)) : ℝ) - (((0 : ℕ)) : ℝ)) * ψ) = (0 : ℝ) from by ring,
      h0, Real.cos_zero]
  ring

/-- The base case `n = 1`: `famTrig 1 ψ = 3 cos ψ`. -/
lemma famTrig_one (ψ : ℝ) : famTrig 1 ψ = 3 * Real.cos ψ := by
  have h0 : famC (((0 : ℕ)) : ℤ) = 1 := by simpa using famC_zero
  have h1 : famC (((1 : ℕ)) : ℤ) = 3 / 2 := by simpa using famC_one
  rw [famTrig, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (((1 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ) = (((1 : ℕ)) : ℤ) from by norm_num,
      show (((1 : ℕ)) : ℤ) - (((1 : ℕ)) : ℤ) = (((0 : ℕ)) : ℤ) from by norm_num,
      show (((2 : ℝ) * (((0 : ℕ)) : ℝ) - (((1 : ℕ)) : ℝ)) * ψ) = -ψ from by ring,
      show (((2 : ℝ) * (((1 : ℕ)) : ℝ) - (((1 : ℕ)) : ℝ)) * ψ) = ψ from by ring,
      h0, h1, Real.cos_neg]
  ring

/-! ## The three-term recurrence of `famTrig` -/

/--
**The three-term recurrence.**  With `S n ψ := famTrig n ψ`,

`(n+2)·S (n+2) ψ = (2n+5)·cos ψ·S (n+1) ψ - (n+3)·S n ψ`.

The proof writes every sum over the common index range `range (n+3)` (the shifts being
harmless because `famC` vanishes on the negative integers) with the common cosine
`cos ((2i - n - 2)ψ)`, and then applies the pointwise identity `famC_ident` termwise. -/
lemma famTrig_rec (n : ℕ) (ψ : ℝ) :
    ((n : ℝ) + 2) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        - ((n : ℝ) + 3) * famTrig n ψ := by
  -- the four families of summands, all with the common cosine `cos ((2i - n - 2)ψ)`
  set P : ℕ → ℝ := fun i => famC ((i : ℤ) - 1) * famC ((n : ℤ) + 2 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hP
  set Q : ℕ → ℝ := fun i => famC (i : ℤ) * famC ((n : ℤ) + 1 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hQ
  set R : ℕ → ℝ := fun i => famC (i : ℤ) * famC ((n : ℤ) + 2 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hR
  set U : ℕ → ℝ := fun i => famC ((i : ℤ) - 1) * famC ((n : ℤ) + 1 - (i : ℤ))
      * Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hU
  -- `S (n+2)` is the sum of `R`
  have hSn2 : famTrig (n + 2) ψ = ∑ i ∈ Finset.range (n + 3), R i := by
    simp only [famTrig, hR]
    refine Finset.sum_congr (by rfl) (fun i _ => ?_)
    rw [show (((n + 2 : ℕ)) : ℤ) = (n : ℤ) + 2 from by push_cast; ring,
        show (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 from by push_cast; ring]
  have hP0 : P 0 = 0 := by
    simp only [hP]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by norm_num, h1]
    ring
  have hQn : Q (n + 2) = 0 := by
    simp only [hQ]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((n : ℤ) + 1 - (((n + 2 : ℕ)) : ℤ)) = (-1 : ℤ) from by push_cast; ring, h1]
    ring
  have hU0 : U 0 = 0 := by
    simp only [hU]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by norm_num, h1]
    ring
  have hUn : U (n + 2) = 0 := by
    simp only [hU]
    have h1 : famC ((-1 : ℤ)) = 0 := famC_eq_zero_of_neg (by norm_num)
    rw [show ((n : ℤ) + 1 - (((n + 2 : ℕ)) : ℤ)) = (-1 : ℤ) from by push_cast; ring, h1]
    ring
  -- `S n` is the sum of `U`
  have hSn : famTrig n ψ = ∑ i ∈ Finset.range (n + 3), U i := by
    rw [show n + 3 = (n + 2) + 1 from by ring, Finset.sum_range_succ, hUn]
    rw [add_zero]
    rw [show n + 2 = (n + 1) + 1 from by ring, Finset.sum_range_succ', hU0]
    rw [add_zero]
    simp only [famTrig]
    refine Finset.sum_congr (by rfl) (fun j _ => ?_)
    simp only [hU]
    rw [show (((j + 1 : ℕ)) : ℤ) - 1 = (j : ℤ) from by push_cast; ring,
        show ((n : ℤ) + 1 - (((j + 1 : ℕ)) : ℤ)) = ((n : ℤ) - (j : ℤ)) from by push_cast; ring,
        show (((2 : ℝ) * (((j + 1 : ℕ)) : ℝ) - ((n : ℝ) + 2)) * ψ)
            = (((2 : ℝ) * (j : ℝ) - (n : ℝ)) * ψ) from by push_cast; ring]
  -- the shifted sums
  have hshiftP : (∑ j ∈ Finset.range (n + 2), P (j + 1)) = ∑ i ∈ Finset.range (n + 3), P i := by
    have h : (∑ i ∈ Finset.range (n + 3), P i)
        = (∑ j ∈ Finset.range (n + 2), P (j + 1)) + P 0 := Finset.sum_range_succ' P (n + 2)
    rw [hP0, add_zero] at h
    exact h.symm
  have hshiftQ : (∑ j ∈ Finset.range (n + 2), Q j) = ∑ i ∈ Finset.range (n + 3), Q i := by
    have h : (∑ i ∈ Finset.range (n + 3), Q i)
        = (∑ j ∈ Finset.range (n + 2), Q j) + Q (n + 2) := Finset.sum_range_succ Q (n + 2)
    rw [hQn, add_zero] at h
    exact h.symm
  -- the doubled cosine expansion of `2 cos ψ · S (n+1)`
  have hstep : ∀ j : ℕ,
      2 * (Real.cos ψ * (famC (j : ℤ) * famC ((((n + 1 : ℕ)) : ℤ) - (j : ℤ))
        * Real.cos (((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ))) = P (j + 1) + Q j := by
    intro j
    simp only [hP, hQ]
    rw [two_cos_mul_aux]
    rw [show ψ + ((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ
            = ((2 : ℝ) * (((j + 1 : ℕ)) : ℝ) - ((n : ℝ) + 2)) * ψ from by push_cast; ring,
        show ψ - ((2 : ℝ) * (j : ℝ) - (((n + 1 : ℕ)) : ℝ)) * ψ
            = -(((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 2)) * ψ) from by push_cast; ring,
        show famC ((((j + 1 : ℕ)) : ℤ) - 1) = famC ((j : ℤ)) from by congr 1; push_cast; ring,
        show famC ((n : ℤ) + 2 - (((j + 1 : ℕ)) : ℤ)) = famC ((n : ℤ) + 1 - (j : ℤ)) from by
          congr 1; push_cast; ring,
        Real.cos_neg]
    push_cast
    ring
  have hcos : 2 * (Real.cos ψ * famTrig (n + 1) ψ)
      = (∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i) := by
    simp only [famTrig]
    rw [show (n + 1) + 1 = n + 2 from by ring]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_add_distrib, hshiftP, hshiftQ]
  -- the termwise identity
  have hterm : ∀ i ∈ Finset.range (n + 3), (2 * ((n : ℝ) + 2)) * R i
      = (2 * (n : ℝ) + 5) * (P i + Q i) - 2 * ((n : ℝ) + 3) * U i := by
    intro i _
    have h := famC_ident n (i : ℤ) ((n : ℤ) + 2 - (i : ℤ)) (by ring)
    have hpred : famC (((n : ℤ) + 2 - (i : ℤ)) - 1) = famC ((n : ℤ) + 1 - (i : ℤ)) := by
      congr 1; ring
    rw [hpred] at h
    simp only [hP, hQ, hR, hU]
    linear_combination (Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ)) * h
  -- the doubled recurrence
  have hdouble : (2 * ((n : ℝ) + 2)) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5)
          * ((∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i))
        - 2 * ((n : ℝ) + 3) * famTrig n ψ := by
    rw [hSn2, Finset.mul_sum]
    rw [Finset.sum_congr rfl hterm]
    rw [hSn]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmain : 2 * (((n : ℝ) + 2) * famTrig (n + 2) ψ)
      = 2 * ((2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
          - ((n : ℝ) + 3) * famTrig n ψ) := by
    have h1 : 2 * (((n : ℝ) + 2) * famTrig (n + 2) ψ)
        = (2 * ((n : ℝ) + 2)) * famTrig (n + 2) ψ := by ring
    have h2 : (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        = (2 * (n : ℝ) + 5)
            * (((∑ i ∈ Finset.range (n + 3), P i) + (∑ i ∈ Finset.range (n + 3), Q i)) / 2) := by
      rw [show (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
            = (2 * (n : ℝ) + 5) * (Real.cos ψ * famTrig (n + 1) ψ) from by ring,
          show Real.cos ψ * famTrig (n + 1) ψ
            = (2 * (Real.cos ψ * famTrig (n + 1) ψ)) / 2 from by ring,
          hcos]
    rw [h1, hdouble, h2]
    ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain

theorem TrigGegen (n : ℕ) (ψ : ℝ) : Work.FTS.PhiStar.Gegenbauer.gC n (Real.cos ψ) = Work.FTS.PhiStar.famTrig n ψ := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [famTrig_zero]
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
  | one =>
      rw [famTrig_one]
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
  | more n ih1 ih2 =>
      have h2 : ((n : ℝ) + 2) * Work.FTS.PhiStar.Gegenbauer.gC (n + 2) (Real.cos ψ)
          = ((n : ℝ) + 2) * famTrig (n + 2) ψ := by
        rw [Work.FTS.PhiStar.Gegenbauer.gC_rec n (Real.cos ψ), ih1, ih2, famTrig_rec n ψ]
      exact mul_left_cancel₀ (by positivity : ((n : ℝ) + 2) ≠ 0) h2

end Work.FTS.PhiStar.FamLopAux
