import Mathlib
import Submission.Work.Cert.Spec

/-!
# `expTaylor_le_exp`

`expTaylor y n 1 S S` is the truncated, floored Taylor sum of `S·exp(y/S)`: starting from `S`, each
step replaces the current term `t` by `⌊t·y/(S·i)⌋` and adds it on.  Every term is the floor of a
nonnegative quantity, hence is at most the corresponding exact Taylor term, so the whole sum is a
lower bound for `S·exp(y/S)`.
-/

namespace Work.Cert

/-- Floor division is bounded above by the exact quotient, for a positive divisor. -/
private lemma ediv_cast_le_div (a b : ℤ) (hb : 0 < b) :
    (((a.ediv b : ℤ)) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have h := Int.ediv_mul_le a hbne
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  calc ((a.ediv b : ℤ) : ℝ) * (b:ℝ) = (((a.ediv b) * b : ℤ) : ℝ) := by push_cast; ring
    _ ≤ (a:ℝ) := by exact_mod_cast h

/-- One step of the recursion: if the current term `t` (at position `i ≥ 1`) is at most the `(i-1)`-st
exact Taylor term `S·z^{i-1}/(i-1)!`, then the next term `⌊t·y/(S·i)⌋` is at most `S·z^i/i!`, where
`z = y/S`. -/
private lemma term_step (y : ℤ) (hy : 0 ≤ y) (z : ℝ) (hz : (S:ℝ) * z = (y:ℝ))
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ)
    (htb : (t:ℝ) ≤ (S:ℝ) * z^(i-1) / (((i-1).factorial:ℕ):ℝ)) :
    ((fdiv (t*y) (S*(i:ℤ)) : ℤ) : ℝ) ≤ (S:ℝ) * z^i / ((i.factorial :ℕ):ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := by norm_num [S]
  have hb : (0:ℤ) < S * (i:ℤ) := by
    have hi0 : (0:ℤ) < (i:ℤ) := by exact_mod_cast (by omega : 0 < i)
    have hS0 : (0:ℤ) < S := by norm_num [S]
    positivity
  have hfl := ediv_cast_le_div (t*y) (S*(i:ℤ)) hb
  have hfac_nn : 0 ≤ (y:ℝ)/((S:ℝ)*(i:ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right htb hfac_nn
  have hfl' : ((fdiv (t*y) (S*(i:ℤ)) : ℤ) : ℝ) ≤ (t:ℝ) * ((y:ℝ)/((S:ℝ)*(i:ℝ))) := by
    refine le_trans hfl ?_
    push_cast
    rw [mul_div_assoc]
  have hident : ((S:ℝ)*z^(i-1)/((((i-1).factorial:ℕ):ℝ))) * ((y:ℝ)/((S:ℝ)*(i:ℝ)))
      = (S:ℝ)*z^i/(((i.factorial:ℕ):ℝ)) := by
    have h1 : i = (i-1)+1 := (Nat.sub_add_cancel hi).symm
    have hzp : z^i = z^(i-1)*z := by
      conv_lhs => rw [h1]
      rw [pow_succ]
    have hifact : i.factorial = (i-1).factorial * i := by
      conv_lhs => rw [h1]
      rw [Nat.factorial_succ, Nat.sub_add_cancel hi]
      exact Nat.mul_comm _ _
    have hf : (((i.factorial):ℕ):ℝ) = ((((i-1).factorial):ℕ):ℝ) * (i:ℝ) := by
      rw [hifact]; push_cast; ring
    rw [hzp, hf, ← hz]
    field_simp
  exact le_trans hfl' (le_trans hmul (le_of_eq hident))

/-- Main induction.  If at an intermediate state the term `t` is bounded by the `(i-1)`-st exact
Taylor term and the accumulator `acc` by `S` times the `i`-term partial sum of `exp z`, then the
result of the floored recursion is still at most `S·exp z`. -/
private lemma key (y : ℤ) (hy : 0 ≤ y) (z : ℝ) (hz : (S:ℝ) * z = (y:ℝ)) (hz0 : 0 ≤ z) :
    ∀ (fuel i : ℕ) (t acc : ℤ), 1 ≤ i → 0 ≤ t →
    (t:ℝ) ≤ (S:ℝ) * z^(i-1) / (((i-1).factorial:ℕ):ℝ) →
    (acc:ℝ) ≤ (S:ℝ) * (∑ k ∈ Finset.range i, z^k / ((k.factorial:ℕ):ℝ)) →
    (expTaylor y fuel i t acc : ℝ) ≤ (S:ℝ) * Real.exp z := by
  have hS : (0:ℝ) < (S:ℝ) := by norm_num [S]
  intro fuel
  induction fuel with
  | zero =>
      intro i t acc hi ht htb hacc
      show (acc:ℝ) ≤ (S:ℝ) * Real.exp z
      calc (acc:ℝ) ≤ (S:ℝ) * (∑ k ∈ Finset.range i, z^k / ((k.factorial:ℕ):ℝ)) := hacc
        _ ≤ (S:ℝ) * Real.exp z :=
            mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hz0 i) (le_of_lt hS)
  | succ fuel ih =>
      intro i t acc hi ht htb hacc
      have ht'_nn : 0 ≤ fdiv (t*y) (S*(i:ℤ)) := by
        apply Int.ediv_nonneg
        · exact mul_nonneg ht hy
        · have : (0:ℤ) ≤ (i:ℤ) := by exact_mod_cast (Nat.zero_le i)
          exact mul_nonneg (le_of_lt (by norm_num [S] : (0:ℤ) < S)) this
      have ht'b : ((fdiv (t*y) (S*(i:ℤ)) : ℤ) : ℝ) ≤
          (S:ℝ)*z^i/(((i.factorial:ℕ):ℝ)) := term_step y hy z hz i hi t htb
      have ht'b' : ((fdiv (t*y) (S*(i:ℤ)) : ℤ) : ℝ) ≤
          (S:ℝ)*(z^i/(((i.factorial:ℕ):ℝ))) := by
        have h := ht'b
        rw [mul_div_assoc] at h
        exact h
      have hacc' : (((acc + fdiv (t*y) (S*(i:ℤ))) : ℤ) : ℝ) ≤
          (S:ℝ) * (∑ k ∈ Finset.range (i+1), z^k / ((k.factorial:ℕ):ℝ)) := by
        rw [Finset.sum_range_succ]
        push_cast
        rw [mul_add]
        exact add_le_add hacc ht'b'
      exact ih (i+1) (fdiv (t*y) (S*(i:ℤ))) (acc + fdiv (t*y) (S*(i:ℤ)))
        (by omega) ht'_nn ht'b hacc'

theorem expTaylor_le_exp (y : ℤ) (hy : 0 ≤ y) (n : ℕ) :
    (expTaylor y n 1 S S : ℝ) ≤ (S : ℝ) * Real.exp ((y : ℝ) / (S : ℝ)) := by
  have hS : (0:ℝ) < (S:ℝ) := by norm_num [S]
  have hSne : (S:ℝ) ≠ 0 := ne_of_gt hS
  have hz : (S:ℝ) * ((y:ℝ)/(S:ℝ)) = (y:ℝ) := by field_simp
  have hz0 : 0 ≤ (y:ℝ)/(S:ℝ) := by positivity
  have ht : (((S:ℤ)):ℝ) ≤
      (S:ℝ) * ((y:ℝ)/(S:ℝ))^(1-1) / (((1-1).factorial:ℕ):ℝ) := by simp
  have hacc : (((S:ℤ)):ℝ) ≤
      (S:ℝ) * (∑ k ∈ Finset.range 1, ((y:ℝ)/(S:ℝ))^k / ((k.factorial:ℕ):ℝ)) := by simp
  exact key y hy ((y:ℝ)/(S:ℝ)) hz hz0 n 1 S S (by norm_num) (by norm_num [S]) ht hacc

end Work.Cert
