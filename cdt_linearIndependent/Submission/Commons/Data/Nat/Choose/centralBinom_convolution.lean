import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# The convolution square of the central binomial coefficients

`Σ_{j=0}^{n} C(2j, j) C(2(n-j), n-j) = 4^n`

We prove this through the closed form `C(2m,m) = (m+1)·(catalan m)` and the
Catalan convolution `Σ_{j=0}^{n} catalan j · catalan (n-j) = catalan (n+1)`.
-/

open scoped BigOperators

namespace Commons.Data.Nat.Choose

private abbrev cb (n : ℕ) : ℚ := Nat.centralBinom n
private abbrev cat (n : ℕ) : ℚ := catalan n

/-- `(m+1) * C(2(m+1), m+1) = 2(2m+1) * C(2m, m)`, over `ℚ`. -/
private lemma cb_succ_rat (m : ℕ) :
    ((m : ℚ) + 1) * cb (m + 1) = 2 * (2 * (m : ℚ) + 1) * cb m := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ m

/-- `(m+1) * catalan m = C(2m, m)`, over `ℚ`. -/
private lemma cat_mul_succ_rat (m : ℕ) :
    ((m : ℚ) + 1) * cat m = cb m := by
  exact_mod_cast succ_mul_catalan_eq_centralBinom m

/-- Catalan convolution over `ℚ`: `Σ_{j=0}^{n} cat j * cat (n-j) = cat (n+1)`. -/
private lemma cat_convolution_rat (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), cat j * cat (n - j)) = cat (n + 1) := by
  have h := catalan_succ' n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n] at h
  exact_mod_cast h.symm

/-- Symmetry of the weighted Catalan convolution:
`Σ (j+1) cat j cat (n-j) = Σ (n+1-j) cat j cat (n-j)`. -/
private lemma cat_weight_symm (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ((j : ℚ) + 1) * cat j * cat (n - j)) =
      (∑ j ∈ Finset.range (n + 1), ((n : ℚ) + 1 - (j : ℚ)) * cat j * cat (n - j)) := by
  let f : ℕ → ℚ := fun m => ((n : ℚ) + 1 - (m : ℚ)) * cat (n - m) * cat m
  have hsum : (∑ j ∈ Finset.range (n + 1), f (n - j)) = (∑ j ∈ Finset.range (n + 1), f j) := by
    simpa using (Finset.sum_range_reflect f (n + 1))
  calc
    (∑ j ∈ Finset.range (n + 1), ((j : ℚ) + 1) * cat j * cat (n - j))
        = (∑ j ∈ Finset.range (n + 1), f (n - j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hw : ((n : ℚ) + 1 - (((n - j) : ℕ) : ℚ)) = (j : ℚ) + 1 := by
            rw [Nat.cast_sub hjn]; ring
          simp [f, Nat.sub_sub_self hjn, hw, mul_left_comm, mul_comm]
    _ = (∑ j ∈ Finset.range (n + 1), f j) := hsum
    _ = (∑ j ∈ Finset.range (n + 1), ((n : ℚ) + 1 - (j : ℚ)) * cat j * cat (n - j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [f, mul_left_comm, mul_comm]

/-- Weighted Catalan convolution:
`2 * Σ (j+1) cat j cat (n-j) = (n+2) * cat (n+1)`. -/
private lemma cat_weighted_convolution (n : ℕ) :
    2 * (∑ j ∈ Finset.range (n + 1), ((j : ℚ) + 1) * cat j * cat (n - j)) =
      ((n : ℚ) + 2) * cat (n + 1) := by
  have hsymm := cat_weight_symm n
  have hconv := cat_convolution_rat n
  let g1 : ℕ → ℚ := fun j => ((j : ℚ) + 1) * cat j * cat (n - j)
  let g2 : ℕ → ℚ := fun j => ((n : ℚ) + 1 - (j : ℚ)) * cat j * cat (n - j)
  let g : ℕ → ℚ := fun j => g1 j + g2 j
  have hg : (∑ j ∈ Finset.range (n + 1), g j) = (∑ j ∈ Finset.range (n + 1), g1 j) +
      (∑ j ∈ Finset.range (n + 1), g2 j) := by
    rw [Finset.sum_add_distrib]
  calc
    2 * (∑ j ∈ Finset.range (n + 1), g1 j)
        = (∑ j ∈ Finset.range (n + 1), g1 j) + (∑ j ∈ Finset.range (n + 1), g2 j) := by
          rw [← hsymm]
          ring
    _ = (∑ j ∈ Finset.range (n + 1), g j) := by
          rw [← hg]
    _ = (∑ j ∈ Finset.range (n + 1), ((n : ℚ) + 2) * (cat j * cat (n - j))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [g, g1, g2]
          ring
    _ = ((n : ℚ) + 2) * (∑ j ∈ Finset.range (n + 1), cat j * cat (n - j)) := by
          rw [← Finset.mul_sum]
    _ = ((n : ℚ) + 2) * cat (n + 1) := by rw [hconv]

/-- `2 * Σ_{j=0}^{n} cb j * cat (n-j) = cb (n+1)`. -/
private lemma cb_cat_convolution (n : ℕ) :
    2 * (∑ j ∈ Finset.range (n + 1), cb j * cat (n - j)) = cb (n + 1) := by
  have hw := cat_weighted_convolution n
  calc
    2 * (∑ j ∈ Finset.range (n + 1), cb j * cat (n - j))
        = 2 * (∑ j ∈ Finset.range (n + 1), ((j : ℚ) + 1) * cat j * cat (n - j)) := by
          refine congrArg (fun x => 2 * x) ?_
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← cat_mul_succ_rat j]
    _ = ((n : ℚ) + 2) * cat (n + 1) := hw
    _ = cb (n + 1) := by
          have hc' : (((n : ℚ) + 1) + 1) * cat (n + 1) = cb (n + 1) := by
            simpa using cat_mul_succ_rat (n + 1)
          rw [show ((n : ℚ) + 2) = ((n : ℚ) + 1) + 1 by ring]
          exact hc'

/-- `cb (n+1) = 2 * Σ_{j=0}^{n} cb j * cb (n-j) / (n-j+1)`. -/
private lemma cb_conv_divided (n : ℕ) :
    cb (n + 1) = 2 * (∑ j ∈ Finset.range (n + 1), cb j * cb (n - j) / (((n - j : ℕ) : ℚ) + 1)) := by
  have hmain := cb_cat_convolution n
  rw [← hmain]
  refine congrArg (fun x => 2 * x) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjm := cat_mul_succ_rat (n - j)
  have hz : ((n - j : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  rw [← hjm]
  field_simp [hz]

/-- Pointwise jump relation used in the convolution recurrence. -/
private lemma cb_jump (n j : ℕ) (hjn : j ≤ n) :
    cb j * cb (n + 1 - j) + 2 * (cb j * cb (n - j) / (((n - j : ℕ) : ℚ) + 1)) =
      4 * (cb j * cb (n - j)) := by
  have hargs : n + 1 - j = (n - j) + 1 := by omega
  rw [hargs]
  have hd : ((n - j : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hrec : cb ((n - j) + 1) =
      (2 * (2 * ((n - j : ℕ) : ℚ) + 1) * cb (n - j)) / (((n - j : ℕ) : ℚ) + 1) := by
    have h := cb_succ_rat (n - j)
    calc
      cb ((n - j) + 1)
          = ((((n - j : ℕ) : ℚ) + 1) * cb ((n - j) + 1)) / (((n - j : ℕ) : ℚ) + 1) := by
              field_simp [hd]
      _ = (2 * (2 * ((n - j : ℕ) : ℚ) + 1) * cb (n - j)) / (((n - j : ℕ) : ℚ) + 1) := by
              rw [h]
  rw [hrec]
  field_simp [hd]
  ring

/-- The convolution `Σ_{j=0}^{n} cb j * cb (n-j)` satisfies
`conv (n+1) = 4 * conv n`. -/
private lemma cbConv_succ (n : ℕ) :
    (∑ j ∈ Finset.range (n + 2), cb j * cb (n + 1 - j)) =
      4 * (∑ j ∈ Finset.range (n + 1), cb j * cb (n - j)) := by
  let f : ℕ → ℚ := fun j => cb j * cb (n + 1 - j)
  have hsplit : (∑ j ∈ Finset.range (n + 2), cb j * cb (n + 1 - j)) =
      (∑ j ∈ Finset.range (n + 1), cb j * cb (n + 1 - j)) + cb (n + 1) * cb 0 := by
    simpa [f, Nat.add_assoc] using (Finset.sum_range_succ f (n + 1))
  have h0 : cb 0 = 1 := by norm_num [cb]
  rw [hsplit, h0, mul_one]
  have hd := cb_conv_divided n
  rw [hd]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact cb_jump n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

lemma centralBinom_convolution (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (Nat.centralBinom j : ℚ) * (Nat.centralBinom (n - j) : ℚ)) =
      (4 : ℚ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∑ j ∈ Finset.range ((n + 1) + 1), (Nat.centralBinom j : ℚ) * (Nat.centralBinom ((n + 1) - j) : ℚ))
            = (∑ j ∈ Finset.range (n + 2), cb j * cb (n + 1 - j)) := by rfl
        _ = 4 * (∑ j ∈ Finset.range (n + 1), cb j * cb (n - j)) := cbConv_succ n
        _ = 4 * ((4 : ℚ) ^ n) := by rw [ih]
        _ = (4 : ℚ) ^ (n + 1) := by ring
