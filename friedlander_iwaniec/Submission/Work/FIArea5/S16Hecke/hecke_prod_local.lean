/-
# `Submission.Work.FIArea5.S16Hecke.hecke_prod_local`

Definitions and elementary lemmas for the local (Euler-factor) positivity underlying
`hecke_prod_coeff_nonneg`.

For real `a, b` with `|a| ≤ 1`, `|b| ≤ 1`, the power series
  `1 / ((1-X)(1-aX)(1-bX)(1-abX))`
has non-negative coefficients.  We package the coefficient sequence as `Gab a b`, defined
explicitly as
  `Gab a b k = Σ_{m=0}^{k/2} (ab)^m · S a (k-2m) · S b (k-2m)`,  `S a n = 1 + a + … + a^n`,
which makes the sign analysis transparent; the companion lemma `Gab_cauchy` records that this is
the coefficient sequence of the four-fold product of geometric series.

`cvs` is the Cauchy product of sequences (convolution over `+`); its ring laws are recorded via the
embedding into formal power series.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Gab_cauchy

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-! ## The Cauchy product -/

/-- Cauchy product (convolution over `+`) of two sequences. -/
def cvs {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  fun n => ∑ i ∈ Finset.range (n+1), f i * g (n - i)

lemma mk_cvs {R : Type*} [Semiring R] (f g : ℕ → R) :
    PowerSeries.mk (cvs f g) = PowerSeries.mk f * PowerSeries.mk g := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j)]
  simp only [cvs]

theorem cvs_comm {R : Type*} [CommSemiring R] (f g : ℕ → R) : cvs f g = cvs g f := by
  funext n
  have h : PowerSeries.mk (cvs f g) = PowerSeries.mk (cvs g f) := by
    rw [mk_cvs, mk_cvs, mul_comm]
  have h2 := congrArg (fun φ => PowerSeries.coeff n φ) h
  simpa using h2

theorem cvs_assoc {R : Type*} [Semiring R] (f g h : ℕ → R) :
    cvs (cvs f g) h = cvs f (cvs g h) := by
  funext n
  have hh : PowerSeries.mk (cvs (cvs f g) h) = PowerSeries.mk (cvs f (cvs g h)) := by
    rw [mk_cvs, mk_cvs, mk_cvs, mk_cvs, mul_assoc]
  have h2 := congrArg (fun φ => PowerSeries.coeff n φ) hh
  simpa using h2

/-- Associativity of the Cauchy product, in the direction used to reassociate factors. -/
theorem cvs_assoc' {R : Type*} [Semiring R] (f g h : ℕ → R) :
    cvs f (cvs g h) = cvs (cvs f g) h := (cvs_assoc f g h).symm

/-! ## Geometric sequences and the local factor -/

/-- The geometric sequence `n ↦ r^n`. -/
def geoSeq (r : ℝ) : ℕ → ℝ := fun n => r^n

/-- The constant-one sequence. -/
def oneSeq : ℕ → ℝ := fun _ => 1

/-! ## Properties of `S` -/

lemma S_succ (x : ℝ) (m : ℕ) : S x (m+1) = S x m + x^(m+1) := by
  rw [S, S, Finset.sum_range_succ]

lemma S_nonneg (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (n : ℕ) : 0 ≤ S x n := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hden : 0 < 1 - x := by linarith
    have hxle : x^(n+1) ≤ 1 :=
      calc x^(n+1) ≤ |x^(n+1)| := le_abs_self _
        _ = |x|^(n+1) := abs_pow x (n+1)
        _ ≤ 1 := pow_le_one₀ (abs_nonneg x) (abs_le.mpr ⟨h1,h2⟩)
    have hkey : S x n = (1 - x^(n+1))/(1-x) := by
      rw [eq_div_iff (ne_of_gt hden)]
      have := geom_sum_mul_neg x (n+1)
      simpa [S] using this
    rw [hkey]; exact div_nonneg (by linarith) hden.le
  · subst heq; rw [S]; simp; positivity

lemma S_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ S x n :=
  Finset.sum_nonneg (fun t _ => pow_nonneg hx t)

lemma S_sub_mul (x : ℝ) (n : ℕ) (hn : 2 ≤ n) : S x n - x * S x (n-2) = 1 + x^n := by
  have e : n - 2 + 1 = n - 1 := by omega
  have f : n - 1 + 1 = n := by omega
  have h1 : S x n = (∑ t ∈ Finset.range n, x^(t+1)) + 1 := by
    rw [S]; exact Finset.sum_range_succ' (fun t => x^t) n
  have h2 : S x (n-2) = ∑ t ∈ Finset.range (n-1), x^t := by rw [S, e]
  have h3 : x * (∑ t ∈ Finset.range (n-1), x^t) = ∑ t ∈ Finset.range (n-1), x^(t+1) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; rw [pow_succ]; ring
  have h4 : (∑ t ∈ Finset.range n, x^(t+1)) = (∑ t ∈ Finset.range (n-1), x^(t+1)) + x^n := by
    have e2 : n = (n-1)+1 := by omega
    rw [e2, Finset.sum_range_succ, f]
  rw [h1, h2, h3, h4]; ring

lemma S_shift (x : ℝ) (n : ℕ) (hn : 2 ≤ n) : S x n + x * S x (n-2) = (1+x) * S x (n-1) := by
  have h1 : S x n = S x (n-1) + x^n := by
    have := S_succ x (n-1); rwa [show n - 1 + 1 = n by omega] at this
  have h2 : S x (n-1) = S x (n-2) + x^(n-1) := by
    have := S_succ x (n-2); rwa [show n - 2 + 1 = n - 1 by omega] at this
  have h3 : x^n = x^(n-1) * x := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  rw [h1, h2, h3]; ring

/-! ## Positive alternating sums -/

lemma altSum_range_two (Q : ℕ → ℝ) (j : ℕ) :
    (∑ m ∈ Finset.range (2*j), (-1:ℝ)^m * Q m) = ∑ i ∈ Finset.range j, (Q (2*i) - Q (2*i+1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2*(j+1) = 2*j + 2 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
    have e1 : (-1:ℝ)^(2*j) = 1 := Even.neg_one_pow ⟨j, by ring⟩
    have e2 : (-1:ℝ)^(2*j+1) = -1 := by
      rw [show 2*j+1 = 2*j + 1 by ring, pow_succ, e1]; norm_num
    rw [e1, e2]; ring

lemma altSum_nonneg (Q : ℕ → ℝ) (hanti : ∀ m, Q (m+1) ≤ Q m) (hnn : ∀ m, 0 ≤ Q m) (M : ℕ) :
    0 ≤ ∑ m ∈ Finset.range M, (-1:ℝ)^m * Q m := by
  have h1 : ∀ j, 0 ≤ ∑ m ∈ Finset.range (2*j), (-1:ℝ)^m * Q m := by
    intro j; rw [altSum_range_two]
    exact Finset.sum_nonneg (fun i _ => by linarith [hanti (2*i)])
  have h2 : ∀ j, 0 ≤ ∑ m ∈ Finset.range (2*j+1), (-1:ℝ)^m * Q m := by
    intro j
    have hs : ∑ m ∈ Finset.range (2*j+1), (-1:ℝ)^m * Q m
        = (∑ m ∈ Finset.range (2*j), (-1:ℝ)^m * Q m) + Q (2*j) := by
      rw [show 2*j+1 = 2*j + 1 by ring, Finset.sum_range_succ]
      have e1 : (-1:ℝ)^(2*j) = 1 := Even.neg_one_pow ⟨j, by ring⟩
      rw [e1, one_mul]
    rw [hs]; linarith [h1 j, hnn (2*j)]
  have hM : 2*(M/2) + M%2 = M := Nat.div_add_mod M 2
  rcases (by omega : M%2 = 0 ∨ M%2 = 1) with h | h
  · rw [← hM, h, Nat.add_zero]; exact h1 (M/2)
  · rw [← hM, h]; exact h2 (M/2)

lemma altSum_nonneg_range (Q : ℕ → ℝ) (M : ℕ)
    (hanti : ∀ m, m+1 < M → Q (m+1) ≤ Q m) (hnn : ∀ m, m < M → 0 ≤ Q m) :
    0 ≤ ∑ m ∈ Finset.range M, (-1:ℝ)^m * Q m := by
  set Q' : ℕ → ℝ := fun m => if m < M then Q m else 0 with hQ'
  have hsum : ∑ m ∈ Finset.range M, (-1:ℝ)^m * Q m = ∑ m ∈ Finset.range M, (-1:ℝ)^m * Q' m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [hQ', if_pos hm]
  rw [hsum]
  apply altSum_nonneg Q'
  · intro m
    by_cases hm : m + 1 < M
    · rw [hQ']; simp only [if_pos hm]
      by_cases hm2 : m < M
      · rw [if_pos hm2]; exact hanti m hm
      · exact absurd hm (by omega)
    · rw [hQ']; simp only [if_neg hm]
      by_cases hm2 : m < M
      · rw [if_pos hm2]; exact hnn m hm2
      · rw [if_neg hm2]
  · intro m
    by_cases hm : m < M
    · rw [hQ']; simp only [if_pos hm]; exact hnn m hm
    · rw [hQ']; simp only [if_neg hm]; exact le_refl 0

/-! ## Non-negativity of `Gab` -/

lemma Gab_symm (a b : ℝ) : Gab a b = Gab b a := by
  funext k; simp only [Gab]; apply Finset.sum_congr rfl; intro m _; ring

lemma Gab_nonneg_mixed (a b : ℝ) (ha0 : 0 ≤ a) (hb1 : -1 ≤ b) (hb0 : b < 0) (k : ℕ) :
    0 ≤ Gab a b k := by
  have hb2 : b ≤ 1 := by linarith
  rw [Gab]
  set c : ℝ := a * (-b) with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg ha0 (by linarith)
  have hgoal : (∑ m ∈ Finset.range (k/2+1), (a*b)^m * S a (k-2*m) * S b (k-2*m))
      = ∑ m ∈ Finset.range (k/2+1), (-1:ℝ)^m * (c^m * S a (k-2*m) * S b (k-2*m)) := by
    apply Finset.sum_congr rfl
    intro m _
    have hab : a*b = -(c) := by rw [hc]; ring
    rw [hab, neg_pow]; ring
  rw [hgoal]
  apply altSum_nonneg_range (fun m => c^m * S a (k-2*m) * S b (k-2*m)) (k/2+1)
  · intro m hm
    have hn : 2 ≤ k - 2*m := by omega
    have hA : 0 ≤ S a (k-2*m) - a * S a (k-2*m-2) := by
      rw [S_sub_mul a (k-2*m) hn]; positivity
    have hB : 0 ≤ S b (k-2*m) - (-b) * S b (k-2*m-2) := by
      rw [show S b (k-2*m) - (-b) * S b (k-2*m-2) = S b (k-2*m) + b * S b (k-2*m-2) by ring,
          S_shift b (k-2*m) hn]
      exact mul_nonneg (by linarith) (S_nonneg b hb1 hb2 _)
    have hSB : 0 ≤ S b (k-2*m) := S_nonneg b hb1 hb2 _
    have hAa : 0 ≤ a * S a (k-2*m-2) := mul_nonneg ha0 (S_nonneg_of_nonneg ha0 _)
    have heq : k - 2*(m+1) = k - 2*m - 2 := by omega
    have hgoal2 : c^m * S a (k-2*m) * S b (k-2*m) - c^(m+1) * S a (k-2*(m+1)) * S b (k-2*(m+1))
        = c^m * (((S a (k-2*m) - a * S a (k-2*m-2)) * S b (k-2*m))
            + (a * S a (k-2*m-2)) * (S b (k-2*m) - (-b) * S b (k-2*m-2))) := by
      rw [heq, pow_succ]; ring
    have : 0 ≤ c^m * S a (k-2*m) * S b (k-2*m) - c^(m+1) * S a (k-2*(m+1)) * S b (k-2*(m+1)) := by
      rw [hgoal2]
      exact mul_nonneg (pow_nonneg hc0 m) (add_nonneg (mul_nonneg hA hSB) (mul_nonneg hAa hB))
    linarith
  · intro m _
    exact mul_nonneg (mul_nonneg (pow_nonneg hc0 m) (S_nonneg_of_nonneg ha0 _)) (S_nonneg b hb1 hb2 _)

theorem Gab_nonneg (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (k : ℕ) : 0 ≤ Gab a b k := by
  have ha1 : -1 ≤ a := (abs_le.mp ha).1
  have ha2 : a ≤ 1 := (abs_le.mp ha).2
  have hb1 : -1 ≤ b := (abs_le.mp hb).1
  have hb2 : b ≤ 1 := (abs_le.mp hb).2
  by_cases ha0 : 0 ≤ a
  · by_cases hb0 : 0 ≤ b
    · rw [Gab]
      exact Finset.sum_nonneg (fun m _ => mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg ha0 hb0) m)
        (S_nonneg_of_nonneg ha0 _)) (S_nonneg_of_nonneg hb0 _))
    · exact Gab_nonneg_mixed a b ha0 hb1 (not_le.mp hb0) k
  · have ha0' : a ≤ 0 := le_of_lt (not_le.mp ha0)
    by_cases hb0 : 0 ≤ b
    · rw [Gab_symm]; exact Gab_nonneg_mixed b a hb0 ha1 (not_le.mp ha0) k
    · have hb0' : b ≤ 0 := le_of_lt (not_le.mp hb0)
      rw [Gab]
      exact Finset.sum_nonneg (fun m _ => mul_nonneg (mul_nonneg
        (pow_nonneg (mul_nonneg_of_nonpos_of_nonpos ha0' hb0') m)
        (S_nonneg a ha1 ha2 _)) (S_nonneg b hb1 hb2 _))

end

end Work.FIArea5.S16Hecke
