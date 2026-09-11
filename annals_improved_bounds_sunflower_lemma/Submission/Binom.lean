import Mathlib

/-!
# Binomial lower tail (Chernoff-type)

`P(Bin(N,q) ≤ N q / 2) ≤ e^{-N q / 8}` for `0 < q ≤ 1`, expressed as a weighted
sum over binary words of length `N` (bit-success probability `q`).
-/
open scoped BigOperators
open Finset

namespace Submission.Binom

/-- binary words of length N -/
abbrev Words (N : ℕ) := Fin N → Bool

/-- weight of a word -/
def wt {N : ℕ} (x : Words N) : ℕ := (Finset.univ.filter (fun i : Fin N => x i)).card

/-- `wt x` equals the sum over coordinates of the coordinate indicators -/
lemma wt_eq (N : ℕ) (x : Words N) : wt x = ∑ i : Fin N, (if x i then 1 else 0) := by
  unfold wt
  rw [Finset.card_filter]

/-- complement indicator sum at a coordinate is one -/
lemma one_eq_alpha_beta {N : ℕ} (x : Words N) (i : Fin N) :
    (if x i then 1 else 0) + (if x i then 0 else 1) = 1 := by
  by_cases xi : x i <;> simp [xi]

/-- the number of zero coordinates of a word is `N - wt x` -/
lemma wt_sub (N : ℕ) (x : Words N) : N - wt x = ∑ i : Fin N, (if x i then 0 else 1) := by
  have hwt : wt x = ∑ i : Fin N, (if x i then 1 else 0) := wt_eq N x
  have hsplit : (∑ i : Fin N, ((if x i then 1 else 0) + (if x i then 0 else 1))) = ∑ i : Fin N, (1 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact one_eq_alpha_beta x i
  have hβsum : (∑ i : Fin N, (if x i then 1 else 0)) + (∑ i : Fin N, (if x i then 0 else 1)) = N := by
    rw [← Finset.sum_add_distrib]
    rw [hsplit]
    simp
  rw [hwt]
  omega

/-- a monomial in `wt x` and `N - wt x` factors over the coordinates of the word -/
lemma weight_prod (N : ℕ) (x : Words N) (u v : ℝ) :
    u ^ (wt x) * v ^ (N - wt x) = ∏ i : Fin N, (if x i then u else v) := by
  rw [wt_sub N x, wt_eq N x]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i hi
  by_cases xi : x i
  · simp [xi]
  · simp [xi]

/-- sum over all binary words of a coordinate-wise product equals `(u+v)^n` -/
lemma sum_word_prod (n : ℕ) (u v : ℝ) :
    (∑ x : Words n, ∏ i : Fin n, (if x i then u else v)) = (u + v) ^ n := by
  induction n with
  | zero => simp [Words]
  | succ n ih =>
      calc
        (∑ x : Words (n+1), ∏ i : Fin (n+1), (if x i then u else v))
            = ∑ x : Words (n+1), (if x 0 then u else v) * (∏ i : Fin n, (if x i.succ then u else v)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Fin.prod_univ_succ]
        _ = ∑ b : Bool, ∑ y : Words n, (if b then u else v) * (∏ i : Fin n, (if y i then u else v)) := by
              let e : (Bool × Words n) ≃ Words (n+1) := Fin.consEquiv (fun _ : Fin (n+1) => Bool)
              calc
                (∑ x : Words (n+1), (if x 0 then u else v) * (∏ i : Fin n, (if x i.succ then u else v)))
                    = ∑ z : Bool × Words n, (if z.1 then u else v) * (∏ i : Fin n, (if z.2 i then u else v)) := by
                      rw [← Equiv.sum_comp e]
                      refine Finset.sum_congr rfl ?_
                      intro z hz
                      simp [e]
                _ = ∑ b : Bool, ∑ y : Words n, (if b then u else v) * (∏ i : Fin n, (if y i then u else v)) := by
                      rw [Fintype.sum_prod_type]
        _ = (u + v) * (∑ y : Words n, ∏ i : Fin n, (if y i then u else v)) := by
              calc
                (∑ b : Bool, ∑ y : Words n, (if b then u else v) * (∏ i : Fin n, (if y i then u else v)))
                    = (∑ b : Bool, (if b then u else v)) * (∑ y : Words n, ∏ i : Fin n, (if y i then u else v)) := by
                      rw [Finset.sum_mul]
                      refine Finset.sum_congr rfl ?_
                      intro b hb
                      rw [Finset.mul_sum]
                _ = (u + v) * (∑ y : Words n, ∏ i : Fin n, (if y i then u else v)) := by
                      congr 1
                      rw [Fintype.sum_bool]
                      simp
        _ = (u + v) ^ (n+1) := by
              rw [ih, pow_succ']

/-- sum over all binary words of length `n` of `u^wt * v^(n-wt)` equals `(u+v)^n` -/
lemma sum_weight_all (n : ℕ) (u v : ℝ) :
    (∑ x : Words n, u ^ (wt x) * v ^ (n - wt x)) = (u + v) ^ n := by
  rw [← sum_word_prod n u v]
  refine Finset.sum_congr rfl ?_
  intro x hx
  exact weight_prod n x u v

/-- weighted probability that the number of 1s is at most `m` (real) -/
noncomputable def binomLe (N : ℕ) (q : ℝ) (m : ℕ) : ℝ :=
  ∑ x : Words N, if wt x ≤ m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0

/-- set of positions where a word has a one -/
def supp {N : ℕ} (x : Words N) : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => x i)

/-- characteristic function of a set of positions -/
def char {N : ℕ} (s : Finset (Fin N)) : Words N := fun i => i ∈ s

lemma wt_char {N : ℕ} (s : Finset (Fin N)) : wt (char s) = s.card := by
  simp [wt, char]

lemma char_supp {N : ℕ} (x : Words N) : char (supp x) = x := by
  funext i
  simp [char, supp]

lemma supp_char {N : ℕ} (s : Finset (Fin N)) : supp (char s) = s := by
  ext i
  simp [char, supp]

/-- binary words of length `N` correspond bijectively to subsets of `Fin N` -/
noncomputable def wordsEquiv (N : ℕ) : Words N ≃ Finset (Fin N) where
  toFun := supp
  invFun := char
  left_inv := char_supp
  right_inv := supp_char

/-- the number of words of length `N` with exactly `w` ones is `N.choose w` -/
lemma card_words_weight (N w : ℕ) :
    (Finset.univ.filter (fun x : Words N => wt x = w)).card = N.choose w := by
  rw [Finset.card_filter]
  calc
    (∑ x : Words N, (if wt x = w then 1 else 0 : ℕ)) = ∑ s : Finset (Fin N), (if s.card = w then 1 else 0 : ℕ) := by
      rw [← Equiv.sum_comp (wordsEquiv N)]
      refine Finset.sum_congr rfl ?_
      intro x hx
      change (if wt x = w then 1 else 0) = if (supp x).card = w then 1 else 0
      by_cases hxw : wt x = w
      · have hxw' : (supp x).card = w := by simpa [supp, wt] using hxw
        simp [hxw, hxw']
      · have hxw' : ¬ (supp x).card = w := by simpa [supp, wt] using hxw
        simp [hxw, hxw']
    _ = (Finset.univ.filter (fun s : Finset (Fin N) => s.card = w)).card := by
      rw [Finset.card_filter]
    _ = N.choose w := by
      have hps : (Finset.univ.filter (fun s : Finset (Fin N) => s.card = w)) =
                 (Finset.univ : Finset (Fin N)).powersetCard w := by
        ext s
        simp [Finset.powersetCard]
      rw [hps]
      have hcard : (Finset.univ : Finset (Fin N)).card = N := by
        simp
      rw [Finset.card_powersetCard]
      rw [hcard]

/-- weighted probability of exactly `w` ones equals `C(N,w) q^w (1-q)^{N-w}` -/
lemma binomEq_eq_choose (N w : ℕ) (q : ℝ) :
    (∑ x : Words N, if wt x = w then q ^ w * (1 - q) ^ (N - w) else 0) =
      (N.choose w : ℝ) * q ^ w * (1 - q) ^ (N - w) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  have hcard : (Finset.univ.filter (fun x : Words N => wt x = w)).card = N.choose w := card_words_weight N w
  rw [hcard]
  ring

/-- per-word bound: `q^w(1-q)^{N-w} ≤ e^{θNq/2}(qe^{-θ})^w(1-q)^{N-w}` when `w ≤ Nq/2` -/
lemma word_term_le (N : ℕ) (q θ : ℝ) {x : Words N}
    (hq0 : 0 ≤ q) (h1 : q ≤ 1) (hθ : 0 ≤ θ)
    (hw : (wt x : ℝ) ≤ (N : ℝ) * q / 2) :
    q ^ (wt x) * (1 - q) ^ (N - wt x) ≤
      Real.exp (θ * ((N : ℝ) * q / 2)) * (q * Real.exp (-θ)) ^ (wt x) * (1 - q) ^ (N - wt x) := by
  let w := wt x
  let B := (1 - q) ^ (N - w)
  have hB0 : 0 ≤ B := pow_nonneg (by linarith : 0 ≤ 1 - q) (N - w)
  have hq0' : 0 ≤ q ^ w := pow_nonneg hq0 w
  have hfac : 1 ≤ Real.exp (θ * (((N : ℝ) * q / 2) - (w : ℝ))) := by
    exact Real.one_le_exp (mul_nonneg hθ (sub_nonneg.mpr hw))
  have hmain : q ^ w * B ≤ q ^ w * B * Real.exp (θ * (((N : ℝ) * q / 2) - (w : ℝ))) := by
    calc
      q ^ w * B ≤ q ^ w * B * 1 := by rw [mul_one]
      _ ≤ q ^ w * B * Real.exp (θ * (((N : ℝ) * q / 2) - (w : ℝ))) :=
            mul_le_mul_of_nonneg_left hfac (mul_nonneg hq0' hB0)
  calc
    q ^ (wt x) * (1 - q) ^ (N - wt x) = q ^ w * B := by rfl
    _ ≤ q ^ w * B * Real.exp (θ * (((N : ℝ) * q / 2) - (w : ℝ))) := hmain
    _ = Real.exp (θ * ((N : ℝ) * q / 2)) * (q * Real.exp (-θ)) ^ (wt x) * (1 - q) ^ (N - wt x) := by
      calc
        q ^ w * B * Real.exp (θ * (((N : ℝ) * q / 2) - (w : ℝ)))
            = q ^ w * B * (Real.exp (θ * ((N : ℝ) * q / 2)) * Real.exp ((w : ℝ) * (-θ))) := by
              rw [show θ * (((N : ℝ) * q / 2) - (w : ℝ)) = θ * ((N : ℝ) * q / 2) + (w : ℝ) * (-θ) by ring]
              rw [Real.exp_add]
        _ = Real.exp (θ * ((N : ℝ) * q / 2)) * (q * Real.exp (-θ)) ^ (wt x) * (1 - q) ^ (N - wt x) := by
              rw [mul_pow]
              rw [← Real.exp_nat_mul (-θ) w]
              ring

/-- `log 2 ≤ 3/4` -/
lemma log_two_le_three_four : Real.log 2 ≤ 3 / 4 := by
  have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h' : (0.6931471808 : ℝ) ≤ 3 / 4 := by norm_num1
  exact le_trans (le_of_lt h) h' 

/-- per-unit logarithm bound: `q ln2/2 + log(1-q/2) ≤ -q/8` for `0 < q ≤ 1` -/
lemma log_perunit (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Real.log 2 * (q / 2) + Real.log (1 - q / 2) ≤ -q / 8 := by
  have hlog1 : Real.log (1 - q / 2) ≤ -(q / 2) := by
    have hpos2 : 0 < 1 - q / 2 := by nlinarith
    have h := Real.log_le_sub_one_of_pos hpos2
    linarith
  calc
    Real.log 2 * (q / 2) + Real.log (1 - q / 2) ≤ Real.log 2 * (q / 2) - q / 2 := by linarith
    _ = q / 2 * (Real.log 2 - 1) := by ring
    _ ≤ q / 2 * (-(1 / 4)) := by
        exact mul_le_mul_of_nonneg_left (by linarith [log_two_le_three_four] : Real.log 2 - 1 ≤ -(1 / 4))
          (le_of_lt (by nlinarith : 0 < q / 2))
    _ = -q / 8 := by ring

/-- per-unit bound: `e^{q ln2 / 2} (1 - q/2) ≤ e^{-q/8}` for `0 < q ≤ 1` -/
lemma exp_perunit (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2) ≤ Real.exp (-q / 8) := by
  have hpos : 0 < Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2) := by
    exact mul_pos (Real.exp_pos _) (by nlinarith : 0 < 1 - q / 2)
  rw [← Real.exp_log hpos]
  rw [Real.exp_le_exp]
  have hb : (1 - q / 2) ≠ 0 := ne_of_gt (by nlinarith : 0 < 1 - q / 2)
  rw [Real.log_mul (Real.exp_pos _).ne' hb]
  rw [Real.log_exp]
  exact log_perunit q hq0 hq1

/-- the exponential half: `e^{-ln 2} = 1/2` -/
lemma exp_neg_log_two : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- P(Bin(N,q) ≤ Nq/2) ≤ exp(-Nq/8), integer-threshold version -/
theorem binomial_lower_tail {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {m : ℕ} (hm : (m : ℝ) ≤ (N : ℝ) * q / 2) :
    binomLe N q m ≤ Real.exp (-((N : ℝ) * q) / 8) := by
  let A : Finset (Words N) := Finset.univ.filter (fun x : Words N => wt x ≤ m)
  have hxwt {x : Words N} (hx : x ∈ A) : (wt x : ℝ) ≤ (N : ℝ) * q / 2 := by
    exact le_trans (by exact_mod_cast (Finset.mem_filter.mp hx).2) hm
  have hbinom : binomLe N q m = ∑ x ∈ A, q ^ (wt x) * (1 - q) ^ (N - wt x) := by
    unfold binomLe
    rw [← Finset.sum_filter]
  have hterm : (∑ x ∈ A, q ^ (wt x) * (1 - q) ^ (N - wt x)) ≤
      ∑ x ∈ A, Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
        (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact word_term_le N q (Real.log 2) (x := x) (le_of_lt hq0) hq1
      ((Real.log_nonneg_iff (by norm_num : (0 : ℝ) < 2)).2 (by norm_num : (1 : ℝ) ≤ 2)) (hxwt hx)
  have hext : (∑ x ∈ A, Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
        (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x))
      = Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
          (∑ x ∈ A, (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) := by
    rw [show (∑ x ∈ A, Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
          (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) =
        (∑ x ∈ A, Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
          ((q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x))) by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [mul_assoc]]
    rw [← Finset.mul_sum (s := A) (a := Real.exp (Real.log 2 * ((N : ℝ) * q / 2)))
          (f := fun x : Words N => (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x))]
  have hdrop : (∑ x ∈ A, (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) ≤
      (∑ x : Words N, (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hx hnx
      exact mul_nonneg (pow_nonneg (mul_nonneg (le_of_lt hq0) (Real.exp_pos _).le) (wt x))
        (pow_nonneg (by linarith : 0 ≤ 1 - q) (N - wt x))
  have hbound : binomLe N q m ≤ Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) * (1 - q / 2) ^ N := by
    calc
      binomLe N q m = ∑ x ∈ A, q ^ (wt x) * (1 - q) ^ (N - wt x) := hbinom
      _ ≤ ∑ x ∈ A, Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
            (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x) := hterm
      _ = Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
            (∑ x ∈ A, (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) := hext
      _ ≤ Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) *
            (∑ x : Words N, (q * Real.exp (-Real.log 2)) ^ (wt x) * (1 - q) ^ (N - wt x)) := by
            exact mul_le_mul_of_nonneg_left hdrop (Real.exp_pos _).le
      _ = Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) * (q * Real.exp (-Real.log 2) + (1 - q)) ^ N := by
            rw [sum_weight_all N (q * Real.exp (-Real.log 2)) (1 - q)]
      _ = Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) * (1 - q / 2) ^ N := by
            congr 1
            rw [exp_neg_log_two]
            ring
  have hper : Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2) ≤ Real.exp (-q / 8) := exp_perunit q hq0 hq1
  have hpowle : (Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2)) ^ N ≤ (Real.exp (-q / 8)) ^ N := by
    exact pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (by linarith : 0 ≤ 1 - q / 2)) hper N
  calc
    binomLe N q m ≤ Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) * (1 - q / 2) ^ N := hbound
    _ = (Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2)) ^ N := by
      calc
        Real.exp (Real.log 2 * ((N : ℝ) * q / 2)) * (1 - q / 2) ^ N
            = Real.exp ((N : ℝ) * (Real.log 2 * (q / 2))) * (1 - q / 2) ^ N := by
              congr 1
              ring_nf
        _ = (Real.exp (Real.log 2 * (q / 2))) ^ N * (1 - q / 2) ^ N := by rw [Real.exp_nat_mul]
        _ = (Real.exp (Real.log 2 * (q / 2)) * (1 - q / 2)) ^ N := by rw [mul_pow]
    _ ≤ (Real.exp (-q / 8)) ^ N := hpowle
    _ = Real.exp (-((N : ℝ) * q) / 8) := by
      calc
        (Real.exp (-q / 8)) ^ N = Real.exp ((N : ℝ) * (-q / 8)) := by rw [Real.exp_nat_mul]
        _ = Real.exp (-((N : ℝ) * q) / 8) := by congr 1; ring

/-- the version with the canonical floor threshold -/
theorem binomial_lower_tail_floor {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    binomLe N q (Nat.floor ((N : ℝ) * q / 2)) ≤ Real.exp (-((N : ℝ) * q) / 8) := by
  apply binomial_lower_tail (N := N) (q := q) hq0 hq1
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  exact Nat.floor_le (by nlinarith)

/-- For `ε ∈ (0,1]`, if `Nq ≥ 16 log(2/ε)` then the tail is ≤ ε. -/
lemma binomial_tail_le_eps {N : ℕ} {q ε : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hNq : 16 * Real.log (2 / ε) ≤ (N : ℝ) * q) :
    binomLe N q (Nat.floor ((N : ℝ) * q / 2)) ≤ ε := by
  have hfloor : binomLe N q (Nat.floor ((N : ℝ) * q / 2)) ≤ Real.exp (-((N : ℝ) * q) / 8) :=
    binomial_lower_tail_floor (N := N) (q := q) hq0 hq1
  have hNq8 : 2 * Real.log (2 / ε) ≤ ((N : ℝ) * q) / 8 := by linarith
  have hexp_le : Real.exp (2 * Real.log (2 / ε)) ≤ Real.exp (((N : ℝ) * q) / 8) :=
    (Real.exp_le_exp).2 hNq8
  have hu : 0 < (2 : ℝ) / ε := by positivity
  have hexp2 : Real.exp (2 * Real.log (2 / ε)) = (2 / ε) ^ 2 := by
    rw [show 2 * Real.log (2 / ε) = Real.log (2 / ε) + Real.log (2 / ε) by ring]
    rw [Real.exp_add]
    rw [Real.exp_log hu]
    rw [pow_two]
  have hsq : (1 : ℝ) / ε ≤ (2 / ε) ^ 2 := by
    have hε4 : ε ≤ 4 := by linarith
    calc
      (1 : ℝ) / ε = ε / ε ^ 2 := by field_simp [hε0.ne']
      _ ≤ 4 / ε ^ 2 := by
        field_simp [hε0.ne']
        linarith
      _ = (2 / ε) ^ 2 := by rw [div_pow]; norm_num
  have h1 : (1 : ℝ) / ε ≤ Real.exp (((N : ℝ) * q) / 8) := by
    calc
      (1 : ℝ) / ε ≤ (2 / ε) ^ 2 := hsq
      _ = Real.exp (2 * Real.log (2 / ε)) := hexp2.symm
      _ ≤ Real.exp (((N : ℝ) * q) / 8) := hexp_le
  have hEpos : 0 < Real.exp (((N : ℝ) * q) / 8) := Real.exp_pos _
  have h1e : 0 < (1 : ℝ) / ε := by positivity
  let E : ℝ := Real.exp (((N : ℝ) * q) / 8)
  have hE : E⁻¹ ≤ ε := by
    have hle : E⁻¹ ≤ (1 / ε)⁻¹ := (inv_le_inv₀ hEpos h1e).2 h1
    calc
      E⁻¹ ≤ (1 / ε)⁻¹ := hle
      _ = ε := by field_simp [hε0.ne']
  have hneg : Real.exp (-((N : ℝ) * q) / 8) = E⁻¹ := by
    rw [show -((N : ℝ) * q) / 8 = -(((N : ℝ) * q) / 8) by ring]
    rw [Real.exp_neg]
  have hstep : Real.exp (-((N : ℝ) * q) / 8) ≤ ε := by
    rw [hneg]
    exact hE
  exact le_trans hfloor hstep

end Submission.Binom
