import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth

open Complex Filter Set
open scoped Topology BigOperators
noncomputable section
namespace Commons.NumberTheory.Zeta

/-- For `x ≥ 1` and `a ≥ 0`, `x ^ (-a) ≤ 1`. -/
private lemma rpow_neg_le_one_of_one_le {x : ℝ} (hx : 1 ≤ x) {a : ℝ} (ha : 0 ≤ a) :
    x ^ (-a) ≤ 1 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hxa : 1 ≤ x ^ a := Real.one_le_rpow hx ha
  have hpos : 0 < x ^ a := lt_of_lt_of_le zero_lt_one hxa
  calc
    x ^ (-a) = (x ^ a)⁻¹ := by rw [Real.rpow_neg hx0]
    _ ≤ 1 := (inv_le_one₀ hpos).2 hxa

private lemma norm_nat_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(((n : ℕ) : ℂ) ^ (-s))‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s)]
  rw [Complex.neg_re]

private lemma norm_head_le (N : ℕ) (s : ℂ) :
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
  calc
    ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-s.re) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact norm_nat_cpow_neg hn1 s

private lemma norm_add_mul_I_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ σ + |t| := by
  calc
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖(Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
        rw [norm_mul, Complex.norm_I]
        rw [Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [h1, h2]
      rw [abs_of_nonneg hσ0]

private lemma norm_nat_cpow_one_sub (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = ((N : ℕ) : ℝ) ^ (1 - s.re) := by
  have hN0 : 0 < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcast : ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0 (1 - s)]
  simp

/-- The exact norm of the Euler–Maclaurin pole term. -/
private lemma pole_norm_eq (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ =
      ((N : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
  rw [norm_div]
  rw [norm_nat_cpow_one_sub N hN s]

/-- Norm of the Euler–Maclaurin tail series. -/
private lemma em_tail_norm_le (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ ≤
      (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := by
  have htel := emTerm_tsum_le N hN s hs0 hs1
  have hnormS : Summable (fun m : ℕ =>
      ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖) := by
    exact htel.1.norm
  calc
    ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
        ≤ ∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_tsum_le_tsum_norm hnormS
    _ ≤ (‖s‖ / s.re) * (((N : ℕ) : ℝ) ^ (-s.re)) := htel.2

/-- For `s` in the box `1/2 ≤ re s`, `re s ≤ 2`, `|im s| ≤ 2` away from the pole at `s = 1`,
the zeta function is bounded by a constant times `(1 + 1/‖s - 1‖)`.  The Euler–Maclaurin
decomposition at `N = 5` keeps the pole term explicit and bounds everything else by a constant. -/
theorem zeta_strip_smallIm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      |t| ≤ 2 → ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (1 + 1 / δ) * (1 + 1 / ‖((σ : ℂ) + Complex.I * (t : ℂ)) - 1‖) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro δ σ t hδ0 hδ1 hσlo hσhi ht hs1
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let w : ℝ := ‖s - 1‖
  let H : ℂ := ∑ n ∈ Finset.Icc 1 5, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ := ((((5 : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
  let Tail : ℂ := ∑' m : ℕ,
        ((((5 + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((5 + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((5 + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))
  let A0 : ℝ := ∑ n ∈ Finset.Icc 1 5, ((n : ℕ) : ℝ) ^ (-σ)
  let P : ℝ := ((5 : ℕ) : ℝ) ^ (1 - σ)
  have hsre : s.re = σ := by simp [s]
  have hσpos : 0 < σ := by linarith
  have hσ0 : 0 ≤ σ := le_of_lt hσpos
  have hs0 : 0 < s.re := by rw [hsre]; exact hσpos
  have hsne : s ≠ 1 := by simpa [s] using hs1
  have hwpos : 0 < w := by
    dsimp [w]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hsne)
  have hσge : (1 / 2 : ℝ) ≤ σ := by linarith
  -- identity ζ = H + M + Tail
  have hid : riemannZeta s = H + M + Tail := by
    have h := zeta_eq_emN (s := s) hs0 hsne 5 (by norm_num : 1 ≤ (5 : ℕ))
    simpa [H, M, Tail] using h
  -- head
  have hHead : ‖H‖ ≤ A0 := by
    have h := norm_head_le 5 s
    dsimp [H, A0]
    rwa [hsre] at h
  -- pole term: exact norm
  have hPole : ‖M‖ = P / w := by
    calc
      ‖M‖ = ‖((((5 : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ := by rfl
      _ = ((5 : ℕ) : ℝ) ^ (1 - σ) / ‖s - 1‖ := by
        rw [pole_norm_eq s 5 (by norm_num : 1 ≤ (5 : ℕ))]
        rw [hsre]
      _ = P / w := by rfl
  -- tail
  have hTail1 : ‖Tail‖ ≤ (‖s‖ / σ) * ((5 : ℕ) : ℝ) ^ (-σ) := by
    have h := em_tail_norm_le s hs0 hsne 5 (by norm_num : 1 ≤ (5 : ℕ))
    dsimp [Tail]
    rwa [hsre] at h
  have hnorm : ‖s‖ ≤ σ + 2 := by
    have h1 : ‖s‖ ≤ σ + |t| := by
      simpa [s] using (norm_add_mul_I_le σ t hσ0)
    linarith
  have hratio : ‖s‖ / σ ≤ 5 := by
    rw [div_le_iff₀ hσpos]
    linarith
  have hpow5 : (5 : ℝ) ^ (-σ) ≤ 1 := by
    exact rpow_neg_le_one_of_one_le (by norm_num : (1 : ℝ) ≤ (5 : ℝ)) (le_of_lt hσpos)
  have hTailA : ‖Tail‖ ≤ 5 * ((5 : ℝ) ^ (-σ)) := by
    have h0 : 0 ≤ (5 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (-σ)
    calc
      ‖Tail‖ ≤ (‖s‖ / σ) * ((5 : ℕ) : ℝ) ^ (-σ) := by
        simpa using hTail1
      _ ≤ 5 * ((5 : ℝ) ^ (-σ)) := mul_le_mul_of_nonneg_right hratio h0
  have hTailB : 5 * ((5 : ℝ) ^ (-σ)) ≤ 5 := by
    have h := mul_le_mul_of_nonneg_left hpow5 (by norm_num : (0 : ℝ) ≤ 5)
    simpa using h
  have hTail : ‖Tail‖ ≤ 5 := le_trans hTailA hTailB
  -- head bound by 5
  have hA05 : A0 ≤ 5 := by
    dsimp [A0]
    have hle : ∀ n ∈ Finset.Icc 1 (5 : ℕ), ((n : ℕ) : ℝ) ^ (-σ) ≤ (1 : ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      exact rpow_neg_le_one_of_one_le hn1R (le_of_lt hσpos)
    calc
      (∑ n ∈ Finset.Icc 1 (5 : ℕ), ((n : ℕ) : ℝ) ^ (-σ))
          ≤ ∑ n ∈ Finset.Icc 1 (5 : ℕ), (1 : ℝ) := Finset.sum_le_sum hle
      _ = 5 := by
        rw [Finset.sum_const]
        norm_num
  -- pole norm bound: P ≤ 5
  have hP5 : P ≤ 5 := by
    dsimp [P]
    calc
      ((5 : ℕ) : ℝ) ^ (1 - σ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (5 : ℝ)) (by linarith)
      _ = 5 := by rw [Real.rpow_one]
  have hPw : P / w ≤ 5 / w := div_le_div_of_nonneg_right hP5 (le_of_lt hwpos)
  -- triangle inequality assembly
  have htri : ‖riemannZeta s‖ ≤ A0 + P / w + 5 := by
    calc
      ‖riemannZeta s‖ = ‖H + M + Tail‖ := by rw [hid]
      _ ≤ ‖H‖ + ‖M‖ + ‖Tail‖ := by
        have h1 : ‖H + M + Tail‖ ≤ ‖H + M‖ + ‖Tail‖ := norm_add_le (H + M) Tail
        have h2 : ‖H + M‖ ≤ ‖H‖ + ‖M‖ := norm_add_le H M
        linarith
      _ ≤ A0 + P / w + 5 := by
        have hMle : ‖M‖ ≤ P / w := le_of_eq hPole
        have hsum1 : ‖H‖ + ‖M‖ ≤ A0 + P / w := add_le_add hHead hMle
        exact add_le_add hsum1 hTail
  have htri2 : ‖riemannZeta s‖ ≤ (10 : ℝ) + 5 / w := by
    calc
      ‖riemannZeta s‖ ≤ A0 + P / w + 5 := htri
      _ ≤ 5 + 5 / w + 5 := by
        have hsum1 : A0 + P / w ≤ 5 + 5 / w := add_le_add hA05 hPw
        exact add_le_add hsum1 (le_refl (5 : ℝ))
      _ = 10 + 5 / w := by ring
  -- factor in the strip parameters
  let X : ℝ := (1 + 1 / δ) * (1 + 1 / w)
  have hX1 : (1 : ℝ) ≤ X := by
    have hd1 : (1 : ℝ) ≤ 1 + 1 / δ := by
      have h : 0 ≤ 1 / δ := by positivity
      linarith
    have hw1 : (1 : ℝ) ≤ 1 + 1 / w := by
      have h : 0 ≤ 1 / w := by positivity
      linarith
    exact one_le_mul_of_one_le_of_one_le hd1 hw1
  have hXw : (1 : ℝ) / w ≤ X := by
    have hd1 : (1 : ℝ) ≤ 1 + 1 / δ := by
      have h : 0 ≤ 1 / δ := by positivity
      linarith
    have h10 : (0 : ℝ) ≤ 1 + 1 / w := by positivity
    have hmul : (1 + 1 / w) ≤ (1 + 1 / δ) * (1 + 1 / w) := by
      simpa using (mul_le_mul_of_nonneg_right hd1 h10)
    calc
      (1 : ℝ) / w ≤ 1 + 1 / w := by linarith
      _ ≤ (1 + 1 / δ) * (1 + 1 / w) := hmul
  have h10 : (10 : ℝ) ≤ 10 * X := by
    simpa using (mul_le_mul_of_nonneg_left hX1 (by norm_num : (0 : ℝ) ≤ 10))
  have h5w : (5 : ℝ) / w ≤ 5 * X := by
    calc
      (5 : ℝ) / w = 5 * ((1 : ℝ) / w) := by ring
      _ ≤ 5 * X := mul_le_mul_of_nonneg_left hXw (by norm_num : (0 : ℝ) ≤ 5)
  have h15 : (10 : ℝ) + 5 / w ≤ 15 * X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hbig : 15 * X ≤ 1000000 * X := by
    exact mul_le_mul_of_nonneg_right (by norm_num : (15 : ℝ) ≤ 1000000) hX0
  have hfin : ‖riemannZeta s‖ ≤ 1000000 * X := le_trans (le_trans htri2 h15) hbig
  calc
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ = ‖riemannZeta s‖ := by simp [s]
    _ ≤ 1000000 * X := hfin
    _ = 1000000 * (1 + 1 / δ) * (1 + 1 / w) := by
      simp [X]
      ring
    _ = 1000000 * (1 + 1 / δ) * (1 + 1 / ‖((σ : ℂ) + Complex.I * (t : ℂ)) - 1‖) := by
      have hw : ‖((σ : ℂ) + Complex.I * (t : ℂ)) - 1‖ = w := by simp [w, s]
      rw [← hw]

end Commons.NumberTheory.Zeta
