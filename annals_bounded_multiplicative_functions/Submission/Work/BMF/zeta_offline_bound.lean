import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An off-line growth bound for the Riemann zeta function

We prove: there is `A > 0` with
`‖ζ(σ + i t)‖ ≤ A * |t| ^ (4 * (1 - σ) ^ (3 / 2))` for `1/2 ≤ σ ≤ 1`, `|t| ≥ 3` and
`σ ≤ 15/16` or `|t| ≤ 10^100`.

The argument is elementary.  On the "compact" part of the region (`|t| ≤ 10^100`) the
Euler–Maclaurin decomposition at `N = 1` gives an explicit bound.  On `σ ≤ 15/16` the same
decomposition at `N = ⌊|t|⌋₊ + 1`, together with the trivial partial-sum bound
`Σ_{n ≤ N} n^{-σ} ≤ 17 N^{1-σ}`, gives `‖ζ(σ+it)‖ ≤ 40 |t|^{1-σ}`; since `1 - σ ≤ 4 (1-σ)^{3/2}`
for `σ ≤ 15/16` this is at most `40 |t|^{4(1-σ)^{3/2}}`.
-/

set_option maxHeartbeats 1600000

namespace Work.BMF

open Complex

/-- **Euler–Maclaurin bound.**  For `σ > 0`, `|t| ≥ 1`, `N ≥ 1`,
`‖ζ(σ+it)‖ ≤ Σ_{n≤N} n^{-σ} + N^{1-σ}/|t| + (‖σ+it‖/σ) N^{-σ}`. -/
private lemma zeta_emN_bound_aux {σ t : ℝ} (hσ0 : 0 < σ) (ht : 1 ≤ |t|) (N : ℕ) (hN : 1 ≤ N) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
        + (((N : ℕ) : ℝ) ^ (1 - σ)) / |t|
        + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s ≠ 1 := by
    intro h
    have hsi : s.im = 0 := by simpa using congrArg Complex.im h
    have : t = 0 := by simpa [hsim] using hsi
    have habs : |t| = 0 := by rw [this]; simp
    have : (0:ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    linarith
  have hid := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN
  have hH : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
    calc ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_num
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-s), Complex.neg_re, hsre]
  have hM : ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖ ≤ (((N : ℕ) : ℝ) ^ (1 - σ)) / |t| := by
    have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hnum : ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = ((N : ℕ) : ℝ) ^ (1 - σ) := by
      have hcast : ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) := by norm_num
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN0 (1 - s), Complex.sub_re,
        Complex.one_re, hsre]
    have hden : |t| ≤ ‖s - 1‖ := by
      have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = t := by simp [hsim]
      rwa [h2] at h1
    have hpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
    rw [norm_div, hnum]
    exact div_le_div_of_nonneg_left (by positivity) hpos hden
  obtain ⟨hsum, hbd⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN s hs0 hs1
  have hT' : ‖(∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
      ≤ (‖s‖ / s.re) * ((N : ℕ) : ℝ) ^ (-s.re) :=
    le_trans (norm_tsum_le_tsum_norm hsum.norm) (by simpa using hbd)
  rw [hid]
  have htri : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) +
        (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        + ‖((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))‖
        + ‖(∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ := by
    have h1 := norm_add_le ((∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)))
      (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))
    have h2 := norm_add_le (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))
      ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
    linarith
  calc _ ≤ _ := htri
    _ ≤ _ + _ + _ := add_le_add (add_le_add hH hM) hT'
    _ = (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
        + (((N : ℕ) : ℝ) ^ (1 - σ)) / |t|
        + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ) := by
        rw [hs]; simp [hsre]

/-- Partial-sum bound: on `1/2 ≤ σ ≤ 15/16`, `Σ_{n ≤ N} n^{-σ} ≤ 17 N^{1-σ}`. -/
private lemma sum_Icc_rpow_neg_le {σ : ℝ} (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 15 / 16) (N : ℕ)
    (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ 17 * (N : ℝ) ^ (1 - σ) := by
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ < 1 := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc ((1:ℕ):ℝ) ((N:ℕ):ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by
      have h1 : (1:ℝ) ≤ x := by simpa using (Set.mem_Icc.mp hx).1
      linarith
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith : -σ ≤ 0)
  have hcomp : (∑ i ∈ Finset.Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-σ))
      ≤ ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ) := by
    simpa using (AntitoneOn.sum_le_integral_Ico (a := 1) (b := N)
      (f := fun x : ℝ => x ^ (-σ)) hN hanti)
  have hconv : (∑ i ∈ Finset.Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-σ))
      = (∑ n ∈ Finset.Icc 2 N, ((n : ℕ) : ℝ) ^ (-σ)) := by
    refine Finset.sum_bij (s := Finset.Ico 1 N) (t := Finset.Icc 2 N)
      (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' : 1 ≤ i ∧ i < N := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb h; omega
    · intro n hn
      have hn' : 2 ≤ n ∧ n ≤ N := Finset.mem_Icc.mp hn
      exact ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; rfl
  rw [hconv] at hcomp
  have hint : (∫ x in (1:ℝ)..(N:ℝ), x ^ (-σ)) = ((N:ℝ)^(1-σ) - 1) / (1-σ) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -σ)), Real.one_rpow]
    rw [show -σ + 1 = 1 - σ by ring]
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · intro hn
      rcases Nat.eq_or_lt_of_le hn.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h, hn.2⟩
    · intro hn
      rcases hn with h | h
      · subst h; exact ⟨le_refl 1, hN⟩
      · exact ⟨le_trans (by norm_num) h.1, h.2⟩
  have hnot1 : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  have hsplit : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
      = 1 + (∑ n ∈ Finset.Icc 2 N, ((n : ℕ) : ℝ) ^ (-σ)) := by
    rw [hIcc, Finset.sum_insert hnot1]
    norm_num
  have hP1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.one_le_rpow hN1R (by linarith)
  have hinv : ((1 : ℝ) - σ)⁻¹ ≤ 16 := by
    have h16 : (0:ℝ) < 1/16 := by norm_num
    have h := one_div_le_one_div_of_le h16 (by linarith : (1:ℝ)/16 ≤ 1 - σ)
    norm_num at h
    linarith
  have hPsub : 0 ≤ (N:ℝ)^(1-σ) - 1 := by linarith
  have hkey : ((N:ℝ)^(1-σ) - 1) / (1-σ) ≤ 16 * ((N:ℝ)^(1-σ) - 1) := by
    rw [div_eq_mul_inv]
    calc ((N:ℝ)^(1-σ) - 1) * (1 - σ)⁻¹ ≤ ((N:ℝ)^(1-σ) - 1) * 16 :=
          mul_le_mul_of_nonneg_left hinv hPsub
      _ = 16 * ((N:ℝ)^(1-σ) - 1) := by ring
  rw [hsplit]
  linarith

/-- For `x ≥ 1/16`, `x ≤ 4 x^{3/2}`. -/
private lemma le_four_mul_rpow_three_halves {x : ℝ} (hx : 1 / 16 ≤ x) :
    x ≤ 4 * x ^ (3 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hsqrt : (1 / 4 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (le_of_lt hx0)]
    norm_num
    linarith
  have h3 : x ^ (3 / 2 : ℝ) = x * x ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left hsqrt (by positivity : (0:ℝ) ≤ 4 * x)]

/-- Region `σ ≤ 15/16`: polynomial growth `‖ζ(σ+it)‖ ≤ 40 |t|^{1-σ}`. -/
private lemma zeta_region_I {σ t : ℝ} (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 15 / 16) (ht : 3 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 40 * |t| ^ (1 - σ) := by
  have hσ0 : 0 < σ := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have habs0 : 0 ≤ |t| := abs_nonneg t
  have h1σnn : 0 ≤ 1 - σ := by linarith
  have h1σle1 : 1 - σ ≤ 1 := by linarith
  set N : ℕ := ⌊|t|⌋₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNself : (N : ℝ) = ((⌊|t|⌋₊ : ℕ) : ℝ) + 1 := by
    rw [hNdef]; push_cast; ring
  have hNge : |t| ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    linarith [h, hNself]
  have hNle : (N : ℝ) ≤ |t| + 1 := by
    have h := Nat.floor_le habs0
    rw [hNself]; linarith
  have hN2t : (N : ℝ) ≤ 2 * |t| := by linarith
  have hNpos : 0 < (N : ℝ) := by
    have h : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hP : 0 ≤ |t| ^ (1 - σ) := Real.rpow_nonneg habs0 _
  have hmain := zeta_emN_bound_aux hσ0 ht1 N hN1
  have hNpow : (N:ℝ)^(1-σ) ≤ 2 * |t|^(1-σ) := by
    have h1 : (N:ℝ)^(1-σ) ≤ (2*|t|)^(1-σ) := Real.rpow_le_rpow hNnonneg hN2t h1σnn
    have h2 : (2*|t|)^(1-σ) = (2:ℝ)^(1-σ) * |t|^(1-σ) := Real.mul_rpow (by norm_num) habs0
    have h3 : (2:ℝ)^(1-σ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h1σle1
      rwa [Real.rpow_one] at h
    calc (N:ℝ)^(1-σ) ≤ (2*|t|)^(1-σ) := h1
      _ = (2:ℝ)^(1-σ) * |t|^(1-σ) := h2
      _ ≤ 2 * |t|^(1-σ) := mul_le_mul_of_nonneg_right h3 hP
  have hS : (∑ n ∈ Finset.Icc 1 N, ((n:ℕ):ℝ)^(-σ)) ≤ 34 * |t|^(1-σ) := by
    calc _ ≤ 17 * (N:ℝ)^(1-σ) := sum_Icc_rpow_neg_le hσlo hσhi N hN1
      _ ≤ 17 * (2 * |t|^(1-σ)) := mul_le_mul_of_nonneg_left hNpow (by norm_num)
      _ = 34 * |t|^(1-σ) := by ring
  have hT2 : (((N:ℝ)^(1-σ))/|t|) ≤ 2 * |t|^(1-σ) := by
    have hle1 : ((N:ℝ)^(1-σ))/|t| ≤ (N:ℝ)^(1-σ) := by
      rw [div_le_iff₀ (by linarith : 0 < |t|)]
      nlinarith [Real.rpow_nonneg hNnonneg (1-σ), ht1]
    linarith [hle1, hNpow]
  have hnorm_s : ‖((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ σ + |t| := by
    have h1 : ‖((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
    have h2 : ‖(σ:ℂ)‖ = σ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h3 : ‖(t:ℂ)*Complex.I‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h3] at h1; exact h1
  have hNneg : (N:ℝ)^(-σ) ≤ |t|^(-σ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith : 0 < |t|) hNge (by linarith : -σ ≤ 0)
  have hT3 : (‖((σ:ℂ)+(t:ℂ)*Complex.I)‖/σ) * (N:ℝ)^(-σ) ≤ 4 * |t|^(1-σ) := by
    have hratio : ‖((σ:ℂ)+(t:ℂ)*Complex.I)‖/σ ≤ 2*(|t|+1) := by
      have h1 : ‖((σ:ℂ)+(t:ℂ)*Complex.I)‖/σ ≤ (σ + |t|)/σ := by gcongr
      have h2 : (σ + |t|)/σ = 1 + |t|/σ := by rw [add_div, div_self (ne_of_gt hσ0)]
      have h3 : |t|/σ ≤ 2*|t| := by
        rw [div_le_iff₀ hσ0]; nlinarith [hσlo, habs0]
      linarith [h1, h2, h3, ht1]
    have hmul : (‖((σ:ℂ)+(t:ℂ)*Complex.I)‖/σ) * (N:ℝ)^(-σ) ≤ (2*(|t|+1)) * |t|^(-σ) :=
      mul_le_mul hratio hNneg (Real.rpow_nonneg hNnonneg (-σ)) (by positivity)
    have hfinal : (2*(|t|+1)) * |t|^(-σ) ≤ 4 * |t|^(1-σ) := by
      have hrsplit : 2*(|t|+1) = 2*|t| + 2 := by ring
      rw [hrsplit, add_mul]
      have hbase : |t|^(1-σ) = |t| * |t|^(-σ) := by
        rw [show (1:ℝ) - σ = 1 + (-σ) by ring,
            Real.rpow_add (by linarith : (0:ℝ) < |t|), Real.rpow_one]
      have h1 : (2*|t|) * |t|^(-σ) = 2 * |t|^(1-σ) := by rw [hbase]; ring
      have h2 : 2 * |t|^(-σ) ≤ 2 * |t|^(1-σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : -σ ≤ 1-σ))
          (by norm_num)
      linarith [h1, h2]
    linarith [hmul, hfinal]
  linarith [hmain, hS, hT2, hT3]

/-- Region `|t| ≤ 10^100`: `‖ζ(σ+it)‖ ≤ 10^101`. -/
private lemma zeta_region_II {σ t : ℝ} (hσlo : 1 / 2 ≤ σ) (_hσhi : σ ≤ 1) (ht : 3 ≤ |t|)
    (ht100 : |t| ≤ 10 ^ 100) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 10 ^ 101 := by
  have hσ0 : 0 < σ := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have habs0 : 0 ≤ |t| := abs_nonneg t
  have hmain := zeta_emN_bound_aux hσ0 ht1 1 (le_refl (1:ℕ))
  have hS : (∑ n ∈ Finset.Icc 1 1, ((n : ℕ) : ℝ) ^ (-σ)) = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hc : (((1 : ℕ)) : ℝ) = (1 : ℝ) := by norm_num
    rw [hc, Real.one_rpow]
  have hT2 : ((1 : ℕ) : ℝ) ^ (1 - σ) / |t| ≤ 1 / 3 := by
    have hc : (((1 : ℕ)) : ℝ) = (1 : ℝ) := by norm_num
    rw [hc, Real.one_rpow]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) ht
  have hnorm_s : ‖((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ σ + |t| := by
    have h1 : ‖((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
    have h2 : ‖(σ:ℂ)‖ = σ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h3 : ‖(t:ℂ)*Complex.I‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h3] at h1; exact h1
  have hT3 : (‖((σ:ℂ) + (t:ℂ)*Complex.I)‖ / σ) * (((1 : ℕ)) : ℝ) ^ (-σ)
      ≤ 1 + 2 * 10 ^ 100 := by
    have hc : (((1 : ℕ)) : ℝ) = (1 : ℝ) := by norm_num
    rw [hc, Real.one_rpow, mul_one]
    have h2 : ‖((σ:ℂ) + (t:ℂ)*Complex.I)‖/σ ≤ (σ+|t|)/σ := by gcongr
    have h3 : (σ+|t|)/σ = 1 + |t|/σ := by rw [add_div, div_self (ne_of_gt hσ0)]
    have h4 : |t|/σ ≤ 2*|t| := by rw [div_le_iff₀ hσ0]; nlinarith [hσlo, habs0]
    linarith [h2, h3, h4, ht100]
  linarith [hmain, hS, hT2, hT3]

theorem zeta_offline_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 3 ≤ |t| →
      (σ ≤ 15 / 16 ∨ |t| ≤ 10 ^ 100) →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := by
  refine ⟨10 ^ 101, by norm_num, ?_⟩
  intro σ t hσlo hσhi ht hdisj
  have ht1 : 1 ≤ |t| := by linarith
  have habs0 : 0 ≤ |t| := abs_nonneg t
  have hf_nonneg : 0 ≤ 4 * (1 - σ) ^ (3 / 2 : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.rpow_nonneg (by linarith : 0 ≤ 1 - σ) _
  by_cases hle : σ ≤ 15 / 16
  · have hI := zeta_region_I hσlo hle ht
    have hexp : 1 - σ ≤ 4 * (1 - σ) ^ (3 / 2 : ℝ) :=
      le_four_mul_rpow_three_halves (by linarith : 1 / 16 ≤ 1 - σ)
    have hpow : |t| ^ (1 - σ) ≤ |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ht1 hexp
    have hP0 : 0 ≤ |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg habs0 _
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 40 * |t| ^ (1 - σ) := hI
      _ ≤ 40 * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ 10 ^ 101 * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by norm_num : (40:ℝ) ≤ 10 ^ 101) hP0
  · have ht100 : |t| ≤ 10 ^ 100 := by
      rcases hdisj with h | h
      · exact absurd h hle
      · exact h
    have hII := zeta_region_II hσlo hσhi ht ht100
    have hbase1 : (1:ℝ) ≤ |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
      Real.one_le_rpow ht1 hf_nonneg
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 10 ^ 101 := hII
      _ = 10 ^ 101 * 1 := by ring
      _ ≤ 10 ^ 101 * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbase1 (by norm_num)

end Work.BMF
