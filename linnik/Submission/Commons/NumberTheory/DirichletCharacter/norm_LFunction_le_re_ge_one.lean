import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Asymptotics.abel_tail_bound_finite
import Submission.Commons.NumberTheory.DirichletCharacter.interval_sum_bound

open Complex DirichletCharacter Filter
open scoped Real BigOperators Topology
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter


/-- Coefficients of a Dirichlet character have norm at most one. -/
private lemma char_coeff_norm_le_one {q : ℕ} (ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(ψ (n : ZMod q) : ℂ)‖ ≤ 1 := by
  simpa using (ψ.norm_le_one (n : ZMod q))

/-- The L-series of a Dirichlet character converges absolutely for `1 < re s`. -/
private lemma char_LSeriesSummable {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s := by
  exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (f := fun n : ℕ => (ψ (n : ZMod q) : ℂ)) (by intro n _; exact char_coeff_norm_le_one ψ n) hs

/-- `n`-th L-series term of the character equals `ψ(n) · n⁻ˢ` for `n ≠ 0`. -/
private lemma char_term_eq {q : ℕ} (ψ : DirichletCharacter ℂ q) {s : ℂ} {k : ℕ} (hk : k ≠ 0) :
    LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k
      = (ψ (k : ZMod q) : ℂ) * (k : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero hk]
  have hnz : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_mul_inv]
  rw [← cpow_neg]

/-- Norm of the `n`-th term is bounded by `n⁻ᵠ` where `σ = re s`, for `n ≠ 0`. -/
private lemma char_term_norm_le {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} {n : ℕ}
    (hn : n ≠ 0) :
    ‖LSeries.term (fun m : ℕ => (ψ (m : ZMod q) : ℂ)) s n‖ ≤ (1 : ℝ) / (n : ℝ) ^ s.re := by
  rw [LSeries.norm_term_eq]
  rw [if_neg hn]
  have hc : ‖(ψ (n : ZMod q) : ℂ)‖ ≤ 1 := char_coeff_norm_le_one ψ n
  have hp : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  calc
    ‖(ψ (n : ZMod q) : ℂ)‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
      exact div_le_div_of_nonneg_right hc (le_of_lt hp)

/-- `(∑_{1 ≤ n ≤ X} 1/n) = harmonic X`, over the reals. -/
private lemma sum_one_div_nat_eq_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / n) = (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  norm_num

/-- Harmonic sum is bounded by `1 + log X`. -/
private lemma harmonic_le_one_add_log_cast (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / n) ≤ 1 + Real.log (X : ℝ) := by
  rw [sum_one_div_nat_eq_harmonic]
  exact harmonic_le_one_add_log X

/-- Head of the L-series: `(∑_{1 ≤ n ≤ X} n^(-σ)) ≤ 1 + log X` for `1 ≤ σ`. -/
private lemma head_rpow_le_log (X : ℕ) {σ : ℝ} (hσ1 : 1 ≤ σ) :
    (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ σ) ≤ 1 + Real.log (X : ℝ) := by
  have hle_term : ∀ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ σ ≤ (1 : ℝ) / n := by
    intro n hn
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < (n : ℝ) := by linarith
    have hpow : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ σ := by
      exact Real.rpow_le_rpow_of_exponent_le hn1r hσ1
    have hpow' : (n : ℝ) ≤ (n : ℝ) ^ σ := by simpa [Real.rpow_one] using hpow
    exact one_div_le_one_div_of_le hn0 hpow'
  calc
    (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ σ) ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / n) := by
      exact Finset.sum_le_sum hle_term
    _ ≤ 1 + Real.log (X : ℝ) := harmonic_le_one_add_log_cast X

/-- `x^(-σ)` is antitone in `x ≥ 1` for `0 < σ`. -/
private lemma rpow_neg_antitone {a b : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b) {σ : ℝ} (hσ : 0 < σ) :
    b ^ (-σ) ≤ a ^ (-σ) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one (le_trans ha1 hab)
  have hle : a ^ σ ≤ b ^ σ := by
    exact Real.rpow_le_rpow (le_of_lt ha0) hab (le_of_lt hσ)
  calc
    b ^ (-σ) = (b ^ σ)⁻¹ := by rw [Real.rpow_neg (le_of_lt hb0)]
    _ ≤ (a ^ σ)⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hb0 σ) (Real.rpow_pos_of_pos ha0 σ)).mpr hle
    _ = a ^ (-σ) := by rw [Real.rpow_neg (le_of_lt ha0)]

/-- Abel (partial summation) bound for the tail of the character L-series over `(X, M]`. -/
private lemma abel_char_tail {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {s : ℂ} (hs0 : 0 < s.re) {X M : ℕ} (hX1n : 1 ≤ X) (hle : X + 1 ≤ M) :
    ‖∑ k ∈ Finset.Icc (X + 1) M, (ψ (k : ZMod q) : ℂ) * (k : ℂ) ^ (-s)‖
      ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  have hB : ∀ x y : ℕ, x ≤ y →
      ‖∑ n ∈ Finset.Icc x y, (ψ (n : ZMod q) : ℂ)‖ ≤ (2 * (q : ℝ)) := by
    intro x y hxy
    simpa using (interval_sum_bound ψ hψ hxy)
  have hb := Commons.Analysis.Asymptotics.abel_tail_bound_finite (a := fun n : ℕ => (ψ (n : ZMod q) : ℂ)) (B := 2 * (q : ℝ))
    hB s hs0 (N := X + 1) (M := M) hle (by omega)
  have hmono : ((X + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (X : ℝ) ^ (-s.re) := by
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hX1n
    exact rpow_neg_antitone hX1 (by exact_mod_cast (by omega : X ≤ X + 1)) hs0
  have hB0 : 0 ≤ 2 * (q : ℝ) := by positivity
  have hc0 : 0 ≤ 1 + ‖s‖ / s.re := by positivity
  calc
    ‖∑ k ∈ Finset.Icc (X + 1) M, (ψ (k : ZMod q) : ℂ) * (k : ℂ) ^ (-s)‖
        ≤ (2 * (q : ℝ)) * ((X + 1 : ℕ) : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := hb
    _ ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
      have h1 : (2 * (q : ℝ)) * ((X + 1 : ℕ) : ℝ) ^ (-s.re)
          ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) := by
        exact mul_le_mul_of_nonneg_left hmono hB0
      exact mul_le_mul_of_nonneg_right h1 hc0

/-- Partial sums `(∑_{1 ≤ k ≤ M} ...)` of the character L-series over an interval:
finite Abel (head + tail) bound for `1 < re s` and `M ≥ X + 1`. -/
private lemma partial_char_sum_bound {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) {s : ℂ} (hs1 : 1 < s.re) {X M : ℕ} (hX1 : 1 ≤ X) (hXM : X + 1 ≤ M) :
    ‖∑ k ∈ Finset.Icc 1 M,
        LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
      ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
        + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  have hcover : Finset.Icc 1 M = (Finset.Icc 1 X) ∪ (Finset.Icc (X + 1) M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 X) (Finset.Icc (X + 1) M) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  have hsplit : (∑ k ∈ Finset.Icc 1 M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)
      = (∑ k ∈ Finset.Icc 1 X, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)
        + (∑ k ∈ Finset.Icc (X + 1) M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k) := by
    rw [hcover, Finset.sum_union hdisj]
  have htail_eq : (∑ k ∈ Finset.Icc (X + 1) M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)
      = ∑ k ∈ Finset.Icc (X + 1) M, (ψ (k : ZMod q) : ℂ) * (k : ℂ) ^ (-s) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      have hk' : X + 1 ≤ k := (Finset.mem_Icc.mp hk).1
      omega
    exact char_term_eq ψ hk0
  have hhead_norm : ‖∑ k ∈ Finset.Icc 1 X, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
      ≤ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re := by
    calc
      ‖∑ k ∈ Finset.Icc 1 X, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
          ≤ ∑ k ∈ Finset.Icc 1 X, ‖LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re := by
            apply Finset.sum_le_sum
            intro k hk
            have hk0 : k ≠ 0 := by
              have hk' : 1 ≤ k := (Finset.mem_Icc.mp hk).1
              omega
            exact char_term_norm_le ψ hk0
  have htail_norm : ‖∑ k ∈ Finset.Icc (X + 1) M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
      ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
    rw [htail_eq]
    exact abel_char_tail ψ hψ (hs0 := by linarith) (X := X) (M := M) hX1 hXM
  calc
    ‖∑ k ∈ Finset.Icc 1 M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
        = ‖(∑ k ∈ Finset.Icc 1 X, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)
            + (∑ k ∈ Finset.Icc (X + 1) M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)‖ := by
            rw [hsplit]
    _ ≤ ‖∑ k ∈ Finset.Icc 1 X, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖
        + ‖∑ k ∈ Finset.Icc (X + 1) M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖ := by
            exact norm_add_le _ _
    _ ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
        + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
            exact add_le_add hhead_norm htail_norm

/-- Partial sums over `Icc 1 M` of a summable sequence (with `a 0 = 0`) tend to its sum. -/
private lemma tendsto_sum_Icc_one {a : ℕ → ℂ} (ha : Summable a) (ha0 : a 0 = 0) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M, a k) atTop (𝓝 (∑' k, a k)) := by
  have hrange : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, a k) atTop (𝓝 (∑' k, a k)) :=
    ha.hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have hcomp : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range (M + 1), a k) atTop (𝓝 (∑' k, a k)) :=
    hrange.comp hshift
  have hsame : (fun M : ℕ => ∑ k ∈ Finset.range (M + 1), a k)
      = fun M : ℕ => ∑ k ∈ Finset.Icc 1 M, a k := by
    funext M
    have hrange_eq : Finset.range (M + 1) = Finset.Icc 0 M := by
      rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
    have hins : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor <;> omega
    calc
      ∑ k ∈ Finset.range (M + 1), a k = ∑ k ∈ Finset.Icc 0 M, a k := by rw [hrange_eq]
      _ = a 0 + ∑ k ∈ Finset.Icc 1 M, a k := by
              have hnotin : 0 ∉ Finset.Icc 1 M := by
                intro hk
                rw [Finset.mem_Icc] at hk
                omega
              rw [hins]
              exact Finset.sum_insert hnotin
      _ = ∑ k ∈ Finset.Icc 1 M, a k := by simp [ha0]
  exact hcomp.congr' (Eventually.of_forall fun M => congrFun hsame M)

/-- Partial sums of the character L-series over `Icc 1 M` tend to the L-series for `1 < re s`. -/
private lemma tendsto_partial_char_LSeries {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs1 : 1 < s.re) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M,
        LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k)
      atTop (𝓝 (LSeries (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s)) := by
  let a : ℕ → ℂ := fun k => LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k
  have hsumm : Summable a := by
    dsimp [a]
    exact char_LSeriesSummable ψ hs1
  have ha0 : a 0 = 0 := by
    simp [a]
  have ht := tendsto_sum_Icc_one hsumm ha0
  simpa [a, LSeries] using ht

/-- The character partial sums `(∑_{1 ≤ k ≤ M})` bound the L-series value for `1 < re s`. -/
private lemma norm_LSeries_char_le_bound {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) {s : ℂ} (hs1 : 1 < s.re) {X : ℕ} (hX1 : 1 ≤ X) :
    ‖LSeries (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s‖
      ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
        + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  have htend := tendsto_partial_char_LSeries ψ hs1
  have hnorm_t : Tendsto (fun M : ℕ =>
        ‖∑ k ∈ Finset.Icc 1 M, LSeries.term (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s k‖)
      atTop (𝓝 ‖LSeries (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s‖) := by
    exact tendsto_norm.comp htend
  exact le_of_tendsto hnorm_t (by
    filter_upwards [eventually_ge_atTop (X + 1)] with M hM
    exact partial_char_sum_bound ψ hψ hs1 hX1 hM)

/-- Additive logarithmic bound for a non-trivial Dirichlet L-function on `Re s > 1`, uniform
in the real part: `‖L(σ + i t, ψ)‖ ≤ 5 + log 2 + log(q·(1+|t|))` for every `1 < σ`. -/
private lemma norm_LFunction_log_re_gt_one {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) :
    ∀ ⦃σ : ℝ⦄, 1 < σ → ∀ t : ℝ,
      ‖ψ.LFunction ((σ : ℂ) + I * (t : ℂ))‖ ≤ 5 + Real.log 2 + Real.log ((q : ℝ) * (1 + |t|)) := by
  intro σ hσ t
  classical
  let U : ℝ := (q : ℝ) * (1 + |t|)
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hsre : s.re = σ := by
    dsimp [s]
    simp
  have hs1 : 1 < s.re := by
    rw [hsre]
    exact hσ
  have hs0 : 0 < s.re := by linarith
  have hσ1 : 1 ≤ σ := le_of_lt hσ
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hqpos)
  have hU1 : (1 : ℝ) ≤ U := by
    dsimp [U]
    exact one_le_mul_of_one_le_of_one_le hq1 (by nlinarith [abs_nonneg t])
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  let X : ℕ := ⌈U⌉₊
  have hXU : U ≤ (X : ℝ) := Nat.le_ceil U
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := le_trans hU1 hXU
  have hX1 : 1 ≤ X := by exact_mod_cast hX1r
  have hXleU1 : (X : ℝ) ≤ U + 1 := by
    have h1 : (X : ℝ) ≤ ((⌊U⌋₊ : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.ceil_le_floor_add_one U)
    have h2 : ((⌊U⌋₊ : ℕ) : ℝ) ≤ U := by
      exact Nat.floor_le (le_of_lt hU0)
    linarith
  have hXle2U : (X : ℝ) ≤ 2 * U := by
    linarith
  have hσpos : 0 < σ := by linarith
  have hnorm_le : ‖s‖ ≤ σ + |t| := by
    have hre' : |s.re| ≤ σ := by
      rw [hsre]
      rw [abs_of_nonneg (le_of_lt hσpos)]
    have him' : |s.im| = |t| := by
      dsimp [s]
      simp
    have htri := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hsn : ‖s‖ / σ ≤ 1 + |t| := by
    have hmt : σ + |t| ≤ σ * (1 + |t|) := by
      have h : |t| ≤ σ * |t| := by
        calc |t| = 1 * |t| := by ring
          _ ≤ σ * |t| := mul_le_mul_of_nonneg_right hσ1 (abs_nonneg t)
      nlinarith
    rw [div_le_iff₀ hσpos]
    calc
      ‖s‖ ≤ σ + |t| := hnorm_le
      _ ≤ σ * (1 + |t|) := hmt
      _ = (1 + |t|) * σ := by ring
  have hone_sn : 1 + ‖s‖ / σ ≤ 2 + |t| := by linarith
  have hbnd := norm_LSeries_char_le_bound ψ hψ (s := s) hs1 (X := X) hX1
  -- hbnd bounds ‖LSeries f s‖ by head + tail where tail uses s.re = σ
  have hL : ψ.LFunction s = LSeries (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s := by
    exact LFunction_eq_LSeries ψ hs1
  have hhead : (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re) ≤ 1 + Real.log (X : ℝ) := by
    rw [hsre]
    exact head_rpow_le_log X hσ1
  have htail1 : (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re)
      ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-σ) * (2 + |t|) := by
    rw [hsre]
    have h1 : 1 + ‖s‖ / σ ≤ 2 + |t| := hone_sn
    have hA0 : 0 ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-σ) := by positivity
    exact mul_le_mul_of_nonneg_left h1 hA0
  have htail2 : (2 * (q : ℝ)) * (X : ℝ) ^ (-σ) * (2 + |t|) ≤ 4 := by
    -- (2q)·X^(-σ)·(2+|t|) ≤ (2q)·X^(-1)·(2+|t|) ≤ (2q)·U⁻¹·(2+|t|)
    --   = 2·(2+|t|)/(1+|t|) ≤ 4
    have hXpow : (X : ℝ) ^ (-σ) ≤ (X : ℝ) ^ (-1 : ℝ) := by
      have hX1e : (1 : ℝ) ≤ (X : ℝ) := hX1r
      have hexp : (-σ : ℝ) ≤ (-1 : ℝ) := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hX1e hexp
    have hXinv : (X : ℝ)⁻¹ ≤ U⁻¹ := by
      -- U ≤ X, both positive: X⁻¹ ≤ U⁻¹
      exact (inv_le_inv₀ (by positivity : 0 < (X : ℝ)) hU0).mpr hXU
    have hqU : (2 * (q : ℝ)) / U = 2 / (1 + |t|) := by
      dsimp [U]
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
      have h1p : (1 + |t| : ℝ) ≠ 0 := by positivity
      field_simp [hqne, h1p]
    calc
      (2 * (q : ℝ)) * (X : ℝ) ^ (-σ) * (2 + |t|)
          ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-1 : ℝ) * (2 + |t|) := by
              have h1 : (2 * (q : ℝ)) * (X : ℝ) ^ (-σ) ≤ (2 * (q : ℝ)) * (X : ℝ) ^ (-1 : ℝ) := by
                exact mul_le_mul_of_nonneg_left hXpow (by positivity)
              have h2 : 0 ≤ 2 + |t| := by positivity
              exact mul_le_mul_of_nonneg_right h1 h2
      _ = (2 * (q : ℝ)) * (X : ℝ)⁻¹ * (2 + |t|) := by
              rw [Real.rpow_neg_one]
      _ ≤ (2 * (q : ℝ)) * U⁻¹ * (2 + |t|) := by
              have h1 : (2 * (q : ℝ)) * (X : ℝ)⁻¹ ≤ (2 * (q : ℝ)) * U⁻¹ := by
                exact mul_le_mul_of_nonneg_left hXinv (by positivity)
              have h2 : 0 ≤ 2 + |t| := by positivity
              exact mul_le_mul_of_nonneg_right h1 h2
      _ = ((2 * (q : ℝ)) / U) * (2 + |t|) := by
              rw [div_eq_mul_inv]
      _ = (2 / (1 + |t|)) * (2 + |t|) := by
              rw [hqU]
      _ ≤ 4 := by
              have hdenpos : 0 < 1 + |t| := by positivity
              rw [div_mul_eq_mul_div]
              exact (div_le_iff₀ hdenpos).mpr (by nlinarith [abs_nonneg t])

  have hlog2le2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlogX : Real.log (X : ℝ) ≤ Real.log (2 * U) := by
    have hposX : 0 < (X : ℝ) := lt_of_lt_of_le zero_lt_one hX1r
    have hpos2U : 0 < 2 * U := by positivity
    exact Real.log_le_log hposX hXle2U
  have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U := by
    exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hU0)
  have hmain : ‖ψ.LFunction s‖ ≤ 5 + Real.log 2 + Real.log U := by
    have h1 : ‖ψ.LFunction s‖
        ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
          + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
      calc
        ‖ψ.LFunction s‖ = ‖LSeries (fun n : ℕ => (ψ (n : ZMod q) : ℂ)) s‖ := by rw [hL]
        _ ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
            + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := hbnd
    calc
      ‖ψ.LFunction s‖
          ≤ (∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) ^ s.re)
            + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := h1
      _ ≤ (1 + Real.log (X : ℝ)) + (2 * (q : ℝ)) * (X : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
              exact add_le_add hhead le_rfl
      _ ≤ (1 + Real.log (X : ℝ)) + 4 := by
              exact add_le_add le_rfl (le_trans htail1 htail2)
      _ ≤ 1 + Real.log (2 * U) + 4 := by
              have h1 : 1 + Real.log (X : ℝ) ≤ 1 + Real.log (2 * U) := by
                linarith [hlogX]
              linarith
      _ ≤ 5 + Real.log 2 + Real.log U := by
              rw [hlog2U]
              linarith
  -- close the statement (s is (σ:ℂ)+ I*t):
  simpa [s, U] using hmain



/-- Additive logarithmic bound for a non-trivial Dirichlet L-function on the line
`Re s = 1`, obtained by continuity from the `Re s > 1` bound:
`‖L(1 + i t, ψ)‖ ≤ 5 + log 2 + log(q·(1+|t|))`. -/
private lemma norm_LFunction_log_re_one {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (t : ℝ) :
    ‖ψ.LFunction ((1 : ℂ) + I * (t : ℂ))‖
      ≤ 5 + Real.log 2 + Real.log ((q : ℝ) * (1 + |t|)) := by
  let B : ℝ := 5 + Real.log 2 + Real.log ((q : ℝ) * (1 + |t|))
  let g : ℝ → ℂ := fun x : ℝ => (x : ℂ) + I * (t : ℂ)
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hgcont : Continuous g := by
    dsimp [g]
    exact Complex.continuous_ofReal.add
      (continuous_const : Continuous (fun _ : ℝ => I * (t : ℂ)))
  have hcont : Continuous (fun x : ℝ => ψ.LFunction (g x)) :=
    (differentiable_LFunction hψ).continuous.comp hgcont
  have htend : Tendsto (fun n : ℕ => ‖ψ.LFunction (g (1 + 1 / (n + 1)))‖)
      atTop (𝓝 ‖ψ.LFunction (g 1)‖) := by
    have h : Tendsto (fun n : ℕ => ψ.LFunction (g (1 + 1 / (n + 1))))
        atTop (𝓝 (ψ.LFunction (g 1))) := hcont.continuousAt.tendsto.comp hseq
    exact tendsto_norm.comp h
  have hle_each : ∀ n : ℕ, ‖ψ.LFunction (g (1 + 1 / (n + 1)))‖ ≤ B := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hgt : (1 : ℝ) < 1 + 1 / (n + 1) := by linarith
    dsimp [B, g]
    exact norm_LFunction_log_re_gt_one ψ hψ hgt t
  have hlim : ‖ψ.LFunction (g 1)‖ ≤ B := by
    exact le_of_tendsto htend (Eventually.of_forall hle_each)
  simpa [g, B] using hlim

/-- Additive bound on the logarithms: `5 + log 2 + log(q·(1+|t|)) ≤ log q + log(2+|t|) + 6`. -/
private lemma log_bound_num {q : ℕ} [NeZero q] (t : ℝ) :
    5 + Real.log 2 + Real.log ((q : ℝ) * (1 + |t|)) ≤
      Real.log (q : ℝ) + Real.log (2 + |t|) + 6 := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have h1p : 0 < 1 + |t| := by positivity
  have h2p : 0 < 2 + |t| := by positivity
  have hmono : 1 + |t| ≤ 2 + |t| := by nlinarith
  have hlog1 : Real.log (1 + |t|) ≤ Real.log (2 + |t|) := Real.log_le_log h1p hmono
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hmul : Real.log ((q : ℝ) * (1 + |t|)) = Real.log (q : ℝ) + Real.log (1 + |t|) := by
    exact Real.log_mul (ne_of_gt hqpos) (ne_of_gt h1p)
  nlinarith


/-- Explicit bound for `|L(χ,s)|` on the closed half-plane `Re s ≥ 1`, for the `goodRadius` proof
(Linnik): `‖LFunction χ s‖ ≤ log N + log(2+|s.im|) + 6` for every nontrivial character `χ mod N`
and every `s` with `1 ≤ s.re`.

Needed because existing `|L|` bounds are ∃-quantified or only cover `Re ∈ (0,1)`; the consumer
bounds `log|Λ(s,χ)|` on large circles and needs the `Re ≥ 1` part explicit, uniform in `σ`
(including `σ = 1`), with logarithm `≤ log N + log(2+|t|) + O(1)`.

Method: `LFunction χ s` equals `Σ_n χ(n)/n^s` for `1 < Re s` (`LFunction_eq_LSeries`); partial
sums converge uniformly on `Re ≥ 1` (character sums over complete periods vanish since `χ ≠ 1`,
so `|Σ_{n≤x} χ(n)| ≤ N`), hence equality extends to `Re s = 1` by continuity.  Abel summation with
`|A(x)| ≤ N`: tail `|Σ_{n>M} χ(n)/n^s| ≤ N·(1+|s|)·M^{-σ}/σ` (bounded by `≤ 1` choosing
`M ≈ N(2+|t|)K`), head `≤ 1 + log M` (since `σ ≥ 1`); total `≤ log N + log(2+|t|) + 6` for a
suitable constant `K`.  Constant `6` is deliberately loose. -/
theorem norm_LFunction_le_re_ge_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      Real.log (N : ℝ) + Real.log (2 + |s.im|) + 6 := by
  let B : ℝ := 5 + Real.log 2 + Real.log ((N : ℝ) * (1 + |s.im|))
  have hB : ‖DirichletCharacter.LFunction χ s‖ ≤ B := by
    by_cases hgt : 1 < s.re
    · have hs_split : s = (s.re : ℂ) + I * (s.im : ℂ) := by
        apply Complex.ext <;> simp
      have hb := norm_LFunction_log_re_gt_one χ hχ hgt s.im
      rw [hs_split]
      simpa [B] using hb
    · have hreq : s.re = 1 := le_antisymm (le_of_not_gt hgt) hs
      have hs_split : s = (1 : ℂ) + I * (s.im : ℂ) := by
        apply Complex.ext <;> simp [hreq]
      have hb := norm_LFunction_log_re_one χ hχ s.im
      rw [hs_split]
      simpa [B] using hb
  calc
    ‖DirichletCharacter.LFunction χ s‖ ≤ B := hB
    _ ≤ Real.log (N : ℝ) + Real.log (2 + |s.im|) + 6 := by
      dsimp [B]
      exact log_bound_num (q := N) s.im


end Commons.NumberTheory.DirichletCharacter
