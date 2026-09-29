import Mathlib
import Submission.Work.C17I.defs
import Submission.Work.C17.beukersUR_two_sided
import Submission.Work.C17.eventually_pow_ge_const_mul_poly

/-!
# Divergence of the unlikely series off the relation (area C17I)

The unlikely `G`-series `P = Submission.CDT.logP a b ra rb rab r0` (paper eq. `defP`,
`Submission.CDT.LogUnlikelyG`) has `n`-th coefficient `cₙ = logPCoeffQ a b ra rb rab r0 n`.

Two facts about `cₙ` are used here.

* **Off-relation decomposition.**  For every `n`,
  `cₙ = logPCoeff (a,b) n + Δ·uₙ(a)uₙ(b)`, where `Δ = r_a η_a + r_b η_b + r_ab η_aη_b − r₀` is
  the "relation deficit" and `logPCoeff` is the *overconvergent* combination
  `r_a·(H(a)−η_aA(a))⋆A(b) + r_b·A(a)⋆(H(b)−η_bA(b)) + r_ab·(H(a)⋆H(b) − η_aη_b·A(a)⋆A(b))`
  (`Submission.CDT.logPCoeff`).  This is pure algebra (`cofR_decomp`): the coefficient
  `logPCoeffQ` is the *rational* combination `r_a vₙ(a)uₙ(b) + r_b uₙ(a)vₙ(b) + r_ab vₙ(a)vₙ(b) −
  r₀uₙ(a)uₙ(b)`, and expanding the η's in `logPCoeff` produces exactly the same expression with
  `r₀` replaced by the relation left-hand side.

* **Growth.**  `logPCoeff` is overconvergent (`Submission.CDT.logPCoeff_beyond_cusp`):
  `|logPCoeff n| ≤ C·sⁿ` with `s·ρ_a·ρ_b < 1`, i.e. `s < α_aα_b`;  and the Beukers coefficients
  satisfy the *sharp* two-sided bound `αⁿ/(n+1) ≤ uₙ(a) ≤ αⁿ`
  (`Work.C17.beukersUR_two_sided`), with `α_a = a + √(a²−1) ≥ 4` for `a ≥ 3`.

So if the relation **fails** (`Δ ≠ 0`) the dominant term `Δ·uₙ(a)uₙ(b)` of `cₙ` grows like
`(α_aα_b)ⁿ/(n+1)²`, which beats the overconvergent remainder `C·sⁿ` because `s < α_aα_b`; the
coefficients therefore grow at least like `((α_aα_b)/6)ⁿ/(n+1)²` and the series `Σ cₙwⁿ` diverges
for every `‖w‖ ≥ 1/6` (indeed for `‖w‖ ≥ 1/(α_aα_b) ≥ 1/34`).

The analytic content is isolated in `logP_engine`.
-/

namespace Work.C17I

open scoped BigOperators Topology

noncomputable section

/-- The `n`-th coefficient of the unlikely series `logP a b ra rb rab r0`, viewed as a real number. -/
def cofR (a b : ℚ) (ra rb rab r0 : ℤ) (n : ℕ) : ℝ :=
  ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℝ)

/-- **Off-relation decomposition of the coefficients of `logP`.**  For every `n`, the `n`-th
coefficient of `logP a b ra rb rab r0` is the overconvergent combination `logPCoeff` plus the
relation deficit `Δ` times the Hadamard product `uₙ(a)uₙ(b)` of the Beukers coefficients. -/
theorem cofR_decomp (a b : ℚ) (ra rb rab r0 : ℤ) (n : ℕ) :
    cofR a b ra rb rab r0 n
      = Submission.CDT.logPCoeff (a : ℝ) (b : ℝ) ra rb rab n
        + ((ra : ℝ) * Submission.CDT.beukersEta (a : ℝ)
            + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
            + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
            - (r0 : ℝ)) * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersUR (b : ℝ) n) := by
  simp only [cofR, Submission.CDT.logP, PowerSeries.coeff_mk]
  unfold Submission.CDT.logPCoeffQ Submission.CDT.logPCoeff Submission.CDT.beukersPaCoeff
    Submission.CDT.beukersPbCoeff Submission.CDT.beukersPabCoeff Submission.CDT.beukersD
  push_cast [Submission.CDT.beukersUR_eq_cast, Submission.CDT.beukersVR_eq_cast]
  ring

/-- **Analytic engine.**  Suppose `c n = D·ua n·ub n + R n` with `D ≠ 0`, `|R n| ≤ C·sⁿ`,
`ua n ≥ Aⁿ/(n+1)`, `ub n ≥ Bⁿ/(n+1)`, `0 < s < A·B` and `6 < A·B`.  Then `Σ cₙwⁿ` diverges for
every `‖w‖ ≥ 1/6`: the dominant term grows like `(A·B)ⁿ/(n+1)²` (which beats both `sⁿ` and the
polynomial loss), and after multiplication by `‖w‖ⁿ ≥ 6⁻ⁿ` it still beats the polynomial. -/
theorem logP_engine (c ua ub : ℕ → ℝ) (D A B s C : ℝ)
    (hD : D ≠ 0) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hC : 0 < C)
    (hsAB : s < A * B) (hAB6 : 6 < A * B)
    (hloa : ∀ n : ℕ, A ^ n / ((n : ℝ) + 1) ≤ ua n)
    (hlob : ∀ n : ℕ, B ^ n / ((n : ℝ) + 1) ≤ ub n)
    (hdec : ∀ n : ℕ, ∃ R : ℝ, c n = D * ua n * ub n + R ∧ |R| ≤ C * s ^ n)
    (w : ℂ) (hw : (1 / 6 : ℝ) ≤ ‖w‖) :
    ¬ Summable (fun n : ℕ => (c n : ℂ) * w ^ n) := by
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hDne : (|D| : ℝ) ≠ 0 := ne_of_gt hDabs
  have huapos : ∀ n : ℕ, 0 < ua n :=
    fun n => lt_of_lt_of_le (by positivity) (hloa n)
  have hubpos : ∀ n : ℕ, 0 < ub n :=
    fun n => lt_of_lt_of_le (by positivity) (hlob n)
  have hu : 1 < A * B / s := by rw [lt_div_iff₀ hs]; linarith
  have hv : 1 < A * B / 6 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 6)]; linarith
  obtain ⟨N1, hN1⟩ := Work.C17.eventually_pow_ge_const_mul_poly (A * B / s) (2 * C / |D|) hu
    (by positivity)
  obtain ⟨N2, hN2⟩ := Work.C17.eventually_pow_ge_const_mul_poly (A * B / 6) (2 / |D|) hv
    (by positivity)
  -- The remainder is dominated by half the dominant term.
  have hbound1 : ∀ n : ℕ, N1 ≤ n → C * s ^ n ≤ (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    have h6 := hN1 n hn
    have h2 : (2 * C / |D|) * ((n : ℝ) + 1) ^ 2 ≤ (A * B / s) ^ n := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hle : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 :=
        pow_le_pow_right₀ hn1 (by norm_num : 2 ≤ 6)
      exact le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) h6
    rw [div_pow] at h2
    have h3 : C * s ^ n * ((n : ℝ) + 1) ^ 2 ≤ (|D| / 2) * (A * B) ^ n := by
      have hm := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (|D| / 2) * s ^ n)
      have e1 : (|D| / 2) * s ^ n * ((2 * C / |D|) * ((n : ℝ) + 1) ^ 2)
          = C * s ^ n * ((n : ℝ) + 1) ^ 2 := by
        field_simp
      have e2 : (|D| / 2) * s ^ n * ((A * B) ^ n / s ^ n) = (|D| / 2) * (A * B) ^ n := by
        field_simp
      rwa [e1, e2] at hm
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
    exact h3
  -- The dominant term, after multiplying by `‖w‖ⁿ ≥ 6⁻ⁿ`, is at least `1`.
  have hbound2 : ∀ n : ℕ, N2 ≤ n → 1 ≤ (|D| / 2) * (A * B / 6) ^ n / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    have h6 := hN2 n hn
    have h2 : (2 / |D|) * ((n : ℝ) + 1) ^ 2 ≤ (A * B / 6) ^ n := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hle : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 :=
        pow_le_pow_right₀ hn1 (by norm_num : 2 ≤ 6)
      exact le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) h6
    have h3 : ((n : ℝ) + 1) ^ 2 ≤ (|D| / 2) * (A * B / 6) ^ n := by
      have hm := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ |D| / 2)
      have e : (|D| / 2) * ((2 / |D|) * ((n : ℝ) + 1) ^ 2) = ((n : ℝ) + 1) ^ 2 := by
        field_simp
      rwa [e] at hm
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
    simpa using h3
  have hmain : ∀ n : ℕ, max N1 N2 ≤ n → 1 ≤ |c n| * ‖w‖ ^ n := by
    intro n hn
    have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨R, hceq, hRb⟩ := hdec n
    have hABn : (A * B) ^ n / ((n : ℝ) + 1) ^ 2 ≤ ua n * ub n := by
      rw [mul_pow]
      have h := mul_le_mul (hloa n) (hlob n) (by positivity) (le_of_lt (huapos n))
      have e : A ^ n / ((n : ℝ) + 1) * (B ^ n / ((n : ℝ) + 1))
          = A ^ n * B ^ n / ((n : ℝ) + 1) ^ 2 := by
        rw [div_mul_div_comm]
        ring
      rwa [e] at h
    have hCs := hbound1 n hn1
    have hDua : |D| * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 ≤ |D| * ua n * ub n := by
      have h := mul_le_mul_of_nonneg_left hABn (abs_nonneg D)
      rw [mul_div_assoc]
      calc |D| * ((A * B) ^ n / ((n : ℝ) + 1) ^ 2) ≤ |D| * (ua n * ub n) := h
        _ = |D| * ua n * ub n := by ring
    have hdabs : |D * ua n * ub n| = |D| * ua n * ub n := by
      rw [abs_mul, abs_mul, abs_of_pos (huapos n), abs_of_pos (hubpos n)]
    have hcn : |D| * ua n * ub n - |R| ≤ |c n| := by
      have h1 : |D * ua n * ub n| = |c n - R| := by rw [hceq]; ring_nf
      have h2 : |c n - R| ≤ |c n| + |R| := by
        have h := abs_add_le (c n) (-R)
        rw [abs_neg] at h
        exact h
      rw [← h1, hdabs] at h2
      linarith
    have hlow : (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 ≤ |c n| := by
      have h1 : |D| * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 - C * s ^ n ≤ |c n| := by
        linarith [hcn, hDua, hRb]
      have h2 : (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2
          ≤ |D| * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 - C * s ^ n := by
        have e : |D| * (A * B) ^ n / ((n : ℝ) + 1) ^ 2
            = 2 * ((|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2) := by ring
        rw [e]
        linarith [hCs]
      linarith
    have hb2 := hbound2 n hn2
    have hw6 : (1 / 6 : ℝ) ^ n ≤ ‖w‖ ^ n := pow_le_pow_left₀ (by norm_num) hw n
    have hpow : (|D| / 2) * (A * B / 6) ^ n / ((n : ℝ) + 1) ^ 2
        ≤ (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 * ‖w‖ ^ n := by
      have h1 : (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 * (1 / 6 : ℝ) ^ n
          ≤ (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 * ‖w‖ ^ n :=
        mul_le_mul_of_nonneg_left hw6 (by positivity)
      have e : (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 * (1 / 6 : ℝ) ^ n
          = (|D| / 2) * (A * B / 6) ^ n / ((n : ℝ) + 1) ^ 2 := by
        have h' : A * B / 6 = (A * B) * (1 / 6) := by ring
        rw [h', mul_pow]
        ring
      rwa [e] at h1
    calc (1 : ℝ) ≤ (|D| / 2) * (A * B / 6) ^ n / ((n : ℝ) + 1) ^ 2 := hb2
      _ ≤ (|D| / 2) * (A * B) ^ n / ((n : ℝ) + 1) ^ 2 * ‖w‖ ^ n := hpow
      _ ≤ |c n| * ‖w‖ ^ n := mul_le_mul_of_nonneg_right hlow (by positivity)
  intro hsumm
  have htend : Filter.Tendsto (fun n : ℕ => ‖(c n : ℂ) * w ^ n‖) Filter.atTop (𝓝 0) := by
    have h := hsumm.tendsto_atTop_zero
    simpa using h.norm
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖(c n : ℂ) * w ^ n‖ < 1 :=
    htend.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N3, hN3⟩ := hev
  have hge := hmain (max (max N1 N2) N3) (le_max_left _ _)
  have hlt := hN3 (max (max N1 N2) N3) (le_max_right _ _)
  have heq : ‖(c (max (max N1 N2) N3) : ℂ) * w ^ (max (max N1 N2) N3)‖
      = |c (max (max N1 N2) N3)| * ‖w‖ ^ (max (max N1 N2) N3) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at hlt
  linarith

theorem logP_series_diverges (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (ra rb rab r0 : ℤ)
    (hA : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ) + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
        ≠ (r0 : ℝ))
    (w : ℂ) (hw : (1 / 6 : ℝ) ≤ ‖w‖) :
    ¬ Summable (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * w ^ n) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set A : ℝ := (a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 1) with hAdef
  set B : ℝ := (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 1) with hBdef
  have hApos : 0 < A := by
    rw [hAdef]; have := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1); linarith
  have hBpos : 0 < B := by
    rw [hBdef]; have := Real.sqrt_nonneg ((b : ℝ) ^ 2 - 1); linarith
  have hAB6 : 6 < A * B := by
    have hA4 : 4 ≤ A := by
      have h1 : (1 : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 - 1) := by
        have h : (1 : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 - 1 := by nlinarith [haR]
        exact (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1)).mpr h
      rw [hAdef]; linarith
    have hB4 : 4 ≤ B := by
      have h1 : (1 : ℝ) ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) := by
        have h : (1 : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 - 1 := by nlinarith [hbR]
        exact (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1)).mpr h
      rw [hBdef]; linarith
    nlinarith
  have hrhoApos : 0 < ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) := by
    have h1 : Real.sqrt ((a : ℝ) ^ 2 - 1) < (a : ℝ) := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < (a : ℝ))]
      nlinarith [haR]
    linarith
  have hrhoBpos : 0 < ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) := by
    have h1 : Real.sqrt ((b : ℝ) ^ 2 - 1) < (b : ℝ) := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < (b : ℝ))]
      nlinarith [hbR]
    linarith
  have hrhoA_mul : ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * A = 1 := by
    rw [hAdef]
    have hsq : (Real.sqrt ((a : ℝ) ^ 2 - 1)) ^ 2 = (a : ℝ) ^ 2 - 1 := by
      rw [Real.sq_sqrt]; nlinarith [sq_nonneg (a : ℝ)]
    nlinarith [hsq, Real.sqrt_nonneg ((a : ℝ) ^ 2 - 1)]
  have hrhoB_mul : ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) * B = 1 := by
    rw [hBdef]
    have hsq : (Real.sqrt ((b : ℝ) ^ 2 - 1)) ^ 2 = (b : ℝ) ^ 2 - 1 := by
      rw [Real.sq_sqrt]; nlinarith [sq_nonneg (b : ℝ)]
    nlinarith [hsq, Real.sqrt_nonneg ((b : ℝ) ^ 2 - 1)]
  have hABrho : A * B * (((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1))) = 1 := by
    calc A * B * (((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)))
        = (((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * A) * (((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) * B) := by ring
      _ = 1 := by rw [hrhoA_mul, hrhoB_mul, mul_one]
  set Δ : ℝ := (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ) + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
        - (r0 : ℝ) with hΔdef
  have hΔne : Δ ≠ 0 := by
    rw [hΔdef]
    intro h
    exact hA (by linarith)
  obtain ⟨C, s, hC, hs, hsc, hbnd⟩ := Submission.CDT.logPCoeff_beyond_cusp a b ha hb ra rb rab
  have hsAB : s < A * B := by
    set c : ℝ := ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 1)) * ((b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - 1)) with hcdef
    have hc : 0 < c := by rw [hcdef]; exact mul_pos hrhoApos hrhoBpos
    have h1 : s * c < 1 := by rw [hcdef]; exact hsc
    have h1' : s < 1 / c := (lt_div_iff₀ hc).mpr h1
    have h2 : A * B = 1 / c := by
      apply (eq_div_iff hc.ne').mpr
      rw [hcdef] at hABrho ⊢
      exact hABrho
    linarith
  have hcoefdec : ∀ n : ℕ, cofR a b ra rb rab r0 n
      = Submission.CDT.logPCoeff (a : ℝ) (b : ℝ) ra rb rab n
        + Δ * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersUR (b : ℝ) n) := by
    intro n
    have h := cofR_decomp a b ra rb rab r0 n
    rw [← hΔdef] at h
    exact h
  have hua : ∀ n : ℕ, A ^ n / ((n : ℝ) + 1) ≤ Submission.CDT.beukersUR (a : ℝ) n := by
    intro n
    have h := (Work.C17.beukersUR_two_sided (a : ℝ) haR n).1
    simpa only [hAdef] using h
  have hub : ∀ n : ℕ, B ^ n / ((n : ℝ) + 1) ≤ Submission.CDT.beukersUR (b : ℝ) n := by
    intro n
    have h := (Work.C17.beukersUR_two_sided (b : ℝ) hbR n).1
    simpa only [hBdef] using h
  have hmain : ¬ Summable (fun n : ℕ => (cofR a b ra rb rab r0 n : ℂ) * w ^ n) :=
    logP_engine (fun n => cofR a b ra rb rab r0 n)
      (fun n => Submission.CDT.beukersUR (a : ℝ) n)
      (fun n => Submission.CDT.beukersUR (b : ℝ) n)
      Δ A B s C hΔne hApos hBpos hs hC hsAB hAB6 hua hub
      (fun n => ⟨Submission.CDT.logPCoeff (a : ℝ) (b : ℝ) ra rb rab n, by rw [hcoefdec n]; ring, hbnd n⟩)
      w hw
  intro hsumm
  exact hmain (hsumm.congr (fun n => by simp only [cofR, Complex.ofReal_ratCast]))

end

end Work.C17I
