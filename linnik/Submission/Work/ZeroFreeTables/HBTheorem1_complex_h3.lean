/-
# ZeroFreeTables — HBTheorem1_complex_h3

The `h = 3` case (cubic `χ₁`) of **HB Lemma 9.5** (Heath-Brown, *Zero-free regions for
Dirichlet L-functions, and the least prime in an arithmetic progression*, PLMS **64** (1992)
265–338, p. 59), in the form needed by `HBTheorem1_complex`:

> if `χ₁` has order `3` and `ρ₁` realises the minimal `λ` among the non-principal zeros of
> height `≤ 10`, then `λ₁ = (1 - Re ρ₁)·log q ≥ 0.389 > 0.348`.

HB's proof (p. 58–59) runs the §9 `P₃`/Chebyshev engine with `a = 2.6`: the pointwise
Chebyshev identity `(3+10x)²(9+10x)² = 14379 + 24480·T₁ + 14900·T₂ + 6000·T₃ + 1250·T₄`
(`T_j` the Chebyshev polynomials, so that `T_j(cos θ) = cos jθ`) is summed against the
`P₃`-weighted von Mangoldt series `Σ(·,·)` (HB (8.4)) and evaluated at the five points
`σ + ijγ₁`, `j = 0,…,4` (`σ = 1 + 2.6/log q`), giving

  `0 ≤ 14379·P₃((a+λ₁)/a) − 24480·P₃(1) + 40630·(a+λ₁)·(1/8 + ε)`,

whose root is `0.389…`; the numerical step is the proved `Work.ZeroFreeTables.h3_arith`, and
the single-point analytic input is the `P₃` engine `Work.ZeroFreeTables.HB95SigmaEngine`
(the `P₃`-functional form of HB Lemma 5.2 with the order-`3` Burgess input `φ = 1/4`, i.e.
error coefficient `φ/2 = 1/8`), with the principal-character bound
`Work.ZeroFreeTables.HB95PrincipalEngine` and the window bookkeeping
`Work.ZeroFreeTables.HB95NearZeros`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB95Arith
import Submission.Work.ZeroFreeTables.Table4.HB83
import Submission.Work.ZeroFreeTables.HB95_h3_engine

open Complex

namespace Work.ZeroFreeTables

/-- An order-`3` Dirichlet character is not real: `χ₁ ^ 2 ≠ 1`. -/
theorem orderThree_sq_ne_one {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (h : orderOf χ₁ = 3) : χ₁ ^ 2 ≠ 1 := by
  intro h2
  have hdvd : orderOf χ₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have h32 : (3 : ℕ) ∣ 2 := by rw [← h]; exact hdvd
  omega

/-- **HB's Chebyshev expansion (9.15)**, in the Chebyshev basis: with `T₀ = 1`,
`T₁ = x`, `T₂ = 2x² − 1`, `T₃ = 4x³ − 3x`, `T₄ = 8x⁴ − 8x² + 1` one has
`14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄ = (3+10x)²(9+10x)² ≥ 0`. -/
theorem chebyshev_five (x : ℝ) :
    14379 + 24480 * x + 14900 * (2 * x ^ 2 - 1) + 6000 * (4 * x ^ 3 - 3 * x)
      + 1250 * (8 * x ^ 4 - 8 * x ^ 2 + 1) = (3 + 10 * x) ^ 2 * (9 + 10 * x) ^ 2 := by
  ring

theorem chebyshev_five_nonneg (x : ℝ) :
    0 ≤ 14379 + 24480 * x + 14900 * (2 * x ^ 2 - 1) + 6000 * (4 * x ^ 3 - 3 * x)
      + 1250 * (8 * x ^ 4 - 8 * x ^ 2 + 1) := by
  rw [chebyshev_five]; positivity

/-- The same expansion read on the unit circle: for `|z| = 1`, with `x = Re z`,
`Σ_j c_j Re(z^j) = (3+10x)²(9+10x)²`.  This is the inequality (9.16) of Heath-Brown's
§9, whose `n`-th summand is `Λ(n)n^{-σ}u(log n/L)` times this non-negative quantity
(`u = α + α²y + (1/3)α³y²` is the `P₃` weight of (8.4)). -/
theorem chebyshev_five_unit {z : ℂ} (hz : z * starRingEnd ℂ z = 1) :
    14379 + 24480 * z.re + 14900 * (z ^ 2).re + 6000 * (z ^ 3).re + 1250 * (z ^ 4).re
      = (3 + 10 * z.re) ^ 2 * (9 + 10 * z.re) ^ 2 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := congrArg Complex.re hz
    simp [Complex.mul_re] at h
    linarith [h]
  have h2re : (z ^ 2).re = 2 * z.re ^ 2 - 1 := by
    rw [pow_two, Complex.mul_re]; nlinarith [hsq]
  have h2im : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]; ring
  have h3re : (z ^ 3).re = 4 * z.re ^ 3 - 3 * z.re := by
    rw [show z ^ 3 = z ^ 2 * z by ring, Complex.mul_re, h2re, h2im]
    linear_combination (-2 * z.re) * hsq
  have h4re : (z ^ 4).re = 8 * z.re ^ 4 - 8 * z.re ^ 2 + 1 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, pow_two, Complex.mul_re, h2re, h2im]
    linear_combination (-4 * z.re ^ 2) * hsq
  rw [h2re, h3re, h4re]
  ring


theorem HBTheorem1_complex_h3 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 3 →
      (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨q₀, H⟩ := HB95_h3_engine (1 / 100000) (by norm_num)
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hord => ?_⟩
  by_contra hcon
  have hle : Work.LinnikContract.lamOf q ρ₁ ≤ 348 / 1000 := le_of_lt (not_le.mp hcon)
  exact hcon (h3_arith hle (by norm_num) (by norm_num) (H q hq χ₁ ρ₁ hm hord hle))

/-! ## The reduction to the `P₃` inequality (★)

The remaining analytic content of the `h = 3` case is the inequality (★) of HB (9.13)/(9.16),
obtained by summing the pointwise Chebyshev inequality `(3+10Re z)²(9+10Re z)² ≥ 0` against
the `P₃`-weighted von Mangoldt series at the five points `σ + ijγ₁` (`σ = 1 + 2.6/log q`,
`a = 2.6`, `N₃ = 40630`).  The numerical step (★) `⟹ λ₁ ≥ 348/1000` is the proved
`Work.ZeroFreeTables.h3_arith`. -/

/-! ## The "`T`-step" of the `P₃` bookkeeping (HB p. 59, the analogue of Lemma 8.3)

For `a = 2.6` and `α = a + λ₁` with `λ₁ ≤ 348/1000`, the positive pole contributions to the
`T₃`-bracket (denominator `a`) are dominated by the negative near-zero contributions
(denominator `α = a + λ₁`), so that `Re T₃ ≤ 0`.  The numeric content is the side condition
(9.17) in the form `6000·(α/a)³ ≤ 16150`. -/

/-- Elementary comparison of the two `P₃` arguments: for `0 < a ≤ α`,
`(αa/(a²+t²))³ ≤ (α/a)³·(α²/(α²+t²))³`. -/
theorem ratio_cube3 {a α t : ℝ} (ha : 0 < a) (hα : 0 < α) (hale : a ≤ α) :
    (α * a / (a^2 + t^2))^3 ≤ (α/a)^3 * (α^2/(α^2 + t^2))^3 := by
  have hkey : ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2))
      = (α*(α^2 - a^2)*t^2)/(a*(a^2+t^2)*(α^2+t^2)) := by
    field_simp
    ring
  have hnum : 0 ≤ α*(α^2 - a^2)*t^2 := by
    have h1 : 0 ≤ α^2 - a^2 := by nlinarith [hale, ha.le, hα.le]
    positivity
  have hden : 0 < a*(a^2+t^2)*(α^2+t^2) := by
    have h1 : 0 < a^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos ha]
    have h2 : 0 < α^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos hα]
    positivity
  have hAB : α * a / (a^2 + t^2) ≤ (α/a) * (α^2/(α^2 + t^2)) := by
    have h3 : 0 ≤ ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2)) := by
      rw [hkey]; exact div_nonneg hnum hden.le
    linarith [h3]
  have hnn : 0 ≤ α * a / (a^2 + t^2) := by
    have h1 : 0 < a^2 + t^2 := by nlinarith [sq_nonneg t, sq_pos_of_pos ha]
    exact div_nonneg (mul_nonneg hα.le ha.le) h1.le
  calc (α * a / (a^2 + t^2))^3 ≤ ((α/a) * (α^2/(α^2 + t^2)))^3 :=
        pow_le_pow_left₀ hnn hAB 3
    _ = (α/a)^3 * (α^2/(α^2 + t^2))^3 := by ring

/-- The numeric side condition (9.17) at `a = 2.6`, `λ₁ ≤ 348/1000`: `6000·(α/a)³ ≤ 16150`. -/
theorem h3_side {lam : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    6000 * (((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3 ≤ 16150 := by
  have hle' : (26:ℝ)/10 + lam ≤ (2948:ℝ)/1000 := by linarith
  have hpos' : 0 < (26:ℝ)/10 + lam := by linarith
  have hcube : ((26:ℝ)/10 + lam)^3 ≤ ((2948:ℝ)/1000)^3 := pow_le_pow_left₀ hpos'.le hle' 3
  rw [div_pow,
    show 6000 * (((26:ℝ)/10 + lam)^3 / ((26:ℝ)/10)^3)
        = (6000 * ((26:ℝ)/10 + lam)^3) / ((26:ℝ)/10)^3 by ring,
    div_le_iff₀ (by norm_num : (0:ℝ) < ((26:ℝ)/10)^3)]
  have h1 : 6000 * ((26:ℝ)/10 + lam)^3 ≤ 6000 * ((2948:ℝ)/1000)^3 :=
    mul_le_mul_of_nonneg_left hcube (by norm_num)
  have h2 : 6000 * ((2948:ℝ)/1000)^3 ≤ 16150 * ((26:ℝ)/10)^3 := by norm_num
  linarith [h1, h2]

/-- **The `T₃`-step.**  For `0 ≤ λ₁ ≤ 348/1000` and every `T`,
`6000·Re P₃(α/(a+iT)) ≤ 14900·Re P₃(α/(α+iT)) + 1250·Re P₃(α/(α+iT))`. -/
theorem h3_Tstep {lam T : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    6000 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10) T
      ≤ 14900 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T
        + 1250 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T := by
  have hs := h3_side h0 hle
  have ha : 0 < ((26:ℝ)/10) := by norm_num
  have hα : 0 < ((26:ℝ)/10) + lam := by linarith
  have hale : ((26:ℝ)/10) ≤ ((26:ℝ)/10) + lam := by linarith
  have hfac : (((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3
      ≤ (((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
        * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3 :=
    ratio_cube3 ha hα hale
  have hle1 := Table4.P3AB_le (((26:ℝ)/10 + lam)) ((26:ℝ)/10) T hα ha hale
  have hge1 := Table4.P3AB_ge (((26:ℝ)/10 + lam)) (((26:ℝ)/10 + lam)) T hα hα le_rfl
  have hbb : 0 ≤ ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3 := by positivity
  have key : 6000 * ((8/3) * (((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3)
      ≤ 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3) := by
    have h1 : 6000 * ((((26:ℝ)/10 + lam) * ((26:ℝ)/10) / (((26:ℝ)/10)^2 + T^2))^3)
        ≤ 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
            * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3) :=
      mul_le_mul_of_nonneg_left hfac (by norm_num)
    have h2 : 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3
          * ((((26:ℝ)/10 + lam)^2) / ((((26:ℝ)/10 + lam)^2) + T^2))^3)
        ≤ 16150 * ((((26:ℝ)/10 + lam)^2 / ((((26:ℝ)/10 + lam)^2) + T^2))^3) := by
      have h3 : 6000 * ((((26:ℝ)/10 + lam) / ((26:ℝ)/10))^3) ≤ 16150 := hs
      nlinarith [h3, hbb]
    have h5 : 0 ≤ (8/3 : ℝ) := by norm_num
    nlinarith [h1, h2, h5]
  have hk : 6000 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10) T
      ≤ 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3) :=
    le_trans (mul_le_mul_of_nonneg_left hle1 (by norm_num)) key
  have hge1' : (8/3) * ((((26:ℝ)/10 + lam)^2) / (((26:ℝ)/10 + lam)^2 + T^2))^3
      ≤ Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T := by
    simpa [pow_two] using hge1
  have hfin : 16150 * ((8/3) * (((26:ℝ)/10 + lam)^2 / (((26:ℝ)/10 + lam)^2 + T^2))^3)
      ≤ 16150 * Table4.P3AB ((26:ℝ)/10 + lam) ((26:ℝ)/10 + lam) T :=
    mul_le_mul_of_nonneg_left hge1' (by norm_num)
  nlinarith [hk, hfin]

/-- **The `P₃` inequality (★) of HB §9 for cubic characters.**  *Superseded:* the engine
`Work.ZeroFreeTables.HB95_h3_engine` proves the inequality directly (with `ε` a free parameter
and the hypothesis `λ₁ ≤ 348/1000`), which is what `HBTheorem1_complex_h3` below uses.  The
abbreviation and the reduction `h3_of_HB95Ineq` are kept for reference only. -/

abbrev HB95Ineq : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 3 →
    Work.LinnikContract.lamOf q ρ₁ ≤ 7 / 10 →
      ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 100000 ∧
        0 ≤ 14379 * P3R ((26 / 10 + Work.LinnikContract.lamOf q ρ₁) / (26 / 10))
              - 24480 * P3R 1
              + 40630 * (26 / 10 + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε)

/-- **HB Theorem 1's `0.348` threshold for cubic characters, from (★).**
If `λ₁ > 7/10` there is nothing to prove; otherwise (★) contradicts the numeric core
`h3_arith`, which is the certificate of the `P₃` polynomial. -/
theorem h3_of_HB95Ineq (h : HB95Ineq) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 3 →
        (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hord => ?_⟩
  by_contra hcon
  have hcon' : Work.LinnikContract.lamOf q ρ₁ < 348 / 1000 := not_le.mp hcon
  have hle : Work.LinnikContract.lamOf q ρ₁ ≤ 7 / 10 := by linarith
  obtain ⟨ε, hε0, hε, hineq⟩ := hq₀ q hq χ₁ ρ₁ hm hord hle
  exact absurd (h3_arith (le_of_lt hcon') hε0 hε hineq) (not_le.mpr hcon')


end Work.ZeroFreeTables
