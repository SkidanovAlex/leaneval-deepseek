/-
# ZeroFreeTables/P3/Pointwise91 — HB (9.1): the pointwise kernel expansion, summed

Heath-Brown's Lemma 9.1 rests on the pointwise (in `n`) inequality

  `0 ≤ χ₀(n) (1 + Re z₀) (K + Re z₁)²`,   `z_j = χ(n) n^{-iγ_j}`,

whose expansion — grouped by the eight pairs `(χ^j, σ + iΔ)` of the argument points `σ`, `σ+iγ₀`,
`σ+i(γ₁−γ₀)`, `σ+iγ₁`, `σ+i(γ₁+γ₀)`, `σ+i(2γ₁−γ₀)`, `σ+2iγ₁`, `σ+i(2γ₁+γ₀)` and the characters
`χ⁰, χ, χ⁰, χ, χ², χ, χ², χ³` with the coefficients `(K²+½), (K²+½), K, 2K, K, ¼, ½, ¼` —
is exactly HB (9.1):

  `0 ≤ HbCombination q χ K σ γ₀ γ₁ a λ₁`.

This file proves that inequality by

* rewriting the eight `SigmaP3` summands as `Λ n · n^{-σ} Re(χ^j(n) n^{-iΔ}) · u(log n / log q)`
  (`hbRaw`, via `ReDivCpow`),
* identifying the eight-term pointwise combination `hbSummand` with
  `Λ n · n^{-σ} · u(log n/log q) · hbKernel K (χ(n)n^{-iγ₀}) (χ(n)n^{-iγ₁})`,
  using the algebraic kernel identity `HbKernelIdentity` on the unit circle and the
  multiplicativity `hbE_add` of the exponential factor, together with the vanishing of all
  summands at non-units `n`,
* showing `hbKernel` is non-negative, `0 ≤ u(log n/log q)` (for `q ≥ 2`, `a > 0`, `λ₁ ≥ 0`),
* and finally linearising the eight absolutely convergent `tsum`s (absolute convergence of
  `Σ Λ(n)(log n)^A n^{-σ}`, `SummableVonMangoldtLogPow`) so that
  `HbCombination` is `(log q)⁻¹` times a `tsum` of non-negative terms (`q ≥ 2`); `q = 1` is
  trivial since then `log q = 0` kills every `SigmaP3`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.Defs
import Submission.Work.ZeroFreeTables.P3.HbKernelIdentity
import Submission.Work.ZeroFreeTables.P3.ReDivCpow
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P3

noncomputable section

/-! ## The exponential factor, the weight, and the summands of `HbCombination` -/

/-- `n^{-iΔ} = exp(-i Δ log n)`: the exponential factor by which `χ(n)` is multiplied in the
`n`-th summand of `Σ(σ + iΔ, χ)` (the factor `n^{-iΔ}` of the complex power `n^{-σ-iΔ}`). -/
def hbE (Δ : ℝ) (n : ℕ) : ℂ := Complex.exp ((((-(Δ * Real.log n)) : ℝ) : ℂ) * Complex.I)

/-- HB's smoothing weight `u(log n / 𝓛)` of (8.4), `𝓛 = log q`, inside `SigmaP3`. -/
def hbW (q : ℕ) (a lam₁ : ℝ) (n : ℕ) : ℝ :=
  (a + lam₁) + (a + lam₁) ^ 2 * (Real.log n / Real.log q)
    + (2/3) * (a + lam₁) ^ 3 * (Real.log n / Real.log q) ^ 2

/-- The `n`-th summand of `SigmaP3 q ψ (σ + iΔ) a λ₁` with the complex power split as
`n^{-σ} · n^{-iΔ}`: `Λ n · n^{-σ} · Re(ψ(n) n^{-iΔ}) · u(log n / log q)`. -/
def hbTerm (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (σ Δ a lam₁ : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (ψ (n : ZMod q) * hbE Δ n).re * (n : ℝ) ^ (-σ)
    * hbW q a lam₁ n

/-- The `n`-th summand of `SigmaP3 q ψ s a λ₁` (with the point `s` kept as a complex variable). -/
def hbRaw (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ : ℝ) : ℕ → ℝ :=
  fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * ((ψ (n : ZMod q) / (n : ℂ) ^ s).re)
    * hbW q a lam₁ n

/-- The pointwise kernel `(K²+½)(1+Re z₀) + K(Re(z₁/z₀) + 2Re z₁ + Re(z₁z₀))
+ ¼(Re(z₁²/z₀) + 2Re(z₁²) + Re(z₁²z₀))`; by `HbKernelIdentity` it equals
`(1 + Re z₀)(K + Re z₁)²` for `z₀, z₁` of modulus one. -/
def hbKernel (K : ℝ) (z₀ z₁ : ℂ) : ℝ :=
  (K ^ 2 + 1/2) * (1 + z₀.re) + K * ((z₁ / z₀).re + 2 * z₁.re + (z₁ * z₀).re)
    + (1/4) * ((z₁ ^ 2 / z₀).re + 2 * (z₁ ^ 2).re + (z₁ ^ 2 * z₀).re)

/-- The pointwise (in `n`) combination of HB (9.1), in the `hbTerm` normal form. -/
def hbSummand (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) : ℝ :=
  (K ^ 2 + 1/2) * (hbTerm q 1 σ 0 a lam₁ n + hbTerm q χ σ γ₀ a lam₁ n)
  + K * (hbTerm q 1 σ (γ₁ - γ₀) a lam₁ n + 2 * hbTerm q χ σ γ₁ a lam₁ n
      + hbTerm q (χ ^ 2) σ (γ₁ + γ₀) a lam₁ n)
  + (1/4) * (hbTerm q χ σ (2 * γ₁ - γ₀) a lam₁ n + 2 * hbTerm q (χ ^ 2) σ (2 * γ₁) a lam₁ n
      + hbTerm q (χ ^ 3) σ (2 * γ₁ + γ₀) a lam₁ n)

/-- The eight characters of HB (9.1), as a function of the index `Fin 8`. -/
def hbChi (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : Fin 8 → DirichletCharacter ℂ q :=
  ![1, χ, 1, χ, χ ^ 2, χ, χ ^ 2, χ ^ 3]

/-- The eight imaginary parts `Δ` of the argument points `σ + iΔ` of HB (9.1). -/
def hbDl (γ₀ γ₁ : ℝ) : Fin 8 → ℝ :=
  ![0, γ₀, γ₁ - γ₀, γ₁, γ₁ + γ₀, 2 * γ₁ - γ₀, 2 * γ₁, 2 * γ₁ + γ₀]

/-- The eight argument points of HB (9.1), as a function of the index `Fin 8`. -/
def hbPt (σ γ₀ γ₁ : ℝ) : Fin 8 → ℂ :=
  fun i => (σ : ℂ) + ((hbDl γ₀ γ₁ i : ℝ) : ℂ) * Complex.I

/-- The eight coefficients of HB (9.1), as a function of the index `Fin 8`. -/
def hbCoef (K : ℝ) : Fin 8 → ℝ :=
  ![K ^ 2 + 1/2, K ^ 2 + 1/2, K, 2 * K, K, 1/4, 1/2, 1/4]

/-- The pointwise (in `n`) combination of HB (9.1), in the `hbRaw` normal form (i.e. literally
the summands of the eight `SigmaP3` terms of `HbCombination`), written as a sum over `Fin 8`. -/
def hbRawSum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ) :
    ℕ → ℝ :=
  fun n => ∑ i : Fin 8, hbCoef K i * hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n

/-! ## The exponential factor `hbE` -/

@[simp] lemma hbE_zero (n : ℕ) : hbE 0 n = 1 := by simp [hbE]

lemma hbE_add (Δ Δ' : ℝ) (n : ℕ) : hbE Δ n * hbE Δ' n = hbE (Δ + Δ') n := by
  unfold hbE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma hbE_ne_zero (Δ : ℝ) (n : ℕ) : hbE Δ n ≠ 0 := Complex.exp_ne_zero _

lemma hbE_norm (Δ : ℝ) (n : ℕ) : ‖hbE Δ n‖ = 1 := by
  rw [hbE, Complex.norm_exp]
  have h : ((((-(Δ * Real.log n)) : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero]
  rw [h, Real.exp_zero]

lemma hbE_sub_div (Δ Δ' : ℝ) (n : ℕ) : hbE (Δ - Δ') n = hbE Δ n / hbE Δ' n := by
  rw [eq_div_iff (hbE_ne_zero Δ' n)]
  rw [hbE_add]
  congr 1
  ring

lemma hbE_two (Δ : ℝ) (n : ℕ) : hbE (2 * Δ) n = hbE Δ n ^ 2 := by
  have h : (2 : ℝ) * Δ = Δ + Δ := by ring
  rw [h, ← hbE_add Δ Δ n, pow_two]

lemma hbE_two_sub (Δ Δ' : ℝ) (n : ℕ) : hbE (2 * Δ - Δ') n = hbE Δ n ^ 2 / hbE Δ' n := by
  rw [hbE_sub_div (2 * Δ) Δ' n, hbE_two]

lemma hbE_two_add (Δ Δ' : ℝ) (n : ℕ) : hbE (2 * Δ + Δ') n = hbE Δ n ^ 2 * hbE Δ' n := by
  rw [← hbE_add (2 * Δ) Δ' n, hbE_two]

/-! ## Positivity of the weight and of the kernel -/

lemma hbW_nonneg {q : ℕ} (hq : 2 ≤ q) {a lam₁ : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam₁) (n : ℕ) :
    0 ≤ hbW q a lam₁ n := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hqpos : 0 < Real.log q := Real.log_pos hq1
  have hα : 0 < a + lam₁ := by linarith
  have hy : 0 ≤ Real.log n / Real.log q := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact div_nonneg (Real.log_nonneg hn1) hqpos.le
  have h1 : hbW q a lam₁ n = (a + lam₁) * (1 + (a + lam₁) * (Real.log n / Real.log q)
      + (2/3) * (a + lam₁) ^ 2 * (Real.log n / Real.log q) ^ 2) := by
    unfold hbW; ring
  rw [h1]
  exact mul_nonneg hα.le (by positivity)

lemma hbKernel_nonneg (K : ℝ) (z₀ z₁ : ℂ) (h₀ : ‖z₀‖ = 1) (h₁ : ‖z₁‖ = 1) :
    0 ≤ hbKernel K z₀ z₁ := by
  rw [hbKernel, HbKernelIdentity K z₀ z₁ h₀ h₁]
  refine mul_nonneg ?_ (sq_nonneg _)
  have h := Complex.re_le_norm (-z₀)
  rw [Complex.neg_re, norm_neg, h₀] at h
  linarith

/-- The algebraic bridge between the "expanded" kernel (the shape produced by the eight summands
of HB (9.1)) and `hbKernel`. -/
lemma kernel_expand (K : ℝ) (c u v : ℂ) (hc : c ≠ 0) (hu : u ≠ 0) :
    (K ^ 2 + 1/2) * (1 + (c * u).re) + K * ((v / u).re + 2 * (c * v).re + (c ^ 2 * (v * u)).re)
      + (1/4) * ((c * (v ^ 2 / u)).re + 2 * (c ^ 2 * v ^ 2).re + (c ^ 3 * (v ^ 2 * u)).re)
    = hbKernel K (c * u) (c * v) := by
  rw [hbKernel]
  have e1 : (c * v) / (c * u) = v / u := by
    rw [div_eq_div_iff (mul_ne_zero hc hu) hu]; ring
  have e3 : (c * v) ^ 2 / (c * u) = c * (v ^ 2 / u) := by
    rw [← mul_div_assoc]
    rw [div_eq_div_iff (mul_ne_zero hc hu) hu]; ring
  have e4 : (c * v) ^ 2 * (c * u) = c ^ 3 * (v ^ 2 * u) := by ring_nf
  have e5 : (c * v) ^ 2 = c ^ 2 * v ^ 2 := by ring_nf
  have e2 : (c * v) * (c * u) = c ^ 2 * (v * u) := by ring_nf
  rw [e4, e1, e3, e5, e2]

/-! ## The `n`-th summand of `SigmaP3`, in the two normal forms -/

/-- `SigmaP3` is `(log q)⁻¹` times the `tsum` of `hbRaw`. -/
lemma SigmaP3_eq_hbRaw (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ : ℝ) :
    SigmaP3 q ψ s a lam₁ = (Real.log q)⁻¹ * ∑' n, hbRaw q ψ s a lam₁ n := rfl

/-- The `n`-th summand of `SigmaP3 q ψ (σ+iΔ) a λ₁` written with `hbE`. -/
lemma hbRaw_eq_hbTerm {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (σ Δ a lam₁ : ℝ)
    (n : ℕ) :
    hbRaw q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n = hbTerm q ψ σ Δ a lam₁ n := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    simp [hbRaw, hbTerm]
  · have hn1 : 1 ≤ n := hn
    simp only [hbRaw, hbTerm, hbE]
    rw [ReDivCpow hn1 σ Δ (ψ (n : ZMod q))]
    ring

/-! ## Summability of the summands -/

/-- The weight `u(log n/log q)` grows at most like `(log n)²`. -/
lemma hbW_abs_le {q : ℕ} (hq : 1 ≤ q) (a lam₁ : ℝ) (n : ℕ) :
    |hbW q a lam₁ n| ≤
      (|a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
        + (2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2)
        * (1 + Real.log n + (Real.log n) ^ 2) := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2inv : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr h2pos.le
  have hlogn : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  set y : ℝ := Real.log n / Real.log q with hydef
  have hy0 : 0 ≤ y := div_nonneg hlogn hlogq
  have hy1 : y ≤ Real.log n * (Real.log 2)⁻¹ := by
    rcases eq_or_lt_of_le hq with hq1 | hq2
    · subst hq1
      rw [hydef, Nat.cast_one, Real.log_one, div_zero]
      exact mul_nonneg hlogn h2inv
    · have hlog2q : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
      have hlogqpos : 0 < Real.log q := lt_of_lt_of_le h2pos hlog2q
      rw [hydef, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hlogqpos h2pos).mpr hlog2q) hlogn
  set C : ℝ := |a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
    + (2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 with hCdef
  have hA : 0 ≤ |a + lam₁| := abs_nonneg _
  have hA2 : 0 ≤ |a + lam₁| ^ 2 := sq_nonneg _
  have h21 : 0 ≤ |a + lam₁| ^ 2 * (Real.log 2)⁻¹ := mul_nonneg hA2 h2inv
  have h32 : 0 ≤ (2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 := by positivity
  have hC1 : |a + lam₁| ≤ C := by rw [hCdef]; linarith
  have hC2 : |a + lam₁| ^ 2 * (Real.log 2)⁻¹ ≤ C := by rw [hCdef]; linarith
  have hC3 : (2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 ≤ C := by rw [hCdef]; linarith
  have key : |hbW q a lam₁ n| ≤
      |a + lam₁| + |a + lam₁| ^ 2 * y + (2/3) * |a + lam₁| ^ 3 * y ^ 2 := by
    rw [hbW]
    have h1 := abs_add_le ((a + lam₁) + (a + lam₁) ^ 2 * y) ((2/3) * (a + lam₁) ^ 3 * y ^ 2)
    have h2 := abs_add_le (a + lam₁) ((a + lam₁) ^ 2 * y)
    have e2 : |(a + lam₁) ^ 2 * y| = |a + lam₁| ^ 2 * y := by
      rw [abs_mul, abs_pow, abs_of_nonneg hy0]
    have e3 : |(2/3) * (a + lam₁) ^ 3 * y ^ 2| = (2/3) * |a + lam₁| ^ 3 * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hy0,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)/3)]
    linarith [h1, h2]
  have hy2 : y ^ 2 ≤ (Real.log n * (Real.log 2)⁻¹) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have hstep : |a + lam₁| + |a + lam₁| ^ 2 * y + (2/3) * |a + lam₁| ^ 3 * y ^ 2
      ≤ |a + lam₁| + |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹)
        + (2/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2 := by
    have hA' : |a + lam₁| ^ 2 * y ≤ |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hy1 hA2
    have hB' : (2/3) * |a + lam₁| ^ 3 * y ^ 2
        ≤ (2/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hy2 (by positivity)
    linarith
  refine key.trans (hstep.trans ?_)
  have e1 : |a + lam₁| ≤ C * 1 := by simpa using hC1
  have e2 : |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹) ≤ C * Real.log n := by
    calc |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹)
        = (|a + lam₁| ^ 2 * (Real.log 2)⁻¹) * Real.log n := by ring
      _ ≤ C * Real.log n := mul_le_mul_of_nonneg_right hC2 hlogn
  have e3 : (2/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2
      ≤ C * (Real.log n) ^ 2 := by
    calc (2/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2
        = ((2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2) * (Real.log n) ^ 2 := by ring
      _ ≤ C * (Real.log n) ^ 2 := mul_le_mul_of_nonneg_right hC3 (sq_nonneg _)
  have hfin : C * 1 + C * Real.log n + C * (Real.log n) ^ 2
      = C * (1 + Real.log n + (Real.log n) ^ 2) := by ring
  linarith [e1, e2, e3, hfin]

/-- The `n`-th summand of `SigmaP3` is dominated by `Λ n · n^{-σ} · |u(log n / log q)|`. -/
lemma hbRaw_abs_le {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 0 < σ)
    (Δ a lam₁ : ℝ) (n : ℕ) :
    |hbRaw q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n|
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * |hbW q a lam₁ n| := by
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have h1 : |(ψ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)).re|
      ≤ (n : ℝ) ^ (-σ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hsne : ((σ : ℂ) + (Δ : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hz : ‖ψ (((0 : ℕ)) : ZMod q) / ((0 : ℕ) : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)‖
          = 0 := by
        have h0s : (((0 : ℕ)) : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I) = 0 := by
          rw [Nat.cast_zero]; exact Complex.zero_cpow hsne
        rw [h0s, div_zero, norm_zero]
      have hz2 : (((0 : ℕ) : ℝ)) ^ (-σ) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
      rw [hz, hz2]
    · have hnp : (0 : ℝ) < n := by exact_mod_cast hn
      have hnorm : ‖(((n : ℝ)) : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)‖ = (n : ℝ) ^ σ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hnp]
        simp
      rw [← Complex.ofReal_natCast n, Complex.norm_div, hnorm]
      calc ‖ψ (n : ZMod q)‖ / (n : ℝ) ^ σ ≤ 1 / (n : ℝ) ^ σ :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ (n : ZMod q))
              (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
        _ = (n : ℝ) ^ (-σ) := by rw [Real.rpow_neg (Nat.cast_nonneg n)]; ring
  rw [hbRaw, abs_mul, abs_mul, abs_of_nonneg hΛ]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hΛ) (abs_nonneg _)

lemma summable_hbRaw {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (Δ a lam₁ : ℝ) :
    Summable (hbRaw q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h0 := SummableVonMangoldtLogPow (σ := σ) hσ 0
  have h1 := SummableVonMangoldtLogPow (σ := σ) hσ 1
  have h2 := SummableVonMangoldtLogPow (σ := σ) hσ 2
  set C : ℝ := |a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
    + (2/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 with hCdef
  have hdom : Summable (fun n : ℕ => C *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ)) :=
    ((h0.add h1).add h2).mul_left C
  refine Summable.of_norm_bounded hdom (fun n => ?_)
  rw [Real.norm_eq_abs]
  refine (hbRaw_abs_le ψ (by linarith : (0:ℝ) < σ) Δ a lam₁ n).trans ?_
  have hW := hbW_abs_le hq1 a lam₁ n
  refine (mul_le_mul_of_nonneg_left hW (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Real.log_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hnr.le, div_eq_mul_inv, hCdef]
    exact le_of_eq (by ring)

lemma summable_hbRaw' {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re)
    (a lam₁ : ℝ) : Summable (hbRaw q ψ s a lam₁) := by
  have h := summable_hbRaw (q := q) ψ hs s.im a lam₁
  rwa [Complex.re_add_im s] at h

lemma summable_hbTerm {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (Δ a lam₁ : ℝ) : Summable (hbTerm q ψ σ Δ a lam₁) :=
  (summable_hbRaw (q := q) ψ hσ Δ a lam₁).congr
    (fun n => hbRaw_eq_hbTerm ψ σ Δ a lam₁ n)

/-- Summability of the eight summand families of HB (9.1). -/
lemma summable_hbChi (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (γ₀ γ₁ a lam₁ : ℝ) (i : Fin 8) :
    Summable (hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁) := by
  fin_cases i <;>
    · simp only [hbChi, hbPt, hbDl]
      simp
      exact summable_hbRaw' _ (by simpa using hσ) _ _

/-! ## The pointwise identity -/

/-- For a unit `n` modulo `q` the eight summands of HB (9.1) combine, at the level of the single
integer `n`, into `Λ n · n^{-σ} · u(log n / log q) · hbKernel K (χ(n)n^{-iγ₀}) (χ(n)n^{-iγ₁})`. -/
lemma hbSummand_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) (hunit : IsUnit (n : ZMod q)) :
    hbSummand q χ K σ γ₀ γ₁ a lam₁ n
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * hbW q a lam₁ n
        * hbKernel K (χ (n : ZMod q) * hbE γ₀ n) (χ (n : ZMod q) * hbE γ₁ n) := by
  have hc : χ (n : ZMod q) ≠ 0 := MulChar.apply_ne_zero_iff.mpr hunit
  have hu : hbE γ₀ n ≠ 0 := hbE_ne_zero _ _
  rw [← kernel_expand K (χ (n : ZMod q)) (hbE γ₀ n) (hbE γ₁ n) hc hu]
  rw [hbSummand]
  simp only [hbTerm]
  rw [MulChar.one_apply hunit, MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0),
      MulChar.pow_apply' χ (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hbE_zero, hbE_sub_div γ₁ γ₀ n, hbE_add γ₁ γ₀ n, hbE_two_sub γ₁ γ₀ n, hbE_two γ₁ n,
    hbE_two_add γ₁ γ₀ n]
  simp only [one_mul, Complex.one_re]
  ring

/-- At a non-unit `n` modulo `q` every Dirichlet character vanishes, hence every summand of
HB (9.1) vanishes. -/
lemma hbSummand_nonunit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) (hunit : ¬ IsUnit (n : ZMod q)) :
    hbSummand q χ K σ γ₀ γ₁ a lam₁ n = 0 := by
  have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ (n : ZMod q) = 0 :=
    fun ψ => MulChar.map_nonunit ψ hunit
  simp [hbSummand, hbTerm, h0]

lemma norm_char_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hunit : IsUnit (n : ZMod q)) : ‖χ (n : ZMod q)‖ = 1 := by
  have h : (↑hunit.unit : ZMod q) = (n : ZMod q) := hunit.unit_spec
  rw [← h]
  exact DirichletCharacter.unit_norm_eq_one χ hunit.unit

lemma hbSummand_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K σ γ₀ γ₁ a lam₁ : ℝ}
    (hq : 2 ≤ q) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) (n : ℕ) :
    0 ≤ hbSummand q χ K σ γ₀ γ₁ a lam₁ n := by
  by_cases hunit : IsUnit (n : ZMod q)
  · rw [hbSummand_unit χ K σ γ₀ γ₁ a lam₁ n hunit]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact hbW_nonneg hq ha hlam n
    · exact hbKernel_nonneg K _ _
        (by rw [norm_mul, norm_char_unit χ hunit, hbE_norm, one_mul])
        (by rw [norm_mul, norm_char_unit χ hunit, hbE_norm, one_mul])
  · rw [hbSummand_nonunit χ K σ γ₀ γ₁ a lam₁ n hunit]

/-! ## Linearisation of the eight `tsum`s -/

/-- Linearity of `tsum` over a finite sum of absolutely convergent series. -/
lemma tsum_finset_lincomb {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (c : ι → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑ i ∈ s, c i * ∑' n, f i n) = ∑' n, ∑ i ∈ s, c i * f i n := by
  rw [Summable.tsum_finsetSum (fun i hi => (hf i hi).mul_left (c i))]
  simp [tsum_mul_left]

lemma hbRawSum_eq_finsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) :
    hbRawSum q χ K σ γ₀ γ₁ a lam₁ n
      = ∑ i : Fin 8, hbCoef K i * hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n := rfl

lemma HbCombination_eq_finsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) :
    HbCombination q χ K σ γ₀ γ₁ a lam₁
      = (Real.log q)⁻¹ * ∑ i : Fin 8, hbCoef K i
          * (∑' n, hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n) := by
  simp only [HbCombination, SigmaP3_eq_hbRaw, hbChi, hbPt, hbCoef, hbDl, Fin.sum_univ_eight]
  simp
  ring

lemma tsum_hbRawSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K σ γ₀ γ₁ a lam₁ : ℝ}
    (hσ : 1 < σ) :
    (∑' n, hbRawSum q χ K σ γ₀ γ₁ a lam₁ n)
      = ∑ i : Fin 8, hbCoef K i
          * (∑' n, hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n) := by
  rw [tsum_finset_lincomb Finset.univ
    (fun i => hbRaw q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁) (hbCoef K)
    (fun i _ => summable_hbChi q χ hσ γ₀ γ₁ a lam₁ i)]
  rfl

/-- The two normal forms of the pointwise combination of HB (9.1) agree: termwise, the eight
`SigmaP3` summands combine into the eight `hbTerm` summands of `hbSummand`. -/
lemma hbRawSum_eq_hbSummand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) (n : ℕ) :
    hbRawSum q χ K σ γ₀ γ₁ a lam₁ n = hbSummand q χ K σ γ₀ γ₁ a lam₁ n := by
  simp only [hbRawSum, hbSummand, hbChi, hbCoef, hbDl, hbPt, Fin.sum_univ_eight, hbRaw_eq_hbTerm]
  simp
  ring

/-- `∑' n, hbSummand n = ∑' n, hbRawSum n`, termwise. -/
lemma tsum_hbSummand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ) :
    (∑' n, hbSummand q χ K σ γ₀ γ₁ a lam₁ n)
      = ∑' n, hbRawSum q χ K σ γ₀ γ₁ a lam₁ n := by
  apply tsum_congr
  intro n
  exact (hbRawSum_eq_hbSummand χ K σ γ₀ γ₁ a lam₁ n).symm

/-! ## The main statement -/

theorem Pointwise91 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ₀ γ₁ a lam₁ : ℝ) (hK : 0 ≤ K) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) :
    0 ≤ Work.ZeroFreeTables.HbCombination q χ K σ γ₀ γ₁ a lam₁ := by
  rcases eq_or_ne q 1 with hq1 | hq1
  · subst hq1
    simp [HbCombination, SigmaP3]
  · have hq2 : 2 ≤ q := by
      have hq0 : 0 < q := NeZero.pos q
      omega
    have hlogq : 0 ≤ (Real.log q)⁻¹ :=
      inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))
    rw [HbCombination_eq_finsum, ← tsum_hbRawSum χ hσ, ← tsum_hbSummand_eq χ K σ γ₀ γ₁ a lam₁]
    exact mul_nonneg hlogq (tsum_nonneg (fun n => hbSummand_nonneg χ hq2 hσ ha hlam n))

end

end Work.ZeroFreeTables.P3
