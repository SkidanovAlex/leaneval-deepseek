/-
# ZeroFreeTables/P3/WLBase — the coefficient-correct weight `hbWL` at the scale `log q`

`SigmaP3L q (Real.log q) ψ s a λ₁` is HB's `Σ(s,ψ)` of (8.4) written with the coefficient-correct
smoothing weight `u(y) = α + α²y + (1/3)α³y²` (`α = a + λ₁`, `y = log n / log q`), whose Laplace
transform is `P₃(α/z)`.  This file introduces the `n`-th summands of that functional, in the two
normal forms used by the proof of the pointwise inequality HB (9.1):

* `hbTermL` — the summand with the complex power split as `n^{-σ} · n^{-iΔ}`,
* `hbRawL` — the summand with the complex power kept whole,
* `hbSummandL` — the eight-term pointwise combination of HB (9.1),
* `hbRawSumL` — the same, written as a sum over the eight pairs `(χ^j, σ + iΔ)`,

together with the elementary facts: the bridge between the two normal forms (`ReDivCpow`), the
non-negativity of the weight, and its polynomial growth bound (`|u(y)| ≪ 1 + log n + (log n)²`).

These are the `L`-counterparts of `hbTerm`, `hbRaw`, `hbSummand`, `hbRawSum` of
`P3/Pointwise91.lean`; the only difference is the `y²`-coefficient `1/3` instead of `2/3`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.Pointwise91
import Submission.Work.ZeroFreeTables.P3.ReDivCpow
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P3

noncomputable section

/-! ## The summands -/

/-- The `n`-th summand of `SigmaP3L q (Real.log q) ψ (σ+iΔ) a λ₁` with the complex power split as
`n^{-σ} · n^{-iΔ}`: `Λ n · n^{-σ} · Re(ψ(n) n^{-iΔ}) · u(log n / log q)`. -/
def hbTermL (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (σ Δ a lam₁ : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (ψ (n : ZMod q) * hbE Δ n).re * (n : ℝ) ^ (-σ)
    * hbWL (Real.log q) a lam₁ n

/-- The `n`-th summand of `SigmaP3L q (Real.log q) ψ s a λ₁` (with the point `s` kept as a complex
variable). -/
def hbRawL (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ : ℝ) : ℕ → ℝ :=
  fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * ((ψ (n : ZMod q) / (n : ℂ) ^ s).re)
    * hbWL (Real.log q) a lam₁ n

/-- The pointwise (in `n`) combination of HB (9.1) with the coefficient-correct weight, in the
`hbTermL` normal form. -/
def hbSummandL (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ)
    (n : ℕ) : ℝ :=
  (K ^ 2 + 1/2) * (hbTermL q 1 σ 0 a lam₁ n + hbTermL q χ σ γ₀ a lam₁ n)
  + K * (hbTermL q 1 σ (γ₁ - γ₀) a lam₁ n + 2 * hbTermL q χ σ γ₁ a lam₁ n
      + hbTermL q (χ ^ 2) σ (γ₁ + γ₀) a lam₁ n)
  + (1/4) * (hbTermL q χ σ (2 * γ₁ - γ₀) a lam₁ n + 2 * hbTermL q (χ ^ 2) σ (2 * γ₁) a lam₁ n
      + hbTermL q (χ ^ 3) σ (2 * γ₁ + γ₀) a lam₁ n)

/-- The pointwise (in `n`) combination of HB (9.1) with the coefficient-correct weight, in the
`hbRawL` normal form (i.e. literally the summands of the eight `SigmaP3L` terms of
`HbCombinationL`), written as a sum over `Fin 8`. -/
def hbRawSumL (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ₀ γ₁ a lam₁ : ℝ) :
    ℕ → ℝ :=
  fun n => ∑ i : Fin 8, hbCoef K i * hbRawL q (hbChi q χ i) (hbPt σ γ₀ γ₁ i) a lam₁ n

/-! ## The two normal forms -/

/-- `SigmaP3L` at the scale `log q` is `(log q)⁻¹` times the `tsum` of `hbRawL`. -/
lemma SigmaP3L_eq_hbRawL (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (s : ℂ) (a lam₁ : ℝ) :
    SigmaP3L q (Real.log q) ψ s a lam₁
      = (Real.log q)⁻¹ * ∑' n, hbRawL q ψ s a lam₁ n := rfl

/-- The `n`-th summand of `SigmaP3L q (Real.log q) ψ (σ+iΔ) a λ₁` written with `hbE`. -/
lemma hbRawL_eq_hbTermL {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (σ Δ a lam₁ : ℝ)
    (n : ℕ) :
    hbRawL q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n = hbTermL q ψ σ Δ a lam₁ n := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    simp [hbRawL, hbTermL]
  · have hn1 : 1 ≤ n := hn
    simp only [hbRawL, hbTermL, hbE]
    rw [ReDivCpow hn1 σ Δ (ψ (n : ZMod q))]
    ring

/-! ## Positivity and growth of the weight -/

/-- The coefficient-correct weight is non-negative for `L > 0`, `a > 0`, `λ₁ ≥ 0`. -/
lemma hbWL_nonneg {L : ℝ} (hL : 0 < L) {a lam₁ : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam₁) (n : ℕ) :
    0 ≤ hbWL L a lam₁ n := by
  have hα : 0 < a + lam₁ := by linarith
  have hy : 0 ≤ Real.log n / L := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact div_nonneg (Real.log_nonneg hn1) hL.le
  have h1 : hbWL L a lam₁ n = (a + lam₁) * (1 + (a + lam₁) * (Real.log n / L)
      + (1/3) * (a + lam₁) ^ 2 * (Real.log n / L) ^ 2) := by
    unfold hbWL; ring
  rw [h1]
  exact mul_nonneg hα.le (by positivity)

/-- The coefficient-correct weight grows at most like `(log n)²`: for a scale `L ≥ log 2`,
`|u(log n / L)| ≤ C (1 + log n + (log n)²)` with `C` depending only on `a + λ₁`. -/
lemma hbWL_abs_le {L : ℝ} (hL : Real.log 2 ≤ L) (a lam₁ : ℝ) (n : ℕ) :
    |hbWL L a lam₁ n| ≤
      (|a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
        + (1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2)
        * (1 + Real.log n + (Real.log n) ^ 2) := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := lt_of_lt_of_le h2pos hL
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have h2inv : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr h2pos.le
  have hlogn : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  set y : ℝ := Real.log n / L with hydef
  have hy0 : 0 ≤ y := by rw [hydef]; exact div_nonneg hlogn hLnn
  have hy1 : y ≤ Real.log n * (Real.log 2)⁻¹ := by
    rw [hydef, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hLpos h2pos).mpr hL) hlogn
  set C : ℝ := |a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
    + (1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 with hCdef
  have hA : 0 ≤ |a + lam₁| := abs_nonneg _
  have hA2 : 0 ≤ |a + lam₁| ^ 2 := sq_nonneg _
  have h21 : 0 ≤ |a + lam₁| ^ 2 * (Real.log 2)⁻¹ := mul_nonneg hA2 h2inv
  have h32 : 0 ≤ (1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 := by positivity
  have hC1 : |a + lam₁| ≤ C := by rw [hCdef]; linarith
  have hC2 : |a + lam₁| ^ 2 * (Real.log 2)⁻¹ ≤ C := by rw [hCdef]; linarith
  have hC3 : (1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2 ≤ C := by rw [hCdef]; linarith
  have hunwrap : hbWL L a lam₁ n
      = (a + lam₁) + (a + lam₁) ^ 2 * y + (1/3) * (a + lam₁) ^ 3 * y ^ 2 := by
    rw [hydef]; rfl
  have key : |hbWL L a lam₁ n| ≤
      |a + lam₁| + |a + lam₁| ^ 2 * y + (1/3) * |a + lam₁| ^ 3 * y ^ 2 := by
    rw [hunwrap]
    have h1 := abs_add_le ((a + lam₁) + (a + lam₁) ^ 2 * y) ((1/3) * (a + lam₁) ^ 3 * y ^ 2)
    have h2 := abs_add_le (a + lam₁) ((a + lam₁) ^ 2 * y)
    have e2 : |(a + lam₁) ^ 2 * y| = |a + lam₁| ^ 2 * y := by
      rw [abs_mul, abs_pow, abs_of_nonneg hy0]
    have e3 : |(1/3) * (a + lam₁) ^ 3 * y ^ 2| = (1/3) * |a + lam₁| ^ 3 * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hy0,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)]
    linarith [h1, h2]
  have hy2 : y ^ 2 ≤ (Real.log n * (Real.log 2)⁻¹) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have hstep : |a + lam₁| + |a + lam₁| ^ 2 * y + (1/3) * |a + lam₁| ^ 3 * y ^ 2
      ≤ |a + lam₁| + |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹)
        + (1/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2 := by
    have hA' : |a + lam₁| ^ 2 * y ≤ |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hy1 hA2
    have hB' : (1/3) * |a + lam₁| ^ 3 * y ^ 2
        ≤ (1/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hy2 (by positivity)
    linarith
  refine key.trans (hstep.trans ?_)
  have e1 : |a + lam₁| ≤ C * 1 := by simpa using hC1
  have e2 : |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹) ≤ C * Real.log n := by
    calc |a + lam₁| ^ 2 * (Real.log n * (Real.log 2)⁻¹)
        = (|a + lam₁| ^ 2 * (Real.log 2)⁻¹) * Real.log n := by ring
      _ ≤ C * Real.log n := mul_le_mul_of_nonneg_right hC2 hlogn
  have e3 : (1/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2
      ≤ C * (Real.log n) ^ 2 := by
    calc (1/3) * |a + lam₁| ^ 3 * (Real.log n * (Real.log 2)⁻¹) ^ 2
        = ((1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2) * (Real.log n) ^ 2 := by ring
      _ ≤ C * (Real.log n) ^ 2 := mul_le_mul_of_nonneg_right hC3 (sq_nonneg _)
  have hfin : C * 1 + C * Real.log n + C * (Real.log n) ^ 2
      = C * (1 + Real.log n + (Real.log n) ^ 2) := by ring
  linarith [e1, e2, e3, hfin]

/-- The `n`-th summand of `SigmaP3L` (in its raw form) is dominated by
`Λ n · n^{-σ} · |u(log n / log q)|`. -/
lemma hbRawL_abs_le {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 0 < σ)
    (Δ a lam₁ : ℝ) (n : ℕ) :
    |hbRawL q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n|
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * |hbWL (Real.log q) a lam₁ n| := by
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
  rw [hbRawL, abs_mul, abs_mul, abs_of_nonneg hΛ]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hΛ) (abs_nonneg _)

end

end Work.ZeroFreeTables.P3
