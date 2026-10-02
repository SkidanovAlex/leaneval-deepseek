import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.API
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.ZeroFreeTables.Rep9.Algebra

open DirichletCharacter Complex
open scoped Classical BigOperators
open Work.LinnikContract

namespace Work.ZeroFreeTables.Rep9

noncomputable section

set_option maxHeartbeats 1000000

/-- The four characters `1, χ, χ², χ³` of the diagonal combination of HB (9.1). -/
def dChi (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : Fin 4 → DirichletCharacter ℂ q :=
  ![1, χ, χ ^ 2, χ ^ 3]

/-- The four imaginary parts `0, γ, 2γ, 3γ` of the diagonal argument points. -/
def dDl (γ : ℝ) : Fin 4 → ℝ := ![0, γ, 2 * γ, 3 * γ]

/-- The four coefficients `K²+K+½, K²+2K+¾, K+½, ¼` of the diagonal combination. -/
def dCoef (K : ℝ) : Fin 4 → ℝ :=
  ![K ^ 2 + K + 1 / 2, K ^ 2 + 2 * K + 3 / 4, K + 1 / 2, 1 / 4]

/-- The `n`-th pointwise combination of the four diagonal summands, in the `hbRawL` normal form
(literally the summands of the four `SigmaP3L` terms of the diagonal combination). -/
def dRawSum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (K σ γ a lam₁ : ℝ)
    (n : ℕ) : ℝ :=
  ∑ i : Fin 4, dCoef K i *
    Work.ZeroFreeTables.P3.hbRawL q (dChi q χ i)
      ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I) a lam₁ n

/-- The target expression is `(log q)⁻¹` times the finite combination of the four absolutely
convergent `tsum`s of the diagonal summands. -/
lemma combination_diag_eq_finsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ a lam₁ : ℝ) :
    (K ^ 2 + K + 1 / 2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
      + (K ^ 2 + 2 * K + 3 / 4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ
          ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
      + (K + 1 / 2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ ^ 2)
          ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) a lam₁
      + (1 / 4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ ^ 3)
          ((σ : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) a lam₁
    = (Real.log q)⁻¹ * ∑ i : Fin 4, dCoef K i *
        (∑' n, Work.ZeroFreeTables.P3.hbRawL q (dChi q χ i)
          ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I) a lam₁ n) := by
  simp only [Work.ZeroFreeTables.P3.SigmaP3L_eq_hbRawL, Fin.sum_univ_four, dCoef, dChi, dDl]
  simp
  ring

/-- Linearity of `tsum` over the four absolutely convergent series of the diagonal combination. -/
lemma tsum_dRawSum_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (K γ a lam₁ : ℝ) :
    (∑' n, dRawSum q χ K σ γ a lam₁ n)
      = ∑ i : Fin 4, dCoef K i *
          (∑' n, Work.ZeroFreeTables.P3.hbRawL q (dChi q χ i)
            ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I) a lam₁ n) := by
  rw [Work.ZeroFreeTables.P3.tsum_finset_lincomb Finset.univ
      (fun i => Work.ZeroFreeTables.P3.hbRawL q (dChi q χ i)
        ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I) a lam₁)
      (dCoef K)
      (fun i _ => Work.ZeroFreeTables.P9.summable_hbRawL' (q := q) (ψ := dChi q χ i)
        (s := ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I)) hq
        (by have h : ((σ : ℂ) + ((dDl γ i : ℝ) : ℂ) * Complex.I).re = σ := by
              simp [Complex.add_re, Complex.mul_re]
            rw [h]; exact hσ) a lam₁)]
  rfl

/-- The two normal forms of the pointwise (in `n`) diagonal combination agree: the four `hbRawL`
summands of the diagonal `SigmaP3L` terms combine into the corresponding `hbSummandL` at
`γ₀ = γ₁ = γ`. -/
lemma dRawSum_eq_hbSummandL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K σ γ a lam₁ : ℝ) (n : ℕ) :
    dRawSum q χ K σ γ a lam₁ n
      = Work.ZeroFreeTables.P3.hbSummandL q χ K σ γ γ a lam₁ n := by
  have h1 : (γ - γ : ℝ) = 0 := by ring
  have h2 : (γ + γ : ℝ) = 2 * γ := by ring
  have h3 : (2 * γ - γ : ℝ) = γ := by ring
  have h4 : (2 * γ + γ : ℝ) = 3 * γ := by ring
  simp only [dRawSum, dCoef, dChi, dDl, Fin.sum_univ_four, Work.ZeroFreeTables.P3.hbSummandL,
    Work.ZeroFreeTables.P3.hbRawL_eq_hbTermL]
  rw [h1, h2, h3, h4]
  simp
  ring

theorem combination_diag {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) {a lam₁ γ K : ℝ}
    (hq : 2 ≤ q) (ha : 0 < a) (hK : 0 < K) (hγ : |γ| ≤ 1) (hlam : 0 ≤ lam₁)
    (hχ₁ : χ₁ ≠ 1) :
    0 ≤ (K^2 + K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
          (((1 + a / Real.log q : ℝ)) : ℂ) a lam₁
      + (K^2 + 2*K + 3/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
          ((((1 + a / Real.log q : ℝ)) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I) a lam₁
      + (K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^2)
          ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*γ : ℝ)) : ℂ) * Complex.I) a lam₁
      + (1/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^3)
          ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*γ : ℝ)) : ℂ) * Complex.I) a lam₁ := by
  have hlogq_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hσ : 1 < (1 + a / Real.log q : ℝ) := by
    have : 0 < a / Real.log q := div_pos ha hlogq_pos
    linarith only [this]
  have hlogq_inv : 0 ≤ (Real.log q)⁻¹ := le_of_lt (inv_pos.mpr hlogq_pos)
  have key :
      (K^2 + K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
            (((1 + a / Real.log q : ℝ)) : ℂ) a lam₁
        + (K^2 + 2*K + 3/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
            ((((1 + a / Real.log q : ℝ)) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I) a lam₁
        + (K + 1/2) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^2)
            ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*γ : ℝ)) : ℂ) * Complex.I) a lam₁
        + (1/4) * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁^3)
            ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*γ : ℝ)) : ℂ) * Complex.I) a lam₁
      = (Real.log q)⁻¹
        * ∑' n, Work.ZeroFreeTables.P3.hbSummandL q χ₁ K (1 + a / Real.log q) γ γ a lam₁ n := by
    rw [combination_diag_eq_finsum (χ := χ₁) (K := K) (σ := 1 + a / Real.log q) (γ := γ)
      (a := a) (lam₁ := lam₁)]
    rw [← tsum_dRawSum_eq (q := q) hq χ₁ (σ := 1 + a / Real.log q) hσ K γ a lam₁]
    congr 1
    exact tsum_congr (fun n => dRawSum_eq_hbSummandL χ₁ K (1 + a / Real.log q) γ a lam₁ n)
  rw [key]
  exact mul_nonneg hlogq_inv
    (tsum_nonneg (fun n => Work.ZeroFreeTables.P9.hbSummandL_nonneg χ₁ hq hσ ha hlam n))


/-! ## The diagonal §9 assembly (the consumer of `combination_diag`) -/


/-! ## Supporting estimates for the principal-character contributions

The diagonal combination hits the *principal* character at a point `σ+iθ` whenever one of
`χ₁², χ₁³` is trivial (the order-2 and order-3 cases of HB §9).  There `Σ(σ+iθ,χ₀)` is bounded
by the pole term `Re P₃(α/((s−1)L))`, which the §9 slack `slack₀ = K²+K+1 − K·Kond K` must
absorb.  The three lemmas below supply exactly that: a growth bound for `Re P₃` along the ray
`α/(a+iθ)`, the elementary numeric fact that `slack₀ ≥ (Kond K+1)/4`, and their combination. -/

/-- `‖(r : ℂ)‖ = |r|`. -/
private lemma cnorm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith only [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r, h]

/-- `Re P₃(w) ≤ P₃^ℝ(‖w‖)`: the real part of HB's `P₃` is dominated by the polynomial
`P₃^ℝ` of the modulus (all coefficients are non-negative). -/
theorem P3_re_le_P3R_norm (w : ℂ) : (P3 w).re ≤ P3R ‖w‖ := by
  have h0 : (P3 w).re ≤ ‖P3 w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have h2 : ‖P3 w‖ ≤ ‖w‖ + ‖w‖^2 + (2/3) * ‖w‖^3 := by
    rw [P3]
    have hA := norm_add_le (w + w^2) ((2/3 : ℂ) * w^3)
    have hB := norm_add_le w (w^2)
    have hC : ‖((2/3 : ℂ) * w^3)‖ = (2/3) * ‖w‖^3 := by
      rw [norm_mul, norm_pow, show ‖(2/3 : ℂ)‖ = (2/3 : ℝ) by norm_num]
    rw [hC] at hA
    rw [norm_pow] at hB
    linarith only [hA, hB]
  simp only [P3R]
  linarith only [h0, h2]

/-- The §9 slack is at least a quarter of `Kond K + 1`:
`(Kond K + 1)/4 ≤ K²+K+1 − K·Kond K`. -/
theorem slack_ge_quarter {K : ℝ} (hK : 0 < K) :
    (Kond K + 1)/4 ≤ K^2 + K + 1 - K * Kond K := by
  have hle' : Kond K ≤ 4*K := min_le_right _ _
  have h4 : (Kond K + 1)/4 ≤ K + 1/4 := by linarith only [hle']
  by_cases h : (1/2 : ℝ) ≤ K
  · have hle : Kond K ≤ K + 3/(4*K) := min_le_left _ _
    have hm : K * Kond K ≤ K * (K + 3/(4*K)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hK)
    have h2 : K * (K + 3/(4*K)) = K^2 + 3/4 := by field_simp
    linarith only [h4, hm, h2, hle']
  · have hlt : K < 1/2 := lt_of_not_ge h
    have hm : K * Kond K ≤ K * (4*K) :=
      mul_le_mul_of_nonneg_left hle' (le_of_lt hK)
    nlinarith only [h4, hm, hlt, hK, hle', h]

/-- **The principal-character contribution at the diagonal points is absorbed by the slack.**
With `((a+λ)/a)³ ≤ Kond K+1`, the pole term at any of the points `s = 1 + a/L + iθ` satisfies
`¼·Re P₃(α/((s−1)L)) ≤ (8/3)·(K²+K+1 − K·Kond K)`. -/
theorem principal_term_le_slack {a lam K θ : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hK : 0 < K)
    (hx3 : ((a + lam)/a)^3 ≤ Kond K + 1) :
    (1/4 : ℝ) * (P3 (((a+lam) : ℂ) / ((a : ℂ) + (θ : ℂ) * Complex.I))).re
      ≤ (8/3) * (K^2 + K + 1 - K * Kond K) := by
  set x : ℝ := (a + lam)/a with hx
  have hx1 : 1 ≤ x := by rw [hx]; rw [le_div_iff₀ ha]; linarith only [hlam]
  set z : ℂ := ((a+lam) : ℂ) / ((a : ℂ) + (θ : ℂ) * Complex.I) with hz
  have hden : (a : ℝ) ≤ ‖((a : ℂ) + (θ : ℂ) * Complex.I)‖ := by
    have h := Complex.abs_re_le_norm (((a : ℂ) + (θ : ℂ) * Complex.I))
    have hre : (((a : ℂ) + (θ : ℂ) * Complex.I)).re = a := by simp
    rw [hre] at h
    exact le_trans (le_abs_self a) h
  have hznorm : ‖z‖ ≤ x := by
    rw [hz, Complex.norm_div, ← Complex.ofReal_add, cnorm_ofReal, hx]
    rw [abs_of_nonneg (by linarith only [ha, hlam] : (0:ℝ) ≤ a + lam)]
    exact div_le_div_of_nonneg_left (by linarith only [ha, hlam]) ha hden
  have h1 : (P3 z).re ≤ P3R ‖z‖ := P3_re_le_P3R_norm z
  have h2 : P3R ‖z‖ ≤ P3R x := P3R_mono (norm_nonneg _) hznorm
  have h3 : P3R x ≤ (8/3) * x^3 := P3R_le_cube hx1
  have h4 : x^3 ≤ Kond K + 1 := by rw [hx]; exact hx3
  have h5 := slack_ge_quarter hK
  linarith only [h1, h2, h3, h4, h5, hx3]


/-- **The diagonal assembly (generic case).**  From the pointwise diagonal inequality
`combination_diag` and the four per-point *upper* bounds for the same four `Σ`-values, HB's
`ineq913` at the diagonal `λ₀ = λ₁`.

The hypotheses `hS0 … hS3` are exactly the conclusions that `Rep9/principalBound`,
`Rep9/masterP3` (+ `Rep9/imprimCorr`) and `Rep9/nearSum_bounds` are dispatched to supply at the
four points `σ`, `σ+iγ`, `σ+2iγ`, `σ+3iγ` of the diagonal `γ = Im ρ₁`:
the multiplicity `m ≥ 2` of `ρ₁` makes the aligned bound read `Σ(σ+iγ,χ₁) ≤ −2P₃(1) + …`, while
in the generic case `χ₁², χ₁³ ≠ χ₀` the near sums at `σ+2iγ`, `σ+3iγ` are non-negative. -/
theorem ineq913_diag_of_pointwise
    {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {a K ε c e₀ e₁ e₂ e₃ : ℝ}
    (hq : 2 ≤ q) (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hZ : Work.LinnikContract.IsZ χ₁ ρ₁)
    (hcond : cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K)
    (hc : c ≤ 1/6 + (K^2 + K + 1 - K * Kond K) / (12*K))
    (hS0 : SigmaP3L q (Real.log q) 1 (((1 + a / Real.log q : ℝ)) : ℂ) a (lamOf q ρ₁)
             ≤ P3R ((a + lamOf q ρ₁)/a) + (a + lamOf q ρ₁) * e₀)
    (hS1 : SigmaP3L q (Real.log q) χ₁
             ((((1 + a / Real.log q : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
             ≤ -(2 * P3R 1) + (a + lamOf q ρ₁) * e₁)
    (hS2 : SigmaP3L q (Real.log q) (χ₁^2)
             ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
             a (lamOf q ρ₁)
             ≤ (a + lamOf q ρ₁) * e₂)
    (hS3 : SigmaP3L q (Real.log q) (χ₁^3)
             ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
             a (lamOf q ρ₁)
             ≤ (a + lamOf q ρ₁) * e₃)
    (he : (K^2 + K + 1/2) * e₀ + (K^2 + 2*K + 3/4) * e₁ + (K + 1/2) * e₂ + (1/4) * e₃
            ≤ c * (K^2 + 3*K + 3/2)) :
    ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε := by
  set lam := lamOf q ρ₁ with hlamdef
  set S0 := SigmaP3L q (Real.log q) 1 (((1 + a / Real.log q : ℝ)) : ℂ) a lam with hS0def
  set S1 := SigmaP3L q (Real.log q) χ₁
      ((((1 + a / Real.log q : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a lam with hS1def
  set S2 := SigmaP3L q (Real.log q) (χ₁^2)
      ((((1 + a / Real.log q : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I) a lam with hS2def
  set S3 := SigmaP3L q (Real.log q) (χ₁^3)
      ((((1 + a / Real.log q : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I) a lam with hS3def
  have hχ₁ : χ₁ ≠ 1 := Work.ZeroFreeTables.isZ_ne_one hZ
  have hγ : |ρ₁.im| ≤ 1 := Work.ZeroFreeTables.isZ_im_le_one hZ
  have hlam : 0 ≤ lam := by
    rw [hlamdef]; exact Work.LinnikContract.API.isZ_lambda_nonneg hq hZ
  have hα : 0 < a + lam := by linarith only [ha, hlam]
  have hcomb : 0 ≤ (K^2 + K + 1/2) * S0 + (K^2 + 2*K + 3/4) * S1
      + (K + 1/2) * S2 + (1/4) * S3 := by
    rw [hS0def, hS1def, hS2def, hS3def]
    exact combination_diag χ₁ hq ha hK hγ hlam hχ₁
  have h1 : (K^2 + K + 1/2) * S0
      ≤ (K^2 + K + 1/2) * (P3R ((a + lam)/a) + (a + lam) * e₀) :=
    mul_le_mul_of_nonneg_left hS0 (by positivity)
  have h2 : (K^2 + 2*K + 3/4) * S1
      ≤ (K^2 + 2*K + 3/4) * (-(2 * P3R 1) + (a + lam) * e₁) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have h3 : (K + 1/2) * S2 ≤ (K + 1/2) * ((a + lam) * e₂) :=
    mul_le_mul_of_nonneg_left hS2 (by linarith only [hK])
  have h4 : (1/4 : ℝ) * S3 ≤ (1/4 : ℝ) * ((a + lam) * e₃) :=
    mul_le_mul_of_nonneg_left hS3 (by norm_num)
  have hkey : 0 ≤ (K^2 + K + 1/2) * (P3R ((a + lam)/a) + (a + lam) * e₀)
      + (K^2 + 2*K + 3/4) * (-(2 * P3R 1) + (a + lam) * e₁)
      + (K + 1/2) * ((a + lam) * e₂) + (1/4 : ℝ) * ((a + lam) * e₃) := by
    linarith only [hcomb, h1, h2, h3, h4, hS3]
  have heα : (a + lam) * ((K^2 + K + 1/2) * e₀ + (K^2 + 2*K + 3/4) * e₁
        + (K + 1/2) * e₂ + (1/4) * e₃)
      ≤ (a + lam) * (c * (K^2 + 3*K + 3/2)) :=
    mul_le_mul_of_nonneg_left he hα.le
  have hD : 0 ≤ (K^2 + K + 1/2) * P3R ((a + lam)/a) - (2*K^2 + 4*K + 3/2) * P3R 1
      + (a + lam) * c * (K^2 + 3*K + 3/2) := by
    linarith only [hkey, heα, hS3, hcomb, h1, h2, h3]
  have hx3 : ((a + lam)/a)^3 ≤ Kond K + 1 := by
    rw [hlamdef]; exact cond913_cube_le ha hlam hcond
  exact ineq913_diag_of_derived ha hK hε hlam hx3 hc hD


end

end Work.ZeroFreeTables.Rep9
