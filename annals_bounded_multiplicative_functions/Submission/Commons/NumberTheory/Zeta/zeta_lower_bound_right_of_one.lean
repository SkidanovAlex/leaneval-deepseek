import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeriesComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Nat
open scoped Topology Real BigOperators

noncomputable section

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.Zeta

/-! # A lower bound for |ζ(1 + h + i t)| uniform in `t`

For `0 < h ≤ 1/4` and every real `t` one has
`|ζ(1 + h + i t)| ≥ c · h` for an absolute constant `c > 0`.
The proof uses the Euler product: for `s = σ + i t` with `σ = 1 + h > 1`,

    |ζ(s)| = ∏_p |1 - p^(-s)|⁻¹  ≥  ∏_p (1 - p^(-σ))  =  1 / ζ(σ),

together with the elementary bound `ζ(σ) ≤ 1 + 1/(σ - 1)`.
-/

/-- `1 - ‖z‖ ≤ ‖(1 - z)⁻¹‖` whenever `‖z‖ < 1`. -/
private lemma factor_le (z : ℂ) (hz : ‖z‖ < 1) : (1 : ℝ) - ‖z‖ ≤ ‖(1 - z)⁻¹‖ := by
  have hsub : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    simpa using (norm_sub_le (1 : ℂ) z)
  have hbpos : 0 < ‖1 - z‖ := by
    have htri : (1 : ℝ) ≤ ‖1 - z‖ + ‖z‖ := by
      simpa using (norm_add_le (1 - z) z)
    have h1mx : 1 - ‖z‖ ≤ ‖1 - z‖ := by linarith
    have hx1' : 0 < 1 - ‖z‖ := by linarith
    exact lt_of_lt_of_le hx1' h1mx
  have hcpos : 0 < 1 + ‖z‖ := by positivity
  have hgoal0 : (1 + ‖z‖)⁻¹ ≤ ‖(1 - z)⁻¹‖ := by
    have hg := (inv_le_inv₀ hcpos hbpos).2 hsub
    rwa [← norm_inv] at hg
  have h2 : 1 - ‖z‖ ≤ (1 + ‖z‖)⁻¹ := by
    have hd : 1 - ‖z‖ ≤ 1 / (1 + ‖z‖) := by
      rw [le_div_iff₀ hcpos]
      have hsq : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
      nlinarith
    rwa [← inv_eq_one_div] at hd
  exact le_trans h2 hgoal0

/-- For `0 ≤ x < 1`: `(‖(1 - x)⁻¹‖)⁻¹ = 1 - x` (with `x` embedded in `ℂ`). -/
private lemma norm_inv_ofReal_eq {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    (‖(1 - Complex.ofReal x)⁻¹‖)⁻¹ = 1 - x := by
  have hxpos : 0 < 1 - x := by linarith
  have h1 : ((1 : ℂ) - Complex.ofReal x) = Complex.ofReal (1 - x) := by norm_num
  calc
    (‖((1 : ℂ) - Complex.ofReal x)⁻¹‖)⁻¹ = (‖(Complex.ofReal (1 - x))⁻¹‖)⁻¹ := by rw [h1]
    _ = ((1 - x)⁻¹)⁻¹ := by
      congr 1
      have h2 := norm_inv (Complex.ofReal (1 - x))
      rw [h2]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hxpos)]
    _ = 1 - x := by
      field_simp [ne_of_gt hxpos]

/-- `p^(-σ)` as a complex number is the coercion of the real power. -/
private lemma prime_cpow_ofReal (p : ℕ) (σ : ℝ) :
    ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) = Complex.ofReal (((p : ℕ) : ℝ) ^ (-σ)) := by
  have hcast : ((p : ℕ) : ℂ) = Complex.ofReal ((p : ℕ) : ℝ) := by norm_num
  have hexp : -(σ : ℂ) = ((-σ : ℝ) : ℂ) := by rw [← Complex.ofReal_neg]
  rw [hcast, hexp]
  exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ ((p : ℕ) : ℝ)) (-σ)).symm

/-- Per-prime identity for the `σ`-side of the Euler product:
`(‖(1 - p^(-σ))⁻¹‖)⁻¹ = 1 - p^(-σ)` (all real, `p` prime, `0 < σ`). -/
private lemma Bnorm_inv (p : ℕ) (hp : 2 ≤ p) (σ : ℝ) (hσ : 0 < σ) :
    (‖(1 - ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖)⁻¹ = 1 - ((p : ℕ) : ℝ) ^ (-σ) := by
  have hx0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-σ) := by positivity
  have hp1s : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hx1 : ((p : ℕ) : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1s (by linarith)
  rw [prime_cpow_ofReal p σ]
  exact norm_inv_ofReal_eq hx0 hx1

/-- Norm of `p^(-s)` (as a complex power) for `p ≥ 2`. -/
private lemma norm_prime_cpow_neg_s (p : ℕ) (hp : 2 ≤ p) {s : ℂ} :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hn : 0 < (p : ℕ) := by omega
  have h := Complex.norm_natCast_cpow_of_pos hn (-s)
  have hre : (-s).re = -s.re := by simp
  rwa [hre] at h

/-- Per-prime comparison: `1 - p^(-σ) ≤ ‖(1 - p^(-s))⁻¹‖` for `1 < s.re = σ`. -/
private lemma Fnorm_lower (p : ℕ) (hp : 2 ≤ p) {s : ℂ} (hs : (1 : ℝ) < s.re) :
    (1 - ((p : ℕ) : ℝ) ^ (-s.re)) ≤ ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
  have hz1 : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_prime_cpow_neg_s p hp]
    have hp1s : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1s (by linarith)
  have hfac := factor_le (((p : ℕ) : ℂ) ^ (-s)) hz1
  simpa [norm_prime_cpow_neg_s p hp] using hfac

/-- Finite Euler-product comparison over the primes `< n`:
`(∏_p ‖(1 - p^(-σ))⁻¹‖)⁻¹ ≤ ∏_p ‖(1 - p^(-s))⁻¹‖`, where `σ = s.re > 1`. -/
private lemma pt_le (s : ℂ) (hs : (1 : ℝ) < s.re) (n : ℕ) :
    (∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)⁻¹ ≤
      ∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
  calc
    (∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)⁻¹
        = ∏ p ∈ n.primesBelow, (‖(1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)⁻¹ := by
            exact (Finset.prod_inv_distrib (fun p : ℕ => ‖(1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)).symm
    _ ≤ ∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      refine Finset.prod_le_prod₀ ?h0 ?h1
      · intro p hp
        exact inv_nonneg.mpr (norm_nonneg ((1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹))
      · intro p hp
        have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
        have hp2 : 2 ≤ p := hpp.two_le
        have hB := Bnorm_inv p hp2 s.re (by linarith)
        have hF := Fnorm_lower p hp2 hs
        rw [hB]
        exact hF

/-- For `1 < s.re`, `|ζ(s)| ≥ 1 / |ζ(s.re)|`.  (Follows from the Euler product:
each Euler factor satisfies `|1 - p^(-s)|⁻¹ ≥ 1 - p^(-σ)` with `σ = s.re`.) -/
private lemma zeta_norm_lower {s : ℂ} (hs : 1 < s.re) :
    (‖riemannZeta (((s.re : ℝ) : ℂ))‖)⁻¹ ≤ ‖riemannZeta s‖ := by
  let aB : ℕ → ℝ := fun n => ∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-(s.re : ℂ)))⁻¹‖
  let bF : ℕ → ℝ := fun n => ∏ p ∈ n.primesBelow, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖
  have hσC : 1 < (((s.re : ℝ) : ℂ)).re := by simpa using hs
  have hB := riemannZeta_eulerProduct (s := ((s.re : ℝ) : ℂ)) hσC
  have hBnorm : Tendsto aB atTop (𝓝 ‖riemannZeta (((s.re : ℝ) : ℂ))‖) := by
    have hbn := hB.norm
    simpa [aB, norm_prod] using hbn
  have hζσ : riemannZeta (((s.re : ℝ) : ℂ)) ≠ 0 := by
    exact riemannZeta_ne_zero_of_one_le_re (s := ((s.re : ℝ) : ℂ)) (by simpa using (le_of_lt hs))
  have hne0 : ‖riemannZeta (((s.re : ℝ) : ℂ))‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hζσ
  have hBinv : Tendsto (fun n : ℕ => (aB n)⁻¹) atTop (𝓝 (‖riemannZeta (((s.re : ℝ) : ℂ))‖)⁻¹) :=
    hBnorm.inv₀ hne0
  have hF := riemannZeta_eulerProduct (s := s) hs
  have hFnorm : Tendsto bF atTop (𝓝 ‖riemannZeta s‖) := by
    have hfn := hF.norm
    simpa [bF, norm_prod] using hfn
  have hpt : ∀ n : ℕ, (aB n)⁻¹ ≤ bF n := by
    intro n
    dsimp [aB, bF]
    exact pt_le s hs n
  exact le_of_tendsto_of_tendsto' hBinv hFnorm hpt

/-! ## Upper bound for the real ζ on `σ > 1` -/

/-- The `ZetaAsymptotics` tail terms are nonnegative. -/
private lemma termTSum_nonneg (σ : ℝ) : 0 ≤ ZetaAsymptotics.termTSum σ := by
  rw [ZetaAsymptotics.termTSum]
  exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) σ)

/-- The real series `∑' n, 1 / (n+1)^σ` converges for `1 < σ`. -/
private lemma real_series_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := (Real.summable_nat_rpow_inv (p := σ)).2 hσ
  have hshift : Summable (fun n : ℕ => (fun m : ℕ => ((m : ℝ) ^ σ)⁻¹) (n + 1)) := (summable_nat_add_iff 1).mpr hs
  apply hshift.congr
  intro n
  norm_num [one_div]

/-- Norm of the `n`-th summand of `ζ(σ)` on the line `re = σ`. -/
private lemma summand_norm (n : ℕ) (σ : ℝ) :
    ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖ = (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ) := by
  have hbase : (((n : ℕ) : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) := by norm_num
  rw [hbase]
  rw [norm_div, norm_one]
  have hnormpow : ‖(((n + 1 : ℕ) : ℂ) ^ (σ : ℂ))‖ = (((n + 1 : ℕ) : ℝ) ^ σ) := by
    have hn := Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1) (σ : ℂ)
    have hre : ((σ : ℂ)).re = σ := by simp
    rwa [hre] at hn
  rw [hnormpow]

/-- For real `1 < σ`: `|ζ(σ)| ≤ 1 + 1 / (σ - 1)`. -/
private lemma zeta_norm_upper (σ : ℝ) (hσ : 1 < σ) : ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  let Zσ : ℝ := ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)
  have hsC : 1 < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have hze := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) hsC
  have hsumNorm : Summable (fun n : ℕ => ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖) := by
    exact (real_series_summable σ hσ).congr (fun n => (summand_norm n σ).symm)
  have hnorm : ‖riemannZeta (σ : ℂ)‖ ≤ Zσ := by
    calc
      ‖riemannZeta (σ : ℂ)‖ = ‖(∑' n : ℕ, (1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ)))‖ := by rw [hze]
      _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖ := by
            exact norm_tsum_le_tsum_norm hsumNorm
      _ = Zσ := by
            dsimp [Zσ]
            refine tsum_congr ?_
            intro n
            exact summand_norm n σ
  have hσpos : (0 : ℝ) < σ := by linarith
  have hT : 0 ≤ σ * ZetaAsymptotics.termTSum σ := mul_nonneg (le_of_lt hσpos) (termTSum_nonneg σ)
  have hconv : Zσ = (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ σ)) := by
    dsimp [Zσ]
    refine tsum_congr ?_
    intro n
    norm_num
  have h := ZetaAsymptotics.zeta_limit_aux1 (s := σ) hσ
  have haux : Zσ - 1 / (σ - 1) = 1 - σ * ZetaAsymptotics.termTSum σ := by
    calc
      Zσ - 1 / (σ - 1) = ((∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ σ)) - 1 / (σ - 1)) := by rw [hconv]
      _ = 1 - σ * ZetaAsymptotics.termTSum σ := h
  have hZle : Zσ ≤ 1 + 1 / (σ - 1) := by linarith
  exact le_trans hnorm hZle

/-- **ζ stays linearly large uniformly to the right of `1`.**

For every `t ∈ ℝ`, `0 < h ≤ 1/4`, one has `|ζ(1 + h + i t)| ≥ (1/2) · h`.
The constant is uniform in `t`. -/
theorem zeta_lower_bound_right_of_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (h t : ℝ), 0 < h → h ≤ 1 / 4 →
      c * h ≤ ‖riemannZeta ((((1 + h : ℝ) : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro h t hhpos hhle
  let s : ℂ := (((1 + h : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hsre : s.re = 1 + h := by simp [s]
  have hs : 1 < s.re := by
    rw [hsre]
    linarith
  have hσ : 1 < 1 + h := by linarith
  let A : ℝ := ‖riemannZeta (((1 + h : ℝ) : ℂ))‖
  have hAeq : A = ‖riemannZeta (((s.re : ℝ) : ℂ))‖ := by
    rw [hsre]
  have hlow := zeta_norm_lower (s := s) hs
  have hApos : 0 < A := by
    have hz : riemannZeta (((1 + h : ℝ) : ℂ)) ≠ 0 := by
      exact riemannZeta_ne_zero_of_one_le_re (s := ((1 + h : ℝ) : ℂ)) (by simp; linarith)
    dsimp [A]
    exact norm_pos_iff.mpr hz
  have hupper : A ≤ 1 + 1 / h := by
    have hup := zeta_norm_upper (1 + h) hσ
    dsimp [A]
    have hden : (1 + h) - 1 = h := by ring
    rwa [hden] at hup
  have hmain1 : h / (1 + h) ≤ A⁻¹ := by
    have hsub := one_div_le_one_div_of_le hApos hupper
    have hfrac : 1 / (1 + 1 / h) = h / (1 + h) := by
      field_simp [hhpos.ne']
      ring
    rw [hfrac] at hsub
    simpa using hsub
  have hhalf : (1 / 2 : ℝ) * h ≤ h / (1 + h) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + h)]
    nlinarith [hhpos, hhle]
  have hlow' : A⁻¹ ≤ ‖riemannZeta s‖ := by
    rw [hAeq]
    exact hlow
  calc
    (1 / 2 : ℝ) * h ≤ h / (1 + h) := hhalf
    _ ≤ A⁻¹ := hmain1
    _ ≤ ‖riemannZeta s‖ := hlow'
    _ = ‖riemannZeta ((((1 + h : ℝ) : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ := by rfl

end Commons.NumberTheory.Zeta
