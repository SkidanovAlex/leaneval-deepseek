import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_real_growth
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_le_norm_Gamma_re
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds

noncomputable section

open Complex Filter Metric Set
open scoped Real Topology BigOperators
set_option maxHeartbeats 800000

namespace Commons.NumberTheory.Zeta

/-- The entire completion `Ξ(s) = 1/2 + (1/2)·s·(s-1)·Λ₀(s)`, inline. -/
private abbrev xiV (z : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z

/-- `xiV` agrees with the naive product `(1/2)·z·(z-1)·Λ(z)` away from `0,1`. -/
private lemma xiV_eq_half_mul (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    xiV z = (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z := by
  unfold xiV
  have hz1m : 1 - z ≠ 0 := by
    intro h
    apply hz1
    rw [show 1 - z = -(z - 1) by ring] at h
    rw [neg_eq_zero] at h
    exact sub_eq_zero.mp h
  have hΛ₀ : completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    have hΛ := completedRiemannZeta_eq z
    rw [hΛ]
    field_simp [hz0, hz1m]
    ring
  calc
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z
        = (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * (completedRiemannZeta z + 1 / z + 1 / (1 - z)) := by
            rw [hΛ₀]
    _ = (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z := by
            field_simp [hz0, hz1m]
            ring

/-- Functional equation of `xiV`. -/
private lemma xiV_one_sub (z : ℂ) : xiV (1 - z) = xiV z := by
  unfold xiV
  have hFE := completedRiemannZeta₀_one_sub z
  calc
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (1 - z) * ((1 - z) - 1) * completedRiemannZeta₀ (1 - z)
        = (1 / 2 : ℂ) + (1 / 2 : ℂ) * (1 - z) * ((1 - z) - 1) * completedRiemannZeta₀ z := by
            rw [hFE]
    _ = (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z := by ring

/-- `xiV` is differentiable (hence continuous). -/
private lemma xiV_differentiable : Differentiable ℂ xiV := by
  unfold xiV
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hhead : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  have hc : Differentiable ℂ (fun _ : ℂ => (1 / 2 : ℂ)) := (differentiable_const (1 / 2 : ℂ))
  exact hc.add (hhead.mul hΛ)

/-- `Λ(z) = ζ(z)·Γℝ(z)` when `z ≠ 0` and the Gamma factor does not vanish. -/
private lemma lambda_eq_zeta_mul_GammaR (z : ℂ) (hz0 : z ≠ 0) (hG : Complex.Gammaℝ z ≠ 0) :
    completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
  have hζ : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z :=
    riemannZeta_def_of_ne_zero hz0
  rw [hζ]
  field_simp [hG]

/-- Product formula for `Λ` on the half-plane `z.re ≥ 2`. -/
private lemma lambda_eq_zeta_mul_GammaR_of_two_le_re (z : ℂ) (hz : 2 ≤ z.re) :
    completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    norm_num at hz
  have hG : Complex.Gammaℝ z ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    linarith
  exact lambda_eq_zeta_mul_GammaR z hz0 hG

/-- `Γℝ(z) ≠ 0` provided `-1 ≤ z.re` and `z ≠ 0`. -/
private lemma Gammaℝ_ne_zero_of_re_ge_neg_one {z : ℂ} (hre : -1 ≤ z.re) (hz0 : z ≠ 0) :
    Complex.Gammaℝ z ≠ 0 := by
  intro h
  have hz := (Complex.Gammaℝ_eq_zero_iff).mp h
  rcases hz with ⟨n, hn⟩
  have hre' : z.re = -(2 * (n : ℝ)) := by
    have hcast : ((2 * (n : ℂ))).re = (2 * (n : ℝ)) := by simp
    rw [hn]
    rw [Complex.neg_re]
    rw [hcast]
  by_cases hn0 : n = 0
  · subst n
    have hz0' : z = 0 := by simpa using hn
    exact hz0 hz0'
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hle : z.re ≤ -2 := by
      rw [hre']
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
      linarith
    linarith

/-- Norm of the real Gamma factor. -/
private lemma norm_GammaR_eq (z : ℂ) :
    ‖Complex.Gammaℝ z‖ = (Real.pi : ℝ) ^ (-(z.re / 2)) * ‖Complex.Gamma (z / 2)‖ := by
  rw [Complex.Gammaℝ_def]
  rw [norm_mul]
  have hπpos : 0 < (Real.pi : ℝ) := Real.pi_pos
  have hre : (-z / 2 : ℂ).re = -(z.re / 2) := by
    rw [Complex.div_re]
    norm_num
    ring
  have hnorm : ‖((Real.pi : ℂ) ^ (-z / 2))‖ = (Real.pi : ℝ) ^ (-(z.re / 2)) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hπpos (-z / 2)
    rw [h]
    rw [hre]
  rw [hnorm]

/-- Real-axis Gamma bound: `‖Γ(σ)‖ ≤ exp(σ·log(σ+2))` for `σ ≥ 1`. -/
private lemma norm_Gamma_ofReal_le (σ : ℝ) (h1 : 1 ≤ σ) :
    ‖Complex.Gamma (σ : ℂ)‖ ≤ Real.exp (σ * Real.log (σ + 2)) := by
  have hΓpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  calc
    ‖Complex.Gamma (σ : ℂ)‖ = ‖(Real.Gamma σ : ℂ)‖ := by rw [Complex.Gamma_ofReal]
    _ = Real.Gamma σ := Complex.norm_of_nonneg hΓpos.le
    _ ≤ Real.exp (σ * Real.log (σ + 2)) :=
      Commons.Analysis.SpecialFunctions.Gamma.real_gamma_growth h1

/-- Right-half-plane Gamma bound in `(1+‖u‖)·log(2+‖u‖)` form. -/
private lemma Gamma_norm_le_exp_of_one_le_re (u : ℂ) (hu : 1 ≤ u.re) :
    ‖Complex.Gamma u‖ ≤ Real.exp ((1 + ‖u‖) * Real.log (2 + ‖u‖)) := by
  have hu0 : 0 < u.re := by linarith
  have h1 := Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_le_norm_Gamma_re u hu0
  have hre_le : u.re ≤ ‖u‖ := le_trans (le_abs_self u.re) (Complex.abs_re_le_norm u)
  have hle1 : u.re * Real.log (u.re + 2) ≤ (1 + ‖u‖) * Real.log (2 + ‖u‖) := by
    have hlog1 : Real.log (u.re + 2) ≤ Real.log (2 + ‖u‖) := by
      apply Real.log_le_log
      · linarith
      · linarith
    have hlog_nonneg : 0 ≤ Real.log (u.re + 2) := by
      apply Real.log_nonneg
      linarith
    have hA : u.re * Real.log (u.re + 2) ≤ ‖u‖ * Real.log (2 + ‖u‖) := by
      have hb : ‖u‖ * Real.log (u.re + 2) ≤ ‖u‖ * Real.log (2 + ‖u‖) := by
        exact mul_le_mul_of_nonneg_left hlog1 (norm_nonneg u)
      have ha : u.re * Real.log (u.re + 2) ≤ ‖u‖ * Real.log (u.re + 2) := by
        exact mul_le_mul_of_nonneg_right hre_le hlog_nonneg
      linarith
    have hb2 : ‖u‖ * Real.log (2 + ‖u‖) ≤ (1 + ‖u‖) * Real.log (2 + ‖u‖) := by
      have hlog2 : 0 ≤ Real.log (2 + ‖u‖) := by
        apply Real.log_nonneg
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith) hlog2
    linarith
  calc
    ‖Complex.Gamma u‖ ≤ ‖Complex.Gamma (u.re : ℂ)‖ := h1
    _ ≤ Real.exp (u.re * Real.log (u.re + 2)) := norm_Gamma_ofReal_le u.re hu
    _ ≤ Real.exp ((1 + ‖u‖) * Real.log (2 + ‖u‖)) := by
      exact Real.exp_le_exp.mpr hle1

/-- `‖(1/2)·u·(u-1)‖ ≤ ‖u‖·(‖u‖+1)`. -/
private lemma half_monomial_norm_le (u : ℂ) :
    ‖((1 / 2 : ℂ) * u * (u - 1))‖ ≤ ‖u‖ * (‖u‖ + 1) := by
  have h12 : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
  have hh : ‖((1 / 2 : ℂ) * u)‖ ≤ ‖u‖ := by
    rw [norm_mul]
    calc
      ‖(1 / 2 : ℂ)‖ * ‖u‖ ≤ (1 : ℝ) * ‖u‖ := mul_le_mul_of_nonneg_right h12 (norm_nonneg u)
      _ = ‖u‖ := by simp
  have hsub : ‖u - 1‖ ≤ ‖u‖ + 1 := by
    calc
      ‖u - 1‖ ≤ ‖u‖ + ‖(1 : ℂ)‖ := norm_sub_le u 1
      _ = ‖u‖ + 1 := by rw [norm_one]
  calc
    ‖((1 / 2 : ℂ) * u * (u - 1))‖ = ‖((1 / 2 : ℂ) * u)‖ * ‖u - 1‖ := by rw [norm_mul]
    _ ≤ ‖u‖ * ‖u - 1‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg (u - 1))
    _ ≤ ‖u‖ * (‖u‖ + 1) := by
      have hmul := mul_le_mul_of_nonneg_right hsub (norm_nonneg u)
      linarith

/-- The norm of `xiV` factors. -/
private lemma xiV_norm_eq (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ‖xiV z‖ = ‖((1 / 2 : ℂ) * z * (z - 1))‖ * ‖completedRiemannZeta z‖ := by
  rw [xiV_eq_half_mul z hz0 hz1]
  rw [norm_mul]

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

/-- The real `p`-series `∑' n, (n+1) ^ (-2)` converges. -/
private lemma summable_nat_add_one_rpow_neg_two :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr hnat

/-- Termwise norm bound: for `2 ≤ s.re`, `‖(n+1)^(-s)‖ ≤ (n+1)^(-2)`. -/
private lemma zeta_term_norm_le_two (s : ℂ) (hs : 2 ≤ s.re) (n : ℕ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by norm_num
  have hnorm : ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
    calc
      ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ‖(((n + 1 : ℕ) : ℂ) ^ s)⁻¹‖ := by simp [one_div]
      _ = ‖(((n + 1 : ℕ) : ℂ) ^ s)‖⁻¹ := by rw [norm_inv]
      _ = (((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹ := by
        rw [hcast]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 s]
      _ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hneg : -s.re ≤ -2 := by linarith
  rw [hnorm]
  exact Real.rpow_le_rpow_of_exponent_le h1 hneg

/-- The Riemann zeta function is bounded on the half-plane of real part at least `2`. -/
private lemma zeta_norm_le_const_of_two_le_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re → ‖riemannZeta s‖ ≤ C := by
  let C : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)
  refine ⟨C, ?_, ?_⟩
  · show 0 < C
    unfold C
    have hsum_g : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
      summable_nat_add_one_rpow_neg_two
    have hts := Summable.tsum_eq_zero_add (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))
      hsum_g
    have hg0 : ((0 + 1 : ℕ) : ℝ) ^ (-2 : ℝ) = 1 := by norm_num
    have hnonneg : 0 ≤ ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-2 : ℝ) := by
      apply tsum_nonneg
      intro n
      have hb : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
      exact le_of_lt (Real.rpow_pos_of_pos hb _)
    rw [hts, hg0]
    linarith
  · intro s hs
    have hs1 : 1 < s.re := by linarith
    let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
    let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)
    have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
      simpa [f] using zeta_eq_tsum_one_div_nat_add_one_cpow hs1
    have hsum_g : Summable g := by
      simpa [g] using summable_nat_add_one_rpow_neg_two
    have hterm : ∀ n : ℕ, ‖f n‖ ≤ g n := by
      intro n
      simpa [f, g] using zeta_term_norm_le_two s hs n
    have hsum_norm : Summable (fun n : ℕ => ‖f n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum_g
    calc
      ‖riemannZeta s‖ = ‖∑' n : ℕ, f n‖ := by rw [hzeta]
      _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hsum_norm hsum_g
      _ = C := by rfl

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

private lemma log5_pos : (0 : ℝ) < Real.log 5 := by
  exact Real.log_pos (by norm_num : (1 : ℝ) < 5)

private lemma log4_add_two_pos : (0 : ℝ) < 2 * (Real.log 4 + 2) := by
  have h : (0 : ℝ) < Real.log 4 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

private lemma three_log5_add_two_pos : (0 : ℝ) < 3 * (Real.log 5 + 2) := by
  have h : (0 : ℝ) < Real.log 5 := log5_pos
  positivity

private lemma re_ge_three_est {ρ : ℝ} (hρ : 3 ≤ ρ) :
    3 * (Real.log 5 + 2) ≤ ρ * (Real.log (ρ + 2) + 2) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hlog : Real.log 5 ≤ Real.log (ρ + 2) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have h5pos : 0 ≤ Real.log 5 := le_of_lt log5_pos
  have hA : 3 * (Real.log 5 + 2) ≤ ρ * (Real.log 5 + 2) := by
    exact mul_le_mul_of_nonneg_right hρ (by linarith)
  have hB : ρ * (Real.log 5 + 2) ≤ ρ * (Real.log (ρ + 2) + 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hρ0
  linarith

private lemma logB_absorb {B ρ : ℝ} (hB : 1 ≤ B) (hρ : 3 ≤ ρ) :
    Real.log B ≤ (Real.log B / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2) := by
  have hpos : 0 < 3 * (Real.log 5 + 2) := three_log5_add_two_pos
  have hge := re_ge_three_est hρ
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  have hfactor : (1 : ℝ) ≤ ρ * (Real.log (ρ + 2) + 2) / (3 * (Real.log 5 + 2)) := by
    exact (le_div_iff₀ hpos).mpr (by simpa using hge)
  calc
    Real.log B ≤ Real.log B * (ρ * (Real.log (ρ + 2) + 2) / (3 * (Real.log 5 + 2))) := by
      simpa using mul_le_mul_of_nonneg_left hfactor hlogB0
    _ = (Real.log B / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2) := by
      ring

private lemma log_ρ3_le {ρ : ℝ} (hρ : 3 ≤ ρ) :
    Real.log (ρ + 3) ≤ ρ * (Real.log (ρ + 2) + 2) := by
  have hlog : Real.log (ρ + 3) ≤ ρ + 2 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ρ + 3)
    linarith
  have hlog2 : 0 ≤ Real.log (ρ + 2) := by
    exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ ρ + 2)
  have hρ0 : 0 ≤ ρ := by linarith
  have hρlog : 0 ≤ ρ * Real.log (ρ + 2) := mul_nonneg hρ0 hlog2
  have hρ2 : 0 ≤ ρ - 2 := by linarith
  have hmain : ρ + 2 ≤ ρ * (Real.log (ρ + 2) + 2) := by
    linarith
  linarith

/-- Absorbing polynomial factors and multiplicative constants into the exponential shape. -/
private lemma poly_mul_exp_le {a B : ℝ} (ha : 0 ≤ a) (hB : 1 ≤ B) {k : ℕ} {ρ : ℝ} (hρ : 3 ≤ ρ) :
    B * (ρ + 3) ^ k * Real.exp (a * ρ * (Real.log (ρ + 2) + 2)) ≤
      Real.exp ((a + (k : ℝ) + Real.log B / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2)) := by
  let E0 : ℝ := ρ * (Real.log (ρ + 2) + 2)
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    have hρ0 : 0 ≤ ρ := by linarith
    have hlg : 0 ≤ Real.log (ρ + 2) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ ρ + 2)
    have hA : 0 ≤ ρ * Real.log (ρ + 2) := mul_nonneg hρ0 hlg
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBfactor : B ≤ Real.exp (Real.log B / (3 * (Real.log 5 + 2)) * E0) := by
    calc
      B = Real.exp (Real.log B) := by rw [Real.exp_log hBpos]
      _ ≤ Real.exp (Real.log B / (3 * (Real.log 5 + 2)) * E0) := by
        exact Real.exp_le_exp.mpr (by
          have h := logB_absorb hB hρ
          simpa [E0, mul_assoc] using h)
  have hPfactor : (ρ + 3) ^ k ≤ Real.exp ((k : ℝ) * E0) := by
    calc
      (ρ + 3) ^ k = Real.exp (Real.log ((ρ + 3) ^ k)) := by
        rw [Real.exp_log (pow_pos (by linarith : (0 : ℝ) < ρ + 3) k)]
      _ = Real.exp ((k : ℝ) * Real.log (ρ + 3)) := by rw [Real.log_pow]
      _ ≤ Real.exp ((k : ℝ) * E0) := by
        exact Real.exp_le_exp.mpr (by
          have h := log_ρ3_le hρ
          have hk : 0 ≤ (k : ℝ) := by positivity
          simpa [E0, mul_assoc] using mul_le_mul_of_nonneg_left h hk)
  have hA1 : Real.exp (a * ρ * (Real.log (ρ + 2) + 2)) = Real.exp (a * E0) := by
    congr 1
    dsimp [E0]
    ring
  have hB2 : B * (ρ + 3) ^ k ≤
      Real.exp (Real.log B / (3 * (Real.log 5 + 2)) * E0) * Real.exp ((k : ℝ) * E0) := by
    exact mul_le_mul hBfactor hPfactor (pow_nonneg (by linarith : (0 : ℝ) ≤ ρ + 3) k)
      (Real.exp_nonneg _)
  calc
    B * (ρ + 3) ^ k * Real.exp (a * ρ * (Real.log (ρ + 2) + 2))
        ≤ (Real.exp (Real.log B / (3 * (Real.log 5 + 2)) * E0) * Real.exp ((k : ℝ) * E0)) *
            Real.exp (a * E0) := by
          rw [hA1]
          exact mul_le_mul hB2 le_rfl (Real.exp_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = Real.exp ((Real.log B / (3 * (Real.log 5 + 2)) + (k : ℝ) + a) * E0) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((a + (k : ℝ) + Real.log B / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2)) := by
      congr 1
      dsimp [E0]
      ring

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

private lemma log_R3_le_log_R2_add_fifth {R : ℝ} (hR : 4 ≤ R) :
    Real.log (R + 3) ≤ Real.log (R + 2) + 1 / 5 := by
  have hpos1 : 0 < R + 3 := by linarith
  have hpos2 : 0 < R + 2 := by linarith
  have hratio : (R + 3) / (R + 2) - 1 = 1 / (R + 2) := by
    field_simp [hpos2.ne']
    ring
  have hsub : Real.log (R + 3) - Real.log (R + 2) ≤ 1 / (R + 2) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (R + 3) / (R + 2))
    rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)] at h
    rw [hratio] at h
    exact h
  have h16 : 1 / (R + 2) ≤ 1 / 5 := by
    exact one_div_le_one_div_of_le (by norm_num : 0 < (5 : ℝ)) (by linarith : (5 : ℝ) ≤ R + 2)
  linarith

/-- FE-left conversion: `(R+1)(log(R+3)+2) ≤ 2R(log(R+2)+2)` for `R ≥ 4`. -/
private lemma leftconv {R : ℝ} (hR : 4 ≤ R) :
    (R + 1) * (Real.log (R + 3) + 2) ≤ 2 * R * (Real.log (R + 2) + 2) := by
  have hlog : Real.log (R + 3) ≤ Real.log (R + 2) + 1 / 5 := log_R3_le_log_R2_add_fifth hR
  have hR54 : R + 1 ≤ (5 / 4 : ℝ) * R := by linarith
  have hA : (R + 1) * (Real.log (R + 3) + 2) ≤ (5 / 4 : ℝ) * R * (Real.log (R + 2) + 1 / 5 + 2) := by
    have h2 : Real.log (R + 3) + 2 ≤ Real.log (R + 2) + 1 / 5 + 2 := by linarith
    have h1n : 0 ≤ Real.log (R + 3) + 2 := by
      exact add_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 3)) (by norm_num)
    exact mul_le_mul hR54 h2 h1n (by positivity : 0 ≤ (5 / 4 : ℝ) * R)
  have hB : (5 / 4 : ℝ) * R * (Real.log (R + 2) + 1 / 5 + 2) ≤ 2 * R * (Real.log (R + 2) + 2) := by
    have hc : (5 / 4 : ℝ) * (Real.log (R + 2) + 1 / 5 + 2) ≤ 2 * (Real.log (R + 2) + 2) := by
      have hlg0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)
      linarith
    have hR0 : 0 ≤ R := by linarith
    linarith only [mul_le_mul_of_nonneg_left hc hR0]
  linarith

/-- Right half-plane growth of `xiV` (used for `Re ≥ 2`, radius ≥ 3). -/
private lemma xiV_bound_right {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ s : ℂ, 2 ≤ s.re → ‖riemannZeta s‖ ≤ C) (u : ℂ) (hu : 2 ≤ u.re) (hu3 : 3 ≤ ‖u‖) :
    ‖xiV u‖ ≤ Real.exp ((3 + Real.log (C + 1) / (3 * (Real.log 5 + 2))) * ‖u‖ *
      (Real.log (‖u‖ + 2) + 2)) := by
  let ρ : ℝ := ‖u‖
  have hρ3 : 3 ≤ ρ := by simpa [ρ] using hu3
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; exact norm_nonneg u
  have hz0 : u ≠ 0 := by
    intro hz0
    have : ‖(0 : ℂ)‖ = 0 := by simp
    rw [hz0] at hu3
    norm_num at hu3
  have hz1 : u ≠ 1 := by
    intro hz1
    have h1 : ‖u‖ = 1 := by rw [hz1]; simp
    linarith only [hu3, h1]
  have hLam : completedRiemannZeta u = riemannZeta u * Complex.Gammaℝ u :=
    lambda_eq_zeta_mul_GammaR_of_two_le_re u hu
  have hnorm : ‖xiV u‖ = ‖((1 / 2 : ℂ) * u * (u - 1))‖ * ‖completedRiemannZeta u‖ :=
    xiV_norm_eq u hz0 hz1
  have hzeta : ‖riemannZeta u‖ ≤ C := hC u hu
  have hσ : -(u.re / 2) ≤ 0 := by linarith
  have h1pi : (1 : ℝ) ≤ Real.pi := by
    have h2 := Real.two_le_pi
    linarith
  have hpi_le0 : (Real.pi : ℝ) ^ (-(u.re / 2)) ≤ (Real.pi : ℝ) ^ (0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1pi hσ
  have hpi_le : (Real.pi : ℝ) ^ (-(u.re / 2)) ≤ 1 := by
    simpa using hpi_le0
  have hdiv : (u / 2).re = u.re / 2 := by
    rw [Complex.div_re]
    norm_num
    ring
  have hre : 1 ≤ (u / 2).re := by
    rw [hdiv]
    linarith
  have hΓhalf : ‖Complex.Gamma (u / 2)‖ ≤ Real.exp ((1 + ‖u / 2‖) * Real.log (2 + ‖u / 2‖)) :=
    Gamma_norm_le_exp_of_one_le_re (u / 2) hre
  have hnormu2 : ‖u / 2‖ = ρ / 2 := by
    dsimp [ρ]
    rw [norm_div]
    norm_num
  have hGR : ‖Complex.Gammaℝ u‖ ≤ Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := by
    calc
      ‖Complex.Gammaℝ u‖ = (Real.pi : ℝ) ^ (-(u.re / 2)) * ‖Complex.Gamma (u / 2)‖ := norm_GammaR_eq u
      _ ≤ 1 * ‖Complex.Gamma (u / 2)‖ := mul_le_mul_of_nonneg_right hpi_le (norm_nonneg _)
      _ = ‖Complex.Gamma (u / 2)‖ := by simp
      _ ≤ Real.exp ((1 + ‖u / 2‖) * Real.log (2 + ‖u / 2‖)) := hΓhalf
      _ = Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := by rw [hnormu2]
  have hLamNorm : ‖completedRiemannZeta u‖ ≤ C * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := by
    calc
      ‖completedRiemannZeta u‖ = ‖riemannZeta u * Complex.Gammaℝ u‖ := by rw [hLam]
      _ = ‖riemannZeta u‖ * ‖Complex.Gammaℝ u‖ := by rw [norm_mul]
      _ ≤ C * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := mul_le_mul hzeta hGR (norm_nonneg _) (le_of_lt hC0)
  have hsub : ‖u - 1‖ ≤ ‖u‖ + 1 := by
    calc
      ‖u - 1‖ ≤ ‖u‖ + ‖(1 : ℂ)‖ := norm_sub_le u 1
      _ = ‖u‖ + 1 := by rw [norm_one]
  have hhead : ‖((1 / 2 : ℂ) * u * (u - 1))‖ ≤ ρ * (ρ + 1) := by
    have h12 : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
    have hh : ‖((1 / 2 : ℂ) * u)‖ ≤ ‖u‖ := by
      rw [norm_mul]
      calc
        ‖(1 / 2 : ℂ)‖ * ‖u‖ ≤ (1 : ℝ) * ‖u‖ := mul_le_mul_of_nonneg_right h12 (norm_nonneg u)
        _ = ‖u‖ := by simp
    calc
      ‖((1 / 2 : ℂ) * u * (u - 1))‖ = ‖((1 / 2 : ℂ) * u)‖ * ‖u - 1‖ := by rw [norm_mul]
      _ ≤ ‖u‖ * ‖u - 1‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg (u - 1))
      _ ≤ ‖u‖ * (‖u‖ + 1) := by
        have hmul := mul_le_mul_of_nonneg_right hsub (norm_nonneg u)
        linarith
      _ = ρ * (ρ + 1) := by dsimp [ρ]
  have hnormMain : ‖xiV u‖ ≤ (ρ * (ρ + 1)) * (C * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2))) := by
    calc
      ‖xiV u‖ = ‖((1 / 2 : ℂ) * u * (u - 1))‖ * ‖completedRiemannZeta u‖ := hnorm
      _ ≤ (ρ * (ρ + 1)) * (C * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2))) :=
        mul_le_mul hhead hLamNorm (norm_nonneg _) (by positivity : 0 ≤ ρ * (ρ + 1))
  have hpoly : (ρ * (ρ + 1)) * C ≤ (C + 1) * (ρ + 3) ^ 2 := by
    have hC0le : 0 ≤ C := le_of_lt hC0
    have h1 : ρ * (ρ + 1) ≤ (ρ + 3) ^ 2 := by
      linarith
    have hC : C ≤ C + 1 := by linarith
    calc
      (ρ * (ρ + 1)) * C = C * (ρ * (ρ + 1)) := by ring
      _ ≤ C * (ρ + 3) ^ 2 := by
        exact mul_le_mul_of_nonneg_left h1 hC0le
      _ ≤ (C + 1) * (ρ + 3) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ (ρ + 3) ^ 2)
  have hexp : Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) ≤ Real.exp (ρ * (Real.log (ρ + 2) + 2)) := by
    apply Real.exp_le_exp.mpr
    have h1a : (1 : ℝ) + ρ / 2 ≤ ρ := by linarith
    have hlog1 : 0 ≤ Real.log (2 + ρ / 2) := by
      apply Real.log_nonneg
      linarith
    have hstep1 : (1 + ρ / 2) * Real.log (2 + ρ / 2) ≤ ρ * Real.log (2 + ρ / 2) := by
      exact mul_le_mul_of_nonneg_right h1a hlog1
    have hlog2 : Real.log (2 + ρ / 2) ≤ Real.log (ρ + 2) := by
      exact Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log (ρ + 2) := by
      apply Real.log_nonneg
      linarith
    have hstep2 : ρ * Real.log (2 + ρ / 2) ≤ ρ * (Real.log (ρ + 2) + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith only [hlog2]) (by linarith only [h1a])
    linarith
  have hmain : ‖xiV u‖ ≤ (C + 1) * (ρ + 3) ^ 2 * Real.exp (ρ * (Real.log (ρ + 2) + 2)) := by
    calc
      ‖xiV u‖ ≤ (ρ * (ρ + 1)) * (C * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2))) := hnormMain
      _ = ((ρ * (ρ + 1)) * C) * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := by ring
      _ ≤ ((C + 1) * (ρ + 3) ^ 2) * Real.exp ((1 + ρ / 2) * Real.log (2 + ρ / 2)) := by
        exact mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
      _ ≤ ((C + 1) * (ρ + 3) ^ 2) * Real.exp (ρ * (Real.log (ρ + 2) + 2)) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (C + 1) * (ρ + 3) ^ 2)
  have hC1 : 1 ≤ C + 1 := by linarith
  have hfin := poly_mul_exp_le (a := (1 : ℝ)) (ha := by norm_num) (B := C + 1) (hB := hC1)
    (k := 2) (ρ := ρ) hρ3
  calc
    ‖xiV u‖ ≤ (C + 1) * (ρ + 3) ^ 2 * Real.exp (ρ * (Real.log (ρ + 2) + 2)) := hmain
    _ = (C + 1) * (ρ + 3) ^ 2 * Real.exp (1 * ρ * (Real.log (ρ + 2) + 2)) := by
      congr 1
      ring_nf
    _ ≤ Real.exp ((1 + 2 + Real.log (C + 1) / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2)) := hfin
    _ = Real.exp ((3 + Real.log (C + 1) / (3 * (Real.log 5 + 2))) * ρ * (Real.log (ρ + 2) + 2)) := by
      congr 1
      ring
    _ = Real.exp ((3 + Real.log (C + 1) / (3 * (Real.log 5 + 2))) * ‖u‖ *
      (Real.log (‖u‖ + 2) + 2)) := rfl

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

/-- `R·(R+1) ≤ (R+3)^2` for `R ≥ 0`. -/
private lemma R_mul_R1_le_sq {R : ℝ} (hR : 0 ≤ R) : R * (R + 1) ≤ (R + 3) ^ 2 := by
  linarith

/-- Middle-strip bound: on the circle of radius `R ≥ 4`, for `-1 ≤ Re ≤ 3` the
whole completion grows only polynomially. -/
private lemma xiV_bound_middle {C K : ℝ} (hC : ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ C * (|t| + 3) ^ 4)
    (hK : ∀ (x y : ℝ), x ∈ Set.Icc (-5) 5 → 1 ≤ |y| →
      ‖Complex.Gamma ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ K * (1 + |y|) ^ 11 * Real.exp (-(Real.pi / 2) * |y|))
    (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    {R : ℝ} (hR : 4 ≤ R) (z : ℂ) (hz : ‖z‖ = R) (hσ1 : -1 ≤ z.re) (hσ3 : z.re < 3) :
    ‖xiV z‖ ≤ (4 * C * K + 1) * (R + 3) ^ 17 := by
  let σ : ℝ := z.re
  let t : ℝ := z.im
  have hzre : z = (σ : ℂ) + Complex.I * (t : ℂ) := by
    apply Complex.ext <;> simp [σ, t]
  have hz0 : z ≠ 0 := by
    intro hz0
    have h0 : ‖z‖ = 0 := by rw [hz0]; simp
    linarith [hz, hR]
  have hz1 : z ≠ 1 := by
    intro hz1
    have h1 : ‖z‖ = 1 := by rw [hz1]; simp
    linarith only [hR, hz, h1]
  have hσlo : -1 ≤ σ := by simpa [σ] using hσ1
  have hσhi : σ ≤ 3 := le_of_lt (by simpa [σ] using hσ3)
  have ht2eq : t ^ 2 = R ^ 2 - σ ^ 2 := by
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      have h1 := Complex.normSq_apply z
      have h2 := Complex.normSq_eq_norm_sq z
      rw [← h2, h1]
      ring
    have hpow : R ^ 2 = σ ^ 2 + t ^ 2 := by
      calc
        R ^ 2 = ‖z‖ ^ 2 := by rw [hz]
        _ = z.re ^ 2 + z.im ^ 2 := hn
        _ = σ ^ 2 + t ^ 2 := by simp [σ, t]
    linarith
  have ht4 : (4 : ℝ) ≤ t ^ 2 := by
    have hR2 : 16 ≤ R ^ 2 := by nlinarith only [hR]
    have hσ2 : σ ^ 2 ≤ 9 := by nlinarith only [hσlo, hσhi]
    linarith
  have htge : (2 : ℝ) ≤ |t| := by
    have hsqmono := Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ≤ t ^ 2)
    norm_num at hsqmono
    have hsqrt : Real.sqrt (t ^ 2) = |t| := Real.sqrt_sq_eq_abs t
    rw [hsqrt] at hsqmono
    exact hsqmono
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have hthalf1 : (1 : ℝ) ≤ |t / 2| := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have hσge0 : -(z.re / 2) ≤ 1 := by
    rw [show z.re / 2 = σ / 2 by simp [σ]]
    linarith
  have hpi_le : (Real.pi : ℝ) ^ (-(z.re / 2)) ≤ 4 := by
    have hbase1 : 1 ≤ Real.pi := by
      have h2 := Real.two_le_pi
      linarith
    have hle0 : (Real.pi : ℝ) ^ (-(z.re / 2)) ≤ (Real.pi : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hσge0
    rw [Real.rpow_one] at hle0
    exact le_trans hle0 (by linarith only [Real.pi_lt_four])
  have hΓR_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_ge_neg_one (by simpa [σ] using hσ1) hz0
  have hΛ : completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z :=
    lambda_eq_zeta_mul_GammaR z hz0 hΓR_ne
  have hzB : ‖riemannZeta z‖ ≤ C * (|t| + 3) ^ 4 := by
    have hh := hC σ t hσlo hσhi ht1
    rw [← hzre] at hh
    exact hh
  have hG : ‖Complex.Gamma (z / 2)‖ ≤ K * (1 + |t / 2|) ^ 11 * Real.exp (-(Real.pi / 2) * |t / 2|) := by
    have harg : z / 2 = ((σ / 2 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
      rw [hzre]
      apply Complex.ext <;> simp <;> ring
    have hx : σ / 2 ∈ Set.Icc (-5) 5 := by
      constructor <;> linarith
    have hb := hK (σ / 2) (t / 2) hx hthalf1
    rw [← harg] at hb
    exact hb
  have hGR : ‖Complex.Gammaℝ z‖ ≤ 4 * (K * (1 + |t / 2|) ^ 11 * Real.exp (-(Real.pi / 2) * |t / 2|)) := by
    calc
      ‖Complex.Gammaℝ z‖ = (Real.pi : ℝ) ^ (-(z.re / 2)) * ‖Complex.Gamma (z / 2)‖ := norm_GammaR_eq z
      _ ≤ 4 * ‖Complex.Gamma (z / 2)‖ := mul_le_mul_of_nonneg_right hpi_le (norm_nonneg _)
      _ ≤ 4 * (K * (1 + |t / 2|) ^ 11 * Real.exp (-(Real.pi / 2) * |t / 2|)) := by
        exact mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 4)
  have hGR2 : ‖Complex.Gammaℝ z‖ ≤ 4 * K * (1 + |t / 2|) ^ 11 := by
    calc
      ‖Complex.Gammaℝ z‖ ≤ 4 * (K * (1 + |t / 2|) ^ 11 * Real.exp (-(Real.pi / 2) * |t / 2|)) := hGR
      _ = 4 * K * (1 + |t / 2|) ^ 11 * Real.exp (-(Real.pi / 2) * |t / 2|) := by ring
      _ ≤ 4 * K * (1 + |t / 2|) ^ 11 * 1 := by
        have he : Real.exp (-(Real.pi / 2) * |t / 2|) ≤ 1 := by
          have hle1 : Real.exp (-((Real.pi / 2) * |t / 2|)) ≤ 1 := (Real.exp_le_one_iff).mpr (by
            have hz0e : 0 ≤ (Real.pi / 2) * |t / 2| := by positivity
            linarith)
          simpa using hle1
        exact mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * K * (1 + |t / 2|) ^ 11)
      _ = 4 * K * (1 + |t / 2|) ^ 11 := by ring
  have hLambda : ‖completedRiemannZeta z‖ ≤ 4 * C * K * (|t| + 3) ^ 4 * (1 + |t / 2|) ^ 11 := by
    calc
      ‖completedRiemannZeta z‖ = ‖riemannZeta z * Complex.Gammaℝ z‖ := by rw [hΛ]
      _ = ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by rw [norm_mul]
      _ ≤ (C * (|t| + 3) ^ 4) * (4 * K * (1 + |t / 2|) ^ 11) := mul_le_mul hzB hGR2 (norm_nonneg _) (by
        exact mul_nonneg hC0 (by positivity : 0 ≤ (|t| + 3) ^ 4))
      _ = 4 * C * K * (|t| + 3) ^ 4 * (1 + |t / 2|) ^ 11 := by ring
  have hhead : ‖((1 / 2 : ℂ) * z * (z - 1))‖ ≤ R * (R + 1) := by
    have hh := half_monomial_norm_le z
    calc
      ‖((1 / 2 : ℂ) * z * (z - 1))‖ ≤ ‖z‖ * (‖z‖ + 1) := hh
      _ ≤ R * (R + 1) := by
        have hz1 : ‖z‖ ≤ R := le_of_eq hz
        have hz2 : ‖z‖ + 1 ≤ R + 1 := by linarith
        exact mul_le_mul hz1 hz2 (by positivity : 0 ≤ ‖z‖ + 1) (by linarith)
  have hCK0 : 0 ≤ 4 * C * K := by
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC0) hK0
  have hmain : ‖xiV z‖ ≤ 4 * C * K * (R + 3) ^ 17 := by
    have hnorm : ‖xiV z‖ = ‖((1 / 2 : ℂ) * z * (z - 1))‖ * ‖completedRiemannZeta z‖ :=
      xiV_norm_eq z hz0 hz1
    have htR : |t| ≤ R := by
      have h1 := Complex.abs_im_le_norm z
      rw [hz] at h1
      simpa [t] using h1
    have hA_le : (|t| + 3) ^ 4 ≤ (R + 3) ^ 4 := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ |t| + 3) (by linarith) 4
    have hx1 : 1 + |t| / 2 ≤ |t| + 3 := by
      have hx0 : 0 ≤ |t| := abs_nonneg t
      linarith
    have hB_le : (1 + |t| / 2) ^ 11 ≤ (R + 3) ^ 11 := by
      have hx2 : 1 + |t| / 2 ≤ R + 3 := by
        have hx0 : 0 ≤ |t| := abs_nonneg t
        linarith [hx1]
      exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t| / 2) hx2 11
    have hR0 : 0 ≤ R := by linarith
    have hRR : R * (R + 1) ≤ (R + 3) ^ 2 := R_mul_R1_le_sq hR0
    have hProd : (R * (R + 1)) * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11) ≤ (R + 3) ^ 17 := by
      calc
        (R * (R + 1)) * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11)
            ≤ (R + 3) ^ 2 * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11) := by
              exact mul_le_mul_of_nonneg_right hRR (by positivity : 0 ≤ (|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11)
        _ ≤ (R + 3) ^ 2 * ((R + 3) ^ 4 * (1 + |t| / 2) ^ 11) := by
              have hA2 : (|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11 ≤ (R + 3) ^ 4 * (1 + |t| / 2) ^ 11 := by
                exact mul_le_mul_of_nonneg_right hA_le (by positivity : 0 ≤ (1 + |t| / 2) ^ 11)
              exact mul_le_mul_of_nonneg_left hA2 (by positivity : 0 ≤ (R + 3) ^ 2)
        _ ≤ (R + 3) ^ 2 * ((R + 3) ^ 4 * (R + 3) ^ 11) := by
              have hB2 : (R + 3) ^ 4 * (1 + |t| / 2) ^ 11 ≤ (R + 3) ^ 4 * (R + 3) ^ 11 := by
                exact mul_le_mul_of_nonneg_left hB_le (by positivity : 0 ≤ (R + 3) ^ 4)
              exact mul_le_mul_of_nonneg_left hB2 (by positivity : 0 ≤ (R + 3) ^ 2)
        _ = (R + 3) ^ 17 := by
              repeat rw [← pow_add]
    have hnorm_abs : |t / 2| = |t| / 2 := by
      rw [abs_div]
      norm_num
    have hLambda_abs : ‖completedRiemannZeta z‖ ≤ 4 * C * K * (|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11 := by
      simpa [hnorm_abs] using hLambda
    have hLambda' : ‖completedRiemannZeta z‖ ≤ 4 * C * K * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11) := by
      exact le_trans hLambda_abs (le_of_eq (by ac_rfl))
    calc
      ‖xiV z‖ = ‖((1 / 2 : ℂ) * z * (z - 1))‖ * ‖completedRiemannZeta z‖ := hnorm
      _ ≤ (R * (R + 1)) * (4 * C * K * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11)) := by
        exact mul_le_mul hhead hLambda' (norm_nonneg _) (by positivity : 0 ≤ R * (R + 1))
      _ ≤ (4 * C * K) * ((R * (R + 1)) * ((|t| + 3) ^ 4 * (1 + |t| / 2) ^ 11)) := by
        exact le_of_eq (by ac_rfl)
      _ ≤ (4 * C * K) * (R + 3) ^ 17 := by
        exact mul_le_mul_of_nonneg_left hProd hCK0

  calc
    ‖xiV z‖ ≤ 4 * C * K * (R + 3) ^ 17 := hmain
    _ ≤ (4 * C * K + 1) * (R + 3) ^ 17 := by
      have hpos : 0 ≤ (R + 3) ^ 17 := by positivity
      linarith

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

/-- `xiV` is bounded on the closed ball of radius `4`. -/
private lemma xiV_bound_ball : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ‖w‖ ≤ 4 → ‖xiV w‖ ≤ B := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) 4
  have hK : IsCompact K := isCompact_closedBall (0 : ℂ) 4
  have hKne : K.Nonempty := by
    refine ⟨(0 : ℂ), ?_⟩
    simp [K]
  have hcont : ContinuousOn (fun z : ℂ => ‖xiV z‖) K := by
    exact xiV_differentiable.continuous.norm.continuousOn
  rcases hK.exists_isMaxOn hKne hcont with ⟨x, hxK, hxmax⟩
  refine ⟨‖xiV x‖, norm_nonneg _, ?_⟩
  intro w hw
  have hwK : w ∈ K := by
    simpa [K] using hw
  exact hxmax hwK

/-- Monotonicity of the exponent shape in `R`. -/
private lemma exp_arg_mono {a R1 R2 : ℝ} (ha : 0 ≤ a) (hR1 : 0 ≤ R1) (h : R1 ≤ R2) :
    a * R1 * (Real.log (R1 + 2) + 2) ≤ a * R2 * (Real.log (R2 + 2) + 2) := by
  have hlog : Real.log (R1 + 2) ≤ Real.log (R2 + 2) := by
    exact Real.log_le_log (by linarith) (by linarith)
  have hE1 : R1 * (Real.log (R1 + 2) + 2) ≤ R2 * (Real.log (R2 + 2) + 2) := by
    have hb1 : Real.log (R1 + 2) + 2 ≤ Real.log (R2 + 2) + 2 := by linarith
    have hb2 : 0 ≤ Real.log (R1 + 2) + 2 := by
      exact add_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ R1 + 2)) (by norm_num)
    have hb3 : 0 ≤ Real.log (R2 + 2) + 2 := by
      have hl : 0 ≤ Real.log (R2 + 2) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ R2 + 2)
      linarith
    have hb4 : R1 * (Real.log (R2 + 2) + 2) ≤ R2 * (Real.log (R2 + 2) + 2) := by
      exact mul_le_mul_of_nonneg_right h hb3
    have hb5 : R1 * (Real.log (R1 + 2) + 2) ≤ R1 * (Real.log (R2 + 2) + 2) := by
      exact mul_le_mul_of_nonneg_left hb1 hR1
    linarith
  calc
    a * R1 * (Real.log (R1 + 2) + 2) = a * (R1 * (Real.log (R1 + 2) + 2)) := by ring
    _ ≤ a * (R2 * (Real.log (R2 + 2) + 2)) := by
      exact mul_le_mul_of_nonneg_left hE1 ha
    _ = a * R2 * (Real.log (R2 + 2) + 2) := by ring

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

/-- Growth of `xiV` on circles of radius `R ≥ 4`. -/
private lemma xiV_circle_big {C2 Cz : ℝ} (hC2p : 0 < C2)
    (hC2 : ∀ s : ℂ, 2 ≤ s.re → ‖riemannZeta s‖ ≤ C2)
    (hCz0 : 0 ≤ Cz)
    (hCz : ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ Cz * (|t| + 3) ^ 4) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 4 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖xiV z‖ ≤ Real.exp (c * R * (Real.log (R + 2) + 2)) := by
  let cR : ℝ := 3 + Real.log (C2 + 1) / (3 * (Real.log 5 + 2))
  let cM : ℝ := 17 + Real.log (4 * Cz * Commons.Analysis.Complex.K11 + 1) / (3 * (Real.log 5 + 2))
  let c : ℝ := 3 * cR + cM
  have hK11 : 0 ≤ Commons.Analysis.Complex.K11 := Commons.Analysis.Complex.K11_pos.le
  have hden : 0 < 3 * (Real.log 5 + 2) := three_log5_add_two_pos
  have hcR0 : 0 ≤ cR := by
    dsimp [cR]
    have hl : 0 ≤ Real.log (C2 + 1) := Real.log_nonneg (by linarith)
    have hq : 0 ≤ Real.log (C2 + 1) / (3 * (Real.log 5 + 2)) := div_nonneg hl (le_of_lt hden)
    linarith
  have hcM0 : 0 ≤ cM := by
    dsimp [cM]
    have hx1 : 1 ≤ 4 * Cz * Commons.Analysis.Complex.K11 + 1 := le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hCz0) hK11)
    have hl : 0 ≤ Real.log (4 * Cz * Commons.Analysis.Complex.K11 + 1) := Real.log_nonneg hx1
    have hq : 0 ≤ Real.log (4 * Cz * Commons.Analysis.Complex.K11 + 1) / (3 * (Real.log 5 + 2)) := div_nonneg hl (le_of_lt hden)
    linarith
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    linarith
  · intro R hR z hz
    let σ : ℝ := z.re
    have hR0 : 0 ≤ R := by linarith
    have hE0 : 0 ≤ R * (Real.log (R + 2) + 2) := by
      have hlog : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith : (1:ℝ) ≤ R + 2)
      exact mul_nonneg hR0 (by linarith)
    by_cases hA : 3 ≤ σ
    · -- right region directly
      have hz3 : 3 ≤ ‖z‖ := by rw [hz]; linarith
      have hA' : 3 ≤ z.re := by simpa [σ] using hA
      have hu2 : 2 ≤ z.re := by linarith
      have b := xiV_bound_right hC2p hC2 z hu2 hz3
      have bR : ‖xiV z‖ ≤ Real.exp (cR * R * (Real.log (R + 2) + 2)) := by
        simpa [cR, hz] using b
      apply le_trans bR
      apply Real.exp_le_exp.mpr
      have hc : cR ≤ c := by dsimp [c]; linarith
      calc
        cR * R * (Real.log (R + 2) + 2) = cR * (R * (Real.log (R + 2) + 2)) := by ring
        _ ≤ c * (R * (Real.log (R + 2) + 2)) := mul_le_mul_of_nonneg_right hc hE0
        _ = c * R * (Real.log (R + 2) + 2) := by ring
    · by_cases hBc : σ ≤ -1
      · -- functional-equation left
        let w : ℂ := 1 - z
        have hzr : z.re ≤ -1 := by simpa [σ] using hBc
        have hwre : 2 ≤ w.re := by
          dsimp [w]
          linarith
        have hw3 : 3 ≤ ‖w‖ := by
          have hz1 : ‖z - 1‖ = ‖w‖ := by
            dsimp [w]
            rw [show z - 1 = -(1 - z) by ring]
            rw [norm_neg]
          have htri : ‖z‖ ≤ ‖z - 1‖ + 1 := by
            have ha := norm_add_le (z - 1) (1 : ℂ)
            have hzid : (z - 1) + 1 = z := by ring
            rw [hzid] at ha
            rw [norm_one] at ha
            exact ha
          have hl : ‖z‖ - 1 ≤ ‖z - 1‖ := by linarith
          rw [hz1] at hl
          have hzR : ‖z‖ = R := hz
          linarith only [hz, hR, hl]
        have bw := xiV_bound_right hC2p hC2 w hwre hw3
        have hFE : ‖xiV z‖ = ‖xiV w‖ := by
          have h : xiV z = xiV w := by
            have h1 := xiV_one_sub z
            simpa [w] using h1.symm
          rw [h]
        have hwR : ‖w‖ ≤ R + 1 := by
          calc
            ‖w‖ = ‖z - 1‖ := by
              dsimp [w]
              rw [show 1 - z = -(z - 1) by ring]
              rw [norm_neg]
            _ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
            _ = ‖z‖ + 1 := by rw [norm_one]
            _ ≤ R + 1 := by
              have hzR : ‖z‖ ≤ R := le_of_eq hz
              linarith
        have hwE : ‖w‖ * (Real.log (‖w‖ + 2) + 2) ≤ (R + 1) * (Real.log (R + 3) + 2) := by
          have h0w : 0 ≤ ‖w‖ := norm_nonneg w
          have hlog1 : Real.log (‖w‖ + 2) ≤ Real.log (R + 3) := by
            exact Real.log_le_log (by linarith) (by linarith)
          have hlog0 : 0 ≤ Real.log (‖w‖ + 2) := by
            exact Real.log_nonneg (by linarith : (1:ℝ) ≤ ‖w‖ + 2)
          have hp1a : ‖w‖ * Real.log (‖w‖ + 2) ≤ (R + 1) * Real.log (‖w‖ + 2) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hlog0
          have hp1b : (R + 1) * Real.log (‖w‖ + 2) ≤ (R + 1) * Real.log (R + 3) := by
            exact mul_le_mul_of_nonneg_left hlog1 (by positivity : 0 ≤ R + 1)
          have hp1 : ‖w‖ * Real.log (‖w‖ + 2) ≤ (R + 1) * Real.log (R + 3) := by linarith
          have hp2 : ‖w‖ * 2 ≤ (R + 1) * 2 := by linarith
          linarith
        have hwE2 : cR * ‖w‖ * (Real.log (‖w‖ + 2) + 2) ≤ cR * (R + 1) * (Real.log (R + 3) + 2) := by
          have h1 : ‖w‖ * (Real.log (‖w‖ + 2) + 2) ≤ (R + 1) * (Real.log (R + 3) + 2) := hwE
          linarith only [mul_le_mul_of_nonneg_left h1 hcR0]
        have hfinal : ‖xiV z‖ ≤ Real.exp ((2 * cR) * R * (Real.log (R + 2) + 2)) := by
          calc
            ‖xiV z‖ = ‖xiV w‖ := hFE
            _ ≤ Real.exp (cR * ‖w‖ * (Real.log (‖w‖ + 2) + 2)) := by
              simpa [cR] using bw
            _ ≤ Real.exp (cR * (R + 1) * (Real.log (R + 3) + 2)) := by
              exact Real.exp_le_exp.mpr hwE2
            _ ≤ Real.exp (cR * (2 * R * (Real.log (R + 2) + 2))) := by
              have h1 : cR * (R + 1) * (Real.log (R + 3) + 2) ≤ cR * (2 * R * (Real.log (R + 2) + 2)) := by
                have h2 := leftconv hR
                have hcR0 : 0 ≤ cR := hcR0
                linarith only [mul_le_mul_of_nonneg_left h2 hcR0]
              exact Real.exp_le_exp.mpr h1
            _ = Real.exp ((2 * cR) * R * (Real.log (R + 2) + 2)) := by ring
        apply le_trans hfinal
        apply Real.exp_le_exp.mpr
        have hc : 2 * cR ≤ c := by dsimp [c]; linarith
        calc
          (2 * cR) * R * (Real.log (R + 2) + 2) = (2 * cR) * (R * (Real.log (R + 2) + 2)) := by ring
          _ ≤ c * (R * (Real.log (R + 2) + 2)) := mul_le_mul_of_nonneg_right hc hE0
          _ = c * R * (Real.log (R + 2) + 2) := by ring
      · -- middle strip
        have hσ1 : -1 ≤ σ := by linarith
        have hσ3s : σ < 3 := lt_of_not_ge hA
        have hKall : ∀ (x y : ℝ), x ∈ Set.Icc (-5) 5 → 1 ≤ |y| →
            ‖Complex.Gamma ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ Commons.Analysis.Complex.K11 * (1 + |y|) ^ 11 * Real.exp (-(Real.pi / 2) * |y|) := by
          intro x y hx hy
          have h := Commons.Analysis.Complex.gamma_upper_all x y hx hy
          simpa [Real.rpow_natCast] using h
        have bm := xiV_bound_middle (C := Cz) (K := Commons.Analysis.Complex.K11) hCz
          hKall
          hCz0 hK11 hR z hz (by simpa [σ] using hσ1) (by simpa [σ] using hσ3s)
        have hB1 : 1 ≤ 4 * Cz * Commons.Analysis.Complex.K11 + 1 := le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hCz0) hK11)
        have hR3 : 3 ≤ R := by linarith
        have hfin := poly_mul_exp_le (a := (0 : ℝ)) (ha := by norm_num)
          (B := 4 * Cz * Commons.Analysis.Complex.K11 + 1) (hB := hB1) (k := 17) (ρ := R) hR3
        have bm' : ‖xiV z‖ ≤ Real.exp (cM * R * (Real.log (R + 2) + 2)) := by
          have h1 : (4 * Cz * Commons.Analysis.Complex.K11 + 1) * (R + 3) ^ 17 ≤
              Real.exp (cM * R * (Real.log (R + 2) + 2)) := by
            calc
              (4 * Cz * Commons.Analysis.Complex.K11 + 1) * (R + 3) ^ 17
                  ≤ (4 * Cz * Commons.Analysis.Complex.K11 + 1) * (R + 3) ^ 17 * Real.exp (0 * R * (Real.log (R + 2) + 2)) := by
                    have he1 : 1 ≤ Real.exp (0 * R * (Real.log (R + 2) + 2)) := by
                      rw [zero_mul]
                      simp
                    exact le_mul_of_one_le_right (by positivity : 0 ≤ (4 * Cz * Commons.Analysis.Complex.K11 + 1) * (R + 3) ^ 17) he1
              _ ≤ Real.exp ((0 + 17 + Real.log (4 * Cz * Commons.Analysis.Complex.K11 + 1) / (3 * (Real.log 5 + 2))) * R * (Real.log (R + 2) + 2)) := by
                    simpa using hfin
              _ ≤ Real.exp (cM * R * (Real.log (R + 2) + 2)) := by
                    exact Real.exp_le_exp.mpr (by
                      dsimp [cM]
                      linarith)
          exact le_trans bm h1
        apply le_trans bm'
        apply Real.exp_le_exp.mpr
        have hc : cM ≤ c := by dsimp [c]; linarith
        calc
          cM * R * (Real.log (R + 2) + 2) = cM * (R * (Real.log (R + 2) + 2)) := by ring
          _ ≤ c * (R * (Real.log (R + 2) + 2)) := mul_le_mul_of_nonneg_right hc hE0
          _ = c * R * (Real.log (R + 2) + 2) := by ring

end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta

/-- **Circle growth of the entire completion**: for some constant `c`, on every circle
`|z| = R` with `R ≥ 2`, `‖Ξ(z)‖ ≤ exp(c·R·(log(R+2)+2))`. -/
theorem xiE_circle_growth :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖((1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)‖ ≤
        Real.exp (c * R * (Real.log (R + 2) + 2)) := by
  rcases zeta_norm_le_const_of_two_le_re with ⟨C2, hC2p, hC2⟩
  rcases zeta_strip_polyGrowth with ⟨Cz, hCzp, hCz⟩
  rcases xiV_circle_big hC2p hC2 hCzp.le hCz with ⟨cB, hcB0, hcBspec⟩
  rcases xiV_bound_ball with ⟨B, hB0, hB⟩
  let cSm : ℝ := Real.log (B + 1) / (2 * (Real.log 4 + 2))
  refine ⟨max cB cSm, ?_⟩
  intro R hR2 z hz
  change ‖xiV z‖ ≤ Real.exp (max cB cSm * R * (Real.log (R + 2) + 2))
  have hR0 : 0 ≤ R := by linarith
  have hE0 : 0 ≤ R * (Real.log (R + 2) + 2) := by
    have hlog : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith : (1:ℝ) ≤ R + 2)
    exact mul_nonneg hR0 (by linarith)
  by_cases hR4 : 4 ≤ R
  · have bnd := hcBspec R hR4 z hz
    apply le_trans bnd
    apply Real.exp_le_exp.mpr
    have hc : cB ≤ max cB cSm := le_max_left cB cSm
    calc
      cB * R * (Real.log (R + 2) + 2) = cB * (R * (Real.log (R + 2) + 2)) := by ring
      _ ≤ max cB cSm * (R * (Real.log (R + 2) + 2)) := mul_le_mul_of_nonneg_right hc hE0
      _ = max cB cSm * R * (Real.log (R + 2) + 2) := by ring
  · -- 2 ≤ R < 4 : compactness
    have hzle : ‖z‖ ≤ 4 := by rw [hz]; linarith
    have hbd : ‖xiV z‖ ≤ B := hB z hzle
    have hcSm0 : 0 ≤ cSm := by
      dsimp [cSm]
      have hx : 1 ≤ B + 1 := by linarith
      have hl : 0 ≤ Real.log (B + 1) := Real.log_nonneg hx
      exact div_nonneg hl (le_of_lt log4_add_two_pos)
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have hEge : 2 * (Real.log 4 + 2) ≤ R * (Real.log (R + 2) + 2) := by
      have hlogR : Real.log 4 ≤ Real.log (R + 2) := by
        exact Real.log_le_log (by norm_num) (by linarith)
      have hA1 : 2 * (Real.log 4 + 2) ≤ R * (Real.log 4 + 2) := by
        exact mul_le_mul_of_nonneg_right hR2 (by linarith)
      have hA2 : R * (Real.log 4 + 2) ≤ R * (Real.log (R + 2) + 2) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hR0
      linarith
    have hmain_small : ‖xiV z‖ ≤ Real.exp (cSm * R * (Real.log (R + 2) + 2)) := by
      calc
        ‖xiV z‖ ≤ B := hbd
        _ ≤ B + 1 := by linarith
        _ = Real.exp (Real.log (B + 1)) := by rw [Real.exp_log (by linarith : 0 < B + 1)]
        _ = Real.exp (cSm * (2 * (Real.log 4 + 2))) := by
          congr 1
          dsimp [cSm]
          field_simp [ne_of_gt log4_add_two_pos]
        _ ≤ Real.exp (cSm * (R * (Real.log (R + 2) + 2))) := by
          exact Real.exp_le_exp.mpr (by
            have h1 : cSm * (2 * (Real.log 4 + 2)) ≤ cSm * (R * (Real.log (R + 2) + 2)) := by
              exact mul_le_mul_of_nonneg_left hEge hcSm0
            simpa using h1)
        _ = Real.exp (cSm * R * (Real.log (R + 2) + 2)) := by ring
    apply le_trans hmain_small
    apply Real.exp_le_exp.mpr
    have hc : cSm ≤ max cB cSm := le_max_right cB cSm
    calc
      cSm * R * (Real.log (R + 2) + 2) = cSm * (R * (Real.log (R + 2) + 2)) := by ring
      _ ≤ max cB cSm * (R * (Real.log (R + 2) + 2)) := mul_le_mul_of_nonneg_right hc hE0
      _ = max cB cSm * R * (Real.log (R + 2) + 2) := by ring

end Commons.NumberTheory.Zeta
