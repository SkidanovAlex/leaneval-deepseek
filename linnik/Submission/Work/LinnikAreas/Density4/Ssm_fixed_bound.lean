import Mathlib
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp
import Submission.Work.LinnikAreas.Density4.isZ_LFunction_zero
import Submission.Work.LinnikAreas.Density4.mollSeries_eq
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le
import Submission.Work.LinnikAreas.Density4.diffOn_Gamma_dslope_mul_lcmF
import Submission.Work.LinnikAreas.Density4.rect_edge_tendsto_zero
import Submission.Work.LinnikAreas.Density4.exp_neg_mul_log_pow_le
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.LinnikAreas.Density4.Ssm_eq_line
import Submission.Work.LinnikAreas.Density4.SsmPhiAux
import Submission.Work.LinnikAreas.Density4.Phi_shifted_bound
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le_gen
import Submission.Work.LinnikAreas.Density4.integrable_gamma_line_mul
import Submission.Work.LinnikAreas.Density4.Ssm_crude_bound
import Submission.Work.LinnikAreas.Density4.integrable_Phi_line_one
import Submission.Work.LinnikAreas.Density4.main_arith
import Submission.Work.LinnikAreas.Density4.Ssm_crude_case
import Submission.Work.LinnikAreas.Density4.lamMax_div_log_small
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

set_option maxHeartbeats 1000000

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-- `(1/2) ≤ log 2`. -/
lemma half_le_log_two : (1:ℝ)/2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- `log log log q ≤ log q` for `q ≥ 2`. -/
lemma logloglog_le_log (q : ℕ) (hq : 2 ≤ q) :
    Real.log (Real.log (Real.log q)) ≤ Real.log q := by
  have hlog : (1:ℝ)/2 ≤ Real.log (q : ℝ) := by
    have h : Real.log 2 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    linarith [half_le_log_two]
  have hpos : 0 < Real.log (q : ℝ) := by linarith
  rcases le_or_gt 0 (Real.log (Real.log (q:ℝ))) with h | h
  · have h1 : Real.log (Real.log (Real.log q)) ≤ Real.log (Real.log q) := Real.log_le_self h
    have h2 : Real.log (Real.log q) ≤ Real.log q := Real.log_le_self hpos.le
    linarith
  · have hlow : -1 ≤ Real.log (Real.log (q:ℝ)) := by
      have h2 : Real.log (1/2 : ℝ) ≤ Real.log (Real.log q) := Real.log_le_log (by norm_num) hlog
      have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have habs : |Real.log (Real.log (q:ℝ))| ≤ 1 := by
      rw [abs_of_neg h]; linarith
    have h2 : Real.log (Real.log (Real.log q)) = Real.log |Real.log (Real.log q)| := by
      rw [Real.log_abs]
    rw [h2]
    have := Real.log_nonpos (abs_nonneg _) habs
    linarith

/-- A zero in the working region lies in the critical strip. -/
lemma isZ_mem_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨N, hN, ψ, hψ1, hψprim, hz⟩ := Work.LinnikContract.API.isZ_primitive_facts h
  exact @Commons.NumberTheory.Linnik.completedL_zero_strip N hN ψ hψ1 hψprim ρ hz

/-- Under the contract's hypothesis `λ(ρ) ≤ λ₀(q)`, a zero in the working region has
`Re ρ ≥ 2/3`: `1 - Re ρ = λ/log q ≤ λ₀(q)/log q ≤ 1/3`. -/
lemma isZ_beta_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hq : 2 ≤ q) (h : IsZ χ ρ) (hlam : lamOf q ρ ≤ lamMax q) : 2/3 ≤ ρ.re := by
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hll : Real.log (Real.log (Real.log q)) ≤ Real.log q := logloglog_le_log q hq
  have hd : 1 - ρ.re ≤ 1/3 := by
    rw [lamOf] at hlam
    have h1 : (1 - ρ.re) ≤ lamMax q / Real.log q := by
      rw [le_div_iff₀ hlogpos]; linarith
    have h2 : lamMax q / Real.log q ≤ (1/3 : ℝ) := by
      rw [lamMax]
      rw [div_div, div_le_iff₀ (by positivity : (0:ℝ) < 3 * Real.log q)]
      linarith [hll]
    linarith
  linarith

/-- AREA 1 (`LBound13`) instantiated on the segment `1 - 1/k ≤ σ ≤ 1` of the critical strip,
for levels `q ≥ 3`. -/
lemma LFunction_line_bound (h1 : Area1) (k : ℕ) (hk : 3 ≤ k) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ q → χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 →
        ‖LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Cb * (q : ℝ) ^ ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
  obtain ⟨Cb, hCbpos, hCb⟩ := h1.1 k hk ε' hε'
  refine ⟨Cb, hCbpos, ?_⟩
  intro q hq χ h3 hχ1 σ t hσ1 hσ2
  refine hCb (N := q) (χ := χ) hχ1 σ t hσ1 ?_
  have hlog1 : 1 < Real.log (q : ℝ) := by
    have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast h3
    have hexp : Real.exp 1 < (q:ℝ) := by linarith [Real.exp_one_lt_d9]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact hexp
  have hloglog : 0 ≤ Real.log (Real.log (q:ℝ)) := Real.log_nonneg hlog1.le
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have : 0 ≤ Real.log (Real.log (q:ℝ)) / Real.log (q:ℝ) := div_nonneg hloglog hlogpos.le
  linarith

/-- Uniform vertical bound for `Γ` on the strip `1/2 ≤ Re ≤ 2`. -/
lemma Gamma_vertical_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 1/2 ≤ a → a ≤ 2 → ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨C₀, hC₀pos, ?_⟩
  intro a ha1 ha2 t
  have h1 := hC₀ a t ha1 ha2
  have hx1 : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ (a - 1/2) ≤ (1 + |t|) ^ (3/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hexp : Real.exp (-(Real.pi / 2) * |t|) = Real.exp (-(Real.pi / 2 * |t|)) := by
    congr 1; ring
  rw [hexp] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC₀pos.le)
    (Real.exp_nonneg _))

/-- The weighted vertical integral of `Γ` is bounded uniformly on `1/2 ≤ Re ≤ 2`. -/
lemma Gamma_line_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 1/2 ≤ a → a ≤ 2 →
      ∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ≤ C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Gamma_vertical_uniform
  set G : ℝ → ℝ := fun t => (1 + |t|) ^ (5/2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|)) with hGdef
  have hGint : Integrable G := by
    rw [hGdef]
    exact integrable_one_add_abs_rpow_exp (5/2) (Real.pi / 2) (by positivity)
  set M : ℝ := ∫ t : ℝ, G t with hMdef
  refine ⟨3 * C₀ * |M| + 1, by positivity, ?_⟩
  intro a ha1 ha2
  have hGnn : ∀ t : ℝ, 0 ≤ G t := fun t => by rw [hGdef]; positivity
  have hle : ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ≤ 3 * C₀ * G t := by
    intro t
    have h1 := hC₀ a ha1 ha2 t
    have hx1 : (0:ℝ) < 1 + |t| := by linarith only [abs_nonneg t]
    have h2 : (2 + |t|) ≤ 3 * (1 + |t|) := by linarith only [abs_nonneg t]
    have h7 : (1 + |t|) ^ (5/2 : ℝ) = (1 + |t|) ^ (3/2 : ℝ) * (1 + |t|) := by
      rw [show (5/2:ℝ) = 3/2 + 1 by norm_num, Real.rpow_add hx1, Real.rpow_one]
    have hGt : G t = (1 + |t|) ^ (5/2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|)) := by rw [hGdef]
    rw [hGt, h7]
    calc ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
        ≤ (C₀ * (1 + |t|) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) * (3 * (1 + |t|)) := by
          apply mul_le_mul h1 h2 (by linarith only [abs_nonneg t]) (by positivity)
      _ = 3 * C₀ * ((1 + |t|) ^ (3/2 : ℝ) * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|))) := by ring
  have hre_eq : ∀ (t : ℝ), ((a : ℂ) + (t : ℂ) * Complex.I).re = a := by
    intro t
    simp [Complex.add_re, Complex.mul_re]
  have hcontΓ : Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop :
      ContinuousAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) t)
    intro m hm
    have hre : ((a : ℂ) + (t : ℂ) * Complex.I).re = (-(m : ℂ)).re := congrArg Complex.re hm
    rw [hre_eq t] at hre
    have h2 : (-(m : ℂ)).re = -(m : ℝ) := by simp
    rw [h2] at hre
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith [ha1]
  have hcont : Continuous (fun t : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) :=
    (hcontΓ.norm).mul (continuous_const.add continuous_abs)
  have hint : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by
    refine (hGint.const_mul (3 * C₀)).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by linarith [abs_nonneg t]))]
    exact hle t
  calc ∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
      ≤ ∫ t : ℝ, 3 * C₀ * G t := integral_mono_ae hint (hGint.const_mul _) (ae_of_all _ hle)
    _ = 3 * C₀ * M := by rw [integral_const_mul, hMdef]
    _ ≤ 3 * C₀ * |M| + 1 := by
        have h1 : M ≤ |M| := le_abs_self M
        nlinarith only [mul_le_mul_of_nonneg_left h1 (by linarith only [hC₀pos] : (0:ℝ) ≤ 3 * C₀)]




/-! ## Contour shift of the Mellin representation (HB (11.9))

We now assemble the proof of HB (11.9).  `Ssm_eq_line` represents `Ssm` as a Mellin integral on
`Re s = 1` with the integrand `Γ(s)X^s L(ρ+s)F(ρ+s)`; using `mollSeries_eq` and the fact that
`Φ` agrees with that integrand off `s = 0` (`Phi_eq_naive`), and then shifting the contour to
`Re s = 1 - ρ.re - 1/k` (`vertical_contour_shift`), we get
`Ssm = (1/2π)∫ Φ(c₁+it) dt` with `c₁ = 1 - ρ.re - 1/k`.
-/

/-- A zero in the (open) critical strip gives the summability hypothesis of `Ssm_eq_line`. -/
lemma summable_norm_mollCoeff_of_pos (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hβ : 0 < ρ.re) :
    Summable (fun n : ℕ => ‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1))) :=
  summable_norm_mollCoeff_mul_rpow q hU χ (by linarith : (1:ℝ) < ρ.re + 1)

/-- The Mellin representation of `Ssm` with the *naive* integrand `Γ(s)X^sL(ρ+s)F(ρ+s)`. -/
theorem Ssm_eq_naive_line (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hU : 0 < U) (hUV : U ≤ V) (hW : 0 < W) (hX : 0 < X) (hβ : 0 < ρ.re) :
    Ssm q U V W X χ ρ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
          * lcmF q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [Ssm_eq_line q U V W X χ ρ hX hβ (summable_norm_mollCoeff_of_pos q hU χ hβ)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  have hlt : 1 < (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  rw [mollSeries_eq q hU hUV hW χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)) hlt]
  ring


/-! ### Pointwise bounds for `Φ` on the shifted vertical line -/

/-- Pointwise bound for the regularised integrand on the shifted line `Re s = c₁ ∶= 1 - ρ.re - 1/k`:
`‖Φ(s)‖ ≤ Cb · log q · (2+|t|) · ‖Γ(s+1)‖ · X^{c₁} · ((VW)^{1/k}(1+log(VW))³)`. -/
theorem norm_Phi_shifted_pointwise (q : ℕ) [NeZero q] (hq : 2 ≤ q) {U V W X : ℝ} (hU : 0 < U)
    (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) {k : ℕ} (hk : 1 ≤ k) {Cb c1 : ℝ} (_hCbpos : 0 < Cb)
    (hL0 : DirichletCharacter.LFunction χ ρ = 0) (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹)
    (hdist : 1 / Real.log q ≤ |c1|)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    ∀ t : ℝ, ‖Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cb * Real.log q * (2 + |t|) * ‖Complex.Gamma (1 + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
          * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3) := by
  intro t
  have hq1 : 1 < q := by omega
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hXpos : 0 < X := hX
  have hVWpos : (0:ℝ) < V * W := mul_pos (by linarith only [hV]) (by linarith only [hW])
  set s : ℂ := (c1 : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hs_re : s.re = c1 := by
    simp only [hsdef, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hs_ge : 1 / Real.log q ≤ ‖s‖ := by
    calc 1 / Real.log q ≤ |c1| := hdist
      _ = |s.re| := by rw [hs_re]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hs_ne : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs_ge
    have : (0:ℝ) < 1 / Real.log q := by positivity
    linarith
  have hs_inv : ‖s⁻¹‖ ≤ Real.log q := by
    rw [norm_inv, inv_le_comm₀ (norm_pos_iff.mpr hs_ne) hlogpos]
    simpa [one_div] using hs_ge
  have hdslope : dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
      = s⁻¹ * DirichletCharacter.LFunction χ (ρ + s) := by
    rw [dslope_of_ne _ hs_ne, slope]
    simp [hL0, smul_eq_mul]
  have hLn : ‖DirichletCharacter.LFunction χ (ρ + s)‖ ≤ Cb * (2 + |t|) := by
    simpa only [hsdef] using hLbd t
  have hs_re' : (ρ + s).re = 1 - (k : ℝ)⁻¹ := by rw [Complex.add_re, hs_re, hc1]; ring
  have hFnorm : ‖lcmF q U V W χ (ρ + s)‖
      ≤ (V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3 :=
    norm_lcmF_le q hU hUV hV hW χ hk hs_re'
  set DD : ℝ := (V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3 with hDDdef
  have key : ‖Phi q U V W X χ ρ s‖
      ≤ Cb * Real.log q * (2 + |t|) * ‖Complex.Gamma (1 + s)‖ * X ^ c1 * DD := by
    have hΓ : ‖Complex.Gamma (1 + s)‖ = ‖Complex.Gamma (s + 1)‖ := by rw [add_comm]
    rw [Phi, hdslope, hΓ]
    simp only [norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hs_re]
    have hstep : ‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖
        ≤ Real.log q * (Cb * (2 + |t|)) :=
      mul_le_mul hs_inv hLn (norm_nonneg _) (by positivity)
    have hA : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
        ≤ ‖Complex.Gamma (s + 1)‖ * (Real.log q * (Cb * (2 + |t|))) :=
      mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
    have hB : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * X ^ c1
        ≤ ‖Complex.Gamma (s + 1)‖ * (Real.log q * (Cb * (2 + |t|))) * X ^ c1 :=
      mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hXpos.le c1)
    have hA0 : (0:ℝ) ≤ ‖Complex.Gamma (s + 1)‖ * (Real.log q * (Cb * (2 + |t|))) * X ^ c1 :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg hlogpos.le
        (mul_nonneg _hCbpos.le (by positivity)))) (Real.rpow_nonneg hXpos.le c1)
    calc ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * X ^ c1 * ‖lcmF q U V W χ (ρ + s)‖
        ≤ ‖Complex.Gamma (s + 1)‖ * (Real.log q * (Cb * (2 + |t|))) * X ^ c1
            * ‖lcmF q U V W χ (ρ + s)‖ :=
          mul_le_mul_of_nonneg_right hB (norm_nonneg _)
      _ ≤ ‖Complex.Gamma (s + 1)‖ * (Real.log q * (Cb * (2 + |t|))) * X ^ c1 * DD :=
          mul_le_mul_of_nonneg_left hFnorm hA0
      _ = Cb * Real.log q * (2 + |t|) * ‖Complex.Gamma (s + 1)‖ * X ^ c1 * DD := by ring
  simpa only [hsdef, hDDdef] using key

/-- Integrability of the regularised integrand on the shifted vertical line. -/
theorem integrable_Phi_line_shifted (q : ℕ) [NeZero q] (hq : 2 ≤ q) {U V W X : ℝ}
    (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) {k : ℕ} (hk : 1 ≤ k) {Cb c1 : ℝ}
    (hCbpos : 0 < Cb) (hL0 : DirichletCharacter.LFunction χ ρ = 0)
    (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹) (ha : -1 < c1)
    (hdist : 1 / Real.log q ≤ |c1|)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    MeasureTheory.Integrable
      (fun t : ℝ => Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hbd := norm_Phi_shifted_pointwise q hq hU hUV hV hW hX χ ρ hk hCbpos hL0 hc1 hdist hLbd
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hVW1 : (1:ℝ) ≤ V * W := one_le_mul_of_one_le_of_one_le hV hW
  set M : ℝ := Cb * Real.log q * X ^ c1 with hMdef
  set DD : ℝ := (V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3 with hDDdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg hCbpos.le hlogq.le) (Real.rpow_nonneg hX.le c1)
  have hDD0 : 0 ≤ DD := by
    rw [hDDdef]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hVW1]) 3)
  have hg : MeasureTheory.Integrable
      (fun t : ℝ => (M * DD) * (‖Complex.Gamma (1 + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
        * (2 + |t|))) := by
    refine ((integrable_gamma_line_mul (c1 + 1) (by linarith)).const_mul (M * DD)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    have hc : (((c1 + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = 1 + ((c1 : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
    simp only [hc]
  refine hg.mono' ?_ ?_
  · have hcont : Continuous
        (fun t : ℝ => Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)) :=
      (continuousOn_Phi q U V W X χ ρ hX hχ).comp_continuous (by fun_prop) (by
        intro t
        show -1 < ((c1 : ℂ) + (t : ℂ) * Complex.I).re
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
        linarith)
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    calc ‖Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cb * Real.log q * (2 + |t|) * ‖Complex.Gamma (1 + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
            * X ^ c1 * ((V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3) := hbd t
      _ = (M * DD) * (‖Complex.Gamma (1 + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖ * (2 + |t|)) := by
          rw [hMdef, hDDdef]; ring


/-- Pointwise bound for `Φ` on the horizontal edges of the rectangle `[c₁,1] × [-T,T]`. -/
theorem norm_Phi_edge_pointwise (h1 : Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q) {U V W X : ℝ}
    (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re ≤ 1)
    (hβim : |ρ.im| ≤ 1)
    {k : ℕ} (hk : 3 ≤ k) {c1 : ℝ} (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc c1 1, ∀ T : ℝ, 1 ≤ T →
      (‖Phi q U V W X χ ρ ((x : ℂ) + (T : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ)) ∧
      (‖Phi q U V W X χ ρ ((x : ℂ) - (T : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ)) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Gamma_vertical_uniform
  obtain ⟨Cb0, hCb0pos, hCb0⟩ := h1.1 k hk (1:ℝ) (by norm_num)
  have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ) < (q:ℝ) := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlog3 : (1:ℝ) ≤ Real.log q := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact Real.exp_one_lt_three
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) hq3
    linarith
  have hVW1 : (1:ℝ) ≤ V * W := one_le_mul_of_one_le_of_one_le hV hW
  set DF : ℝ := (V * W) ^ (1 / (k:ℝ)) * (1 + Real.log (V * W)) ^ 3 with hDFdef
  have hDF0 : 0 ≤ DF := by
    rw [hDFdef]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [Real.log_nonneg hVW1]) 3)
  set CL : ℝ := Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) + (Real.log q + 8)
    with hCLdef
  have hCL0 : 0 < CL := by rw [hCLdef]; positivity
  have hCLbig : Real.log q + 8 ≤ CL := by
    rw [hCLdef]
    have h0 : (0:ℝ) ≤ Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) :=
      mul_nonneg hCb0pos.le (Real.rpow_nonneg (by linarith) _)
    linarith only [h0]
  have hCLbig2 : Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) ≤ CL := by
    rw [hCLdef]; linarith only [hlogq]
  have hLunif : ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ CL * (2 + |t|) := by
    intro σ t hσ1 hσ2
    rcases lt_or_ge σ 1 with hσlt | hσge
    · have hb := hCb0 (χ := χ) hχ σ t hσ1 (by
        have hll : 0 ≤ Real.log (Real.log (q:ℝ)) / Real.log (q:ℝ) :=
          div_nonneg (Real.log_nonneg hlog3) hlogq.le
        linarith only [hll, hσlt])
      refine le_trans hb ?_
      have hσle : (0:ℝ) ≤ 1 - σ := by linarith only [hσlt]
      have hk0 : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
      have hkk : (0:ℝ) ≤ 1 + 1/(k:ℝ) := by positivity
      have hexp0 : (0:ℝ) ≤ (1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + 1 :=
        add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσle) hkk) (by norm_num)
      have hexp : ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + 1)
          ≤ (1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1 := by
        have hle : 1 - σ ≤ 1/(k:ℝ) := by
          rw [div_eq_inv_mul] at hσ1 ⊢; linarith only [hσ1]
        nlinarith only [mul_le_mul_of_nonneg_right hle hkk]
      have hpow : (q:ℝ) ^ ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + 1)
          ≤ (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hq1] : (1:ℝ) ≤ (q:ℝ)) hexp
      have h1 : Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + 1)
          ≤ Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) :=
        mul_le_mul_of_nonneg_left hpow hCb0pos.le
      have h3 : Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + 1) * (1 + |t|)
          ≤ Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) * (2 + |t|) :=
        mul_le_mul h1 (by linarith only [abs_nonneg t]) (by positivity)
          (mul_nonneg hCb0pos.le (Real.rpow_nonneg (by linarith only [hq1]) _))
      have h4 : Cb0 * (q:ℝ) ^ ((1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + 1) * (2 + |t|)
          ≤ CL * (2 + |t|) :=
        mul_le_mul_of_nonneg_right hCLbig2 (by linarith only [abs_nonneg t])
      linarith only [h3, h4]
    · have hb := Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ
        ((σ:ℂ) + (t:ℂ) * Complex.I) (by simp; linarith only [hσge])
      have him : (((σ:ℂ) + (t:ℂ) * Complex.I)).im = t := by simp
      rw [him] at hb
      have hloglt : Real.log (2 + |t|) ≤ 1 + |t| := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 + |t| by positivity)
        linarith only [this]
      have habs : (0:ℝ) ≤ |t| := abs_nonneg t
      refine le_trans hb ?_
      have h6 : Real.log (q:ℝ) + Real.log (2 + |t|) + 6 ≤ Real.log (q:ℝ) + 7 + |t| := by
        linarith only [hloglt]
      have h7 : Real.log (q:ℝ) + 7 + |t| ≤ (Real.log (q:ℝ) + 8) * (2 + |t|) := by
        nlinarith only [hlog3, habs, mul_nonneg (by linarith only [hlog3] : (0:ℝ) ≤ Real.log q) habs]
      have h8 : (Real.log (q:ℝ) + 8) * (2 + |t|) ≤ CL * (2 + |t|) :=
        mul_le_mul_of_nonneg_right hCLbig (by linarith only [habs])
      linarith only [h6, h7, h8]
  set CLtot : ℝ := 4 * CL + ‖DirichletCharacter.LFunction χ ρ‖ with hCLtotdef
  have hCLtot0 : 0 ≤ CLtot := by rw [hCLtotdef]; positivity
  have hX0 : (0:ℝ) ≤ X := by linarith only [hX]
  refine ⟨Cg * CLtot * X * DF * 4 + 1, by positivity, ?_⟩
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ x ∈ Set.Icc c1 1, ∀ T : ℝ, 1 ≤ T →
      ‖Phi q U V W X χ ρ ((x : ℂ) + (ε * (T : ℂ)) * Complex.I)‖
        ≤ (Cg * CLtot * X * DF * 4 + 1) * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ) := by
    intro ε hε x hx T hT
    obtain ⟨hx1, hx2⟩ := hx
    have hT0 : (0:ℝ) < T := by linarith only [hT]
    have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    have hεT : |ε * T| = T := by rw [abs_mul, hεabs, one_mul, abs_of_pos hT0]
    have hc1' : c1 = 1 - ρ.re - 1/(k:ℝ) := by rw [hc1, one_div]
    have hx1' : 1 - ρ.re - 1/(k:ℝ) ≤ x := by rw [← hc1']; exact hx1
    have hkinv : (k:ℝ)⁻¹ ≤ 1/3 := by
      have h : (1:ℝ) / (k:ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 3 ≤ k by omega))
      simpa [one_div] using h
    have hxlow : -(1/3:ℝ) ≤ x := by linarith only [hx1', hkinv, hβ1, one_div (k:ℝ)]
    set s : ℂ := (x : ℂ) + (ε * (T : ℂ)) * Complex.I with hsdef
    have hs_eq : s = ((x : ℝ) : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    have hs_re : s.re = x := by rw [hs_eq]; simp
    have hs_im : s.im = ε * T := by rw [hs_eq]; simp
    have hs_norm : T ≤ ‖s‖ := by
      calc T = |s.im| := by rw [hs_im, hεT]
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hs_ne : s ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hs_norm; linarith only [hs_norm, hT0]
    have hΓb : ‖Complex.Gamma (s + 1)‖
        ≤ Cg * (1 + T) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2) * T) := by
      have hcast : s + 1 = ((x + 1 : ℝ) : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I := by
        rw [hs_eq]; push_cast; ring
      have hb := hCg (x + 1) (by linarith only [hxlow, hx2]) (by linarith only [hxlow, hx2]) (ε * T)
      have hb' : ‖Complex.Gamma (s + 1)‖
          ≤ Cg * (1 + T) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) := by
        rw [hcast]
        simpa only [hεT] using hb
      rwa [show -(Real.pi / 2) * T = -(Real.pi / 2 * T) from by ring]
    have hLedge : ‖DirichletCharacter.LFunction χ (ρ + s)‖ ≤ CL * (3 + T) := by
      have hre : (ρ + s).re = ρ.re + x := by rw [Complex.add_re, hs_re]
      have him : (ρ + s).im = ρ.im + ε * T := by rw [Complex.add_im, hs_im]
      have hsplit : ρ + s = ((ρ.re + x : ℝ) : ℂ) + ((ρ.im + ε * T : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, him]
      rw [hsplit]
      have hb := hLunif (ρ.re + x) (ρ.im + ε * T) (by linarith only [hx1']) (by linarith only [hβ1, hx2])
      refine le_trans hb ?_
      have h2 : (2 : ℝ) + |ρ.im + ε * T| ≤ 3 + T := by
        have hab := abs_add_le ρ.im (ε * T)
        rw [hεT] at hab
        linarith only [hab, hβim]
      exact mul_le_mul_of_nonneg_left h2 hCL0.le
    have hdsl : ‖dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s‖ ≤ CLtot := by
      have hnum : ‖DirichletCharacter.LFunction χ (ρ + s) - DirichletCharacter.LFunction χ ρ‖
          ≤ CL * (3 + T) + ‖DirichletCharacter.LFunction χ ρ‖ :=
        le_trans (norm_sub_le _ _) (add_le_add hLedge le_rfl)
      rw [dslope_of_ne _ hs_ne, slope]
      simp only [smul_eq_mul, vsub_eq_sub, sub_zero, add_zero, norm_mul]
      have hinv : ‖s⁻¹‖ ≤ T⁻¹ := by rw [norm_inv]; exact inv_anti₀ hT0 hs_norm
      calc ‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s) - DirichletCharacter.LFunction χ ρ‖
          ≤ T⁻¹ * (CL * (3 + T) + ‖DirichletCharacter.LFunction χ ρ‖) :=
            mul_le_mul hinv hnum (norm_nonneg _) (by positivity)
        _ ≤ CLtot := by
            rw [hCLtotdef]
            have h1 : T⁻¹ * (CL * (3 + T)) ≤ 4 * CL := by
              rw [inv_mul_le_iff₀ hT0]; nlinarith only [mul_le_mul_of_nonneg_left hT hCL0.le]
            have h2 : T⁻¹ * ‖DirichletCharacter.LFunction χ ρ‖
                ≤ ‖DirichletCharacter.LFunction χ ρ‖ := by
              rw [inv_mul_le_iff₀ hT0]
              nlinarith only [mul_le_mul_of_nonneg_left hT (norm_nonneg (DirichletCharacter.LFunction χ ρ))]
            calc T⁻¹ * (CL * (3 + T) + ‖DirichletCharacter.LFunction χ ρ‖)
                = T⁻¹ * (CL * (3 + T)) + T⁻¹ * ‖DirichletCharacter.LFunction χ ρ‖ := by ring
              _ ≤ 4 * CL + ‖DirichletCharacter.LFunction χ ρ‖ := add_le_add h1 h2
    have hXb : ‖(X : ℂ) ^ s‖ ≤ X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < X), hs_re]
      calc X ^ x ≤ X ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hX]) hx2
        _ = X := Real.rpow_one X
    have hFb : ‖lcmF q U V W χ (ρ + s)‖ ≤ DF := by
      have hre : 1 - (k:ℝ)⁻¹ ≤ (ρ + s).re := by
        have hh : (ρ + s).re = ρ.re + x := by rw [Complex.add_re, hs_re]
        rw [hh]; linarith [hx1']
      simpa [hDFdef] using
        norm_lcmF_le_gen q hU hUV hV hW χ (k := k) (by omega : 1 ≤ k) hre
    have hT4 : (1 + T) ^ (3/2:ℝ) ≤ 4 * T ^ (4:ℝ) := by
      have h1 : (1 + T) ≤ 2 * T := by linarith only [hT]
      have h2 : (1 + T) ^ (3/2:ℝ) ≤ (2 * T) ^ (3/2:ℝ) :=
        Real.rpow_le_rpow (by linarith only [hT]) h1 (by norm_num)
      have h3 : (2 * T) ^ (3/2:ℝ) = 2 ^ (3/2:ℝ) * T ^ (3/2:ℝ) :=
        Real.mul_rpow (by norm_num) hT0.le
      have h4 : (2:ℝ) ^ (3/2:ℝ) ≤ 4 := by
        have h2' : (2:ℝ) ^ (3/2:ℝ) = 2 * Real.sqrt 2 := by
          rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num),
            Real.rpow_one, ← Real.sqrt_eq_rpow]
        rw [h2']
        nlinarith only [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have h5 : T ^ (3/2:ℝ) ≤ T ^ (4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hT]) (by norm_num)
      have hT32 : (0:ℝ) ≤ T ^ (3/2:ℝ) := Real.rpow_nonneg hT0.le _
      calc (1 + T) ^ (3/2:ℝ) ≤ (2 * T) ^ (3/2:ℝ) := h2
        _ = 2 ^ (3/2:ℝ) * T ^ (3/2:ℝ) := h3
        _ ≤ 4 * T ^ (3/2:ℝ) := mul_le_mul_of_nonneg_right h4 hT32
        _ ≤ 4 * T ^ (4:ℝ) := mul_le_mul_of_nonneg_left h5 (by norm_num)
    rw [Phi, norm_mul, norm_mul, norm_mul]
    have hstep := mul_le_mul (mul_le_mul (mul_le_mul hΓb hdsl (norm_nonneg _) (by positivity))
      hXb (norm_nonneg _) (by positivity)) hFb (norm_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hE0 : 0 ≤ Real.exp (-(Real.pi / 2) * T) := Real.exp_nonneg _
    have hT40 : 0 ≤ T ^ (4:ℝ) := Real.rpow_nonneg hT0.le _
    have hred : Cg * (1 + T) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2) * T) * CLtot * X * DF
        ≤ (Cg * CLtot * X * DF * 4) * (Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ)) := by
      have h1 : Cg * (1 + T) ^ (3/2 : ℝ) ≤ Cg * (4 * T ^ (4:ℝ)) :=
        mul_le_mul_of_nonneg_left hT4 hCgpos.le
      calc Cg * (1 + T) ^ (3/2 : ℝ) * Real.exp (-(Real.pi / 2) * T) * CLtot * X * DF
          = (Cg * (1 + T) ^ (3/2 : ℝ))
              * (Real.exp (-(Real.pi / 2) * T) * CLtot * X * DF) := by ring
        _ ≤ (Cg * (4 * T ^ (4:ℝ))) * (Real.exp (-(Real.pi / 2) * T) * CLtot * X * DF) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (Cg * CLtot * X * DF * 4) * (Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ)) := by ring
    refine le_trans hred ?_
    calc (Cg * CLtot * X * DF * 4) * (Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ))
        = (Cg * CLtot * X * DF * 4) * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ) := by ring
      _ ≤ (Cg * CLtot * X * DF * 4 + 1) * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith only []) hE0) hT40
  intro x hx T hT
  refine ⟨?_, ?_⟩
  · have hk1 := key 1 (Or.inl rfl)
    simpa using hk1 x hx T hT
  · have hk2 := key (-1) (Or.inr rfl)
    simpa [sub_eq_add_neg] using hk2 x hx T hT

/-! ## The remaining assembly

The lemmas below (`isZ_mem_strip`, `isZ_beta_ge`, `LFunction_line_bound`, `Gamma_vertical_uniform`,
`Gamma_line_integral_bound`) supply the analytic bounds.  The remaining work is the assembly of
HB (11.9):

1. `Ssm_eq_line` + `mollSeries_eq` give `Ssm = (1/2π) ∫_{Re s = 1} Γ(s) X^s L(ρ+s) F(ρ+s) ds`;
2. the integrand is regularised as `Phi = Γ(s+1)·(L(ρ+·)-L(ρ))/s·X^s·F(ρ+s)`, which is entire
   (`diffOn_Gamma_dslope_mul_lcmF`) and agrees with the naive integrand off `s = 0`
   (`LFunction χ ρ = 0` by `isZ_LFunction_zero`);
3. `vertical_contour_shift` moves the contour to `Re s = 1 - Re ρ - 1/k`, where
   `Re(ρ+s) = 1 - 1/k` so that AREA 1 applies and `norm_lcmF_le` applies;
4. the resulting bound is
   `≪ Cb·CΓ·(log q)^{x/3+4}·q^{-(x-v-w-1/3)/k + 1/(3k²) + ε'}`;
5. when the shifted contour passes within `1/log q` of `s = 0` (equivalently
   `|1 - Re ρ - 1/k| < 1/log q`), the hypothesis forces `q` into a bounded range
   (`lamMax_div_log_small`), where `Ssm_crude_bound` applies.
-/


/-! ## Plan for the remaining assembly (HB (11.9))

**Status.**  The analytic bounds in this file are proved; the auxiliary lemmas
`Ssm_eq_line` (Mellin representation on `Re s = 1`), `mollSeries_eq`,
`diffOn_Gamma_dslope_mul_lcmF`, `norm_lcmF_le`, `norm_lcmF_le_gen`, `isZ_LFunction_zero`,
`Gamma_line_integral_bound`, `Gamma_vertical_uniform`, `rect_edge_tendsto_zero`,
`exp_neg_mul_log_pow_le`, `lamMax_div_log_small`, `Phi_shifted_bound` and the definitions
`mollCoeff`, `lcmF`, `mollSeries`, `Phi` (in `SsmSetup.lean`) are available.  What remains is
the assembly described below.

**The key point (why the contour must be kept away from `s = 0`).**  Bounding the shifted
contour integral by `‖Γ‖ · ‖L‖ · ‖F‖` naively fails: near `s = 0` the pole of `Γ` is cancelled
by the zero of `L(ρ+·)`, and the true size of the integrand there is `|L'(ρ)|`, which is *not*
controlled by the AREA 1 bound.  The regularised integrand `Phi = Γ(s+1)·(L(ρ+·)-L(ρ))/s·X^s·F`
is entire and takes care of the cancellation, and the extra hypothesis
`1/log q ≤ |1 - Re ρ - 1/k|` makes the shifted contour `Re s = 1 - Re ρ - 1/k` stay at distance
`≥ 1/log q` from `s = 0`.  Then `‖dslope‖ = ‖L(ρ+s)‖/‖s‖ ≤ Cb·(2+|t|)·log q`, which is exactly
what the estimate needs (the AREA 1 exponent `1/(3k)` is preserved).  When
`|1 - Re ρ - 1/k| < 1/log q`, the hypotheses `λ(ρ) ≤ λ₀(q)` force
`1/k < (λ₀(q)+1)/log q`, i.e. `q` is bounded (`lamMax_div_log_small`), and there
`Ssm_crude_bound` applies.

**Steps.**

1. Per level `q ≥ 16`, with `U = q^u, V = q^v, W = q^w, X = q^x`, `δ := 1 - ρ.re`,
   `c₁ := δ - 1/k`:
   `Ssm = (1/2π)∫_{Re s = 1} Γ(s)X^s L(ρ+s)F(ρ+s) ds` (`Ssm_eq_line` + `mollSeries_eq`);
   the integrand agrees with `Phi` off `s = 0` (`hL0 := isZ_LFunction_zero`, `Gamma_add_one`,
   `dslope_of_ne`), and `vertical_contour_shift` (with `diffOn_Gamma_dslope_mul_lcmF` and the
   integrability/edge hypotheses) gives `Ssm = (1/2π)∫ Φ(c₁+it) dt`.
2. `Phi_shifted_bound` then bounds that integral by
   `Cb·CΓ·log q·X^{c₁}·((VW)^{1/k}(1+log(VW))³)`, where `Cb` comes from `LFunction_line_bound`
   (AREA 1, on `1-1/k ≤ σ ≤ 1`) and `CΓ` from `Gamma_line_integral_bound` (`a = c₁+1 ∈ [2/3,2]`).
   Using `X^{c₁} = q^{xδ}q^{-x/k}`, `q^{xδ} = e^{xλ} ≤ e^{xλ₀} ≤ (log q)^{x/3}`,
   `(VW)^{1/k} = q^{(v+w)/k}` and `1 + log(VW) ≤ (1+v+w)log q`, this is
   `≪ (log q)^{x/3+4}·q^{-δ'/k + 1/(3k²) + ε'}` with `δ' = x - v - w - 1/3`.
3. Choose `k` with `3 ≤ k` and `δ'k > 2`, and `ε' := δ'/(2k) > 0`; then
   `μ := δ'/k - 1/(3k²) - ε' > 0`.
4. For `q ≥ Q` (with `Q` from `exp_neg_mul_log_pow_le`, exponent `x/3 + 6`):
   `‖Ssm‖ ≤ C(log q)^{x/3+5}q^{-μ} ≤ C/log q`.
5. For the remaining `q` (in particular all `q` with `|c₁| < 1/log q`, which are bounded by
   `lamMax_div_log_small`), `Ssm_crude_bound` with the absolute constant
   `B` from `card_divisors_le_rpow 1/2` and `norm_mollCoeff_le` gives
   `‖Ssm‖ ≤ B(X+1)³ ≤ B((max Q 16)^x + 1)³`, and `log q ≥ log 2 > 0` converts this to `C/log q`.
6. Conclude with `C := max(C_main, B' * log(max Q 16)) + 1`.
-/

/-- `(k:ℝ)⁻¹ ≤ 1/3` for `k ≥ 3`. -/
lemma kinv_le_third {k : ℕ} (hk : 3 ≤ k) : (k:ℝ)⁻¹ ≤ 1/3 := by
  have h : (1:ℝ) / (k:ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
  simpa [one_div] using h

/-- In the "shifted contour close to `0`" case the hypothesis `λ(ρ) ≤ λ₀(q)` forces a bound on
`q`: if `|1 - ρ.re - 1/k| < 1/log q` and `(λ₀(q)+1)/log q < 1/k`, we get a contradiction. -/
lemma small_case_bounded (q : ℕ) (hq : 2 ≤ q) {k : ℕ} (hk : 0 < k)
    (hQlam : (Real.log (Real.log (Real.log (q:ℝ))) / 3 + 1) / Real.log (q:ℝ) < 1/(k:ℝ))
    {ρ : ℂ} (hlam : Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hsmall : |1 - ρ.re - (k:ℝ)⁻¹| < 1/Real.log q) : False := by
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hc1 : -(1/Real.log q) < 1 - ρ.re - (k:ℝ)⁻¹ := (abs_lt.mp hsmall).1
  have hki : (k:ℝ)⁻¹ = 1/(k:ℝ) := (one_div (k:ℝ)).symm
  rw [hki] at hc1
  have hlam' : (1 - ρ.re) * Real.log (q:ℝ) ≤ Real.log (Real.log (Real.log (q:ℝ))) / 3 := by
    simpa [Work.LinnikContract.lamOf, Work.LinnikContract.lamMax] using hlam
  have h3 : 1 - ρ.re ≤ (Real.log (Real.log (Real.log (q:ℝ))) / 3) / Real.log (q:ℝ) := by
    rw [le_div_iff₀ hlogpos]; linarith
  have h4 : (Real.log (Real.log (Real.log (q:ℝ))) / 3 + 1) / Real.log (q:ℝ)
      = (Real.log (Real.log (Real.log (q:ℝ))) / 3) / Real.log (q:ℝ) + 1/Real.log (q:ℝ) :=
    add_div _ _ _
  rw [h4] at hQlam
  have hone : (0:ℝ) < 1/Real.log (q:ℝ) := by positivity
  have : 1/(k:ℝ) < (Real.log (Real.log (Real.log (q:ℝ))) / 3) / Real.log (q:ℝ)
      + 1/Real.log (q:ℝ) := by linarith
  linarith

/-! ## The contour shift and the final assembly -/

/-- The two horizontal edge integrals of `Φ` over the rectangle `[c₁,1] × [-R,R]` tend to `0`. -/
theorem Phi_edge_tendsto (h1 : Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q) {U V W X : ℝ}
    (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re ≤ 1)
    (hβim : |ρ.im| ≤ 1)
    {k : ℕ} (hk : 3 ≤ k) {c1 : ℝ} (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹) (hc1le : c1 ≤ 1) :
    Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in c1..1,
        Phi q U V W X χ ρ ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in c1..1,
        Phi q U V W X χ ρ ((x : ℂ) - (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbd⟩ := norm_Phi_edge_pointwise h1 q hq hU hUV hV hW hX χ hχ ρ hβ0 hβ1 hβim hk hc1
  refine ⟨rect_edge_tendsto_zero (Phi q U V W X χ ρ) c1 1 4 C hc1le hCpos ?_, ?_⟩
  · intro x hx T hT
    exact (hbd x hx T hT).1
  · have harg : ∀ (x R : ℝ), starRingEnd ℂ ((x : ℂ) + (R : ℂ) * Complex.I)
        = (x : ℂ) - (R : ℂ) * Complex.I := by
      intro x R
      simp [map_add, map_mul]
      ring
    have hb : ∀ x ∈ Set.Icc c1 1, ∀ T : ℝ, 1 ≤ T →
        ‖(fun s : ℂ => Phi q U V W X χ ρ (starRingEnd ℂ s)) ((x : ℂ) + (T : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ (4:ℝ) := by
      intro x hx T hT
      beta_reduce
      rw [harg x T]
      exact (hbd x hx T hT).2
    have h2 := rect_edge_tendsto_zero (fun s : ℂ => Phi q U V W X χ ρ (starRingEnd ℂ s)) c1 1 4 C
      hc1le hCpos hb
    have heq : (fun R : ℝ => ∫ x : ℝ in c1..1,
          Phi q U V W X χ ρ (starRingEnd ℂ ((x : ℂ) + (R : ℂ) * Complex.I)))
        = fun R : ℝ => ∫ x : ℝ in c1..1, Phi q U V W X χ ρ ((x : ℂ) - (R : ℂ) * Complex.I) := by
      funext R
      beta_reduce
      apply intervalIntegral.integral_congr
      intro x _
      beta_reduce
      rw [harg x R]
    rw [heq] at h2
    exact h2

/-- **The contour shift.**  On the vertical line `Re s = c₁ = 1 - ρ.re - 1/k` the regularised
integrand is integrable; hence `Ssm` equals `(1/2π) ∫ Φ(c₁+it) dt`. -/
theorem Ssm_contour_shift (h1 : Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {U V W X : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re ≤ 1)
    (hβim : |ρ.im| ≤ 1)
    {k : ℕ} (hk : 3 ≤ k) {c1 Cb : ℝ} (hc1 : c1 = 1 - ρ.re - (k:ℝ)⁻¹) (hCbpos : 0 < Cb)
    (hL0 : DirichletCharacter.LFunction χ ρ = 0)
    (hdist : 1 / Real.log q ≤ |c1|)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    Ssm q U V W X χ ρ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Phi q U V W X χ ρ ((c1 : ℂ) + (t : ℂ) * Complex.I) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hXpos : 0 < X := by linarith
  have hA := Ssm_eq_naive_line q U V W X χ ρ hU hUV (by linarith) hXpos hβ0
  have hstep2 : (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
        * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
        * DirichletCharacter.LFunction χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
        * lcmF q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Phi q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    have hFG : (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
          * lcmF q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = fun t : ℝ => Phi q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      funext t
      have hsne : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        simp at hre
      rw [Phi_eq_naive q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I) hL0 hsne]
    rw [hFG]
  have hkinv : (k:ℝ)⁻¹ ≤ 1/3 := by
    have h : (1:ℝ) / (k:ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 3 ≤ k by omega))
    simpa [one_div] using h
  have hk0 : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
  have hc1gt : -1 < c1 := by rw [hc1]; linarith [hβ1, hkinv]
  have hc1le : c1 ≤ 1 := by rw [hc1]; linarith [hβ0, hk0]
  have hFd : ∀ R : ℝ, DifferentiableOn ℂ (Phi q U V W X χ ρ)
      (Set.uIcc c1 1 ×ℂ Set.uIcc (-R) R) := fun R =>
    diffOn_Gamma_dslope_mul_lcmF q U V W X χ hχ hXpos ρ c1 1 hc1gt hc1le R
  have hIp := integrable_Phi_line_shifted q (by omega) hU hUV hV hW hXpos χ hχ ρ
    (by omega : 1 ≤ k) hCbpos hL0 hc1 hc1gt hdist hLbd
  have hIq := integrable_Phi_line_one q hU hUV hV hW hXpos χ hχ ρ hβ0 hL0
  obtain ⟨htop, hbot⟩ :=
    Phi_edge_tendsto h1 q hq hU hUV hV hW hX χ hχ ρ hβ0 hβ1 hβim hk hc1 hc1le
  have hshift := Commons.Analysis.Complex.vertical_contour_shift (Phi q U V W X χ ρ) c1 1
    hc1le hFd hIp hIq htop hbot
  rw [hA, hstep2]
  exact congrArg (fun z : ℂ => (1 / (2 * Real.pi)) * z) hshift

/-- **The main (large `q`) case of HB (11.9).**  Under the "shifted contour is far from `0`"
hypothesis `1/log q ≤ |1 - ρ.re - 1/k|`, the contour shift together with the AREA 1 bound gives
`‖Ssm‖ ≤ C/log q` for all `q` beyond a threshold depending only on the fixed parameters. -/
theorem Ssm_main_bound (h1 : Area1) (u v w x : ℝ) (hw : 0 < w) (hwu : w < u) (huv : u < v)
    (hvx : v < x) (hx : v + w + 1/3 < x)
    (k : ℕ) (hk : 3 ≤ k) (e : ℝ) (he : 0 < e)
    (hek : e + 1/(3*((k:ℝ))^2) < (x - v - w - 1/3)/(k:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      3 ≤ q → χ ≠ 1 → DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 1 →
      Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q →
      (1 / Real.log q) ≤ |1 - ρ.re - (k:ℝ)⁻¹| → Q ≤ q →
      ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖ ≤ C / Real.log q := by
  obtain ⟨Cb0, hCb0pos, hCb0⟩ := LFunction_line_bound h1 k hk he
  obtain ⟨CΓ, hCΓpos, hCΓ⟩ := Gamma_line_integral_bound
  obtain ⟨K, hKpos, Q₀, hK⟩ := main_arith v w x hw (by linarith) hvx hx k hk e he hek
  refine ⟨Cb0 * CΓ * K / (2 * Real.pi) + 1, by positivity, max Q₀ 16, ?_⟩
  intro q _ χ ρ hq3 hχ hL0 hβ0 hβ1 hβim hlam hdist hqQ
  have hqQ0 : Q₀ ≤ q := le_trans (le_max_left _ _) hqQ
  have hq16 : 16 ≤ q := le_trans (le_max_right _ _) hqQ
  have hq2 : 2 ≤ q := by omega
  have hq1R : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1R
  have hxv : 0 < x := by linarith
  have hvw : 0 < v + w := by linarith
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hU : (0:ℝ) < (q:ℝ)^u := Real.rpow_pos_of_pos hqpos u
  have hUV : (q:ℝ)^u ≤ (q:ℝ)^v :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (q:ℝ)) (by linarith)
  have hV : (1:ℝ) ≤ (q:ℝ)^v := Real.one_le_rpow (by linarith) (by linarith)
  have hW : (1:ℝ) ≤ (q:ℝ)^w := Real.one_le_rpow (by linarith) (by linarith)
  have hX : (1:ℝ) ≤ (q:ℝ)^x := Real.one_le_rpow (by linarith) (by linarith)
  have hXpos : (0:ℝ) < (q:ℝ)^x := by linarith
  have hlogq1 : (1:ℝ) < Real.log (q:ℝ) := by
    have hlog3 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact Real.exp_one_lt_three
    exact lt_of_lt_of_le hlog3
      (Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ q by omega)))
  have hloglog_pos : 0 < Real.log (Real.log (q:ℝ)) := Real.log_pos hlogq1
  set E : ℝ := (1/3:ℝ) * (1/(k:ℝ)) * (1 + 1/(k:ℝ)) + e with hEdef
  set c1 : ℝ := 1 - ρ.re - (k:ℝ)⁻¹ with hc1def
  set Cb : ℝ := Cb0 * (q:ℝ)^E with hCbdef
  have hCbpos : 0 < Cb := by rw [hCbdef]; positivity
  have hLbd : ∀ t : ℝ,
      ‖DirichletCharacter.LFunction χ (ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I))‖ ≤ Cb * (2 + |t|) := by
    intro t
    have hp : (0:ℝ) ≤ 1/(k:ℝ) := by positivity
    have hb := hCb0 q χ hq3 hχ (1 - 1/(k:ℝ)) (ρ.im + t) le_rfl (by linarith)
    have hEeq : (1/3:ℝ) * (1 - (1 - 1/(k:ℝ))) * (1 + 1/(k:ℝ)) + e = E := by
      rw [hEdef]; field_simp; ring
    rw [hEeq] at hb
    have harg : ρ + ((c1 : ℂ) + (t : ℂ) * Complex.I)
        = (((1 - 1/(k:ℝ)) : ℝ) : ℂ) + (((ρ.im + t) : ℝ) : ℂ) * Complex.I := by
      rw [hc1def]
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    refine le_trans hb ?_
    have h2 : (1:ℝ) + |ρ.im + t| ≤ 2 + |t| := by
      have := abs_add_le ρ.im t; linarith only [this, hβim]
    rw [hCbdef]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hΓ : ∫ t : ℝ, ‖Complex.Gamma ((((c1 : ℂ) + (t : ℂ) * Complex.I)) + 1)‖ * (2 + |t|) ≤ CΓ := by
    have hkinv := kinv_le_third hk
    have hk0 : (0:ℝ) ≤ (k:ℝ)⁻¹ := by positivity
    have h := hCΓ (c1 + 1) (by rw [hc1def]; linarith [hβ1, hkinv])
      (by rw [hc1def]; linarith [hβ0, hk0])
    refine le_of_eq_of_le ?_ h
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have harg : ((c1 : ℂ) + (t : ℂ) * Complex.I) + 1 = (((c1 + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg]
  have hcontour := Ssm_contour_shift h1 q hq3 hU hUV hV hW hX χ hχ ρ hβ0 hβ1 hβim hk hc1def hCbpos
    hL0 hdist hLbd
  have hPhi := Phi_shifted_bound hq2 χ hχ ρ (by omega : 1 ≤ k) hCbpos hCΓpos hU hUV hV hW hX hL0
    hc1def hdist hLbd hΓ
  set DF : ℝ := ((q:ℝ)^v * (q:ℝ)^w) ^ (1/(k:ℝ)) * (1 + Real.log ((q:ℝ)^v * (q:ℝ)^w))^3 with hDFdef
  have hnorm : ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖
      ≤ (1/(2*Real.pi)) * (Cb * CΓ * Real.log q * ((q:ℝ)^x)^c1 * DF) := by
    rw [hcontour]
    rw [norm_mul]
    have hconst : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
      have hgoal : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by
        rw [Complex.ofReal_div (1:ℝ) (2*Real.pi), Complex.ofReal_mul (2:ℝ) Real.pi]
        norm_num
      have h1 : ‖(((1/(2*Real.pi) : ℝ)) : ℂ)‖ = |(1/(2*Real.pi) : ℝ)| :=
        RCLike.norm_ofReal (1/(2*Real.pi))
      rw [← hgoal, h1, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*Real.pi))]
    rw [hconst, hDFdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (MeasureTheory.norm_integral_le_integral_norm _) hPhi
  -- the arithmetic
  have hc1split : ((q:ℝ)^x)^c1 = ((q:ℝ)^(x*(1-ρ.re))) * ((q:ℝ)^(-(x/(k:ℝ)))) := by
    have hexp : x * c1 = x * (1 - ρ.re) + (-(x/(k:ℝ))) := by rw [hc1def]; field_simp; ring
    rw [← Real.rpow_mul hqpos.le x c1, hexp, Real.rpow_add hqpos]
  have hLL : (q:ℝ)^(x*(1-ρ.re)) ≤ (Real.log (Real.log (q:ℝ)))^(x/3) := by
    rw [Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hloglog_pos]
    apply Real.exp_le_exp.mpr
    have hlam : (1 - ρ.re) * Real.log q ≤ Real.log (Real.log (Real.log (q:ℝ))) / 3 := by
      simpa [Work.LinnikContract.lamOf, Work.LinnikContract.lamMax] using hlam
    calc Real.log (q:ℝ) * (x * (1 - ρ.re))
        = x * ((1 - ρ.re) * Real.log (q:ℝ)) := by ring
      _ ≤ x * (Real.log (Real.log (Real.log (q:ℝ))) / 3) :=
          mul_le_mul_of_nonneg_left hlam hxv.le
      _ = Real.log (Real.log (Real.log (q:ℝ))) * (x / 3) := by ring_nf
  have hDFpow : ((q:ℝ)^v * (q:ℝ)^w) ^ (1/(k:ℝ)) = (q:ℝ)^((v+w)/(k:ℝ)) := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_mul hqpos.le]
    congr 1; field_simp
  have hDFlog : Real.log ((q:ℝ)^v * (q:ℝ)^w) = (v + w) * Real.log (q:ℝ) := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hqpos v))
      (ne_of_gt (Real.rpow_pos_of_pos hqpos w)), Real.log_rpow hqpos, Real.log_rpow hqpos]
    ring
  have hExpeq : E + -(x/(k:ℝ)) + (v+w)/(k:ℝ)
      = 1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ) := by
    rw [hEdef]; field_simp; ring
  have hQ : (q:ℝ)^E * (q:ℝ)^(-(x/(k:ℝ))) * (q:ℝ)^((v+w)/(k:ℝ))
      = (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ)) := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos, hExpeq]
  set Mexpr : ℝ := Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ)))^(x/3)
      * (1 + (v+w) * Real.log (q:ℝ))^3
      * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ)) with hMexprdef
  have hid : Cb * CΓ * Real.log q * ((q:ℝ)^x)^c1 * DF
      = Cb0 * CΓ * Real.log q
          * ((q:ℝ)^(x*(1-ρ.re))
              * ((q:ℝ)^E * (q:ℝ)^(-(x/(k:ℝ))) * (q:ℝ)^((v+w)/(k:ℝ))))
          * (1 + (v+w) * Real.log (q:ℝ))^3 := by
    rw [hCbdef, hDFdef, hDFpow, hDFlog, hc1split]
    ring
  have hscale : Cb0 * CΓ * Real.log q
        * ((q:ℝ)^(x*(1-ρ.re))
            * ((q:ℝ)^E * (q:ℝ)^(-(x/(k:ℝ))) * (q:ℝ)^((v+w)/(k:ℝ))))
        * (1 + (v+w) * Real.log (q:ℝ))^3 ≤ Cb0 * CΓ * Mexpr := by
    rw [hMexprdef, hQ]
    have hA0 : (0:ℝ) ≤ Cb0 * CΓ * Real.log q := by positivity
    have hQ0 : (0:ℝ) ≤ (1 + (v+w) * Real.log (q:ℝ))^3 := by positivity
    have hstep : (q:ℝ)^(x*(1-ρ.re)) * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ))
        ≤ (Real.log (Real.log (q:ℝ)))^(x/3) * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ)) :=
      mul_le_mul_of_nonneg_right hLL (Real.rpow_nonneg hqpos.le _)
    calc Cb0 * CΓ * Real.log q * ((q:ℝ)^(x*(1-ρ.re)) * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ)))
          * (1 + (v+w) * Real.log (q:ℝ))^3
        ≤ Cb0 * CΓ * Real.log q
            * ((Real.log (Real.log (q:ℝ)))^(x/3) * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ)))
            * (1 + (v+w) * Real.log (q:ℝ))^3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hA0) hQ0
      _ = Cb0 * CΓ * (Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ)))^(x/3)
            * (1 + (v+w) * Real.log (q:ℝ))^3 * (q:ℝ)^(1/(3*(k:ℝ)) + 1/(3*(k:ℝ)^2) + e - (x - v - w)/(k:ℝ))) := by ring
  have hM := hK q hqQ0
  calc ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖
      ≤ (1/(2*Real.pi)) * (Cb * CΓ * Real.log q * ((q:ℝ)^x)^c1 * DF) := hnorm
    _ ≤ (1/(2*Real.pi)) * (Cb0 * CΓ * Mexpr) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hid]
        exact hscale
    _ = (Cb0 * CΓ * (1/(2*Real.pi))) * Mexpr := by ring
    _ ≤ (Cb0 * CΓ * (1/(2*Real.pi))) * (K / Real.log q) :=
        mul_le_mul_of_nonneg_left (by rw [← hMexprdef] at hM; exact hM) (by positivity)
    _ = (Cb0 * CΓ * K / (2 * Real.pi)) / Real.log q := by ring
    _ ≤ (Cb0 * CΓ * K / (2 * Real.pi) + 1) / Real.log q := by
        rw [div_le_div_iff_of_pos_right hlogq]; linarith

/-- **HB (1992) §11, (11.9), with the constant quantified inside the exponents.** For each *fixed* tuple of exponents `0 < w < u < v < x` with `v + w + 1/3 < x` and `2w + 1/3 < u` there is `C > 0` such that for every `q ≥ 2`, every `χ : DirichletCharacter ℂ q` and every zero `ρ` of `χ` in the working region `|Im ρ| ≤ 1` with `λ(ρ) ≤ λ₀(q)`, the smoothed sum `Ssm = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n/X}` (with `U = q^u, V = q^v, W = q^w, X = q^x`) satisfies `‖Ssm‖ ≤ C / log q`. -/
theorem Ssm_fixed_bound (h1 : Work.LinnikContract.Area1) :
    ∀ (u v w x : ℝ), 0 < w → w < u → u < v → v < x → v + w + 1/3 < x → 2*w + 1/3 < u →
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        2 ≤ q → Work.LinnikContract.IsZ χ ρ →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q →
        ‖Work.LinnikAreas.Density4.Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖
          ≤ C / (Real.log q) := by
  intro u v w x hw hwu huv hvx hx h2w
  set δ : ℝ := x - v - w - 1/3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith only [hx]
  -- pick `k ≥ 3` with `δ k > 2`
  have hkexists : ∃ k : ℕ, 3 ≤ k ∧ 2 < δ * (k:ℝ) := by
    refine ⟨max 3 (Nat.floor (2/δ) + 1), le_max_left _ _, ?_⟩
    have h1' : 2/δ < (Nat.floor (2/δ) : ℝ) + 1 := Nat.lt_floor_add_one (2/δ)
    have h2' : ((Nat.floor (2/δ) : ℕ) : ℝ) + 1 ≤ ((max 3 (Nat.floor (2/δ) + 1) : ℕ) : ℝ) := by
      have hh : Nat.floor (2/δ) + 1 ≤ max 3 (Nat.floor (2/δ) + 1) := le_max_right _ _
      exact_mod_cast hh
    have h3' : 2/δ < ((max 3 (Nat.floor (2/δ) + 1) : ℕ) : ℝ) := lt_of_lt_of_le h1' h2'
    rw [div_lt_iff₀ hδpos] at h3'
    linarith
  obtain ⟨k, hk3, hkδ⟩ := hkexists
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have he : 0 < δ / (2 * (k:ℝ)) := by positivity
  have hek : δ/(2*(k:ℝ)) + 1/(3*((k:ℝ))^2) < (x - v - w - 1/3)/(k:ℝ) := by
    have hδeq : x - v - w - 1/3 = δ := hδdef.symm
    rw [hδeq]
    have h2 : δ/(2*(k:ℝ)) + 1/(3*((k:ℝ))^2) = (3*δ*(k:ℝ) + 2)/(6*((k:ℝ))^2) := by
      field_simp; ring
    have h3 : δ/(k:ℝ) = (6*δ*(k:ℝ))/(6*((k:ℝ))^2) := by
      field_simp
    rw [h2, h3, div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 6*((k:ℝ))^2)]
    linarith only [hkδ]
  obtain ⟨Qlam, hQlam⟩ := lamMax_div_log_small (1/(k:ℝ)) (by positivity)
  obtain ⟨Cmain, hCmainpos, Qmain, hmain⟩ :=
    Ssm_main_bound h1 u v w x hw hwu huv hvx hx k hk3 (δ/(2*(k:ℝ))) he hek
  obtain ⟨Ccrude, hCrudepos, hcrude⟩ :=
    Ssm_crude_case u v w x hw huv hvx (by linarith) (max (max Qmain 16) Qlam)
  refine ⟨max Cmain Ccrude, lt_max_of_lt_left hCmainpos, ?_⟩
  intro q _ χ ρ hq2 hZ hlam
  have hρ0 : 0 < ρ.re := (isZ_mem_strip hZ).1
  have hρ1 : ρ.re < 1 := (isZ_mem_strip hZ).2
  have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogpos' : (0:ℝ) ≤ Real.log (q:ℝ) := hlogpos.le
  by_cases hqQ : max (max Qmain 16) Qlam ≤ q
  · have hq3 : 3 ≤ q := by
      have h16 : 16 ≤ q :=
        le_trans (le_max_right Qmain 16) (le_trans (le_max_left (max Qmain 16) Qlam) hqQ)
      omega
    have hQl := hQlam q (le_trans (le_max_right (max Qmain 16) Qlam) hqQ)
    have hcase : (1 / Real.log (q:ℝ)) ≤ |1 - ρ.re - (k:ℝ)⁻¹| := by
      by_contra hcon
      push_neg at hcon
      exact (small_case_bounded q hq2 (by omega) hQl hlam hcon).elim
    have hb := hmain q χ ρ hq3 hZ.1 (isZ_LFunction_zero hZ) hρ0 (le_of_lt hρ1) hZ.2.2 hlam hcase
      (le_trans (le_max_left Qmain 16) (le_trans (le_max_left (max Qmain 16) Qlam) hqQ))
    exact le_trans hb (div_le_div_of_nonneg_right (le_max_left _ _) hlogpos')
  · have hlt : q < max (max Qmain 16) Qlam := lt_of_not_ge hqQ
    have hb := hcrude q hq2 hlt χ ρ (le_of_lt hρ0)
    exact le_trans hb (div_le_div_of_nonneg_right (le_max_right _ _) hlogpos')
