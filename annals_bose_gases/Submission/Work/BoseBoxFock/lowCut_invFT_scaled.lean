import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.BoseFixB1S.kineticCrux.kinFT_decay_scale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The fixed profile `f(‖·‖)` and its basic properties -/

/-- The fixed compactly supported `C^∞` radial profile `q ↦ f(‖q‖)` attached to a `LowCut`. -/
def lowCutProf (fc : Work.BoseBoxFix.LowCut) : E3 → ℂ := fun q => ((fc.f ‖q‖ : ℝ) : ℂ)

/-- `q ↦ f(‖q‖)` is `C^∞`: near `0` it is the constant `f 0 = 1`, and away from `0` it is the
composition of the `C^∞` function `f` with the (smooth off the origin) norm. -/
lemma contDiff_radial_lowCut (fc : Work.BoseBoxFix.LowCut) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 => fc.f ‖q‖) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  rcases eq_or_ne q 0 with hq0 | hq
  · subst hq0
    refine (contDiffAt_const (c := fc.f 0)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E3) zero_lt_one] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [fc.one ‖y‖ (le_of_lt hy), fc.one 0 (by norm_num)]
  · exact (fc.smooth.contDiffAt (x := ‖q‖)).comp q (contDiffAt_norm ℝ hq)

/-- The complexified profile `f(‖·‖)` is `C^∞`. -/
lemma contDiff_lowCutProf (fc : Work.BoseBoxFix.LowCut) :
    ContDiff ℝ (⊤ : ℕ∞) (lowCutProf fc) := by
  have h2 := (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).comp (contDiff_radial_lowCut fc)
  have h2' : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 => Complex.ofRealCLM (fc.f ‖q‖)) := h2
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 => ((fc.f ‖q‖ : ℝ) : ℂ)) := by
    simpa [Complex.ofRealCLM_apply] using h2'
  exact h3

/-- `f(‖·‖)` is compactly supported, with support in the closed ball of radius `2`. -/
lemma hasCompactSupport_lowCutProf (fc : Work.BoseBoxFix.LowCut) :
    HasCompactSupport (lowCutProf fc) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : E3) 2)
    (isCompact_closedBall 0 2) ?_
  intro q hq
  rw [Function.mem_support] at hq
  by_contra hmem
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hmem
  refine hq ?_
  rw [lowCutProf, fc.zero ‖q‖ (le_of_lt hmem)]
  simp

/-! ## The elementary two-bound interpolation -/

/-- If `z ≤ A` and `r^N z ≤ A` then `z ≤ 2^N A / (1+r)^N` (for `A ≥ 0`, `r ≥ 0`). -/
lemma two_bound_arith (N : ℕ) {A r z : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (h1 : z ≤ A)
    (h2 : r ^ N * z ≤ A) : z ≤ 2 ^ N * A / (1 + r) ^ N := by
  have h1r : 0 < 1 + r := by linarith
  have hpos : 0 < (1 + r) ^ N := pow_pos h1r N
  rcases le_total r 1 with hr1 | hr1
  · rw [le_div_iff₀ hpos]
    have h2N : (1 + r) ^ N ≤ 2 ^ N := pow_le_pow_left₀ h1r.le (by linarith) N
    calc z * (1 + r) ^ N ≤ A * (1 + r) ^ N := mul_le_mul_of_nonneg_right h1 hpos.le
      _ ≤ A * 2 ^ N := mul_le_mul_of_nonneg_left h2N hA
      _ = 2 ^ N * A := by ring
  · have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
    have hz : z ≤ A / r ^ N := by
      rw [le_div_iff₀ (pow_pos hrpos N)]
      calc z * r ^ N = r ^ N * z := by ring
        _ ≤ A := h2
    refine hz.trans ?_
    rw [div_le_div_iff₀ (pow_pos hrpos N) hpos]
    calc A * (1 + r) ^ N ≤ A * (2 * r) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1r.le (by linarith) N) hA
      _ = 2 ^ N * A * r ^ N := by rw [mul_pow]; ring

/-! ## Schwartz decay of the inverse transform of the profile -/

/-- The `L¹` bound: `‖kinFT u ξ‖ ≤ ∫‖u‖`. -/
lemma norm_kinFT_le_integral (u : E3 → ℂ) (ξ : E3) :
    ‖Submission.BoseGases.kinFT u ξ‖ ≤ ∫ y : E3, ‖u y‖ := by
  rw [Submission.BoseGases.kinFT]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with y
  have hre : (-(Complex.I * (inner ℝ ξ y : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]

/-- **Rapid decay of `kinFT (f(‖·‖))`.**  For every `N` there is a constant with
`‖kinFT (f(‖·‖)) ξ‖ ≤ C/(1+‖ξ‖)^N`, uniformly in `ξ`. -/
lemma lowCut_kinFT_decay (fc : Work.BoseBoxFix.LowCut) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : E3,
      ‖Submission.BoseGases.kinFT (lowCutProf fc) ξ‖ ≤ C / (1 + ‖ξ‖) ^ N := by
  intro N
  refine ⟨2 ^ N * max (∫ q : E3, ‖lowCutProf fc q‖)
      (∫ q : E3, ‖iteratedFDeriv ℝ N (lowCutProf fc) q‖), by positivity, fun ξ => ?_⟩
  have hA0 : 0 ≤ ∫ q : E3, ‖lowCutProf fc q‖ := integral_nonneg (fun q => norm_nonneg _)
  have hAnn : 0 ≤ max (∫ q : E3, ‖lowCutProf fc q‖)
      (∫ q : E3, ‖iteratedFDeriv ℝ N (lowCutProf fc) q‖) := le_trans hA0 (le_max_left _ _)
  have h1 : ‖Submission.BoseGases.kinFT (lowCutProf fc) ξ‖
      ≤ max (∫ q : E3, ‖lowCutProf fc q‖)
          (∫ q : E3, ‖iteratedFDeriv ℝ N (lowCutProf fc) q‖) :=
    (norm_kinFT_le_integral (lowCutProf fc) ξ).trans (le_max_left _ _)
  have h2 : ‖ξ‖ ^ N * ‖Submission.BoseGases.kinFT (lowCutProf fc) ξ‖
      ≤ max (∫ q : E3, ‖lowCutProf fc q‖)
          (∫ q : E3, ‖iteratedFDeriv ℝ N (lowCutProf fc) q‖) :=
    (Work.BoseFixB1S.kineticCrux.kinFT_decay_core N (lowCutProf fc)
      (contDiff_lowCutProf fc) (hasCompactSupport_lowCutProf fc) ξ).trans (le_max_right _ _)
  exact two_bound_arith N hAnn (norm_nonneg ξ) h1 h2

/-! ## The change of variables and the assembly -/

/-- **The scaled Schwartz bound, in the scale variable `K`.** -/
lemma lowCut_invFT_scale (fc : Work.BoseBoxFix.LowCut) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ), 0 < K → ∀ x : E3,
      ‖∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          ((fc.f (‖p‖ / K) : ℝ) : ℂ)‖
        ≤ C * K ^ 3 * (1 + K * ‖x‖) ^ (-(N : ℤ)) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := lowCut_kinFT_decay fc N
  refine ⟨C₀, hC₀nn, ?_⟩
  intro K hK x
  set F : E3 → ℂ := fun p => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / K) : ℝ) : ℂ) with hF
  -- the substitution `p = K • q`
  have hcv : (∫ p : E3, F p) = (K ^ 3) • (∫ q : E3, F (K • q)) := by
    have hfr : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
    have h := Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure E3))
      (f := fun y : E3 => F (K • y)) hK.le
    rw [hfr] at h
    rw [show (∫ p : E3, F p) = ∫ y : E3, (fun y : E3 => F (K • y)) (K⁻¹ • y) from by
      simp only [smul_smul, mul_inv_cancel₀ hK.ne', one_smul]]
    exact h
  -- the pointwise identification of the rescaled integrand
  have hZ : (∫ q : E3, F (K • q)) = Submission.BoseGases.kinFT (lowCutProf fc) (-(K • x)) := by
    rw [Submission.BoseGases.kinFT]
    apply integral_congr_ae
    filter_upwards with q
    rw [hF]
    show Complex.exp (Complex.I * (inner ℝ (K • q) x : ℂ)) *
        ((fc.f (‖K • q‖ / K) : ℝ) : ℂ)
      = Complex.exp (-(Complex.I * (inner ℝ (-(K • x)) q : ℂ))) * ((fc.f ‖q‖ : ℝ) : ℂ)
    have hinner : (inner ℝ (-(K • x)) q) = -(inner ℝ (K • q) x) := by
      rw [inner_neg_left, real_inner_comm q (K • x), real_inner_smul_right,
        real_inner_smul_left]
    have harg : Complex.I * (inner ℝ (K • q) x : ℂ)
        = -(Complex.I * (inner ℝ (-(K • x)) q : ℂ)) := by
      rw [hinner]
      push_cast
      ring
    have hnorm : ‖K • q‖ / K = ‖q‖ := by
      rw [norm_smul, Real.norm_of_nonneg hK.le, mul_div_cancel_left₀ _ hK.ne']
    rw [harg, hnorm]
  have hnormZ : ‖∫ q : E3, F (K • q)‖ ≤ C₀ / (1 + K * ‖x‖) ^ N := by
    rw [hZ]
    have hb := hC₀ (-(K • x))
    have hnormarg : ‖-(K • x)‖ = K * ‖x‖ := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hK.le]
    rwa [hnormarg] at hb
  calc ‖∫ p : E3, F p‖
      = ‖(K ^ 3) • (∫ q : E3, F (K • q))‖ := by rw [hcv]
    _ = K ^ 3 * ‖∫ q : E3, F (K • q)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hK.le 3)]
    _ ≤ K ^ 3 * (C₀ / (1 + K * ‖x‖) ^ N) :=
        mul_le_mul_of_nonneg_left hnormZ (pow_nonneg hK.le 3)
    _ = C₀ * K ^ 3 * (1 + K * ‖x‖) ^ (-(N : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        ring

/-- **(A) The scaled Schwartz bound on the smoothed cutoff's inverse Fourier transform.**
`f` is the corpus's smooth cutoff (`LowCut`: `f = 1` on `(-∞,1]`, `f = 0` on `[2,∞)`, `C^∞`), so
`p ↦ f(‖p‖/(2κ))` is smooth and compactly supported, and its inverse Fourier transform obeys the
*scaled* Schwartz bound: every order `N` of decay is bought at the price of the rescaled argument
`2κ‖x‖`.  This is the quantitative input of the smooth-symbol Poisson/aliasing estimate
(`Submission/Work/BoseBoxFock/FINDING_etaHRow_lattice_small_crux.md` §11c): the aliasing terms are
evaluated at arguments `≳ ℓ|m|` while the kernel's scale is `1/(2κ) = d²ℓ`, so the effective
Schwartz argument is `≳ |m|/d²`.

Proof route: substitute `p = 2κ·q` (a linear change of variables in `ℝ³`), reducing the statement
to `|∫_q f(‖q‖) e^{i⟪2κx,q⟫} dq| ≤ C_N (1 + ‖2κx‖)^{-N}` for the *fixed* compactly supported
`C^∞` profile `f(‖·‖)`: split `‖2κx‖ ≤ 1` (trivial bound `‖f‖_1`) and `‖2κx‖ > 1` (integrate by
parts `N` times with `Δ_q`, `(i‖2κx‖)^{-2N}`, using `Δ^N(f(‖·‖)) ∈ C_c^∞`). -/
theorem lowCut_invFT_scaled (fc : Work.BoseBoxFix.LowCut) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : ℝ) (_hκ : 0 < κ) (x : EuclideanSpace ℝ (Fin 3)),
      ‖∫ p : EuclideanSpace ℝ (Fin 3),
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / (2 * κ)) : ℝ) : ℂ)‖
        ≤ C * (2 * κ) ^ 3 * (1 + (2 * κ) * ‖x‖) ^ (-(N : ℤ)) := by
  intro N
  obtain ⟨C, hCnn, hC⟩ := lowCut_invFT_scale fc N
  exact ⟨C, hCnn, fun κ hκ x => hC (2 * κ) (by positivity) x⟩

end Work.BoseBoxFock
