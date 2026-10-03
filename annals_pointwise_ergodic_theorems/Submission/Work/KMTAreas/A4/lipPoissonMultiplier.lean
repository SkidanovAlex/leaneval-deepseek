/-
# The Poisson-summation identity behind Proposition `lip` (Krause--Mirek--Tao, §5)

This module proves the twisted Poisson-summation identity

  `ε ∑_{u ∈ ℤ} ψ(ε u) e^{-2πi u θ} = ∑_{n ∈ ℤ} 𝓕ψ((θ + n)/ε)`

used in the construction of the major-arc function `F` of Proposition `lip` (the smoothing weight
`w(m) = ε (N')⁻¹ ∑_{m'} ψ(ε (m - m'))` is a dilated, periodised Schwartz function, and this identity
identifies its Fourier coefficients with the values `𝓕ψ((θ + n)/ε)`).

The proof is Mathlib's Poisson summation formula (`Real.tsum_eq_tsum_fourier_of_rpow_decay`) applied
to the *modulated* dilated Schwartz function `x ↦ e^{-2πiθx} ε ψ(ε x)`: its Fourier transform is
`𝓕ψ((· + θ)/ε)` (`lipRealFourierCharMul` and `realFourier_dilation`), and both it and its transform
decay like `⟨t⟩^{-12}` (from the Schwartz decay of `ψ` and `𝓕ψ`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The character `fourier (-u)` on the frequency circle, evaluated at the class of `θ`, is
`e^{-2πi u θ}`: the value of the additive character `𝐞` at `-(θ u)`. -/
lemma lipFourierNegCoe (u : ℤ) (θ : ℝ) :
    (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ) = (𝐞 (-(θ * (u : ℝ))) : ℂ) := by
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- **Modulation.**  Multiplying a function by the character `x ↦ e^{-2πiθx}` shifts its Fourier
transform by `θ`: `𝓕(x ↦ e^{-2πiθx} g x)(ξ) = 𝓕g(ξ + θ)`. -/
lemma lipRealFourierCharMul (g : ℝ → ℂ) (θ ξ : ℝ) :
    realFourier (fun x : ℝ => (𝐞 (-(θ * x)) : ℂ) * g x) ξ = realFourier g (ξ + θ) := by
  have hsmul : ∀ (z : Circle) (w : ℂ), z • w = (z : ℂ) * w := by
    intro z w; rw [Circle.smul_def, Algebra.smul_def]; simp
  simp only [realFourier]
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  simp_rw [hsmul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  rw [show -(x * ξ) + -(θ * x) = -(x * (ξ + θ)) by ring]

/-- **Big-`O` at infinity with a threshold.**  If `‖φ t‖ ≤ D (|t|⁻¹)^12` for all `|t| ≥ M` (with
`0 ≤ M`), then `φ = O((|·|)^{-12})` at infinity.  This is the version of
`isBigO_cocompact_of_le_inv_pow` needed for a function whose decay only starts at a finite scale
(here `2|θ|`, beyond which `(θ + t)/ε` is comparable with `|t|`). -/
lemma lipIsBigO_cocompact_of_le_inv_pow_large {φ : ℝ → ℂ} {D M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, M ≤ |t| → ‖φ t‖ ≤ D * (|t|⁻¹) ^ 12) :
    φ =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
  rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
  constructor
  · refine Asymptotics.IsBigO.of_bound D (Filter.eventually_atBot.mpr ⟨-M, fun t ht => ?_⟩)
    have ht' : M ≤ |t| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hg : ‖|t| ^ (-(12 : ℝ))‖ = (|t|⁻¹) ^ 12 := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), rpow_neg_twelve (abs_nonneg t)]
    rw [hg]
    exact h t ht'
  · refine Asymptotics.IsBigO.of_bound D (Filter.eventually_atTop.mpr ⟨M, fun t ht => ?_⟩)
    have ht' : M ≤ |t| := by
      rw [abs_of_nonneg (by linarith)]
      exact ht
    have hg : ‖|t| ^ (-(12 : ℝ))‖ = (|t|⁻¹) ^ 12 := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), rpow_neg_twelve (abs_nonneg t)]
    rw [hg]
    exact h t ht'

/-- **The Poisson-summation identity of Proposition `lip`** (Krause--Mirek--Tao, §5):
for a Schwartz function `ψ`, `0 < ε` and `θ ∈ ℝ`,

`ε ∑_{u ∈ ℤ} ψ(ε u) e^{-2πi u θ} = ∑_{n ∈ ℤ} 𝓕ψ((θ + n)/ε)`.

This is Poisson summation applied to the modulated dilation `x ↦ e^{-2πiθx} ε ψ(ε x)`. -/
theorem lipPoissonMultiplier (ψ : Work.Analysis.InverseTheory.SchwartzR) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    (ε : ℂ) * ∑' u : ℤ, ((ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((θ : ℝ) : Work.Analysis.InverseTheory.FreqCircle) : ℂ))
      = ∑' n : ℤ, (Work.KMTAreas.A4.schFT ψ ((θ + (n : ℝ)) / ε)) := by
  set C : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; have := schwartzSeminormSum_nonneg ψ; positivity
  have hψdec : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t := by
    intro t; rw [hCdef]; exact schwartz_decay ψ t
  have hFdec : ∀ t : ℝ, ‖realFourier (ψ : ℝ → ℂ) t‖ ≤ C * jbDecay 12 t := by
    intro t; rw [hCdef]; exact schwartz_fourier_decay ψ t
  -- the modulated, dilated Schwartz function whose Poisson summation is the identity
  let F : ℝ → ℂ := fun x : ℝ => (𝐞 (-(θ * x)) : ℂ) * ((ε : ℂ) * (ψ (ε * x) : ℂ))
  have hcont : Continuous F := by
    show Continuous fun x : ℝ => (𝐞 (-(θ * x)) : ℂ) * ((ε : ℂ) * (ψ (ε * x) : ℂ))
    have h1 : Continuous fun x : ℝ => (𝐞 (-(θ * x)) : ℂ) := by
      have hlin : Continuous fun x : ℝ => (2 * Real.pi * (-(θ * x)) : ℝ) := by fun_prop
      have h2 : Continuous fun x : ℝ => Complex.exp (↑(2 * Real.pi * (-(θ * x))) * Complex.I) :=
        Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hlin |>.mul continuous_const)
      simpa only [Real.fourierChar_apply] using h2
    have h3 : Continuous fun x : ℝ => (ψ (ε * x) : ℂ) :=
      ψ.continuous.comp (continuous_const.mul continuous_id)
    exact h1.mul (continuous_const.mul h3)
  -- decay of `F` itself
  have hF_bigO : F =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    refine isBigO_cocompact_of_le_inv_pow (D := C * (ε⁻¹) ^ 12 * ε) (by positivity) ?_
    intro t ht
    have hnorm : ‖F t‖ = ε * ‖ψ (ε * t)‖ := by
      show ‖(𝐞 (-(θ * t)) : ℂ) * ((ε : ℂ) * (ψ (ε * t) : ℂ))‖ = ε * ‖ψ (ε * t)‖
      rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_of_nonneg hε.le]
    have hjb : jbDecay 12 (ε * t) ≤ ((ε * |t|)⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      rw [inv_le_inv₀ (jb_pos _) (by positivity)]
      calc ε * |t| = |ε * t| := by rw [abs_mul, abs_of_pos hε]
        _ ≤ jb (ε * t) := abs_le_jb _
    calc ‖F t‖ = ε * ‖ψ (ε * t)‖ := hnorm
      _ ≤ ε * (C * jbDecay 12 (ε * t)) := mul_le_mul_of_nonneg_left (hψdec _) hε.le
      _ ≤ ε * (C * ((ε * |t|)⁻¹) ^ 12) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjb hCpos.le) hε.le
      _ = (C * (ε⁻¹) ^ 12 * ε) * (|t|⁻¹) ^ 12 := by rw [mul_inv, mul_pow]; ring
  -- the Fourier transform of `F`
  have hFF_eq : ∀ t : ℝ, (𝓕 F) t = realFourier (ψ : ℝ → ℂ) ((θ + t) / ε) := by
    intro t
    show realFourier F t = _
    dsimp only [F]
    have h := lipRealFourierCharMul (fun x : ℝ => (ε : ℂ) * (ψ (ε * x) : ℂ)) θ t
    rw [h]
    rw [realFourier_dilation (ψ : ℝ → ℂ) hε (t + θ)]
    rw [show t + θ = θ + t by ring]
  -- decay of `𝓕F` (only from scale `max (2|θ|) 1` onwards, which is where the two sides are
  -- comparable)
  have hFF_bigO : (𝓕 F) =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    rw [show (𝓕 F) = (fun t : ℝ => realFourier (ψ : ℝ → ℂ) ((θ + t) / ε)) from funext hFF_eq]
    refine lipIsBigO_cocompact_of_le_inv_pow_large (D := max (C * (2 * ε) ^ 12) C)
      (M := max (2 * |θ|) 1) (by positivity) ?_
    intro t ht
    have hθt : 2 * |θ| ≤ |t| := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
    have ht0 : 0 < |t| := lt_of_lt_of_le zero_lt_one ht1
    have h2 : |t| / 2 ≤ |θ + t| := by
      have h := abs_add_le (θ + t) (-θ)
      have h' : θ + t + -θ = t := by ring
      rw [h', abs_neg] at h
      linarith
    have h3 : |t| / (2 * ε) ≤ |(θ + t) / ε| := by
      rw [abs_div, abs_of_pos hε]
      have h := div_le_div_of_nonneg_right h2 hε.le
      rw [div_div] at h
      exact h
    have hB : 0 < |t| / (2 * ε) := by positivity
    have hA : 0 < |(θ + t) / ε| := lt_of_lt_of_le hB h3
    have hinv : (|(θ + t) / ε|)⁻¹ ≤ 2 * ε * |t|⁻¹ := by
      calc (|(θ + t) / ε|)⁻¹ ≤ (|t| / (2 * ε))⁻¹ := (inv_le_inv₀ hA hB).mpr h3
        _ = 2 * ε * |t|⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have hinv12 : ((|(θ + t) / ε|)⁻¹) ^ 12 ≤ ((2 * ε) * |t|⁻¹) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hinv 12
    have hjb1 : jbDecay 12 ((θ + t) / ε) ≤ ((|(θ + t) / ε|)⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      rw [inv_le_inv₀ (jb_pos _) hA]
      exact abs_le_jb _
    calc ‖realFourier (ψ : ℝ → ℂ) ((θ + t) / ε)‖ ≤ C * jbDecay 12 ((θ + t) / ε) := hFdec _
      _ ≤ C * ((2 * ε) * |t|⁻¹) ^ 12 := mul_le_mul_of_nonneg_left (hjb1.trans hinv12) hCpos.le
      _ = (C * (2 * ε) ^ 12) * (|t|⁻¹) ^ 12 := by rw [mul_pow]; ring
      _ ≤ max (C * (2 * ε) ^ 12) C * (|t|⁻¹) ^ 12 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- Poisson summation for `F`
  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay (f := F) hcont
    (by norm_num : (1 : ℝ) < 12) hF_bigO hFF_bigO (0 : ℝ)
  -- the two sides
  have hL : (∑' n : ℤ, F ((0 : ℝ) + (n : ℝ))) =
      (ε : ℂ) * ∑' u : ℤ, ((ψ (ε * (u : ℝ)) : ℂ) *
        (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ)) := by
    have hstep1 : (∑' n : ℤ, F ((0 : ℝ) + (n : ℝ))) = ∑' n : ℤ, F (n : ℝ) := by
      refine tsum_congr fun n => ?_
      rw [zero_add]
    rw [hstep1]
    have hstep2 : (∑' n : ℤ, F (n : ℝ)) =
        ∑' n : ℤ, (ε : ℂ) * ((ψ (ε * (n : ℝ)) : ℂ) * (𝐞 (-(θ * (n : ℝ))) : ℂ)) := by
      refine tsum_congr fun n => ?_
      dsimp only [F]
      ring
    rw [hstep2, tsum_mul_left]
    congr 1
    refine tsum_congr fun u => ?_
    rw [lipFourierNegCoe]
  have hR : (∑' n : ℤ, (𝓕 F) (n : ℝ) * fourier n ((0 : ℝ) : UnitAddCircle)) =
      ∑' n : ℤ, schFT ψ ((θ + (n : ℝ)) / ε) := by
    refine tsum_congr fun n => ?_
    have hzero : fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
      rw [fourier_coe_apply]; simp
    rw [hzero, mul_one, hFF_eq n, realFourier_coe]
    rfl
  calc (ε : ℂ) * ∑' u : ℤ, ((ψ (ε * (u : ℝ)) : ℂ) *
          (fourier (-u) ((θ : ℝ) : FreqCircle) : ℂ))
      = ∑' n : ℤ, F ((0 : ℝ) + (n : ℝ)) := hL.symm
    _ = ∑' n : ℤ, (𝓕 F) (n : ℝ) * fourier n ((0 : ℝ) : UnitAddCircle) := hpoisson
    _ = ∑' n : ℤ, schFT ψ ((θ + (n : ℝ)) / ε) := hR

end Work.KMTAreas.A4
