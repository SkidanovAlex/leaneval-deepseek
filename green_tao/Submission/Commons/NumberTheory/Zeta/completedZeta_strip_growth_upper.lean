import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds

noncomputable section
open Complex
open scoped Real Topology BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.Zeta

/-- `‖σ + i·t‖ ≤ σ + |t|` for `0 ≤ σ`. -/
private lemma norm_add_mul_I_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ σ + |t| := by
  calc
    ‖((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ ‖(σ : ℂ)‖ + ‖(Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ = σ + |t| := by
      have h1 : ‖(σ : ℂ)‖ = |σ| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
        rw [norm_mul, Complex.norm_I]
        rw [Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [h1, h2]
      rw [abs_of_nonneg hσ0]

/-- `Λ(s) = Gammaℝ(s)·ζ(s)` for `Re s > 0` with `s ≠ 0`. -/
private lemma completedRiemannZeta_eq_GammaR_mul (s : ℂ) (hs0 : s ≠ 0) (hsre : 0 < s.re) :
    completedRiemannZeta s = s.Gammaℝ * riemannZeta s := by
  have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hζ : riemannZeta s = completedRiemannZeta s / s.Gammaℝ := riemannZeta_def_of_ne_zero hs0
  calc
    completedRiemannZeta s = (completedRiemannZeta s / s.Gammaℝ) * s.Gammaℝ := by
      field_simp [hG]
    _ = s.Gammaℝ * riemannZeta s := by
      rw [hζ]
      ring

/-- Uniform polynomial upper bound for the Deligne Gamma factor on the strip
`0 < σ ≤ 2`, `|t| ≥ 2`:
`‖Gammaℝ (σ + i·t)‖ ≤ C · (1 + |t|) · e^{-π·|t|/4}`.

The key step is the elementary shift `|Γ(x + iy)| = |Γ(x + 1 + iy)| / |x + iy|
≤ |Γ(x + 1 + iy)| / |y|` for `x ∈ (0,1]`, `|y| ≥ 1`, which converts the
uniform (in real part ∈ [1,2]) exponential-decay bound of `Γ` into one valid
uniformly on the whole strip `0 < Re ≤ 2`. -/
private lemma norm_GammaR_strip_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ t : ℝ, 0 < σ → σ ≤ 2 → 2 ≤ |t| →
        ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * (1 + |t|) * Real.exp (-(Real.pi / 4) * |t|) := by
  let K0 : ℝ := Commons.Analysis.Complex.Mbig * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)
  let C : ℝ := 2 * K0
  have hMpos : 0 < Commons.Analysis.Complex.Mbig := Commons.Analysis.Complex.Mbig_pos
  have hK0pos : 0 < K0 := by
    dsimp [K0]
    have hpi2 : 0 < (Real.pi / 2) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by positivity) (2 : ℝ)
    exact mul_pos (mul_pos hMpos (Real.exp_pos 1)) hpi2
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) hK0pos
  · intro σ t hσ0 hσ2 ht
    let x : ℝ := σ / 2
    let y : ℝ := t / 2
    let w : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    have hx0 : 0 < x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 := by dsimp [x]; linarith
    have hy_ge' : (1 : ℝ) ≤ |t| / 2 := by
      calc
        (1 : ℝ) = (2 : ℝ) / 2 := by norm_num
        _ ≤ |t| / 2 := by
          exact div_le_div₀ (abs_nonneg t) ht (by norm_num : (0 : ℝ) < (2 : ℝ)) (le_rfl : (2 : ℝ) ≤ (2 : ℝ))
    have hy_ge : 1 ≤ |y| := by
      dsimp [y]
      simpa [abs_div] using hy_ge'
    have hy_pos : 0 < |y| := by linarith
    have hw_ne : w ≠ 0 := by
      intro h
      have hwim : w.im = 0 := congrArg Complex.im h
      have hy0 : y = 0 := by simpa [w] using hwim
      have hyabs : |y| = 0 := by rw [hy0]; simp
      linarith
    have hx1a : 1 ≤ x + 1 := by linarith
    have hx1b : x + 1 ≤ 2 := by linarith
    have hU := Commons.Analysis.Complex.gamma_upper_main (L := (2 : ℝ))
        (by norm_num : (2 : ℝ) ≤ 11) hx1a hx1b y
    let E : ℝ := Real.exp (-(Real.pi / 2) * |y|)
    have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg _
    have hwadd : w + 1 = (((x + 1 : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
      dsimp [w]
      apply Complex.ext <;> simp
    have hΓw1 : ‖Complex.Gamma (w + 1)‖ ≤ K0 * (1 + |y|) ^ (2 : ℝ) * E := by
      dsimp [K0, E]
      simpa [hwadd] using hU
    have hΓw1_nonneg : 0 ≤ ‖Complex.Gamma (w + 1)‖ := norm_nonneg _
    have hq : (1 + |y|) ^ (2 : ℝ) / |y| ≤ 2 * (1 + |y|) := by
      have hrpow : (1 + |y|) ^ (2 : ℝ) = (1 + |y|) ^ 2 := Real.rpow_natCast (1 + |y|) 2
      rw [hrpow]
      have h1 : (1 + |y|) ≤ 2 * |y| := by nlinarith
      have hbase0 : 0 ≤ 1 + |y| := by positivity
      have hsq : (1 + |y|) ^ 2 ≤ 2 * |y| * (1 + |y|) := by
        calc
          (1 + |y|) ^ 2 = (1 + |y|) * (1 + |y|) := by ring
          _ ≤ (2 * |y|) * (1 + |y|) := mul_le_mul_of_nonneg_right h1 hbase0
      calc
        (1 + |y|) ^ 2 / |y| ≤ (2 * |y| * (1 + |y|)) / |y| := by
          exact div_le_div₀ (by positivity) hsq hy_pos (le_rfl)
        _ = 2 * (1 + |y|) := by
          field_simp [hy_pos.ne']
    have hGΓ : ‖Complex.Gamma w‖ ≤ C * (1 + |y|) * E := by
      have hdivy : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ / |y| := by
        have hGrec : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hw_ne
        have hGdiv : Complex.Gamma (w + 1) / w = Complex.Gamma w := by
          rw [hGrec]
          field_simp [hw_ne]
        have hnorm_eq : ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by
          calc
            ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1) / w‖ := by rw [hGdiv]
            _ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by rw [norm_div]
        have hnorm_ge_y : |y| ≤ ‖w‖ := by
          calc |y| = |w.im| := by simp [w]
            _ ≤ ‖w‖ := Complex.abs_im_le_norm w
        calc
          ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := hnorm_eq
          _ ≤ ‖Complex.Gamma (w + 1)‖ / |y| := by
            exact div_le_div₀ (norm_nonneg _) (le_rfl) hy_pos hnorm_ge_y
      calc
        ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ / |y| := hdivy
        _ ≤ (K0 * (1 + |y|) ^ (2 : ℝ) * E) / |y| := by
          have hcpos : 0 ≤ K0 * (1 + |y|) ^ (2 : ℝ) * E := by
            have hbase0 : 0 ≤ 1 + |y| := by positivity
            have hpow0 : 0 ≤ (1 + |y|) ^ (2 : ℝ) := Real.rpow_nonneg hbase0 (2 : ℝ)
            exact mul_nonneg (mul_nonneg hK0pos.le hpow0) hE0
          exact div_le_div₀ hcpos hΓw1 hy_pos (le_rfl)
        _ ≤ C * (1 + |y|) * E := by
          have hA : (K0 * (1 + |y|) ^ (2 : ℝ) * E) / |y| = K0 * E * ((1 + |y|) ^ (2 : ℝ) / |y|) := by
            field_simp [hy_pos.ne']
          have hB : K0 * E * ((1 + |y|) ^ (2 : ℝ) / |y|) ≤ K0 * E * (2 * (1 + |y|)) := by
            exact mul_le_mul_of_nonneg_left hq (mul_nonneg hK0pos.le hE0)
          rw [hA]
          calc
            K0 * E * ((1 + |y|) ^ (2 : ℝ) / |y|) ≤ K0 * E * (2 * (1 + |y|)) := hB
            _ = C * (1 + |y|) * E := by
              dsimp [C]
              ring
    have habs : |y| = |t| / 2 := by
      dsimp [y]
      rw [abs_div]
      norm_num
    have hpi_le : Real.pi ^ (-(σ / 2)) ≤ 1 := by
      have hb : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
      have hle : -(σ / 2) ≤ (0 : ℝ) := by linarith
      simpa using (Real.rpow_le_rpow_of_exponent_le hb hle)
    have hGammaR : ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (1 + |t|) * Real.exp (-(Real.pi / 4) * |t|) := by
      let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
      have hs2 : s / 2 = w := by
        dsimp [s, w, x, y]
        apply Complex.ext <;> simp
      have hnorm : ‖s.Gammaℝ‖ = Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma w‖ := by
        calc
          ‖s.Gammaℝ‖ = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
            rw [Complex.Gammaℝ_def, norm_mul]
          _ = (Real.pi : ℝ) ^ ((-s / 2).re) * ‖Complex.Gamma (s / 2)‖ := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
          _ = Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma w‖ := by
            have hre : ((-s / 2).re) = -(σ / 2) := by
              dsimp [s]
              simp
              ring
            rw [hre, hs2]
      calc
        ‖Complex.Gammaℝ s‖ = Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma w‖ := hnorm
        _ ≤ 1 * ‖Complex.Gamma w‖ := by
          exact mul_le_mul_of_nonneg_right hpi_le (norm_nonneg _)
        _ = ‖Complex.Gamma w‖ := by ring
        _ ≤ C * (1 + |y|) * E := hGΓ
        _ = C * (1 + |y|) * Real.exp (-(Real.pi / 4) * |t|) := by
          have hexp : E = Real.exp (-(Real.pi / 4) * |t|) := by
            dsimp [E]
            congr 1
            rw [habs]
            ring
          rw [hexp]
        _ ≤ C * (1 + |t|) * Real.exp (-(Real.pi / 4) * |t|) := by
          have hlt : 1 + |y| ≤ 1 + |t| := by
            rw [habs]
            nlinarith [abs_nonneg t]
          have he0 : 0 ≤ Real.exp (-(Real.pi / 4) * |t|) := Real.exp_nonneg _
          have hc0 : 0 ≤ C := le_of_lt (by
            dsimp [C]
            exact mul_pos (by norm_num : (0 : ℝ) < 2) hK0pos)
          have hmul1 : C * (1 + |y|) ≤ C * (1 + |t|) :=
            mul_le_mul_of_nonneg_left hlt hc0
          exact mul_le_mul_of_nonneg_right hmul1 he0
    exact hGammaR

/-- **Strip growth of the completed zeta.** On the strip `0 < σ ≤ 2`, `|t| ≥ 2`,
the completed function `ξ(s) = (1/2)·s·(s-1)·Λ(s)` (where `Λ = completedRiemannZeta`)
satisfies `‖ξ(σ + i·t)‖ ≤ C·(|t|+3)^7·e^{-π|t|/4}` with a uniform constant `C`.

Proof ingredients: on the half-plane `Re s > 0` we have `Λ(s) = Γℝ(s)·ζ(s)`;
`|ζ(σ+i t)| ≤ C₁(|t|+3)⁴` (quartic strip bound) and, uniformly in `σ ∈ (0,2]`,
`‖Γℝ(σ+i t)‖ ≤ C₂·(1+|t|)·e^{-π|t|/4}` (shifted Gamma bound), while the
quadratic factor `s(s-1)` contributes `(|t|+3)²`.  Total polynomial degree `7`. -/
theorem completedZeta_strip_growth_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ t : ℝ, 0 < σ → σ ≤ 2 → 2 ≤ |t| →
        ‖(fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s)
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (|t| + 3) ^ 7 * Real.exp (-(Real.pi / 4) * |t|) := by
  rcases norm_GammaR_strip_le with ⟨CΓ, hCΓ0, hCΓspec⟩
  rcases Commons.NumberTheory.Zeta.zeta_strip_polyGrowth with ⟨Cζ, hCζ0, hCζspec⟩
  refine ⟨CΓ * Cζ, mul_pos hCΓ0 hCζ0, ?_⟩
  intro σ t hσ0 hσ2 ht
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let E : ℝ := Real.exp (-(Real.pi / 4) * |t|)
  have hs0 : s ≠ 0 := by
    intro h
    have hwim : s.im = 0 := congrArg Complex.im h
    have ht_ne : t ≠ 0 := by
      intro htz
      rw [htz] at ht
      norm_num at ht
    have hsi : s.im = t := by simp [s]
    exact ht_ne (by simpa [hsi] using hwim)
  have hsre : 0 < s.re := by simp [s, hσ0]
  have hLambda : completedRiemannZeta s = s.Gammaℝ * riemannZeta s :=
    completedRiemannZeta_eq_GammaR_mul s hs0 hsre
  have hG : ‖s.Gammaℝ‖ ≤ CΓ * (1 + |t|) * E := by
    simpa [s, E] using hCΓspec σ t hσ0 hσ2 ht
  have hZ : ‖riemannZeta s‖ ≤ Cζ * (|t| + 3) ^ 4 := by
    have hσlo : -1 ≤ σ := by linarith
    have hσ3 : σ ≤ 3 := by linarith
    have ht1 : 1 ≤ |t| := by linarith
    simpa [s] using hCζspec σ t hσlo hσ3 ht1
  have hE0 : 0 ≤ E := by dsimp [E]; exact Real.exp_nonneg _
  have hσ0le : 0 ≤ σ := le_of_lt hσ0
  have hhead1 : ‖s‖ ≤ |t| + 3 := by
    have h := norm_add_mul_I_le σ t hσ0le
    dsimp [s] at h ⊢
    nlinarith
  have hhead2 : ‖s - 1‖ ≤ |t| + 3 := by
    have hnorm : ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s (1 : ℂ)
    calc
      ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using hnorm
      _ ≤ |t| + 3 := by
        have h := norm_add_mul_I_le σ t hσ0le
        dsimp [s] at h ⊢
        nlinarith
  have hnormΛ : ‖completedRiemannZeta s‖ ≤ CΓ * Cζ * (|t| + 3) ^ 5 * E := by
    calc
      ‖completedRiemannZeta s‖ = ‖s.Gammaℝ‖ * ‖riemannZeta s‖ := by
        rw [hLambda, norm_mul]
      _ ≤ (CΓ * (1 + |t|) * E) * (Cζ * (|t| + 3) ^ 4) := by
        have hG0 : 0 ≤ CΓ * (1 + |t|) * E := by positivity
        have hZ0 : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
        exact mul_le_mul hG hZ hZ0 hG0
      _ = (CΓ * Cζ) * (1 + |t|) * (|t| + 3) ^ 4 * E := by ring
      _ ≤ (CΓ * Cζ) * (|t| + 3) ^ 5 * E := by
        have hlt : (1 + |t|) ≤ |t| + 3 := by nlinarith [abs_nonneg t]
        have hx0 : 0 ≤ (|t| + 3) ^ 4 := by positivity
        have hcc0 : 0 ≤ CΓ * Cζ := mul_nonneg hCΓ0.le hCζ0.le
        calc
          (CΓ * Cζ) * (1 + |t|) * (|t| + 3) ^ 4 * E
              = (CΓ * Cζ) * E * ((1 + |t|) * (|t| + 3) ^ 4) := by ring
          _ ≤ (CΓ * Cζ) * E * ((|t| + 3) * (|t| + 3) ^ 4) := by
            have h1 : (1 + |t|) * (|t| + 3) ^ 4 ≤ (|t| + 3) * (|t| + 3) ^ 4 :=
              mul_le_mul_of_nonneg_right hlt hx0
            exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hcc0 hE0)
          _ = (CΓ * Cζ) * (|t| + 3) ^ 5 * E := by ring
  have hs_arg : ((σ : ℂ) + (t : ℂ) * Complex.I) = s := by
    dsimp [s]
    ring
  calc
    ‖(fun s0 : ℂ => (1 / 2 : ℂ) * s0 * (s0 - 1) * completedRiemannZeta s0)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖(1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s‖ := by
            rw [hs_arg]
    _ = ‖(1 / 2 : ℂ)‖ * ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ = ‖(1 / 2 : ℂ)‖ * (‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖) := by ring
    _ ≤ 1 * (‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖) := by
        have h12 : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
        have hA : 0 ≤ ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖ := by positivity
        exact mul_le_mul_of_nonneg_right h12 hA
    _ = ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖ := by ring
    _ ≤ (|t| + 3) * (|t| + 3) * ‖completedRiemannZeta s‖ := by
        have hh1 : ‖s‖ * ‖s - 1‖ ≤ (|t| + 3) * (|t| + 3) := by
          exact mul_le_mul hhead1 hhead2 (norm_nonneg _) (by positivity : (0 : ℝ) ≤ |t| + 3)
        exact mul_le_mul_of_nonneg_right hh1 (norm_nonneg _)
    _ = (|t| + 3) ^ 2 * ‖completedRiemannZeta s‖ := by ring
    _ ≤ (|t| + 3) ^ 2 * ((CΓ * Cζ) * (|t| + 3) ^ 5 * E) := by
        exact mul_le_mul_of_nonneg_left hnormΛ (by positivity : (0 : ℝ) ≤ (|t| + 3) ^ 2)
    _ = (CΓ * Cζ) * (|t| + 3) ^ 7 * E := by ring
    _ ≤ (CΓ * Cζ) * (|t| + 3) ^ 7 * Real.exp (-(Real.pi / 4) * |t|) := by
        dsimp [E]
        rfl

end Commons.NumberTheory.Zeta
