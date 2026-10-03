import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_real_growth

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.DirichletCharacter

/-!
# A polynomial bound for the gamma-factor ratio on a left band

For `s = σ + I·t` with `-1 ≤ σ ≤ 1/8` and `|t| ≥ 1` we prove (for both parities)

`‖(χ⁻¹).gammaFactor (1 - s) / χ.gammaFactor s‖ ≤ C·(1+|t|)^4`.

Since `gammaFactor (χ⁻¹) = gammaFactor χ` (the Archimedean factor depends only on the
parity, and inversion preserves parity), the two parity cases reduce to the real-analytic
bounds (with `Gammaℝ s = π^(-s/2)·Γ(s/2)`)

* even:  `‖Gammaℝ (1-s) / Gammaℝ s‖ ≤ C·(1+|t|)^4`,
* odd:   `‖Gammaℝ (2-s) / Gammaℝ (s+1)‖ ≤ C·(1+|t|)^4`.

The plan (uniform in `σ` on the band):
1. an explicit rotation-angle bound (`angleBound`), copied in elementary real analysis:
   `e^{θ·y}·(cos θ)^(-2) ≤ e·(π/2)^2·(1+|y|)^2·e^{-(π/2)|y|}` for an admissible `θ`;
2. from `PL.GammaRotate.rot_estimate` and the real-axis bound `Γ(u) ≤ 32/5` on
   `[1/4, 2]`, a **uniform upper bound** for `|Γ(u + I·y)|` with decay `e^{-(π/2)|y|}`
   valid for every real part `u ∈ [1/4, 2]`;
3. Euler reflection `|Γ(z)·Γ(1-z)| = π/|sin(π·z)|` plus `|sin| ≤ e^{π|Im z|}` and (2)
   gives a **uniform lower bound** for `|Γ(r + I·y)|` with the same decay, valid for real
   parts `r ∈ [-1/2, 3/4]` once `|y| ≥ 1/2`;
4. rescale by halves to `Gammaℝ` (factor `π^{-a/2}` is harmless): a uniform upper bound
   for `|Gammaℝ (a + I·τ)|` (`7/8 ≤ a ≤ 3`) and a uniform lower bound for
   `|Gammaℝ (b + I·t)|` (`-1 ≤ b ≤ 9/8`, `|t| ≥ 1`), both with the same decay
   `e^{-(π/4)|t|}`;
5. divide: the decay factors cancel and the ratio is bounded by a constant times
   `(1+|t|)^4`, uniformly in `σ ∈ [-1, 1/8]`.
-/

namespace GammaRatioBand

open Filter MeasureTheory Set
open scoped Real Topology

/-- Jordan-type bound: for `0 < σ` and `0 < d ≤ 1`,
`(sin d)^{-σ} ≤ (π/2)^σ · (1/d)^σ`. -/
private lemma sin_pow_neg_le (σ : ℝ) (hσ : 0 < σ) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1) :
    (Real.sin d) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 / d) ^ σ := by
  have hdpi : d ≤ Real.pi / 2 := by linarith [hd', Real.two_le_pi]
  have hdpi' : d < Real.pi := by linarith [hd', Real.two_le_pi]
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdpi'
  let a : ℝ := (2 / Real.pi) * d
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_sin : a ≤ Real.sin d := by
    dsimp [a]
    exact Real.mul_le_sin hd.le hdpi
  have hsininv_le : (Real.sin d)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hsinpos ha).2 ha_sin
  have ha_inv : a⁻¹ = (Real.pi / 2) * (1 / d) := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hd.ne']
  calc
    (Real.sin d) ^ (-σ) = (Real.sin d)⁻¹ ^ σ := by rw [Real.rpow_neg_eq_inv_rpow]
    _ ≤ a⁻¹ ^ σ := Real.rpow_le_rpow (inv_nonneg.mpr hsinpos.le) hsininv_le (le_of_lt hσ)
    _ = (Real.pi / 2 * (1 / d)) ^ σ := by rw [ha_inv]
    _ = (Real.pi / 2) ^ σ * (1 / d) ^ σ := Real.mul_rpow (le_of_lt Real.pi_div_two_pos) (by positivity)

/-- The case `0 ≤ t`: choose `θ = -π/2 + 1/(1+t)`. -/
private lemma angleBound_nonneg (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rw [abs_of_nonneg ht]
  let θ : ℝ := -(Real.pi / 2) + 1 / (1 + t)
  have h1pt : 0 < 1 + t := by linarith
  have hu0 : 0 < 1 / (1 + t) := by exact div_pos zero_lt_one h1pt
  have hu1 : 1 / (1 + t) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + t)) := by
    dsimp [θ]
    rw [show -(Real.pi / 2) + 1 / (1 + t) = -(Real.pi / 2 - 1 / (1 + t)) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + t))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + t)) = 1 + t := by
    field_simp [h1pt.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + t) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + t))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + t) ^ σ := by rw [hrec]
  have hut : (1 / (1 + t)) * t ≤ 1 := by
    field_simp [h1pt.ne']
    linarith
  have hθt : θ * t ≤ -(Real.pi / 2) * t + 1 := by
    dsimp [θ]
    calc
      (-(Real.pi / 2) + 1 / (1 + t)) * t
          = -(Real.pi / 2) * t + (1 / (1 + t)) * t := by ring
      _ ≤ -(Real.pi / 2) * t + 1 := add_le_add_right hut (-(Real.pi / 2) * t)
  have hA : Real.exp (θ * t) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by
    calc
      Real.exp (θ * t) ≤ Real.exp (-(Real.pi / 2) * t + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * t) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * t))).le
  have hcomb : Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + t) ^ σ * Real.exp (-(Real.pi / 2) * t) := by ring⟩

/-- The case `t ≤ 0`: choose `θ = π/2 - 1/(1-t)`. -/
private lemma angleBound_nonpos (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : t ≤ 0) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  let s : ℝ := -t
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = -s := by dsimp [s]; ring
  have habs : |t| = s := by
    dsimp [s]
    rw [abs_of_nonpos ht]
  rw [habs, hts]
  let θ : ℝ := Real.pi / 2 - 1 / (1 + s)
  have h1ps : 0 < 1 + s := by linarith
  have hu0 : 0 < 1 / (1 + s) := by exact div_pos zero_lt_one h1ps
  have hu1 : 1 / (1 + s) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
    · dsimp [θ]; linarith
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + s)) := by
    dsimp [θ]
    rw [Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + s))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + s)) = 1 + s := by
    field_simp [h1ps.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + s) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + s))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + s) ^ σ := by rw [hrec]
  have hus : (1 / (1 + s)) * s ≤ 1 := by
    field_simp [h1ps.ne']
    linarith
  have hθt : θ * (-s) ≤ -(Real.pi / 2) * s + 1 := by
    dsimp [θ]
    calc
      (Real.pi / 2 - 1 / (1 + s)) * (-s)
          = -(Real.pi / 2) * s + (1 / (1 + s)) * s := by ring
      _ ≤ -(Real.pi / 2) * s + 1 := add_le_add_right hus (-(Real.pi / 2) * s)
  have hA : Real.exp (θ * (-s)) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by
    calc
      Real.exp (θ * (-s)) ≤ Real.exp (-(Real.pi / 2) * s + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * s) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * s))).le
  have hcomb : Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + s) ^ σ * Real.exp (-(Real.pi / 2) * s) := by ring⟩

/-- Explicit rotation-angle bound at exponent `2` (the `σ`-case we need):
for every real `y` there is an admissible rotation angle `θ` with
`e^{θ·y}·(cos θ)^{-2} ≤ e·(π/2)^2·(1+|y|)^2·e^{-(π/2)|y|}`. -/
private lemma angleBound_two (y : ℝ) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * y) * (Real.cos θ) ^ (-(2 : ℝ)) ≤
        (Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
          Real.exp (-(Real.pi / 2) * |y|) := by
  rcases le_total 0 y with hy | hy
  · exact angleBound_nonneg 2 (by norm_num) hy
  · exact angleBound_nonpos 2 (by norm_num) hy

/-- The real Gamma function is bounded by `32/5` on `[1/4, 2]`. -/
private lemma real_gamma_band_le (u : ℝ) (hu1 : (1 / 4 : ℝ) ≤ u) (hu2 : u ≤ 2) :
    Real.Gamma u ≤ 32 / 5 := by
  by_cases hle : u ≤ 1
  · exact Commons.Analysis.SpecialFunctions.Gamma.real_gamma_le_thirtytwo_fifths hu1 hle
  · have h1 : 1 ≤ u := le_of_not_ge hle
    have h2 : u ≤ 2 := hu2
    have hsmall : Real.Gamma u ≤ 2 :=
      Commons.Analysis.SpecialFunctions.Gamma.real_gamma_le_two_of_le_two h1 h2
    linarith

/-- A positive lower bound for `(π/2) ^ u` useful in the exponent arithmetic. -/
private lemma pi_div_two_pow_pos (u : ℝ) : 0 < (Real.pi / 2) ^ u :=
  Real.rpow_pos_of_pos Real.pi_div_two_pos u

/-- **Uniform upper bound for the complex Gamma function on vertical lines with decay**:
for every real part `u ∈ [1/4, 2]` and every real `y`,
`‖Γ(u + I·y)‖ ≤ CΓ·(1+|y|)^2·e^{-(π/2)|y|}` with an absolute constant `CΓ`. -/
private lemma Gamma_upper_band :
    ∃ CΓ : ℝ, 0 < CΓ ∧ ∀ (u y : ℝ), (1 / 4 : ℝ) ≤ u → u ≤ 2 →
      ‖Complex.Gamma ((u : ℂ) + Complex.I * (y : ℂ))‖ ≤
        CΓ * (1 + |y|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |y|) := by
  let CΓ : ℝ := (32 / 5) * Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)
  refine ⟨CΓ, by dsimp [CΓ]; positivity, ?_⟩
  intro u y hu1 hu2
  have hu_pos : 0 < u := by linarith
  rcases angleBound_two y with ⟨θ, hθabs, hθcos, hθb⟩
  let s : ℂ := (u : ℂ) + Complex.I * (y : ℂ)
  have hs0 : 0 < s.re := by
    dsimp [s]
    simp [hu_pos]
  have hest := PL.GammaRotate.rot_estimate s hs0 hθabs
  have hre : s.re = u := by simp [s]
  have him : s.im = y := by simp [s]
  have h₁ : ‖Complex.Gamma s‖ ≤
      Real.Gamma u * (Real.exp (θ * y) * (Real.cos θ) ^ (-u)) := by
    rw [hre, him] at hest
    simpa [mul_assoc] using hest
  have hc0 : 0 ≤ (Real.cos θ) ^ (-u) := (Real.rpow_pos_of_pos hθcos (-u)).le
  have hE0 : 0 ≤ Real.exp (θ * y) := (Real.exp_pos (θ * y)).le
  have hpow_le : (Real.cos θ) ^ (-u) ≤ (Real.cos θ) ^ (-(2 : ℝ)) := by
    -- 0 < cos θ ≤ 1 and 2 ≥ u, so (cos θ)^{-u} ≤ (cos θ)^{-2}
    have hc_le_one : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h2u : (2 : ℝ) - u ≥ 0 := by linarith
    have hbase_pos : 0 < Real.cos θ := hθcos
    have hmono : (Real.cos θ) ^ ((2 : ℝ) - u) ≤ 1 := by
      exact Real.rpow_le_one hbase_pos.le hc_le_one h2u
    have hrel : (Real.cos θ) ^ (-u) = (Real.cos θ) ^ (-(2 : ℝ)) * (Real.cos θ) ^ ((2 : ℝ) - u) := by
      rw [← Real.rpow_add hθcos (-(2 : ℝ)) (2 - u)]
      congr 1
      ring
    rw [hrel]
    exact mul_le_of_le_one_right (Real.rpow_pos_of_pos hθcos (-(2 : ℝ))).le hmono
  have hcomb0 : Real.exp (θ * y) * (Real.cos θ) ^ (-u) ≤
      Real.exp (θ * y) * (Real.cos θ) ^ (-(2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hpow_le hE0
  have hθb' : Real.exp (θ * y) * (Real.cos θ) ^ (-(2 : ℝ)) ≤
      (Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
        Real.exp (-(Real.pi / 2) * |y|) := hθb
  have hcomb : Real.exp (θ * y) * (Real.cos θ) ^ (-u) ≤
      (Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
        Real.exp (-(Real.pi / 2) * |y|) := hcomb0.trans hθb'
  have hΓu_le : Real.Gamma u ≤ 32 / 5 := real_gamma_band_le u hu1 hu2
  have hΓu0 : 0 ≤ Real.Gamma u := (Real.Gamma_pos_of_pos hu_pos).le
  calc
    ‖Complex.Gamma s‖ ≤ Real.Gamma u * (Real.exp (θ * y) * (Real.cos θ) ^ (-u)) := h₁
    _ ≤ Real.Gamma u * ((Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
          Real.exp (-(Real.pi / 2) * |y|)) := by
            exact mul_le_mul_of_nonneg_left hcomb hΓu0
    _ ≤ (32 / 5) * ((Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
          Real.exp (-(Real.pi / 2) * |y|)) := by
            have hrest0 : 0 ≤ (Real.exp 1 * (Real.pi / 2) ^ (2 : ℝ)) * (1 + |y|) ^ (2 : ℝ) *
                Real.exp (-(Real.pi / 2) * |y|) := by positivity
            exact mul_le_mul_of_nonneg_right hΓu_le hrest0
    _ = CΓ * (1 + |y|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |y|) := by
            dsimp [CΓ]
            ring

/-- **Uniform lower bound for the complex Gamma function near the imaginary axis**:
for every real part `r ∈ [-1/2, 3/4]` and `|y| ≥ 1/2`,
`cΓ·(1+|y|)^{-2}·e^{-(π/2)|y|} ≤ ‖Γ(r + I·y)‖` with an absolute constant `cΓ > 0`.

Proof: Euler reflection `|Γ(z)·Γ(1-z)| = π/|sin(π·z)|`; the lower bound
`π/|sin(π·z)| ≥ π·e^{-π|y|}` comes from `|sin| ≤ e^{|Im·|}` (and `sin(π·z) ≠ 0`, which
holds since `|y| ≥ 1/2`), and `|Γ(1-z)|` is controlled by `Gamma_upper_band` (real part
`1 - r ∈ [1/4, 3/2] ⊆ [1/4, 2]`). -/
private lemma Gamma_lower_strip :
    ∃ cΓ : ℝ, 0 < cΓ ∧ ∀ (r y : ℝ), -(1 / 2 : ℝ) ≤ r → r ≤ 3 / 4 → 1 / 2 ≤ |y| →
      cΓ * (1 + |y|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |y|) ≤
        ‖Complex.Gamma ((r : ℂ) + Complex.I * (y : ℂ))‖ := by
  obtain ⟨CΓ, hCΓ, hCΓbody⟩ := Gamma_upper_band
  let cΓ : ℝ := Real.pi / CΓ
  have hcΓ : 0 < cΓ := by
    dsimp [cΓ]
    exact div_pos Real.pi_pos hCΓ
  refine ⟨cΓ, hcΓ, ?_⟩
  intro r y hr1 hr2 hy
  let z : ℂ := (r : ℂ) + Complex.I * (y : ℂ)
  have hy_ne : y ≠ 0 := by
    intro hy0
    rw [hy0] at hy
    norm_num at hy
  have himz : (((Real.pi : ℂ) * z).im) = Real.pi * y := by
    rw [Complex.im_ofReal_mul]
    simp [z]
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    exact Commons.Analysis.SpecialFunctions.Gamma.sin_ne_zero_of_im_ne_zero (by
      rw [himz]
      exact mul_ne_zero Real.pi_ne_zero hy_ne)
  have h1r_lo : (1 / 4 : ℝ) ≤ 1 - r := by linarith
  have h1r_hi : 1 - r ≤ 2 := by linarith
  have hU := hCΓbody (1 - r) (-y) h1r_lo h1r_hi
  have harg1 : 1 - z = ((1 - r : ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z]
  have hU1 : ‖Complex.Gamma (1 - z)‖ ≤
      CΓ * (1 + |y|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |y|) := by
    simpa [harg1, abs_neg] using hU
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |y|) := by
    have h1 := Commons.Analysis.SpecialFunctions.Gamma.norm_sin_le_exp_abs_im ((Real.pi : ℂ) * z)
    calc
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp |(((Real.pi : ℂ) * z).im)| := h1
      _ = Real.exp (Real.pi * |y|) := by
        rw [himz]
        congr 1
        rw [abs_mul, abs_of_pos Real.pi_pos]
  have hsin_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := norm_pos_iff.mpr hsin_ne
  have hprod := Commons.Analysis.SpecialFunctions.Gamma.Gamma_mul_Gamma_one_sub_norm z
  let a : ℝ := Real.pi * Real.exp (-(Real.pi * |y|))
  have hA1 : a ≤ Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    dsimp [a]
    have hInv : Real.exp (-(Real.pi * |y|)) ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
      simpa [Real.exp_neg] using
        (inv_le_inv₀ (Real.exp_pos (Real.pi * |y|)) hsin_pos).mpr (by simpa using hsin_le)
    exact mul_le_mul_of_nonneg_left hInv (le_of_lt Real.pi_pos)
  let P : ℝ := 1 + |y|
  let E2 : ℝ := Real.exp (-(Real.pi / 2) * |y|)
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hE20 : 0 < E2 := by dsimp [E2]; exact Real.exp_pos _
  have hP2pos : 0 < P ^ (2 : ℝ) := Real.rpow_pos_of_pos hP0 (2 : ℝ)
  have hExp : Real.exp (-(Real.pi * |y|)) = E2 * E2 := by
    dsimp [E2]
    rw [← Real.exp_add]
    congr 1
    ring
  have hA2 : a ≤ ‖Complex.Gamma z‖ * (CΓ * P ^ (2 : ℝ) * E2) := by
    calc
      a ≤ Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := hA1
      _ = ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := hprod.symm
      _ ≤ ‖Complex.Gamma z‖ * (CΓ * P ^ (2 : ℝ) * E2) := by
        dsimp [P, E2]
        exact mul_le_mul_of_nonneg_left hU1 (norm_nonneg _)
  have h0 : a / CΓ ≤ ‖Complex.Gamma z‖ * (P ^ (2 : ℝ) * E2) := by
    exact (div_le_iff₀ hCΓ).mpr (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hA2)
  have h1 : (a / CΓ) / (P ^ (2 : ℝ) * E2) ≤ ‖Complex.Gamma z‖ := by
    exact (div_le_iff₀ (mul_pos hP2pos hE20)).mpr (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h0)
  have hconv : (Real.pi / CΓ) * P ^ (-(2 : ℝ)) * E2 = (a / CΓ) / (P ^ (2 : ℝ) * E2) := by
    have hneg : P ^ (-(2 : ℝ)) = (P ^ (2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg]
      exact hP0.le
    have ha_eq : a = Real.pi * E2 * E2 := by
      dsimp [a]
      rw [hExp]
      ring
    calc
      (Real.pi / CΓ) * P ^ (-(2 : ℝ)) * E2
          = (Real.pi / CΓ) * (P ^ (2 : ℝ))⁻¹ * E2 := by rw [hneg]
      _ = (Real.pi * E2) / (CΓ * P ^ (2 : ℝ)) := by
          field_simp [hCΓ.ne', hP2pos.ne']
      _ = ((Real.pi * E2 * E2) / CΓ) / (P ^ (2 : ℝ) * E2) := by
          field_simp [hE20.ne', hP2pos.ne']
      _ = (a / CΓ) / (P ^ (2 : ℝ) * E2) := by rw [ha_eq]
  calc
    cΓ * (1 + |y|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |y|)
        = (Real.pi / CΓ) * P ^ (-(2 : ℝ)) * E2 := by
          dsimp [cΓ, P, E2]
    _ = (a / CΓ) / (P ^ (2 : ℝ) * E2) := hconv
    _ ≤ ‖Complex.Gamma z‖ := h1
    _ = ‖Complex.Gamma ((r : ℂ) + Complex.I * (y : ℂ))‖ := by simp [z]

/-- **Uniform upper bound for `Gammaℝ` on the right band** (with `e^{-(π/4)|τ|}` decay):
for every real part `a ∈ [7/8, 3]` and every real `τ`,
`‖Gammaℝ (a + I·τ)‖ ≤ Cnum·(1+|τ|)^2·e^{-(π/4)|τ|}`. -/
private lemma gammaR_upper_band :
    ∃ Cnum : ℝ, 0 < Cnum ∧ ∀ (a τ : ℝ), (7 / 8 : ℝ) ≤ a → a ≤ 3 →
      ‖Complex.Gammaℝ ((a : ℂ) + Complex.I * (τ : ℂ))‖ ≤
        Cnum * (1 + |τ|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 4) * |τ|) := by
  obtain ⟨CΓ, hCΓ, hCΓbody⟩ := Gamma_upper_band
  refine ⟨CΓ, hCΓ, ?_⟩
  intro a τ ha1 ha3
  have ha2 : (1 / 4 : ℝ) ≤ a / 2 := by linarith
  have ha2' : a / 2 ≤ 2 := by linarith
  have hΓ := hCΓbody (a / 2) (τ / 2) ha2 ha2'
  have hArg : ((a : ℂ) + I * (τ : ℂ)) / 2 = ((a / 2 : ℝ) : ℂ) + I * (((τ / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hnorm : ‖Complex.Gammaℝ ((a : ℂ) + I * (τ : ℂ))‖
      = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (τ : ℂ)) / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi_le_one : Real.pi ^ (-a / 2) ≤ 1 := by
    have hnonpos : -a / 2 ≤ 0 := by linarith
    have h := Real.rpow_le_rpow_of_exponent_le hπ1 hnonpos
    simpa using h
  have hB2 : (1 + |τ / 2|) ^ (2 : ℝ) ≤ (1 + |τ|) ^ (2 : ℝ) := by
    have hx0 : 0 ≤ 1 + |τ / 2| := by positivity
    have hxy : 1 + |τ / 2| ≤ 1 + |τ| := by
      have h : |τ / 2| ≤ |τ| := by
        rw [abs_div]
        have ht0 : 0 ≤ |τ| := abs_nonneg τ
        nlinarith
      linarith
    exact Real.rpow_le_rpow hx0 hxy (by norm_num : (0 : ℝ) ≤ 2)
  have hE : Real.exp (-(Real.pi / 2) * |τ / 2|) = Real.exp (-(Real.pi / 4) * |τ|) := by
    congr 1
    rw [abs_div]
    ring
  have hΓ' : ‖Complex.Gamma (((a : ℂ) + I * (τ : ℂ)) / 2)‖ ≤
      CΓ * (1 + |τ / 2|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|) := by
    simpa [hArg] using hΓ
  have hrest0 : 0 ≤ CΓ * (1 + |τ / 2|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|) := by positivity
  have hpi0 : 0 ≤ Real.pi ^ (-a / 2) := (Real.rpow_pos_of_pos Real.pi_pos (-a / 2)).le
  calc
    ‖Complex.Gammaℝ ((a : ℂ) + I * (τ : ℂ))‖
        = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (τ : ℂ)) / 2)‖ := hnorm
    _ ≤ (Real.pi ^ (-a / 2)) * (CΓ * (1 + |τ / 2|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|)) := by
          exact mul_le_mul_of_nonneg_left hΓ' hpi0
    _ ≤ 1 * (CΓ * (1 + |τ / 2|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|)) := by
          exact mul_le_mul_of_nonneg_right hpi_le_one hrest0
    _ = CΓ * (1 + |τ / 2|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|) := by ring
    _ ≤ CΓ * (1 + |τ|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2) * |τ / 2|) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB2 (le_of_lt hCΓ)) (Real.exp_pos _).le
    _ = CΓ * (1 + |τ|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 4) * |τ|) := by rw [hE]

/-- **Uniform lower bound for `Gammaℝ` on the left band** (with `e^{-(π/4)|t|}` decay):
for every real part `b ∈ [-1, 9/8]` and `|t| ≥ 1`,
`cG·(1+|t|)^{-2}·e^{-(π/4)|t|} ≤ ‖Gammaℝ (b + I·t)‖`. -/
private lemma gammaR_lower_band :
    ∃ cG : ℝ, 0 < cG ∧ ∀ (b t : ℝ), -1 ≤ b → b ≤ (9 / 8 : ℝ) → 1 ≤ |t| →
      cG * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|) ≤
        ‖Complex.Gammaℝ ((b : ℂ) + Complex.I * (t : ℂ))‖ := by
  obtain ⟨cΓ, hcΓ, hcΓbody⟩ := Gamma_lower_strip
  let cG : ℝ := Real.pi ^ (-(9 / 16 : ℝ)) * cΓ
  have hcG : 0 < cG := by
    dsimp [cG]
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos (-(9 / 16 : ℝ))) hcΓ
  refine ⟨cG, hcG, ?_⟩
  intro b t hb1 hb2 ht
  have hr1 : -(1 / 2 : ℝ) ≤ b / 2 := by linarith
  have hr2 : b / 2 ≤ 3 / 4 := by linarith
  have hty : 1 / 2 ≤ |t / 2| := by
    rw [abs_div]
    have ht0 : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hL := hcΓbody (b / 2) (t / 2) hr1 hr2 hty
  have hArg : ((b : ℂ) + I * (t : ℂ)) / 2 = ((b / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hnorm : ‖Complex.Gammaℝ ((b : ℂ) + I * (t : ℂ))‖
      = (Real.pi ^ (-b / 2)) * ‖Complex.Gamma (((b : ℂ) + I * (t : ℂ)) / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi_le : Real.pi ^ (-(9 / 16 : ℝ)) ≤ Real.pi ^ (-b / 2) := by
    have hne : -(9 / 16 : ℝ) ≤ -b / 2 := by linarith
    exact Real.rpow_le_rpow_of_exponent_le hπ1 hne
  have hExp : Real.exp (-(Real.pi / 2) * |t / 2|) = Real.exp (-(Real.pi / 4) * |t|) := by
    congr 1
    rw [abs_div]
    ring
  have hB : (1 + |t|) ^ (-(2 : ℝ)) ≤ (1 + |t / 2|) ^ (-(2 : ℝ)) := by
    have hb0 : 0 < 1 + |t / 2| := by positivity
    have hle : 1 + |t / 2| ≤ 1 + |t| := by
      have h : |t / 2| ≤ |t| := by
        rw [abs_div]
        have ht0 : 0 ≤ |t| := abs_nonneg t
        nlinarith
      linarith
    exact Real.rpow_le_rpow_of_nonpos hb0 hle (by norm_num : (-(2 : ℝ)) ≤ 0)
  have hL' : cΓ * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|) ≤
      ‖Complex.Gamma (((b : ℂ) + I * (t : ℂ)) / 2)‖ := by
    simpa [hArg] using hL
  have hpi0 : 0 ≤ Real.pi ^ (-b / 2) := (Real.rpow_pos_of_pos Real.pi_pos (-b / 2)).le
  have hb2' : 0 ≤ (1 + |t / 2|) ^ (-(2 : ℝ)) :=
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |t / 2|) (-(2 : ℝ))).le
  have he0 : 0 ≤ Real.exp (-(Real.pi / 2) * |t / 2|) := (Real.exp_pos _).le
  have hcΓ0 : 0 ≤ cΓ := le_of_lt hcΓ
  have hmain0 : (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t / 2|) ^ (-(2 : ℝ)) *
      Real.exp (-(Real.pi / 2) * |t / 2|) ≤ (Real.pi ^ (-b / 2)) *
        (cΓ * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|)) := by
    calc
      (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|)
          = Real.pi ^ (-(9 / 16 : ℝ)) * (cΓ * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|)) := by ring
      _ ≤ Real.pi ^ (-b / 2) * (cΓ * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|)) := by
            gcongr
  have h2 : (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|)
      ≤ (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|) := by
    have hpq0 : 0 ≤ Real.pi ^ (-(9 / 16 : ℝ)) * cΓ := mul_nonneg (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) hcΓ0
    calc
      (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|)
          = (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|) := by rw [hExp]
      _ ≤ (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|) := by
            gcongr
  calc
    cG * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|)
        = (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|) := rfl
    _ ≤ (Real.pi ^ (-(9 / 16 : ℝ)) * cΓ) * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|) := h2
    _ ≤ (Real.pi ^ (-b / 2)) * (cΓ * (1 + |t / 2|) ^ (-(2 : ℝ)) * Real.exp (-(Real.pi / 2) * |t / 2|)) := hmain0
    _ ≤ (Real.pi ^ (-b / 2)) * ‖Complex.Gamma (((b : ℂ) + I * (t : ℂ)) / 2)‖ := by
          exact mul_le_mul_of_nonneg_left hL' hpi0
    _ = ‖Complex.Gammaℝ ((b : ℂ) + I * (t : ℂ))‖ := hnorm.symm

/-- **Even-parity gamma ratio on the band** (uniform in `σ`): for `s = σ + I·t` with
`-1 ≤ σ ≤ 1/8` and `|t| ≥ 1`, `‖Gammaℝ (1 - s) / Gammaℝ s‖ ≤ C·(1+|t|)^4`. -/
private theorem gammaR_ratio_band_even :
    ∃ C κ : ℝ, 0 < C ∧ 0 ≤ κ ∧ ∀ (σ : ℝ), -1 ≤ σ → σ ≤ (1 / 8 : ℝ) → ∀ (t : ℝ), 1 ≤ |t| →
      ‖Complex.Gammaℝ (1 - ((σ : ℂ) + I * (t : ℂ))) /
          Complex.Gammaℝ ((σ : ℂ) + I * (t : ℂ))‖ ≤ C * (1 + |t|) ^ κ := by
  obtain ⟨Cnum, hCnum, hUp⟩ := gammaR_upper_band
  obtain ⟨cG, hcG, hLo⟩ := gammaR_lower_band
  refine ⟨Cnum / cG, (4 : ℝ), div_pos hCnum hcG, by norm_num, ?_⟩
  intro σ hσlo hσhi t ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let B : ℝ := 1 + |t|
  let E : ℝ := Real.exp (-(Real.pi / 4) * |t|)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hEpos : 0 < E := by dsimp [E]; exact Real.exp_pos _
  have hnum_arg : 1 - s = ((1 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hUp_hi : (7 / 8 : ℝ) ≤ 1 - σ := by linarith
  have hUp_lo : 1 - σ ≤ 3 := by linarith
  have hnum : ‖Complex.Gammaℝ (1 - s)‖ ≤ Cnum * B ^ (2 : ℝ) * E := by
    have h := hUp (1 - σ) (-t) hUp_hi hUp_lo
    simpa [hnum_arg, B, E, abs_neg] using h
  have hLo_hi : σ ≤ 9 / 8 := by linarith
  have hden : cG * B ^ (-(2 : ℝ)) * E ≤ ‖Complex.Gammaℝ s‖ := by
    have h := hLo σ t hσlo hLo_hi ht
    simpa [s, B, E] using h
  have hnum0 : 0 ≤ Cnum * B ^ (2 : ℝ) * E := by positivity
  have hden_pos : 0 < cG * B ^ (-(2 : ℝ)) * E := by
    have hBq : 0 < B ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hBpos (-(2 : ℝ))
    positivity
  have hp : (2 : ℝ) - (-(2 : ℝ)) = 4 := by norm_num
  have hEq : (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E) =
      (Cnum / cG) * B ^ (4 : ℝ) := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hcGne : cG ≠ 0 := ne_of_gt hcG
    have hBqEpos : 0 < B ^ (-(2 : ℝ)) * E := mul_pos (Real.rpow_pos_of_pos hBpos (-(2 : ℝ))) hEpos
    calc
      (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E)
          = (Cnum / cG) * ((B ^ (2 : ℝ) * E) / (B ^ (-(2 : ℝ)) * E)) := by
            field_simp [hcGne, hBqEpos.ne']
      _ = (Cnum / cG) * (B ^ (2 : ℝ) / B ^ (-(2 : ℝ))) := by
            congr 1
            field_simp [hEne]
      _ = (Cnum / cG) * B ^ ((2 : ℝ) - (-(2 : ℝ))) := by
            congr 1
            exact (Real.rpow_sub hBpos (2 : ℝ) (-(2 : ℝ))).symm
      _ = (Cnum / cG) * B ^ (4 : ℝ) := by rw [hp]
  calc
    ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖
        = ‖Complex.Gammaℝ (1 - s)‖ / ‖Complex.Gammaℝ s‖ := by rw [norm_div]
    _ ≤ (Cnum * B ^ (2 : ℝ) * E) / ‖Complex.Gammaℝ s‖ := by
          exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E) := by
          exact div_le_div_of_nonneg_left hnum0 hden_pos hden
    _ = (Cnum / cG) * B ^ (4 : ℝ) := hEq
    _ = (Cnum / cG) * (1 + |t|) ^ (4 : ℝ) := rfl

/-- **Odd-parity gamma ratio on the band** (uniform in `σ`): for `s = σ + I·t` with
`-1 ≤ σ ≤ 1/8` and `|t| ≥ 1`, `‖Gammaℝ (2 - s) / Gammaℝ (s + 1)‖ ≤ C·(1+|t|)^4`. -/
private theorem gammaR_ratio_band_odd :
    ∃ C κ : ℝ, 0 < C ∧ 0 ≤ κ ∧ ∀ (σ : ℝ), -1 ≤ σ → σ ≤ (1 / 8 : ℝ) → ∀ (t : ℝ), 1 ≤ |t| →
      ‖Complex.Gammaℝ (2 - ((σ : ℂ) + I * (t : ℂ))) /
          Complex.Gammaℝ (((σ : ℂ) + I * (t : ℂ)) + 1)‖ ≤ C * (1 + |t|) ^ κ := by
  obtain ⟨Cnum, hCnum, hUp⟩ := gammaR_upper_band
  obtain ⟨cG, hcG, hLo⟩ := gammaR_lower_band
  refine ⟨Cnum / cG, (4 : ℝ), div_pos hCnum hcG, by norm_num, ?_⟩
  intro σ hσlo hσhi t ht
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let B : ℝ := 1 + |t|
  let E : ℝ := Real.exp (-(Real.pi / 4) * |t|)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hEpos : 0 < E := by dsimp [E]; exact Real.exp_pos _
  have hnum_arg : 2 - s = ((2 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hUp_hi : (7 / 8 : ℝ) ≤ 2 - σ := by linarith
  have hUp_lo : 2 - σ ≤ 3 := by linarith
  have hnum : ‖Complex.Gammaℝ (2 - s)‖ ≤ Cnum * B ^ (2 : ℝ) * E := by
    have h := hUp (2 - σ) (-t) hUp_hi hUp_lo
    simpa [hnum_arg, B, E, abs_neg] using h
  have hden_arg : s + 1 = ((σ + 1 : ℝ) : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hLo_hi : σ + 1 ≤ 9 / 8 := by linarith
  have hden : cG * B ^ (-(2 : ℝ)) * E ≤ ‖Complex.Gammaℝ (s + 1)‖ := by
    have h := hLo (σ + 1) t (by linarith) hLo_hi ht
    simpa [hden_arg, s, B, E] using h
  have hnum0 : 0 ≤ Cnum * B ^ (2 : ℝ) * E := by positivity
  have hden_pos : 0 < cG * B ^ (-(2 : ℝ)) * E := by
    have hBq : 0 < B ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hBpos (-(2 : ℝ))
    positivity
  have hp : (2 : ℝ) - (-(2 : ℝ)) = 4 := by norm_num
  have hEq : (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E) =
      (Cnum / cG) * B ^ (4 : ℝ) := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hcGne : cG ≠ 0 := ne_of_gt hcG
    have hBqEpos : 0 < B ^ (-(2 : ℝ)) * E := mul_pos (Real.rpow_pos_of_pos hBpos (-(2 : ℝ))) hEpos
    calc
      (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E)
          = (Cnum / cG) * ((B ^ (2 : ℝ) * E) / (B ^ (-(2 : ℝ)) * E)) := by
            field_simp [hcGne, hBqEpos.ne']
      _ = (Cnum / cG) * (B ^ (2 : ℝ) / B ^ (-(2 : ℝ))) := by
            congr 1
            field_simp [hEne]
      _ = (Cnum / cG) * B ^ ((2 : ℝ) - (-(2 : ℝ))) := by
            congr 1
            exact (Real.rpow_sub hBpos (2 : ℝ) (-(2 : ℝ))).symm
      _ = (Cnum / cG) * B ^ (4 : ℝ) := by rw [hp]
  calc
    ‖Complex.Gammaℝ (2 - s) / Complex.Gammaℝ (s + 1)‖
        = ‖Complex.Gammaℝ (2 - s)‖ / ‖Complex.Gammaℝ (s + 1)‖ := by rw [norm_div]
    _ ≤ (Cnum * B ^ (2 : ℝ) * E) / ‖Complex.Gammaℝ (s + 1)‖ := by
          exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Cnum * B ^ (2 : ℝ) * E) / (cG * B ^ (-(2 : ℝ)) * E) := by
          exact div_le_div_of_nonneg_left hnum0 hden_pos hden
    _ = (Cnum / cG) * B ^ (4 : ℝ) := hEq
    _ = (Cnum / cG) * (1 + |t|) ^ (4 : ℝ) := rfl

end GammaRatioBand

/-- **Polynomial bound for the archimedean gamma-factor ratio on the band**
`-1 ≤ σ ≤ 1/8`, `|t| ≥ 1`: for `s = σ + I·t`,

`‖(χ⁻¹).gammaFactor (1 - s) / χ.gammaFactor s‖ ≤ C·(1+|t|)^κ`.

Since the Archimedean factor `gammaFactor` depends only on the parity of the character
and inversion preserves parity, `gammaFactor (χ⁻¹) (1 - s) = gammaFactor χ (1 - s)`
(`PL.AfeAssembly.gammaFactor_inv_eq`), and the parity cases reduce to the real-analytic
bounds `gammaR_ratio_band_even`/`gammaR_ratio_band_odd` on `Gammaℝ`. -/
theorem gammaFactor_ratio_band_large_t {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C κ : ℝ, 0 < C ∧ 0 ≤ κ ∧ ∀ (σ : ℝ), -1 ≤ σ → σ ≤ (1 / 8 : ℝ) → ∀ t : ℝ,
      1 ≤ |t| →
      ‖(χ⁻¹).gammaFactor (1 - ((σ : ℂ) + I * (t : ℂ))) /
          χ.gammaFactor ((σ : ℂ) + I * (t : ℂ))‖ ≤ C * (1 + |t|) ^ κ := by
  rcases χ.even_or_odd with hE | hO
  · obtain ⟨Ce, κe, hCe, hκe, hbe⟩ := GammaRatioBand.gammaR_ratio_band_even
    refine ⟨Ce, κe, hCe, hκe, ?_⟩
    intro σ hσlo hσhi t ht
    rw [PL.AfeAssembly.gammaFactor_inv_eq]
    rw [hE.gammaFactor_def (1 - ((σ : ℂ) + I * (t : ℂ))), hE.gammaFactor_def ((σ : ℂ) + I * (t : ℂ))]
    exact hbe σ hσlo hσhi t ht
  · obtain ⟨Co, κo, hCo, hκo, hbo⟩ := GammaRatioBand.gammaR_ratio_band_odd
    refine ⟨Co, κo, hCo, hκo, ?_⟩
    intro σ hσlo hσhi t ht
    rw [PL.AfeAssembly.gammaFactor_inv_eq]
    rw [hO.gammaFactor_def (1 - ((σ : ℂ) + I * (t : ℂ))), hO.gammaFactor_def ((σ : ℂ) + I * (t : ℂ))]
    have harg : (1 - ((σ : ℂ) + I * (t : ℂ))) + 1 = 2 - ((σ : ℂ) + I * (t : ℂ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    exact hbo σ hσlo hσhi t ht

end Commons.NumberTheory.DirichletCharacter

