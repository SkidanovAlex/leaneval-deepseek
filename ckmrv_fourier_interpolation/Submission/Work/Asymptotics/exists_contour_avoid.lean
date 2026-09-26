/-
# The contour-avoidance lemma for the CKMRV local continuation at `1 + i s₀`

This file proves `Work.Asymptotics.exists_contour_avoid`: around the point `1 + i s₀` there is a
hyperbolic ball of radius `ε`, a rectangular detour of the imaginary axis (parameters
`A₁ = ξ₁ = A₂ = ξ₂ = A`) such that

* (condition 1) for every `t` outside the two intervals `I₁ = (s₀-A, s₀+A)`,
  `I₂ = (s₀⁻¹-A, s₀⁻¹+A)` and every `τ` in the ball, `j τ ≠ j (i t)`, i.e. the `j`-orbit of `i t`
  misses the ball;
* (condition 2) every `SL(2,ℤ)`-translate of a point of the boundary of the detour rectangle is
  at hyperbolic distance `≥ ε` from `1 + i s₀`, i.e. the contour (as a curve in the *second*
  variable) avoids the moving poles.

## Ingredients

* `web_near_center_param`: web points near `1 + i s₀` are parametrised by `t` or by `t⁻¹`.  This
  combines the proved `webAvoidBall` (web points near the centre have real part `1`) with the
  algebraic classification `eq_one_or_neg_one_or_S_of_smul_imagAxis`.
* `jInvariantFun_eq_smul_of_eq`: `j` separates `SL(2,ℤ)`-orbits, so condition (1) is equivalent
  to the statement that the *orbit* of `i t` misses the ball.
* `orbitGap_imagAxis`: the `SL(2,ℤ)`-orbit of `i s₀` is uniformly discrete at `i s₀`; this is the
  quantitative input for condition (2).
* `curve_Q_bounds`, `ofReImT_dist_bounds`: elementary estimates for the detour rectangle.
-/
import Mathlib
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-! ## Toolkit -/

/-- `cosh x ≤ 1 + x ^ 2` for `|x| ≤ 1`. -/
lemma cosh_le_one_add_sq {x : ℝ} (hx : x ^ 2 ≤ 1) : Real.cosh x ≤ 1 + x ^ 2 := by
  have h1 : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := Real.cosh_le_exp_half_sq x
  have hu0 : 0 < 1 - x ^ 2 / 2 := by linarith
  have h2 : Real.exp (x ^ 2 / 2) ≤ 1 / (1 - x ^ 2 / 2) := by
    have h := Real.one_sub_le_exp_neg (x ^ 2 / 2)
    rw [Real.exp_neg] at h
    have hinv := inv_anti₀ hu0 h
    simp only [one_div] at hinv ⊢
    simpa using hinv
  have h3 : 1 / (1 - x ^ 2 / 2) ≤ 1 + x ^ 2 := by
    rw [div_le_iff₀ hu0]
    nlinarith [sq_nonneg x]
  linarith

/-- `SL(2,ℤ)` acts on `ℍ` by isometries. -/
lemma dist_smul_SL2Z (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x y : UpperHalfPlane) :
    dist (γ • x) (γ • y) = dist x y := by
  rw [show γ • x = (γ.map (Int.castRingHom ℝ)) • x from rfl,
    show γ • y = (γ.map (Int.castRingHom ℝ)) • y from rfl]
  exact dist_smul _ _ _

/-- `T` maps `i s₀` to the centre `1 + i s₀`. -/
lemma T_smul_imagAxis (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ModularGroup.T • Work.Kernels.imagAxis s₀ hs₀ = onePlusI s₀ hs₀ := by
  rw [UpperHalfPlane.modular_T_smul]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd]
  simp [onePlusI, Work.Kernels.imagAxis]

/-- `S` maps `i s₀` to `i/s₀`. -/
lemma S_smul_imagAxis (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀
      = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  simp only [Work.Kernels.imagAxis]
  congr 1
  rw [show (-((s₀ : ℂ) * Complex.I)) = -((s₀ : ℂ)) * Complex.I by ring]
  rw [mul_inv, Complex.inv_I, inv_neg]
  simp [mul_comm]

/-- `-1 ∈ SL(2,ℤ)` acts trivially on `ℍ`. -/
lemma neg_one_smul_SL2Z (z : UpperHalfPlane) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z = z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

/-- `-γ ∈ SL(2,ℤ)` acts on `ℍ` as `γ` does. -/
lemma neg_smul_SL2Z (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    (-γ) • z = γ • z := by
  have h : (-γ) = γ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by rw [mul_neg, mul_one]
  rw [h, mul_smul, neg_one_smul_SL2Z]

/-- **The algebraic heart of the web parametrisation.**  If `σ • (i t)` has real part `1` then it
is `1 + i t` (for `σ = ±T`) or `1 + i/t` (for `σ = ±TS`); in particular its imaginary part is `t`
or `t⁻¹`. -/
lemma im_eq_or_inv_of_re_eq_one {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {t : ℝ} (ht : 0 < t)
    (hre : (σ • Work.Kernels.imagAxis t ht).re = 1) :
    (σ • Work.Kernels.imagAxis t ht).im = t ∨ (σ • Work.Kernels.imagAxis t ht).im = t⁻¹ := by
  set w : UpperHalfPlane := σ • Work.Kernels.imagAxis t ht with hw
  have hy : 0 < w.im := w.im_pos
  have hcoe : (w : ℂ) = 1 + (w.im : ℂ) * Complex.I := by
    have h := Complex.re_add_im (w : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hre] at h
    rw [← h]; simp
  have hTw : ((ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • w : UpperHalfPlane)
      = Work.Kernels.imagAxis w.im hy := by
    apply UpperHalfPlane.ext
    rw [show (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.T ^ (-1 : ℤ)
          from by rw [zpow_neg_one],
      UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd, hcoe, Work.Kernels.imagAxis]
    norm_num
  have hmain : (ModularGroup.T⁻¹ * σ) • Work.Kernels.imagAxis t ht = Work.Kernels.imagAxis w.im hy := by
    rw [mul_smul, ← hw]; exact hTw
  rcases eq_one_or_neg_one_or_S_of_smul_imagAxis ht hy hmain with h | h | h | h
  · left
    have hσ : σ = ModularGroup.T := by
      calc σ = ModularGroup.T * (ModularGroup.T⁻¹ * σ) := by group
        _ = ModularGroup.T * 1 := by rw [h]
        _ = ModularGroup.T := mul_one _
    rw [hw, hσ, T_smul_imagAxis t ht]
    simp [onePlusI]
  · left
    have hσ : σ = -ModularGroup.T := by
      calc σ = ModularGroup.T * (ModularGroup.T⁻¹ * σ) := by group
        _ = ModularGroup.T * (-1) := by rw [h]
        _ = -ModularGroup.T := by rw [mul_neg, mul_one]
    rw [hw, hσ, neg_smul_SL2Z, T_smul_imagAxis t ht]
    simp [onePlusI]
  · right
    have hσ : σ = ModularGroup.T * ModularGroup.S := by
      calc σ = ModularGroup.T * (ModularGroup.T⁻¹ * σ) := by group
        _ = ModularGroup.T * ModularGroup.S := by rw [h]
    rw [hw, hσ, mul_smul, S_smul_imagAxis t ht, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.vadd_im]
    simp [Work.Kernels.imagAxis]
  · right
    have hσ : σ = -(ModularGroup.T * ModularGroup.S) := by
      calc σ = ModularGroup.T * (ModularGroup.T⁻¹ * σ) := by group
        _ = ModularGroup.T * (-ModularGroup.S) := by rw [h]
        _ = -(ModularGroup.T * ModularGroup.S) := by rw [mul_neg]
    rw [hw, hσ, neg_smul_SL2Z, mul_smul, S_smul_imagAxis t ht, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.vadd_im]
    simp [Work.Kernels.imagAxis]

/-- **Web points near `1 + i s₀`.**  Inside a ball of radius `r` around the centre, every web
point `σ • (i t)` has real part `1` and imaginary part `t` or `t⁻¹`. -/
lemma web_near_center_param (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < r →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨ (σ • Work.Kernels.imagAxis t ht).im = t⁻¹) := by
  obtain ⟨r, hr, hweb⟩ := webAvoidBall s₀ hs₀
  refine ⟨r, hr, fun σ t ht hdist => ?_⟩
  have hre : (σ • Work.Kernels.imagAxis t ht).re = 1 := by
    have := hweb σ t ht hdist
    rwa [UpperHalfPlane.coe_re] at this
  exact ⟨hre, im_eq_or_inv_of_re_eq_one ht hre⟩

/-- If `z` has real part `1` and is within `ε ≤ 1/2` of `1 + i s₀`, then
`|z.im - s₀| ≤ 2 s₀ ε`. -/
lemma abs_im_sub_le_of_dist {s₀ ε : ℝ} (hs₀ : 0 < s₀) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    {z : UpperHalfPlane} (hz : z.re = 1) (h : dist z (onePlusI s₀ hs₀) < ε) :
    |z.im - s₀| ≤ 2 * s₀ * ε := by
  have hcosh := UpperHalfPlane.cosh_dist' z (onePlusI s₀ hs₀)
  rw [onePlusI_re, onePlusI_im, hz] at hcosh
  have hle : Real.cosh (dist z (onePlusI s₀ hs₀)) ≤ Real.cosh ε := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg hε0]
    exact le_of_lt h
  rw [hcosh] at hle
  have hcoshε : Real.cosh ε ≤ 1 + ε ^ 2 := cosh_le_one_add_sq (by nlinarith)
  have hden : 0 < 2 * z.im * s₀ := by positivity
  rw [div_le_iff₀ hden] at hle
  have hkey : (z.im - s₀) ^ 2 ≤ 2 * s₀ * z.im * ε ^ 2 := by nlinarith [hle, hcoshε]
  by_cases hge : s₀ ≤ z.im
  · have hd0 : 0 ≤ z.im - s₀ := by linarith
    rw [abs_of_nonneg hd0]
    set d : ℝ := z.im - s₀ with hd
    have hd2 : d ^ 2 ≤ 2 * s₀ * (s₀ + d) * ε ^ 2 := by
      rw [hd] at hkey ⊢; nlinarith [hkey]
    by_contra hcon
    have hlt : 2 * s₀ * ε < d := lt_of_not_ge hcon
    have hfac : d ^ 2 - 2 * s₀ * ε ^ 2 * d - 2 * s₀ ^ 2 * ε ^ 2
        = (d - 2 * s₀ * ε) * (d + 2 * s₀ * ε * (1 - ε)) + 2 * s₀ ^ 2 * ε ^ 2 * (1 - 2 * ε) := by
      ring
    have hA : 0 < d - 2 * s₀ * ε := by linarith
    have hB : 0 < d + 2 * s₀ * ε * (1 - ε) := by nlinarith
    have hprod : 0 < (d - 2 * s₀ * ε) * (d + 2 * s₀ * ε * (1 - ε)) := mul_pos hA hB
    have hsec : 0 ≤ 2 * s₀ ^ 2 * ε ^ 2 * (1 - 2 * ε) :=
      mul_nonneg (by positivity) (by linarith)
    have hL : d ^ 2 - 2 * s₀ * ε ^ 2 * d - 2 * s₀ ^ 2 * ε ^ 2 ≤ 0 := by nlinarith [hd2]
    rw [hfac] at hL
    linarith
  · have hd0 : z.im - s₀ ≤ 0 := by linarith
    rw [abs_of_nonpos hd0]
    have hle' : z.im ≤ s₀ := le_of_lt (lt_of_not_ge hge)
    have hb : 2 * s₀ * z.im * ε ^ 2 ≤ 2 * s₀ * s₀ * ε ^ 2 := by
      have hpos : (0:ℝ) ≤ 2 * s₀ * ε ^ 2 := by positivity
      calc 2 * s₀ * z.im * ε ^ 2 = (2 * s₀ * ε ^ 2) * z.im := by ring
        _ ≤ (2 * s₀ * ε ^ 2) * s₀ := mul_le_mul_of_nonneg_left hle' hpos
        _ = 2 * s₀ * s₀ * ε ^ 2 := by ring
    have h2 : (z.im - s₀) ^ 2 ≤ (2 * s₀ * ε) ^ 2 := by nlinarith [hkey, hb]
    have h3 := sq_le_sq.mp h2
    rw [abs_of_nonpos hd0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s₀ * ε)] at h3
    linarith

/-! ## The gap at `i s₀` in the `SL(2,ℤ)`-orbit -/

/-- **Quantitative discreteness of the orbit of `i s₀`.**  The quantity
`(w.re ^ 2 + (w.im - s₀) ^ 2) / w.im` equals `2 s₀ (cosh (dist w (i s₀)) - 1)`, so a positive
lower bound `F₀` on it for every `w = μ • (i s₀) ≠ i s₀` is exactly a positive lower bound on the
hyperbolic distance from `i s₀` to the rest of the orbit. -/
theorem orbitGap_imagAxis (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ F₀ : ℝ, 0 < F₀ ∧ ∀ μ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      μ • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
      F₀ ≤ (((μ • Work.Kernels.imagAxis s₀ hs₀).re) ^ 2
              + ((μ • Work.Kernels.imagAxis s₀ hs₀).im - s₀) ^ 2)
             / ((μ • Work.Kernels.imagAxis s₀ hs₀).im) := by
  refine ⟨min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀)), ?_, ?_⟩
  · have h1 : 0 < 1/s₀ := by positivity
    have h2 : 0 < s₀^5/(1+s₀^2) := by positivity
    have h3 : 0 < (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀) := by
      by_cases h : s₀ = 1
      · rw [if_pos h]; norm_num
      · rw [if_neg h]
        have hne' : (1:ℝ) - s₀^2 ≠ 0 := by intro hh; exact h (by nlinarith [hh, hs₀])
        rw [show ((1:ℝ) - s₀^2)^2 = |1 - s₀^2|^2 by rw [sq_abs]]
        exact div_pos (pow_pos (abs_pos.mpr hne') 2) hs₀
    exact lt_min h1 (lt_min h2 h3)
  · intro μ hne
    have hdetZ : μ 0 0 * μ 1 1 - μ 0 1 * μ 1 0 = 1 := by
      have hh := μ.2; rwa [Matrix.det_fin_two] at hh
    set M : ℝ := ((μ 1 0 : ℤ) : ℝ)^2 * s₀^2 + ((μ 1 1 : ℤ) : ℝ)^2 with hM
    have hMpos : 0 < M := by
      have hcd : ¬ ((μ 1 0 : ℤ) = 0 ∧ (μ 1 1 : ℤ) = 0) := by
        rintro ⟨h1, h2⟩
        rw [h1, h2] at hdetZ; norm_num at hdetZ
      have hsum : (((μ 1 0 : ℤ) : ℝ) * s₀)^2 + ((μ 1 1 : ℤ) : ℝ)^2 ≠ 0 := by
        intro hh
        have h1 : (((μ 1 0 : ℤ) : ℝ) * s₀)^2 = 0 := by
          nlinarith [sq_nonneg (((μ 1 0 : ℤ) : ℝ) * s₀), sq_nonneg ((μ 1 1 : ℤ) : ℝ)]
        have h2 : ((μ 1 1 : ℤ) : ℝ)^2 = 0 := by
          nlinarith [sq_nonneg (((μ 1 0 : ℤ) : ℝ) * s₀), sq_nonneg ((μ 1 1 : ℤ) : ℝ)]
        have hc0 : ((μ 1 0 : ℤ) : ℝ) = 0 := by
          have := sq_eq_zero_iff.mp h1
          exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hs₀)
        have hd0 : ((μ 1 1 : ℤ) : ℝ) = 0 := by simpa using sq_eq_zero_iff.mp h2
        exact hcd ⟨by exact_mod_cast hc0, by exact_mod_cast hd0⟩
      rw [hM, show ((μ 1 0 : ℤ) : ℝ)^2 * s₀^2 = (((μ 1 0 : ℤ) : ℝ) * s₀)^2 by ring]
      exact lt_of_le_of_ne (by positivity) (Ne.symm hsum)
    set Y : ℝ := (μ • Work.Kernels.imagAxis s₀ hs₀).im with hYdef
    set R : ℝ := (μ • Work.Kernels.imagAxis s₀ hs₀).re with hRdef
    have hY : Y = s₀ / M := by
      have h := (web_re_im μ s₀ hs₀).1
      rw [UpperHalfPlane.coe_im] at h
      rw [hYdef, h]
    have hR : R = ((((μ 0 0 : ℤ) : ℝ) - ((μ 1 0 : ℤ) : ℝ)) * ((μ 1 0 : ℤ) : ℝ) * s₀^2
            + (((μ 0 1 : ℤ) : ℝ) - ((μ 1 1 : ℤ) : ℝ)) * ((μ 1 1 : ℤ) : ℝ)) / M + 1 := by
      have h := (web_re_im μ s₀ hs₀).2
      have h1 : ((↑(μ • Work.Kernels.imagAxis s₀ hs₀) : ℂ) - 1).re
          = (μ • Work.Kernels.imagAxis s₀ hs₀).re - 1 := by
        rw [Complex.sub_re, UpperHalfPlane.coe_re, Complex.one_re]
      rw [h1] at h
      rw [hRdef]
      linarith
    have hQ : (R^2 + (Y - s₀)^2)/Y = M * R^2/s₀ + s₀*(1-M)^2/M := by
      rw [hY]; field_simp
    have hsq : ∀ z : ℤ, z ≠ 0 → (1:ℝ) ≤ ((z : ℤ) : ℝ)^2 := by
      intro z hz
      have h1 : (1:ℤ) ≤ |z| := Int.one_le_abs hz
      have h2 : (1:ℝ) ≤ |((z : ℤ) : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h1
      have h3 := sq_le_sq.mpr (show |(1:ℝ)| ≤ |((z : ℤ) : ℝ)| by simpa using h2)
      simpa using h3
    have his₀ : (μ • Work.Kernels.imagAxis s₀ hs₀) = Work.Kernels.imagAxis s₀ hs₀ ↔ R = 0 ∧ Y = s₀ := by
      constructor
      · intro h
        exact ⟨by rw [hRdef, h]; simp [Work.Kernels.imagAxis],
               by rw [hYdef, h]; simp [Work.Kernels.imagAxis]⟩
      · rintro ⟨h1, h2⟩
        apply UpperHalfPlane.ext
        rw [Complex.ext_iff]
        exact ⟨by rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, ← hRdef, h1]; simp [Work.Kernels.imagAxis],
               by rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, ← hYdef, h2]; simp [Work.Kernels.imagAxis]⟩
    by_cases hc : μ 1 0 = 0
    · have had : μ 0 0 * μ 1 1 = 1 := by rw [hc] at hdetZ; linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
      · have hcR : ((μ 1 0 : ℤ) : ℝ) = 0 := by rw [hc]; norm_num
        have hM1 : M = 1 := by rw [hM, hcR, hd]; norm_num
        have hY1 : Y = s₀ := by rw [hY, hM1]; norm_num
        have hRval : R = ((μ 0 1 : ℤ) : ℝ) ∨ R = -((μ 0 1 : ℤ) : ℝ) := by
          rw [hR, hM1, hcR, hd]; left; ring
        have hbne : μ 0 1 ≠ 0 := by
          intro hb0
          exact hne (his₀.mpr ⟨by rcases hRval with h | h <;> rw [h] <;> simp [hb0], hY1⟩)
        have hs1 : (1:ℝ) ≤ ((μ 0 1 : ℤ) : ℝ)^2 := hsq (μ 0 1) hbne
        have hRsq : R^2 = ((μ 0 1 : ℤ) : ℝ)^2 := by rcases hRval with h | h <;> rw [h] <;> ring
        have hQv : (R^2 + (Y - s₀)^2)/Y = R^2/s₀ := by rw [hY1]; ring
        calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
            ≤ 1/s₀ := min_le_left _ _
          _ ≤ R^2/s₀ := by rw [hRsq]; exact div_le_div_of_nonneg_right hs1 hs₀.le
          _ = (R^2 + (Y - s₀)^2)/Y := hQv.symm
      · have hcR : ((μ 1 0 : ℤ) : ℝ) = 0 := by rw [hc]; norm_num
        have hM1 : M = 1 := by rw [hM, hcR, hd]; norm_num
        have hY1 : Y = s₀ := by rw [hY, hM1]; norm_num
        have hRval : R = ((μ 0 1 : ℤ) : ℝ) ∨ R = -((μ 0 1 : ℤ) : ℝ) := by
          rw [hR, hM1, hcR, hd]; right; ring
        have hbne : μ 0 1 ≠ 0 := by
          intro hb0
          exact hne (his₀.mpr ⟨by rcases hRval with h | h <;> rw [h] <;> simp [hb0], hY1⟩)
        have hs1 : (1:ℝ) ≤ ((μ 0 1 : ℤ) : ℝ)^2 := hsq (μ 0 1) hbne
        have hRsq : R^2 = ((μ 0 1 : ℤ) : ℝ)^2 := by rcases hRval with h | h <;> rw [h] <;> ring
        have hQv : (R^2 + (Y - s₀)^2)/Y = R^2/s₀ := by rw [hY1]; ring
        calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
            ≤ 1/s₀ := min_le_left _ _
          _ ≤ R^2/s₀ := by rw [hRsq]; exact div_le_div_of_nonneg_right hs1 hs₀.le
          _ = (R^2 + (Y - s₀)^2)/Y := hQv.symm
    · by_cases hd : μ 1 1 = 0
      · have hbc : μ 0 1 * μ 1 0 = -1 := by
          have h := hdetZ; rw [hd] at h; linarith
        rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hbc with ⟨hb, hc1⟩ | ⟨hb, hc1⟩
        · have hcR : ((μ 1 0 : ℤ) : ℝ) = -1 := by rw [hc1]; norm_num
          have hMv : M = s₀^2 := by rw [hM, hcR, hd]; ring
          have hYv : Y = 1/s₀ := by rw [hY, hMv]; field_simp
          have hRval : R = ((μ 0 0 : ℤ) : ℝ) ∨ R = -((μ 0 0 : ℤ) : ℝ) := by
            rw [hR, hMv, hc1, hb, hd]; right; field_simp; ring
          have hRsq : R^2 = ((μ 0 0 : ℤ) : ℝ)^2 := by rcases hRval with h | h <;> rw [h] <;> ring
          have hQv : (R^2 + (Y - s₀)^2)/Y = R^2 * s₀ + (1 - s₀^2)^2/s₀ := by
            rw [hYv]; field_simp
          by_cases h1 : s₀ = 1
          · have hane : μ 0 0 ≠ 0 := by
              intro ha0
              refine hne (his₀.mpr ⟨?_, hYv.trans (by rw [h1]; norm_num)⟩)
              rcases hRval with h | h <;> rw [h] <;> simp [ha0]
            have hs1 : (1:ℝ) ≤ ((μ 0 0 : ℤ) : ℝ)^2 := hsq (μ 0 0) hane
            have hQ1 : (R^2 + (Y - s₀)^2)/Y = R^2 := by rw [hQv, h1]; ring
            calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ 1 := by rw [h1]; norm_num
              _ ≤ R^2 := by rw [hRsq]; exact hs1
              _ = (R^2 + (Y - s₀)^2)/Y := hQ1.symm
          · have hFs : min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ (1 - s₀^2)^2/s₀ := by
              rw [if_neg h1]
              exact le_trans (min_le_right _ _) (min_le_right _ _)
            calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ (1 - s₀^2)^2/s₀ := hFs
              _ ≤ R^2 * s₀ + (1 - s₀^2)^2/s₀ := by nlinarith [sq_nonneg R, hs₀]
              _ = (R^2 + (Y - s₀)^2)/Y := hQv.symm
        · have hcR : ((μ 1 0 : ℤ) : ℝ) = 1 := by rw [hc1]; norm_num
          have hMv : M = s₀^2 := by rw [hM, hcR, hd]; ring
          have hYv : Y = 1/s₀ := by rw [hY, hMv]; field_simp
          have hRval : R = ((μ 0 0 : ℤ) : ℝ) ∨ R = -((μ 0 0 : ℤ) : ℝ) := by
            rw [hR, hMv, hc1, hb, hd]; left; field_simp; ring
          have hRsq : R^2 = ((μ 0 0 : ℤ) : ℝ)^2 := by rcases hRval with h | h <;> rw [h] <;> ring
          have hQv : (R^2 + (Y - s₀)^2)/Y = R^2 * s₀ + (1 - s₀^2)^2/s₀ := by
            rw [hYv]; field_simp
          by_cases h1 : s₀ = 1
          · have hane : μ 0 0 ≠ 0 := by
              intro ha0
              refine hne (his₀.mpr ⟨?_, hYv.trans (by rw [h1]; norm_num)⟩)
              rcases hRval with h | h <;> rw [h] <;> simp [ha0]
            have hs1 : (1:ℝ) ≤ ((μ 0 0 : ℤ) : ℝ)^2 := hsq (μ 0 0) hane
            have hQ1 : (R^2 + (Y - s₀)^2)/Y = R^2 := by rw [hQv, h1]; ring
            calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ 1 := by rw [h1]; norm_num
              _ ≤ R^2 := by rw [hRsq]; exact hs1
              _ = (R^2 + (Y - s₀)^2)/Y := hQ1.symm
          · have hFs : min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ (1 - s₀^2)^2/s₀ := by
              rw [if_neg h1]
              exact le_trans (min_le_right _ _) (min_le_right _ _)
            calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
                ≤ (1 - s₀^2)^2/s₀ := hFs
              _ ≤ R^2 * s₀ + (1 - s₀^2)^2/s₀ := by nlinarith [sq_nonneg R, hs₀]
              _ = (R^2 + (Y - s₀)^2)/Y := hQv.symm
      · have hC1 : (1:ℝ) ≤ ((μ 1 0 : ℤ) : ℝ)^2 := hsq (μ 1 0) hc
        have hD1 : (1:ℝ) ≤ ((μ 1 1 : ℤ) : ℝ)^2 := hsq (μ 1 1) hd
        have hMge : 1 + s₀^2 ≤ M := by rw [hM]; nlinarith [hC1, hD1, sq_nonneg s₀]
        have hfac : (1 - M)^2 * (1 + s₀^2) - s₀^4 * M
            = (M - 1 - s₀^2) * (2*s₀^2 + s₀^4 + (M - 1 - s₀^2) * (1 + s₀^2)) := by ring
        have hdiv : s₀^4/(1+s₀^2) ≤ (1-M)^2/M := by
          have he : 0 ≤ M - 1 - s₀^2 := by linarith
          have hnonneg : 0 ≤ (1 - M)^2 * (1 + s₀^2) - s₀^4 * M := by rw [hfac]; positivity
          rw [div_le_iff₀ (show (0:ℝ) < 1 + s₀^2 by positivity)]
          rw [div_mul_eq_mul_div, le_div_iff₀ hMpos]
          linarith
        have hstep : s₀^5/(1+s₀^2) ≤ M * R^2/s₀ + s₀*(1-M)^2/M := by
          have h1 : 0 ≤ M * R^2/s₀ := by positivity
          have h2 : s₀ * (s₀^4/(1+s₀^2)) ≤ s₀ * ((1-M)^2/M) := mul_le_mul_of_nonneg_left hdiv hs₀.le
          have h3 : s₀^5/(1+s₀^2) = s₀ * (s₀^4/(1+s₀^2)) := by ring
          have h4 : s₀ * ((1-M)^2/M) = s₀*(1-M)^2/M := by ring
          linarith
        calc min (1/s₀) (min (s₀^5/(1+s₀^2)) (if s₀ = 1 then 1 else (1-s₀^2)^2/s₀))
            ≤ s₀^5/(1+s₀^2) := le_trans (min_le_right _ _) (min_le_left _ _)
          _ ≤ M * R^2/s₀ + s₀*(1-M)^2/M := hstep
          _ = (R^2 + (Y - s₀)^2)/Y := hQ.symm
/-! ## Estimates for the detour rectangle -/

/-- Elementary bounds for the quantity `(u ^ 2 + (v - c) ^ 2) / v` on the boundary of the
rectangle `(0,A] × [c-A, c+A)` or `[-A,0) × [c-A, c+A]`. -/
lemma curve_Q_bounds {A c u v : ℝ} (hA : 0 < A) (hc : A < c) (hv : 0 < v)
    (h : (0 < u ∧ u < A ∧ (v = c - A ∨ v = c + A)) ∨ (u = A ∧ c - A < v ∧ v < c + A)
      ∨ ((-A < u ∧ u < 0) ∧ (v = c - A ∨ v = c + A)) ∨ (u = -A ∧ c - A < v ∧ v < c + A)) :
    A ^ 2 / (c + A) ≤ (u ^ 2 + (v - c) ^ 2) / v ∧
      (u ^ 2 + (v - c) ^ 2) / v ≤ 2 * A ^ 2 / (c - A) := by
  have ha : |u| ≤ A := by
    rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1, h2, h3⟩
    · rw [abs_of_pos h1]; linarith
    · rw [abs_of_pos h1]; linarith
    · rw [h1, abs_of_pos hA]
    · rw [abs_of_neg h2]; linarith
    · rw [abs_of_neg h2]; linarith
    · rw [h1, abs_neg, abs_of_pos hA]
  have hb : |v - c| ≤ A := by
    rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1, h2, h3⟩
    · rw [h3, show c - A - c = -A by ring, abs_neg, abs_of_pos hA]
    · rw [h3, show c + A - c = A by ring, abs_of_pos hA]
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [h3, show c - A - c = -A by ring, abs_neg, abs_of_pos hA]
    · rw [h3, show c + A - c = A by ring, abs_of_pos hA]
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc1 : |u| = A ∨ |v - c| = A := by
    rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1, h2, h3⟩
    · right; rw [h3, show c - A - c = -A by ring, abs_neg, abs_of_pos hA]
    · right; rw [h3, show c + A - c = A by ring, abs_of_pos hA]
    · left; rw [h1, abs_of_pos hA]
    · right; rw [h3, show c - A - c = -A by ring, abs_neg, abs_of_pos hA]
    · right; rw [h3, show c + A - c = A by ring, abs_of_pos hA]
    · left; rw [h1, abs_neg, abs_of_pos hA]
  have hu2 : u ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs u, ← sq_abs A]; exact sq_le_sq.mpr (by simpa [abs_of_pos hA] using ha)
  have hv2 : (v - c) ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs (v - c), ← sq_abs A]; exact sq_le_sq.mpr (by simpa [abs_of_pos hA] using hb)
  have hvc : v ≤ c + A := by have := (abs_le.mp hb).2; linarith
  have hvlo : c - A ≤ v := by have := (abs_le.mp hb).1; linarith
  have hq1 : A ^ 2 ≤ u ^ 2 + (v - c) ^ 2 := by
    rcases hc1 with h1 | h1
    · have : u ^ 2 = A ^ 2 := by rw [← sq_abs u, h1]
      linarith [sq_nonneg (v - c)]
    · have : (v - c) ^ 2 = A ^ 2 := by rw [← sq_abs (v - c), h1]
      linarith [sq_nonneg u]
  constructor
  · rw [div_le_iff₀ (show (0:ℝ) < c + A by linarith), div_mul_eq_mul_div, le_div_iff₀ hv]
    nlinarith [hq1, hv, hvc]
  · rw [div_le_iff₀ hv, div_mul_eq_mul_div, le_div_iff₀ (show (0:ℝ) < c - A by linarith)]
    nlinarith [hu2, hv2, hvlo, hv]

/-- The distance from a boundary point of the detour rectangle around `i c` to `i c`. -/
lemma ofReImT_dist_bounds {A c u v : ℝ} (hA : 0 < A) (hc : A < c) (hv : 0 < v)
    (h : (0 < u ∧ u < A ∧ (v = c - A ∨ v = c + A)) ∨ (u = A ∧ c - A < v ∧ v < c + A)
      ∨ ((-A < u ∧ u < 0) ∧ (v = c - A ∨ v = c + A)) ∨ (u = -A ∧ c - A < v ∧ v < c + A)) :
    Real.arcosh (1 + A ^ 2 / (2 * c * (c + A))) ≤
        dist (ofReImT u v) (Work.Kernels.imagAxis c (lt_trans hA hc)) ∧
      dist (ofReImT u v) (Work.Kernels.imagAxis c (lt_trans hA hc)) ≤
        Real.arcosh (1 + A ^ 2 / (c * (c - A))) := by
  have hcpos : 0 < c := lt_trans hA hc
  have hQ := curve_Q_bounds hA hc hv h
  have hzre : (ofReImT u v).re = u := ofReImT_re u v hv
  have hzim : (ofReImT u v).im = v := ofReImT_im u v hv
  have hcre : (Work.Kernels.imagAxis c hcpos).re = 0 := by simp [Work.Kernels.imagAxis]
  have hcim : (Work.Kernels.imagAxis c hcpos).im = c := by simp [Work.Kernels.imagAxis]
  have hcosh : Real.cosh (dist (ofReImT u v) (Work.Kernels.imagAxis c hcpos))
      = 1 + ((u ^ 2 + (v - c) ^ 2) / v) / (2 * c) := by
    rw [UpperHalfPlane.cosh_dist', hzre, hzim, hcre, hcim]
    field_simp
    ring
  constructor
  · have hX : (1:ℝ) ≤ 1 + A ^ 2 / (2 * c * (c + A)) := by
      have h : (0:ℝ) < A ^ 2 / (2 * c * (c + A)) := by positivity
      linarith
    have hmono : Real.cosh (Real.arcosh (1 + A ^ 2 / (2 * c * (c + A))))
        ≤ Real.cosh (dist (ofReImT u v) (Work.Kernels.imagAxis c hcpos)) := by
      rw [Real.cosh_arcosh hX, hcosh]
      have hgoal : A ^ 2 / (2 * c * (c + A)) ≤ ((u ^ 2 + (v - c) ^ 2) / v) / (2 * c) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : A ^ 2 ≤ ((u ^ 2 + (v - c) ^ 2) / v) * (c + A) :=
          (div_le_iff₀ (show (0:ℝ) < c + A by linarith)).mp hQ.1
        nlinarith [h1, hv, hA, hcpos]
      linarith
    have h2 := Real.cosh_le_cosh.mp hmono
    rwa [abs_of_nonneg (Real.arcosh_nonneg hX), abs_of_nonneg dist_nonneg] at h2
  · have hY : (1:ℝ) ≤ 1 + A ^ 2 / (c * (c - A)) := by
      have h : (0:ℝ) < A ^ 2 / (c * (c - A)) := by positivity
      linarith
    have hmono : Real.cosh (dist (ofReImT u v) (Work.Kernels.imagAxis c hcpos))
        ≤ Real.cosh (Real.arcosh (1 + A ^ 2 / (c * (c - A)))) := by
      rw [Real.cosh_arcosh hY, hcosh]
      have hgoal : ((u ^ 2 + (v - c) ^ 2) / v) / (2 * c) ≤ A ^ 2 / (c * (c - A)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : ((u ^ 2 + (v - c) ^ 2) / v) * (c - A) ≤ 2 * A ^ 2 :=
          (le_div_iff₀ (show (0:ℝ) < c - A by linarith)).mp hQ.2
        nlinarith [h1, hv, hA, hcpos]
      linarith
    have h2 := Real.cosh_le_cosh.mp hmono
    rwa [abs_of_nonneg (Real.arcosh_nonneg hY), abs_of_nonneg dist_nonneg] at h2

/-- Triangle-inequality packaging: if `q` is `δ` away from `p`, `z` is within `r` of `p`, and
`ε ≤ δ - r`, then `ε ≤ dist z q`. -/
lemma le_dist_of_le_dist_sub {p q z : UpperHalfPlane} {r δ ε : ℝ}
    (hδ : δ ≤ dist p q) (hz : dist z p ≤ r) (hε : ε ≤ δ - r) : ε ≤ dist z q := by
  have htri : dist p q ≤ dist p z + dist z q := dist_triangle p z q
  have hz' : dist p z ≤ r := by rwa [dist_comm] at hz
  linarith


/-! ## The main theorem -/

theorem exists_contour_avoid (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ A₁ ξ₁ A₂ ξ₂ : ℝ,
      0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧ A₁ < s₀ ∧ ξ₁ < 1 ∧
      (A₂ = 0 ↔ ξ₂ = 0) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
        t ∉ Set.Ioo (s₀ - A₁) (s₀ + A₁) → t ∉ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
        ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (u v : ℝ), 0 < v →
        ((0 < u ∧ u < ξ₁ ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁)))
        ∨ (u = ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)
        ∨ ((-ξ₂ < u ∧ u < 0) ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂) →
        ε ≤ dist (γ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀)) := by
  obtain ⟨F₀, hF₀pos, hgapQ⟩ := orbitGap_imagAxis s₀ hs₀
  set δ₀ : ℝ := Real.arcosh (1 + F₀/(2*s₀)) with hδ₀
  have hδ₀gt : (1:ℝ) < 1 + F₀/(2*s₀) := by
    have h : (0:ℝ) < F₀/(2*s₀) := by positivity
    linarith
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; exact Real.arcosh_pos hδ₀gt
  have hgapD : ∀ ν : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ν • Work.Kernels.imagAxis s₀ hs₀ ≠ Work.Kernels.imagAxis s₀ hs₀ →
      δ₀ ≤ dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀) := by
    intro ν hν
    have hQ := hgapQ ν hν
    have hre : (Work.Kernels.imagAxis s₀ hs₀).re = 0 := by simp [Work.Kernels.imagAxis]
    have him : (Work.Kernels.imagAxis s₀ hs₀).im = s₀ := by simp [Work.Kernels.imagAxis]
    have hcosh := UpperHalfPlane.cosh_dist' (ν • Work.Kernels.imagAxis s₀ hs₀)
      (Work.Kernels.imagAxis s₀ hs₀)
    rw [hre, him] at hcosh
    have h2 : Real.cosh (dist (ν • Work.Kernels.imagAxis s₀ hs₀) (Work.Kernels.imagAxis s₀ hs₀))
        = 1 + (((((ν • Work.Kernels.imagAxis s₀ hs₀).re) ^ 2
            + ((ν • Work.Kernels.imagAxis s₀ hs₀).im - s₀) ^ 2)
          / (ν • Work.Kernels.imagAxis s₀ hs₀).im) / (2 * s₀)) := by
      rw [hcosh]; field_simp; ring
    have h1 : Real.cosh δ₀ ≤ Real.cosh (dist (ν • Work.Kernels.imagAxis s₀ hs₀)
        (Work.Kernels.imagAxis s₀ hs₀)) := by
      rw [hδ₀, Real.cosh_arcosh (le_of_lt hδ₀gt), h2]
      have := div_le_div_of_nonneg_right hQ (by positivity : (0:ℝ) ≤ 2 * s₀)
      linarith
    have h3 := Real.cosh_le_cosh.mp h1
    rwa [abs_of_nonneg hδ₀pos.le, abs_of_nonneg dist_nonneg] at h3
  obtain ⟨rw₀, hrw₀pos, hweb⟩ := web_near_center_param s₀ hs₀
  obtain ⟨m, hmpos, hmle1, hm_le_s₀, hm_le_inv⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ s₀ ∧ m ≤ s₀⁻¹ := by
    refine ⟨min s₀ s₀⁻¹, lt_min hs₀ (inv_pos.mpr hs₀), ?_, min_le_left _ _, min_le_right _ _⟩
    rcases le_or_gt s₀ 1 with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (inv_lt_one_of_one_lt₀ h).le
  obtain ⟨A, hApos, hA_le_m4, hA_le_s, hAne⟩ :
      ∃ A : ℝ, 0 < A ∧ A ≤ m/4 ∧ A ≤ m * Real.sqrt (F₀/(4*s₀)) / 4 ∧ A ≠ |s₀ - s₀⁻¹| := by
    set P : ℝ := min (m/4) (m * Real.sqrt (F₀/(4*s₀)) / 4) with hP
    have hPpos : 0 < P := by
      rw [hP]
      refine lt_min (by linarith) ?_
      have h1 : 0 < Real.sqrt (F₀/(4*s₀)) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have hAle : (if |s₀ - s₀⁻¹| = P then P/2 else P) ≤ P := by
      split
      · linarith
      · exact le_rfl
    refine ⟨if |s₀ - s₀⁻¹| = P then P/2 else P, ?_, ?_, ?_, ?_⟩
    · split
      · linarith
      · exact hPpos
    · exact le_trans hAle (by rw [hP]; exact min_le_left _ _)
    · exact le_trans hAle (by rw [hP]; exact min_le_right _ _)
    · split
      · rename_i h
        intro hh
        rw [← h] at hh
        linarith
      · rename_i h
        exact fun hh => h hh.symm
  have hAltm : A < m := by linarith
  have hAlt_s₀ : A < s₀ := lt_of_lt_of_le hAltm hm_le_s₀
  have hAlt_inv : A < s₀⁻¹ := lt_of_lt_of_le hAltm hm_le_inv
  have hAlt_one : A < 1 := lt_of_lt_of_le hAltm hmle1
  have hrmax_lt : ∀ c : ℝ, m ≤ c → Real.arcosh (1 + A^2/(c*(c-A))) < δ₀ := by
    intro c hc
    have hc0 : 0 < c := lt_of_lt_of_le hmpos hc
    have hcA : 0 < c - A := by
      have : A < c := lt_of_lt_of_le hAltm hc
      linarith
    have hden : 0 < c*(c-A) := by positivity
    have hkey : A^2/(c*(c-A)) ≤ F₀/(4*s₀) := by
      rw [div_le_iff₀ hden]
      have hsqF : (Real.sqrt (F₀/(4*s₀)))^2 = F₀/(4*s₀) := Real.sq_sqrt (by positivity)
      have hcq : (3*m^2)/4 ≤ c*(c-A) := by
        have h2 : 3*m/4 ≤ c - A := by linarith [hA_le_m4, hc]
        have h3 := mul_le_mul hc h2 (by linarith) (le_of_lt hc0)
        linarith [h3]
      have hA2 : A^2 ≤ m^2 * (F₀/(4*s₀)) / 16 := by
        have h1 : A ≤ m * Real.sqrt (F₀/(4*s₀)) / 4 := hA_le_s
        nlinarith [h1, hApos, hsqF]
      nlinarith [hA2, hcq, hmpos, hF₀pos, hs₀]
    have hco : Real.cosh (Real.arcosh (1 + A^2/(c*(c-A)))) < Real.cosh δ₀ := by
      have h1 : (0:ℝ) < A^2/(c*(c-A)) := by positivity
      have h3 : F₀/(4*s₀) < F₀/(2*s₀) := by
        have h4 : 0 < F₀/(4*s₀) := by positivity
        have h5 : F₀/(4*s₀) + F₀/(4*s₀) = F₀/(2*s₀) := by field_simp; ring
        linarith
      rw [Real.cosh_arcosh (by linarith), hδ₀, Real.cosh_arcosh (le_of_lt hδ₀gt)]
      linarith [hkey, h3]
    have h2 := Real.cosh_lt_cosh.mp hco
    rwa [abs_of_nonneg (Real.arcosh_nonneg (by
          have : (0:ℝ) < A^2/(c*(c-A)) := by positivity
          linarith)),
      abs_of_nonneg hδ₀pos.le] at h2
  obtain ⟨Rmx, hRmxlt, hRmx1, hRmx2⟩ :
      ∃ R : ℝ, R < δ₀ ∧ Real.arcosh (1 + A^2/(s₀*(s₀-A))) ≤ R ∧
        Real.arcosh (1 + A^2/(s₀⁻¹*(s₀⁻¹-A))) ≤ R := by
    refine ⟨max (Real.arcosh (1 + A^2/(s₀*(s₀-A))))
      (Real.arcosh (1 + A^2/(s₀⁻¹*(s₀⁻¹-A)))), ?_, le_max_left _ _, le_max_right _ _⟩
    apply max_lt
    · exact hrmax_lt s₀ hm_le_s₀
    · exact hrmax_lt s₀⁻¹ hm_le_inv
  obtain ⟨Rmn, hRmnpos, hRmn1, hRmn2⟩ :
      ∃ R : ℝ, 0 < R ∧ R ≤ Real.arcosh (1 + A^2/(2*s₀*(s₀+A))) ∧
        R ≤ Real.arcosh (1 + A^2/(2*s₀⁻¹*(s₀⁻¹+A))) := by
    refine ⟨min (Real.arcosh (1 + A^2/(2*s₀*(s₀+A))))
      (Real.arcosh (1 + A^2/(2*s₀⁻¹*(s₀⁻¹+A)))), ?_, min_le_left _ _, min_le_right _ _⟩
    apply lt_min
    · apply Real.arcosh_pos
      have h : (0:ℝ) < A^2/(2*s₀*(s₀+A)) := by positivity
      linarith
    · apply Real.arcosh_pos
      have h : (0:ℝ) < A^2/(2*s₀⁻¹*(s₀⁻¹+A)) := by positivity
      linarith
  obtain ⟨ε, hεpos, hε4, hεA, hεAs, hεw, hεδ, hεr⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ ε ≤ A/(4*s₀) ∧ ε ≤ A*s₀/8 ∧ ε ≤ rw₀ ∧
        ε ≤ δ₀ - Rmx ∧ ε ≤ Rmn := by
    have hδRmx : 0 < δ₀ - Rmx := by linarith
    refine ⟨min (1/4) (min (A/(4*s₀)) (min (A*s₀/8) (min rw₀ (min (δ₀ - Rmx) Rmn)))),
      lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (lt_min hrw₀pos
        (lt_min hδRmx hRmnpos)))), min_le_left _ _, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))

  refine ⟨ε, hεpos, A, A, A, A, hApos, hApos, hApos.le, hApos.le, hAlt_s₀, hAlt_one, ?_, ?_, ?_⟩
  · exact ⟨id, id⟩
  · intro γ t ht ht1 ht2 τ hτ hjeq
    obtain ⟨σ, hσ⟩ := jInvariantFun_eq_smul_of_eq hjeq
    have hdist : dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < ε := by
      rw [hσ]; exact hτ
    have hltw : dist (σ • Work.Kernels.imagAxis t ht) (onePlusI s₀ hs₀) < rw₀ :=
      lt_of_lt_of_le hdist hεw
    have hr := hweb σ t ht hltw
    have hb := abs_im_sub_le_of_dist hs₀ hεpos.le (by linarith [hε4]) hr.1 hdist
    rcases hr.2 with him | him
    · have h1 : |t - s₀| ≤ 2*s₀*ε := by rw [← him]; exact hb
      have h3 : s₀ * ε ≤ A/4 := by
        have h := mul_le_mul_of_nonneg_left hεA hs₀.le
        rwa [show s₀ * (A/(4*s₀)) = A/4 by field_simp] at h
      have h2 : |t - s₀| < A := by linarith
      exact ht1 ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩
    · have hty : t = ((σ • Work.Kernels.imagAxis t ht).im)⁻¹ := by rw [him, inv_inv]
      set y : ℝ := (σ • Work.Kernels.imagAxis t ht).im with hydef
      have hypos : 0 < y := by rw [hydef]; exact (σ • Work.Kernels.imagAxis t ht).im_pos
      have hyge : s₀/2 ≤ y := by
        have h2 := abs_le.mp hb
        have h3 : 2*s₀*ε ≤ s₀/2 := by nlinarith [hε4, hs₀]
        linarith [h2.1, h3]
      have hbnd : |t - s₀⁻¹| * s₀ ≤ 4*ε := by
        have h1 : |s₀ - y| ≤ 2*s₀*ε := by rw [abs_sub_comm]; exact hb
        have hsub : t - s₀⁻¹ = (s₀ - y)/(y*s₀) := by rw [hty]; field_simp
        have h2 : |t - s₀⁻¹| * s₀ = |s₀ - y| / y := by
          rw [hsub, abs_div, abs_of_pos (by positivity : (0:ℝ) < y*s₀)]
          field_simp
        rw [h2, div_le_iff₀ hypos]
        nlinarith [h1, hyge, hs₀, hεpos.le]
      have hfin : |t - s₀⁻¹| < A := by
        have h3 : 4*ε ≤ A*s₀/2 := by
          have h := mul_le_mul_of_nonneg_left hεAs (by norm_num : (0:ℝ) ≤ 4)
          linarith
        have h4 : |t - s₀⁻¹| * s₀ ≤ A*s₀/2 := le_trans hbnd h3
        have h5 : |t - s₀⁻¹| ≤ A/2 := by
          have h6 : |t - s₀⁻¹| = (|t - s₀⁻¹| * s₀)/s₀ := by field_simp
          rw [h6]
          calc (|t - s₀⁻¹| * s₀)/s₀ ≤ (A*s₀/2)/s₀ := div_le_div_of_nonneg_right h4 hs₀.le
            _ = A/2 := by field_simp
        linarith [h5, hApos]
      exact ht2 ⟨by linarith [(abs_lt.mp hfin).1], by linarith [(abs_lt.mp hfin).2]⟩
  · intro γ u v hv hdisj
    have hdist : dist (γ • ofReImT u v) (onePlusI s₀ hs₀)
        = dist (ofReImT u v) ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀) := by
      have hγ : γ • (γ⁻¹ • onePlusI s₀ hs₀) = onePlusI s₀ hs₀ := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [show dist (γ • ofReImT u v) (onePlusI s₀ hs₀)
            = dist (γ • ofReImT u v) (γ • (γ⁻¹ • onePlusI s₀ hs₀)) by rw [hγ], dist_smul_SL2Z]
      congr 1
      rw [← T_smul_imagAxis s₀ hs₀, mul_smul]
    rcases hdisj with h1 | h2 | h3 | h4
    · obtain ⟨hlow, hhigh⟩ :=
        ofReImT_dist_bounds (A := A) (c := s₀) (u := u) (v := v) hApos hAlt_s₀ hv (Or.inl h1)
      rw [show Work.Kernels.imagAxis s₀ (lt_trans hApos hAlt_s₀)
            = Work.Kernels.imagAxis s₀ hs₀ from rfl] at hlow hhigh
      by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
          = Work.Kernels.imagAxis s₀ hs₀
      · rw [hdist, hbase]
        exact le_trans (le_trans hεr hRmn1) hlow
      · rw [hdist]
        have hδ := hgapD (γ⁻¹ * ModularGroup.T) hbase
        rw [dist_comm] at hδ
        refine le_dist_of_le_dist_sub hδ hhigh ?_
        linarith [hεδ, hRmx1]
    · obtain ⟨hlow, hhigh⟩ :=
        ofReImT_dist_bounds (A := A) (c := s₀) (u := u) (v := v) hApos hAlt_s₀ hv
          (Or.inr (Or.inl h2))
      rw [show Work.Kernels.imagAxis s₀ (lt_trans hApos hAlt_s₀)
            = Work.Kernels.imagAxis s₀ hs₀ from rfl] at hlow hhigh
      by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
          = Work.Kernels.imagAxis s₀ hs₀
      · rw [hdist, hbase]
        exact le_trans (le_trans hεr hRmn1) hlow
      · rw [hdist]
        have hδ := hgapD (γ⁻¹ * ModularGroup.T) hbase
        rw [dist_comm] at hδ
        refine le_dist_of_le_dist_sub hδ hhigh ?_
        linarith [hεδ, hRmx1]
    · obtain ⟨hlow, hhigh⟩ :=
        ofReImT_dist_bounds (A := A) (c := s₀⁻¹) (u := u) (v := v) hApos hAlt_inv hv
          (Or.inr (Or.inr (Or.inl h3)))
      rw [show Work.Kernels.imagAxis s₀⁻¹ (lt_trans hApos hAlt_inv)
            = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) from rfl] at hlow hhigh
      by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
          = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
      · rw [hdist, hbase]
        exact le_trans (le_trans hεr hRmn2) hlow
      · rw [hdist]
        refine le_dist_of_le_dist_sub (p := Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀))
          (q := (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
          (z := ofReImT u v) (r := Real.arcosh (1 + A^2/(s₀⁻¹*(s₀⁻¹-A)))) (δ := δ₀) ?_ hhigh ?_
        · have hν : (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀
              ≠ Work.Kernels.imagAxis s₀ hs₀ := by
            intro hh
            apply hbase
            calc (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
                = ((ModularGroup.S * ModularGroup.S⁻¹) * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀ := by rw [mul_inv_cancel, one_mul]
              _ = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀) := by rw [mul_assoc, mul_smul]
              _ = ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀ := by rw [hh]
              _ = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) := S_smul_imagAxis s₀ hs₀
          have hgap := hgapD (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) hν
          rw [dist_comm] at hgap
          have h5 : dist (ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀)
                ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
              = dist (Work.Kernels.imagAxis s₀ hs₀)
                ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀) := by
            have hA : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
                = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀) := by
              rw [show ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀)
                  = (ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)))
                    • Work.Kernels.imagAxis s₀ hs₀ from (mul_smul _ _ _).symm,
                show ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    = γ⁻¹ * ModularGroup.T by group]
            rw [hA, dist_smul_SL2Z]
          rw [← S_smul_imagAxis s₀ hs₀, h5]
          exact hgap
        · linarith [hεδ, hRmx2]
    · obtain ⟨hlow, hhigh⟩ :=
        ofReImT_dist_bounds (A := A) (c := s₀⁻¹) (u := u) (v := v) hApos hAlt_inv hv
          (Or.inr (Or.inr (Or.inr h4)))
      rw [show Work.Kernels.imagAxis s₀⁻¹ (lt_trans hApos hAlt_inv)
            = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) from rfl] at hlow hhigh
      by_cases hbase : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
          = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀)
      · rw [hdist, hbase]
        exact le_trans (le_trans hεr hRmn2) hlow
      · rw [hdist]
        refine le_dist_of_le_dist_sub (p := Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀))
          (q := (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
          (z := ofReImT u v) (r := Real.arcosh (1 + A^2/(s₀⁻¹*(s₀⁻¹-A)))) (δ := δ₀) ?_ hhigh ?_
        · have hν : (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀
              ≠ Work.Kernels.imagAxis s₀ hs₀ := by
            intro hh
            apply hbase
            calc (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
                = ((ModularGroup.S * ModularGroup.S⁻¹) * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀ := by rw [mul_inv_cancel, one_mul]
              _ = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀) := by rw [mul_assoc, mul_smul]
              _ = ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀ := by rw [hh]
              _ = Work.Kernels.imagAxis s₀⁻¹ (inv_pos.mpr hs₀) := S_smul_imagAxis s₀ hs₀
          have hgap := hgapD (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) hν
          rw [dist_comm] at hgap
          have h5 : dist (ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀)
                ((γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀)
              = dist (Work.Kernels.imagAxis s₀ hs₀)
                ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)) • Work.Kernels.imagAxis s₀ hs₀) := by
            have hA : (γ⁻¹ * ModularGroup.T) • Work.Kernels.imagAxis s₀ hs₀
                = ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀) := by
              rw [show ModularGroup.S • ((ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    • Work.Kernels.imagAxis s₀ hs₀)
                  = (ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T)))
                    • Work.Kernels.imagAxis s₀ hs₀ from (mul_smul _ _ _).symm,
                show ModularGroup.S * (ModularGroup.S⁻¹ * (γ⁻¹ * ModularGroup.T))
                    = γ⁻¹ * ModularGroup.T by group]
            rw [hA, dist_smul_SL2Z]
          rw [← S_smul_imagAxis s₀ hs₀, h5]
          exact hgap
        · linarith [hεδ, hRmx2]

end Work.Asymptotics
