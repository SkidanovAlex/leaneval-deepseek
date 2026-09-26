import Mathlib

namespace Work.Asymptotics

open Complex Real

noncomputable section

/-- **The exact squared-norm identity.**  For real `x, ε`,
`‖e^{2π(ε - xi)} - 1‖² = (ρ - 1)² + 2ρ(1 - cos 2πx)` with `ρ = e^{2πε}`. -/
lemma expTwoPi_norm_sub_one_sq (x ε : ℝ) :
    ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖^2
      = (Real.exp (2 * Real.pi * ε) - 1)^2
        + 2 * Real.exp (2 * Real.pi * ε) * (1 - Real.cos (2 * Real.pi * x)) := by
  have hre : (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)).re = 2 * Real.pi * ε := by
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have him : (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)).im = -(2 * Real.pi * x) := by
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hWnorm : ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I))‖
      = Real.exp (2 * Real.pi * ε) := by rw [Complex.norm_exp, hre]
  have hWre : (Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I))).re
      = Real.exp (2 * Real.pi * ε) * Real.cos (2 * Real.pi * x) := by
    rw [Complex.exp_re, hre, him, Real.cos_neg]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  rw [show Complex.normSq (Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)))
        = Real.exp (2 * Real.pi * ε)^2 by rw [Complex.normSq_eq_norm_sq, hWnorm]]
  rw [Complex.normSq_one, map_one, mul_one, hWre]
  ring

/-- `1 - cos(2πu) ≥ 8u²` for `|u| ≤ 1/2`. -/
lemma one_sub_cos_twoPi_ge_eight (u : ℝ) (hu : |u| ≤ 1/2) :
    8 * u^2 ≤ 1 - Real.cos (2 * Real.pi * u) := by
  have hpiu : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [hu, Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hpiu
  have h2 : 2 / Real.pi * |Real.pi * u| = 2 * |u| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; field_simp
  have hsin' : 2 * |u| ≤ |Real.sin (Real.pi * u)| := by linarith [hsin, h2.le]
  have hsq : (2 * |u|)^2 ≤ Real.sin (Real.pi * u)^2 := by
    rw [← sq_abs (Real.sin (Real.pi * u))]
    exact pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * |u|) hsin' 2
  have hcos : Real.cos (2 * Real.pi * u) = 1 - 2 * Real.sin (Real.pi * u)^2 := by
    rw [show 2 * Real.pi * u = 2 * (Real.pi * u) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hcos]
  have hh : (2 * |u|)^2 = 4 * u^2 := by rw [mul_pow, sq_abs]; ring
  nlinarith [hsq, hh]

/-- For `0 ≤ s ≤ log 2`, `s/2 ≤ 1 - e^{-s}`. -/
lemma one_sub_exp_neg_ge_half (s : ℝ) (hs0 : 0 ≤ s) (hsle : s ≤ Real.log 2) :
    s / 2 ≤ 1 - Real.exp (-s) := by
  have hs : 0 < Real.exp s := Real.exp_pos s
  have h2 : Real.exp s ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]; exact Real.exp_le_exp.mpr hsle
  have hge : s ≤ Real.exp s - 1 := by have := Real.add_one_le_exp s; linarith
  have h1 : 1 - Real.exp (-s) = (Real.exp s - 1) / Real.exp s := by
    rw [Real.exp_neg, inv_eq_one_div]; field_simp
  rw [h1]
  have ha : s / 2 ≤ s / Real.exp s := div_le_div_of_nonneg_left hs0 hs h2
  have hb : s / Real.exp s ≤ (Real.exp s - 1) / Real.exp s :=
    div_le_div_of_nonneg_right hge hs.le
  linarith

/-- `|t|/2 ≤ |e^t - 1|` for `-log 2 ≤ t ≤ log 2`. -/
lemma abs_exp_sub_one_ge_half (t : ℝ) (ht0 : -Real.log 2 ≤ t) (_ht1 : t ≤ Real.log 2) :
    |t| / 2 ≤ |Real.exp t - 1| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h1 : 0 ≤ Real.exp t - 1 := by have := Real.one_le_exp ht; linarith
    rw [abs_of_nonneg h1]
    have h2 := Real.add_one_le_exp t
    linarith
  · have h2 : Real.exp t - 1 < 0 := by have := Real.exp_lt_one_iff.mpr ht; linarith
    rw [abs_of_neg ht, abs_of_neg h2]
    have := one_sub_exp_neg_ge_half (-t) (by linarith) (by linarith)
    rw [neg_neg] at this
    linarith [this]

/-- **The core estimate for a point at distance `≤ 1/2` from an integer.** -/
lemma expTwoPi_lattice_core (u ε : ℝ) (hu : |u| ≤ 1/2) :
    (1/4) * min 1 ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ * (1 + Real.exp (2 * Real.pi * ε))
      ≤ ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (u : ℂ) * Complex.I)) - 1‖ := by
  set ρ := Real.exp (2 * Real.pi * ε) with hρ
  set M := min 1 ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ with hM
  set W := Complex.exp (2 * Real.pi * ((ε : ℂ) - (u : ℂ) * Complex.I)) with hW
  have hre : (2 * Real.pi * ((ε : ℂ) - (u : ℂ) * Complex.I)).re = 2 * Real.pi * ε := by
    norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hWnorm : ‖W‖ = ρ := by rw [hW, Complex.norm_exp, hre, hρ]
  have hsq : ‖W - 1‖^2 = (ρ - 1)^2 + 2 * ρ * (1 - Real.cos (2 * Real.pi * u)) := by
    rw [hW, hρ]; exact expTwoPi_norm_sub_one_sq u ε
  have hMle1 : M ≤ 1 := by rw [hM]; exact min_le_left _ _
  have hMleW : M ≤ ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ := by rw [hM]; exact min_le_right _ _
  have hMnn : 0 ≤ M := by rw [hM]; exact le_min zero_le_one (norm_nonneg _)
  rcases le_or_gt ρ (1/2) with hle | hlt
  · have hW1 : 1 - ρ ≤ ‖W - 1‖ := by
      have h := norm_sub_norm_le (1 : ℂ) W
      rw [norm_one, hWnorm] at h
      rwa [norm_sub_rev] at h
    have h3 : (1/4) * M * (1 + ρ) ≤ 3/8 := by
      have hρ3 : 1 + ρ ≤ 3/2 := by linarith
      have h1 : (1/4) * M * (1 + ρ) ≤ (1/4) * M * (3/2) :=
        mul_le_mul_of_nonneg_left hρ3 (mul_nonneg (by norm_num) hMnn)
      nlinarith [h1, hMle1, hMnn]
    linarith
  · rcases le_or_gt 2 ρ with hge | hgt2
    · have hW1 : ρ - 1 ≤ ‖W - 1‖ := by
        have h := norm_sub_norm_le W (1 : ℂ)
        rw [norm_one, hWnorm] at h
        exact h
      have h3 : (1/4) * M * (1 + ρ) ≤ ρ - 1 := by
        have h1 : (1/4) * M * (1 + ρ) ≤ (1/4) * (1 + ρ) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 1 + ρ)
          nlinarith [hMle1, hMnn]
        nlinarith [h1, hge]
      linarith
    · have h2log : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
      have ht_le : 2 * Real.pi * ε ≤ Real.log 2 := by
        have h' : Real.exp (2 * Real.pi * ε) < Real.exp (Real.log 2) := by
          rw [h2log, ← hρ]; exact hgt2
        exact le_of_lt (Real.exp_lt_exp.mp h')
      have hhalf : Real.exp (-Real.log 2) = 1/2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      have ht_ge : -Real.log 2 ≤ 2 * Real.pi * ε := by
        have h' : Real.exp (-Real.log 2) < Real.exp (2 * Real.pi * ε) := by
          rw [hhalf, ← hρ]; exact hlt
        exact le_of_lt (Real.exp_lt_exp.mp h')
      have habs : |2 * Real.pi * ε| / 2 = Real.pi * |ε| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]; ring
      have hexp : Real.pi * |ε| ≤ |ρ - 1| := by
        have h := abs_exp_sub_one_ge_half (2 * Real.pi * ε) ht_ge ht_le
        rw [habs, ← hρ] at h
        exact h
      have hA : Real.pi^2 * ε^2 ≤ (ρ - 1)^2 := by
        have h1 : (Real.pi * |ε|)^2 ≤ (ρ - 1)^2 := by
          rw [← sq_abs (ρ - 1)]
          exact pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.pi * |ε|) hexp 2
        have h2 : (Real.pi * |ε|)^2 = Real.pi^2 * ε^2 := by rw [mul_pow, sq_abs]
        rwa [h2] at h1
      have hB : 8 * u^2 ≤ 2 * ρ * (1 - Real.cos (2 * Real.pi * u)) := by
        have hc := one_sub_cos_twoPi_ge_eight u hu
        have h2ρ : 1 ≤ 2 * ρ := by linarith
        have := mul_le_mul h2ρ hc (by positivity : (0:ℝ) ≤ 8 * u^2)
          (by positivity : (0:ℝ) ≤ 2 * ρ)
        linarith [this]
      have hnorm2 : ‖(u : ℂ) + (ε : ℂ) * Complex.I‖^2 = u^2 + ε^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        ring
      have hpi2 : (8:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
      have hA' : 8 * ε^2 ≤ (ρ - 1)^2 := by
        have := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg ε)
        linarith [hA, this]
      have h8 : 8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖^2 ≤ ‖W - 1‖^2 := by
        rw [hsq, hnorm2]
        linarith [hA', hB]
      have hsq8 : Real.sqrt 8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ ≤ ‖W - 1‖ := by
        have hn : 0 ≤ ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ := norm_nonneg _
        have h1 : Real.sqrt 8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖
            = Real.sqrt (8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖^2) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_sq hn]
        rw [h1]
        calc Real.sqrt (8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖^2)
            ≤ Real.sqrt (‖W - 1‖^2) := Real.sqrt_le_sqrt h8
          _ = ‖W - 1‖ := Real.sqrt_sq (norm_nonneg _)
      have hsqrt83 : (3/4 : ℝ) ≤ Real.sqrt 8 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      have hB2 : (3/4) * M ≤ ‖W - 1‖ := by
        have h1 : (3/4) * M ≤ (3/4) * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ :=
          mul_le_mul_of_nonneg_left hMleW (by norm_num)
        have h2 : (3/4) * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖
            ≤ Real.sqrt 8 * ‖(u : ℂ) + (ε : ℂ) * Complex.I‖ :=
          mul_le_mul_of_nonneg_right hsqrt83 (norm_nonneg _)
        linarith [h1, h2, hsq8]
      have h3 : (1/4) * M * (1 + ρ) ≤ (3/4) * M := by
        have hρ3 : 1 + ρ ≤ 3 := by linarith
        have h1 : (1/4) * M * (1 + ρ) ≤ (1/4) * M * 3 :=
          mul_le_mul_of_nonneg_left hρ3 (mul_nonneg (by norm_num) hMnn)
        nlinarith [h1]
      linarith [h3, hB2]

/-- **Quantitative non-vanishing of `e^{2πζ} - 1` near its zero set, with the correct scaling
in the exponential direction.**  For `|x| ≤ 1` and any `ε : ℝ`, writing `ζ = ε - x i`
(so that `e^{2πζ} = e^{2πε} e^{-2πi x}`, of modulus `e^{2πε}`) and
`ω = x + ε i = i ζ` (so that `‖ω - n‖ = ‖ζ + i n‖` for `n ∈ {-1,0,1}`),

  `c · min 1 (min ‖ω‖ (min ‖ω - 1‖ ‖ω + 1‖)) · (1 + e^{2πε}) ≤ ‖e^{2πζ} - 1‖`.

The exponential `e^{2πζ}` equals `1` exactly when `ζ ∈ iℤ`; for `|x| ≤ 1` the zeros `i n` with
`n ∈ {-1,0,1}` exhaust those of distance `≤ 1` from `ζ` (the nearest integer to `x` is one of
`-1,0,1`), so the three displayed points are the relevant ones.  The factor
`(1 + |e^{2πζ}|) = 1 + e^{2πε}` is the natural scale: for large positive `ε` the point
`e^{2πζ}` runs off to infinity and `‖e^{2πζ} - 1‖ ≍ |e^{2πζ}|`.  The proof is an elementary
case analysis on `ρ = e^{2πε}` (`ρ ≤ 1/2`, `1/2 ≤ ρ ≤ 2`, `ρ ≥ 2`) using
`‖e^{2πζ} - 1‖² = (ρ - 1)² + 2ρ(1 - cos 2πx)`, `|e^u - 1| ≥ 3|ε|` for `|2πε| ≤ log 2`, and
`1 - cos(2πx) = 2 sin²(πx) ≥ 8 dist(x,ℤ)²` for `dist(x,ℤ) ≤ 1/2` (the latter from
`Real.mul_abs_le_abs_sin`).  Numerically `c = 1/2` suffices (so `1/4` is certainly safe). -/
theorem ExpTwoPiLatticeLower :
    ∃ c : ℝ, 0 < c ∧ ∀ (x ε : ℝ), |x| ≤ 1 →
      c * (min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
        (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
          ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)))
        * (1 + Real.exp (2 * Real.pi * ε))
      ≤ ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖ := by
  refine ⟨1/4, by norm_num, ?_⟩
  intro x ε hx
  have hxle : x ≤ 1 := (abs_le.mp hx).2
  have hxge : -1 ≤ x := (abs_le.mp hx).1
  rcases le_or_gt (1/2 : ℝ) x with hxa | hxa
  · have hu : |x - 1| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
    have hcos : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x - 1)) := by
      have h := Real.cos_sub_two_pi (2 * Real.pi * x)
      rw [show 2 * Real.pi * x - 2 * Real.pi = 2 * Real.pi * (x - 1) by ring] at h
      exact h.symm
    have hRHS : ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖
        = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x - 1 : ℝ) : ℂ) * Complex.I)) - 1‖ := by
      have h1 := expTwoPi_norm_sub_one_sq x ε
      have h2 := expTwoPi_norm_sub_one_sq (x - 1) ε
      have h3 : ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖^2
          = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x - 1 : ℝ) : ℂ) * Complex.I)) - 1‖^2 := by
        rw [h1, h2, hcos]
      have h4 := congrArg Real.sqrt h3
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
    have hshift : ((x : ℂ) + (ε : ℂ) * Complex.I - 1)
        = ((x - 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I := by push_cast; ring
    have htriple : min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
        (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
          ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖))
        ≤ min 1 ‖((x - 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖ := by
      apply min_le_min_left
      calc min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
              (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖ ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)
          ≤ ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖ := le_trans (min_le_right _ _) (min_le_left _ _)
        _ = ‖((x - 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖ := by rw [hshift]
    calc (1/4) * (min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
            (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
              ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)))
          * (1 + Real.exp (2 * Real.pi * ε))
        ≤ (1/4) * min 1 ‖((x - 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖
            * (1 + Real.exp (2 * Real.pi * ε)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left htriple (by norm_num)
      _ ≤ ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x - 1 : ℝ) : ℂ) * Complex.I)) - 1‖ :=
          expTwoPi_lattice_core (x - 1) ε hu
      _ = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖ := hRHS.symm
  · rcases le_or_gt x (-1/2) with hxb | hxb
    · have hu : |x + 1| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
      have hcos : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x + 1)) := by
        have h := Real.cos_add_two_pi (2 * Real.pi * x)
        rw [show 2 * Real.pi * x + 2 * Real.pi = 2 * Real.pi * (x + 1) by ring] at h
        exact h.symm
      have hRHS : ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖
          = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x + 1 : ℝ) : ℂ) * Complex.I)) - 1‖ := by
        have h1 := expTwoPi_norm_sub_one_sq x ε
        have h2 := expTwoPi_norm_sub_one_sq (x + 1) ε
        have h3 : ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖^2
            = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x + 1 : ℝ) : ℂ) * Complex.I)) - 1‖^2 := by
          rw [h1, h2, hcos]
        have h4 := congrArg Real.sqrt h3
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
      have hshift : ((x : ℂ) + (ε : ℂ) * Complex.I + 1)
          = ((x + 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I := by push_cast; ring
      have htriple : min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
          (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
            ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖))
          ≤ min 1 ‖((x + 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖ := by
        apply min_le_min_left
        calc min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
                (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖ ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)
            ≤ ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖ :=
              le_trans (min_le_right _ _) (min_le_right _ _)
          _ = ‖((x + 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖ := by rw [hshift]
      calc (1/4) * (min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
              (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
                ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)))
            * (1 + Real.exp (2 * Real.pi * ε))
          ≤ (1/4) * min 1 ‖((x + 1 : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖
              * (1 + Real.exp (2 * Real.pi * ε)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left htriple (by norm_num)
        _ ≤ ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - ((x + 1 : ℝ) : ℂ) * Complex.I)) - 1‖ :=
            expTwoPi_lattice_core (x + 1) ε hu
        _ = ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖ := hRHS.symm
    · have hu : |x| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
      have htriple : min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
          (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
            ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖))
          ≤ min 1 ‖(x : ℂ) + (ε : ℂ) * Complex.I‖ :=
        min_le_min_left 1 (min_le_left _ _)
      calc (1/4) * (min 1 (min ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
              (min ‖(x : ℂ) + (ε : ℂ) * Complex.I - 1‖
                ‖(x : ℂ) + (ε : ℂ) * Complex.I + 1‖)))
            * (1 + Real.exp (2 * Real.pi * ε))
          ≤ (1/4) * min 1 ‖(x : ℂ) + (ε : ℂ) * Complex.I‖
              * (1 + Real.exp (2 * Real.pi * ε)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left htriple (by norm_num)
        _ ≤ ‖Complex.exp (2 * Real.pi * ((ε : ℂ) - (x : ℂ) * Complex.I)) - 1‖ :=
            expTwoPi_lattice_core x ε hu

end

end Work.Asymptotics
