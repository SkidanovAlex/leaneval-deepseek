import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.P9.zetaFarZeroSqBound
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_re_one
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_re_two

namespace Work.ZeroFreeTables.P9

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

/-- `‖(1 / w) ^ 2‖ = 1 / ‖w‖ ^ 2` for `w : ℂ`. -/
private lemma norm_inv_sq' (w : ℂ) : ‖(1 / w) ^ 2‖ = 1 / ‖w‖ ^ 2 := by
  rw [norm_pow, norm_div, norm_one, div_pow, one_pow]

/-- If `0 < δ` and `δ / 2 ≤ r`, then `(1/r)³ ≤ (2/δ)(1+4/δ²)/(1+r²)`. -/
private lemma one_div_cube_le {δ r : ℝ} (hδ : 0 < δ) (hr : δ / 2 ≤ r) :
    (1 / r) ^ 3 ≤ (2 / δ) * ((1 + 4 / δ ^ 2) / (1 + r ^ 2)) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have h1 : 1 / r ≤ 2 / δ := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < δ / 2 by positivity) hr
    rwa [one_div_div] at h
  have h2 : 1 / r ^ 2 ≤ (1 + 4 / δ ^ 2) / (1 + r ^ 2) := by
    rw [div_le_div_iff₀ (pow_pos hrpos 2) (by positivity : (0 : ℝ) < 1 + r ^ 2)]
    have hkey : (1 : ℝ) ≤ (4 / δ ^ 2) * r ^ 2 := by
      have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
      have h2r : δ ≤ 2 * r := by linarith
      have h4 : δ ^ 2 ≤ 4 * r ^ 2 := by
        have h := pow_le_pow_left₀ (le_of_lt hδ) h2r 2
        nlinarith [h]
      rw [div_mul_eq_mul_div]
      calc (1 : ℝ) = δ ^ 2 / δ ^ 2 := (div_self (ne_of_gt hδ2)).symm
        _ ≤ 4 * r ^ 2 / δ ^ 2 := div_le_div_of_nonneg_right h4 (le_of_lt hδ2)
    have hexp : (1 + 4 / δ ^ 2) * r ^ 2 = (4 / δ ^ 2) * r ^ 2 + r ^ 2 := by ring
    linarith [hkey, hexp]
  have hcube : (1 / r) ^ 3 = (1 / r) * (1 / r ^ 2) := by
    rw [div_pow, one_pow, one_div_mul_one_div]
    congr 1
    ring
  rw [hcube]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Far-zero bound for the cube kernel.** -/
private lemma zetaFarZeroCubeBound_aux {a δ L Cz : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hLt : 1 < L) (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L)
    (hnz : ∀ u : ℂ, riemannZeta u = 0 → δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖)
    (hCz : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz) :
    (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re)
      ≥ -(2 / δ) * (1 + 4 / δ ^ 2) * Cz := by
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have haLpos : 0 < a / L := div_pos ha hLpos
  have hsc : 1 < s.re := by rw [hsre]; linarith
  have hfar : ∀ u : ℂ, analyticOrderNatAt completedRiemannZeta u ≠ 0 → δ / 2 ≤ ‖s - u‖ := by
    intro u hord
    have hζ : riemannZeta u = 0 := by
      have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hord
        exact hord
          (analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_zero)
      rw [riemannZeta_def_of_ne_zero hu0, apply_eq_zero_of_analyticOrderNatAt_ne_zero hord,
        zero_div]
    have hδu : δ < ‖((1 : ℂ) + (s.im : ℂ) * Complex.I) - u‖ := hnz u hζ
    have haLδ : a / L ≤ δ / 2 := by
      rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 2)]
      linarith [haδL]
    have hw0 : s - ((1 : ℂ) + (s.im : ℂ) * Complex.I) = ((a / L : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
          sub_zero, add_zero]
        linarith [hsre]
      · simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
          add_zero, zero_add, sub_self]
    have hsw0 : ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ = a / L := by
      rw [hw0, Complex.norm_of_nonneg (le_of_lt haLpos)]
    have htri : ‖((1 : ℂ) + (s.im : ℂ) * Complex.I) - u‖
        ≤ ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ + ‖s - u‖ := by
      have hsplit : ((1 : ℂ) + (s.im : ℂ) * Complex.I) - u
          = (s - u) - (s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)) := by ring
      rw [hsplit]
      calc ‖(s - u) - (s - ((1 : ℂ) + (s.im : ℂ) * Complex.I))‖
          ≤ ‖s - u‖ + ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ = ‖s - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ + ‖s - u‖ := add_comm _ _
    linarith [hδu, htri, hsw0, haLδ, hδ]
  have hsummSq : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2) :=
    zetaZeroSum_summable_gen 1 le_rfl hsc
  have hsummC : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 3) :=
    zetaZeroSum_summable_gen 2 (by norm_num) hsc
  have hfsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re) := by
    have h := Complex.reCLM.summable hsummC
    refine h.congr (fun u => ?_)
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
  have hksumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) hsummSq.norm
    · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
    · by_cases h0 : analyticOrderNatAt completedRiemannZeta u = 0
      · simp [h0]
      · have hr : δ / 2 ≤ ‖s - u‖ := hfar u h0
        have hrpos : 0 < ‖s - u‖ := lt_of_lt_of_le (by positivity) hr
        have hle1 : 1 / (1 + ‖s - u‖ ^ 2) ≤ 1 / ‖s - u‖ ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (pow_pos hrpos 2)]
          nlinarith [sq_nonneg ‖s - u‖]
        calc (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
            ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / ‖s - u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hle1 (Nat.cast_nonneg _)
          _ = ‖(analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2‖ := by
              rw [norm_mul, Complex.norm_natCast, norm_inv_sq']
  have hpt : ∀ u : ℂ, ((-(2 / δ)) * (1 + 4 / δ ^ 2)) *
      ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re := by
    intro u
    by_cases h0 : analyticOrderNatAt completedRiemannZeta u = 0
    · simp [h0]
    · have hr : δ / 2 ≤ ‖s - u‖ := hfar u h0
      have hrpos : 0 < ‖s - u‖ := lt_of_lt_of_le (by positivity) hr
      have h₁ : -(1 / ‖s - u‖) ^ 3 ≤ ((1 / (s - u)) ^ 3).re := by
        have h' := Complex.abs_re_le_norm ((1 / (s - u)) ^ 3)
        rw [abs_le] at h'
        have hn : ‖(1 / (s - u)) ^ 3‖ = (1 / ‖s - u‖) ^ 3 := by
          rw [norm_pow, norm_div, norm_one]
        linarith [h'.1, hn]
      have h₂ : -(((2 / δ) * (1 + 4 / δ ^ 2)) / (1 + ‖s - u‖ ^ 2))
          ≤ -(1 / ‖s - u‖) ^ 3 := by
        have hb := one_div_cube_le hδ hr (r := ‖s - u‖)
        rw [← mul_div_assoc] at hb
        linarith [hb]
      have hc : (0 : ℝ) ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) := Nat.cast_nonneg _
      have key : ((-(2 / δ)) * (1 + 4 / δ ^ 2)) *
            ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
          = (analyticOrderNatAt completedRiemannZeta u : ℝ) *
            (-(((2 / δ) * (1 + 4 / δ ^ 2)) / (1 + ‖s - u‖ ^ 2))) := by ring
      rw [key]
      exact le_trans (mul_le_mul_of_nonneg_left h₂ hc) (mul_le_mul_of_nonneg_left h₁ hc)
  have hgsumm : Summable (fun u : ℂ => ((-(2 / δ)) * (1 + 4 / δ ^ 2)) *
      ((analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))) :=
    Summable.mul_left _ hksumm
  have hkey : ((-(2 / δ)) * (1 + 4 / δ ^ 2)) *
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re := by
    have h := Summable.tsum_le_tsum hpt hgsumm hfsumm
    rwa [tsum_mul_left] at h
  have hneg : ((-(2 / δ)) * (1 + 4 / δ ^ 2)) ≤ 0 := by
    have : (0 : ℝ) < 2 / δ * (1 + 4 / δ ^ 2) := by positivity
    nlinarith [this]
  have hmain : ((-(2 / δ)) * (1 + 4 / δ ^ 2)) * Cz ≤
      ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re :=
    le_trans (mul_le_mul_of_nonpos_left hCz hneg) hkey
  have heq : -(2 / δ) * (1 + 4 / δ ^ 2) * Cz = ((-(2 / δ)) * (1 + 4 / δ ^ 2)) * Cz := by ring
  rw [heq]
  exact hmain

/-- The iterated derivatives of `logDeriv (L(·,χ))` for the trivial character of modulus `1`
agree with those of `logDeriv ζ`, since `L(1) = ζ` on `Re s > 1`. -/
private lemma iteratedDeriv_logDeriv_LFunction_one {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    iteratedDeriv j (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))) s
      = iteratedDeriv j (logDeriv riemannZeta) s := by
  have hsub : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hevL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [hsub] with z hz
    have hone : (fun x : ℕ => (1 : DirichletCharacter ℂ 1) (x : ZMod 1)) = (1 : ℕ → ℂ) := by
      funext x
      rw [show ((x : ZMod 1)) = (1 : ZMod 1) from Subsingleton.elim _ _]
      exact MulChar.map_one _
    rw [DirichletCharacter.LFunction_eq_LSeries _ hz, hone]
    exact LSeries_one_eq_riemannZeta (s := z) hz
  have hev : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
      =ᶠ[𝓝 s] logDeriv riemannZeta := logDeriv_congr_nhds hevL
  rw [hev.iteratedDeriv_eq]

/-- `SigmaP3L` at the trivial character of modulus `1` in terms of the derivatives of
`logDeriv ζ` (the specialisation to `χ = 1`, `N = 1` of `SigmaP3L_eq_logDeriv_derivs`). -/
private lemma SigmaP3L_one_eq_iteratedDeriv {a lam₁ L : ℝ} {s : ℂ} (hs : 1 < s.re) :
    SigmaP3L 1 L 1 s a lam₁
      = -((a + lam₁) / L) * (logDeriv riemannZeta s).re
        + ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 (logDeriv riemannZeta) s).re
        - (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 (logDeriv riemannZeta) s).re := by
  have h := SigmaP3L_eq_logDeriv_derivs (1 : DirichletCharacter ℂ 1) hs a lam₁ L
  rw [iteratedDeriv_logDeriv_LFunction_one hs 1, iteratedDeriv_logDeriv_LFunction_one hs 2] at h
  rw [show logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) s
        = logDeriv riemannZeta s from by
      simpa only [iteratedDeriv_zero] using iteratedDeriv_logDeriv_LFunction_one hs 0] at h
  exact h

theorem zetaEngine_principal {a lam₁ δ L Ct Cz C₀ : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L) (haδL : 2 * a ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L)
    (hnz : ∀ u : ℂ, riemannZeta u = 0 → δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖)
    (hC0 : (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀)
    (hCz : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct) :
    Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁
      ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + ((a + lam₁) / L) * C₀
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have haL : 0 < a / L := div_pos ha hLpos
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hA : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith) (le_of_lt hLpos)
  have hSigma := SigmaP3L_one_eq_iteratedDeriv (a := a) (lam₁ := lam₁) (L := L) hs1
  have hr1 := zetaDiffExplicit_re_one hs1
  have hr2 := zetaDiffExplicit_re_two hs1
  have hP3 : (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
      = ((a + lam₁) / L) * (1 / (s - 1)).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - 1)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - 1)) ^ 3).re := by
    rw [Work.ZeroFreeTables.P9.P3_re_div_eq a lam₁ L s 1]
  have hB1 : 0 ≤ (logDeriv riemannZeta s).re + (1 / (s - 1)).re + C₀ := by
    have h := hC0
    rw [Complex.neg_re] at h
    linarith
  have hZ1 : -(1 + 4 / δ ^ 2) * Cz ≤
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re) :=
    zetaFarZeroSqBound ha hδ hLt haδL hsre hnz hCz
  have hZ2 : -(2 / δ) * (1 + 4 / δ ^ 2) * Cz ≤
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re) :=
    zetaFarZeroCubeBound_aux ha hδ hLt haδL hsre hnz hCz
  have hT1 : -Ct ≤ (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2).re) :=
    (abs_le.mp hS2).1
  have hT2 : -Ct ≤ (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re) :=
    (abs_le.mp hS3).1
  have e2 : (a + lam₁) ^ 2 / L ^ 2 = ((a + lam₁) / L) ^ 2 := by ring
  have e3 : (a + lam₁) ^ 3 / L ^ 3 = ((a + lam₁) / L) ^ 3 := by ring
  rw [hSigma, hP3, hr1, hr2, e2, e3]
  have h1 : 0 ≤ ((a + lam₁) / L) *
      ((logDeriv riemannZeta s).re + (1 / (s - 1)).re + C₀) := mul_nonneg hA hB1
  have h2c : 0 ≤ (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re)
        + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2).re)
        + ((1 + 4 / δ ^ 2) * Cz + Ct) := by linarith [hZ1, hT1]
  have h2 : 0 ≤ ((a + lam₁) / L) ^ 2 *
      ((∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re)
        + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2).re)
        + ((1 + 4 / δ ^ 2) * Cz + Ct)) :=
    mul_nonneg (sq_nonneg ((a + lam₁) / L)) h2c
  have h3c : 0 ≤ (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re)
        + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re)
        + ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) := by linarith [hZ2, hT2]
  have h3b : (0:ℝ) ≤ ((a + lam₁) / L) ^ 3 := pow_nonneg hA 3
  have h3 : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 *
      ((∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 3).re)
        + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3).re)
        + ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct)) :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/3) h3b) h3c
  nlinarith [h1, h2, h3]

end Work.ZeroFreeTables.P9
