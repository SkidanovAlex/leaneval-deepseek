import Mathlib
import Submission.Work.FIArea6Road.HeartZcAux
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.HeartAux
import Submission.Work.FIArea6Road.HeartZcVertLine
import Submission.Work.FIArea6Road.HeartZcHorizLeft
import Submission.Work.FIArea6Road.HeartZcHorizRight

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `HeartZcShiftedLine` — the contour shift in the *reverse* direction

The §16 heart needs the bound on the integral of `G(s) = mellin p (s) · Zc s` along the
**right-hand** vertical line `σr = 1 + 1/log N`, `|Im s| ≤ heightT Pa`, in terms of the
**shifted** line `σ₀ = 1 - δ` and the two horizontal segments.  Cauchy's theorem on the
rectangle `[σ₀, σr] × [-T, T]` (`HeartAux.norm_int_shift_le`, applied with the two vertical
lines interchanged) gives

`‖∫_{σr} G‖ ≤ ‖∫_{σ₀} G‖ + ‖∫_{σr}^{σ₀} G(· - iT)‖ + ‖∫_{σr}^{σ₀} G(· + iT)‖`,

and the three terms are bounded by

* `HeartZcVertLine` — the shifted line, `π · (10⁷ C_z d (4log N)⁶) · N^{σ₀} C^{δ}`;
* `HeartZcHorizLeft` / `HeartZcHorizRight` — the horizontal pieces, whose sum is twice
  `(10⁷ C_z d (4log N)⁶) · T⁻¹ · N(δ + e/log N)`.

The only place where the arithmetic of `Params` enters is `δ ≤ 1/log Pz < 1/2`
(`log Pz > 2`, from `100 ≤ log N` and the lower end `(loglog x)² ≤ log Pz` of (4.4)) and
`δ ≤ c_h/(2 d^ε (log T + 1))`, which put the shifted line inside the analyticity region
`1 - c_h/(2 d^ε log(|m|+|Im s|+3)) < re s` of `heartZcHyp`.
-/

/-- `10 ≤ heightT Pa`. -/
lemma hzc_heightT_ge (Pa : Work.FITop.Params) : 10 ≤ Work.FIArea6Hecke.heightT Pa := by
  rw [Work.FIArea6Hecke.heightT]
  have h := Real.exp_pos (Real.sqrt (Real.log Pa.N))
  linarith

/-- Strict form of `heart_log_arg_le`: `log (|m| + |t| + 3) < log (heightT Pa) + 1` on the
rectangle `|t| ≤ heightT Pa`. -/
lemma hzc_log_arg_lt (Pa : Work.FITop.Params) (m : ℤ) (t : ℝ)
    (hT : (1 : ℝ) ≤ Work.FIArea6Hecke.heightT Pa)
    (hm : |(m : ℝ)| + 3 ≤ Work.FIArea6Hecke.heightT Pa)
    (ht : |t| ≤ Work.FIArea6Hecke.heightT Pa) :
    Real.log (|(m : ℝ)| + |t| + 3) < Real.log (Work.FIArea6Hecke.heightT Pa) + 1 := by
  have hTpos : (0 : ℝ) < Work.FIArea6Hecke.heightT Pa := by linarith
  have hle : |(m : ℝ)| + |t| + 3 ≤ 2 * Work.FIArea6Hecke.heightT Pa := by
    linarith [abs_nonneg (m : ℝ), ht, hm]
  have hpos : (0 : ℝ) < |(m : ℝ)| + |t| + 3 := by positivity
  have hlog : Real.log (|(m : ℝ)| + |t| + 3)
      ≤ Real.log (2 * Work.FIArea6Hecke.heightT Pa) := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)] at hlog
  have hl2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  linarith

/-- `2 < log Pz` from `100 ≤ log N`: the upper end `N < x^{1/2}(log x)^{-B} ≤ x^{1/2}` of (4.6)
gives `log x > 2 log N ≥ 200`, so `(loglog x)² > 4 > 2`, and `(loglog x)² ≤ log Pz` by (4.4). -/
lemma hzc_logPz_gt_two (Pa : Work.FITop.Params) (hL100 : 100 ≤ Real.log Pa.N) :
    2 < Real.log (Pa.Pz : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlogx1 : 1 < Real.log (Pa.x : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    have h3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    linarith
  have hlogx_pos : 0 < Real.log (Pa.x : ℝ) := by linarith
  have hloglogxpos : 0 < Real.log (Real.log (Pa.x : ℝ)) := Real.log_pos hlogx1
  have hlogNlt : Real.log Pa.N < (1 / 2) * Real.log (Pa.x : ℝ)
      - Pa.B * Real.log (Real.log (Pa.x : ℝ)) := by
    have hlt := Real.log_lt_log (by linarith [Pa.hN1]) Pa.hNhi
    have hxr : 0 < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _
    have hlr : 0 < (Real.log (Pa.x : ℝ)) ^ (-Pa.B) := Real.rpow_pos_of_pos hlogx_pos (-Pa.B)
    rw [Real.log_mul (ne_of_gt hxr) (ne_of_gt hlr), Real.log_rpow hxpos,
      Real.log_rpow hlogx_pos] at hlt
    linarith [hlt]
  have hlogx200 : 200 < Real.log (Pa.x : ℝ) := by
    have h2 : (1 / 2) * Real.log (Pa.x : ℝ) - Pa.B * Real.log (Real.log (Pa.x : ℝ))
        ≤ (1 / 2) * Real.log (Pa.x : ℝ) := by
      have : 0 ≤ Pa.B * Real.log (Real.log (Pa.x : ℝ)) :=
        mul_nonneg (le_of_lt Pa.hB) (le_of_lt hloglogxpos)
      linarith
    linarith [hL100, hlogNlt, h2]
  have hloglog2 : 2 < Real.log (Real.log (Pa.x : ℝ)) := by
    have h1 : Real.log 200 < Real.log (Real.log (Pa.x : ℝ)) :=
      Real.log_lt_log (by norm_num) hlogx200
    have h2 : (2 : ℝ) < Real.log 200 := by
      have he : Real.exp 2 < 200 := by
        have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        rw [heq]; nlinarith [Real.exp_pos 1]
      have h := Real.log_lt_log (Real.exp_pos 2) he
      rwa [Real.log_exp] at h
    linarith
  have hsq : (2 : ℝ) < (Real.log (Real.log (Pa.x : ℝ))) ^ 2 := by
    nlinarith [hloglog2, sq_nonneg (Real.log (Real.log (Pa.x : ℝ)) - 2)]
  linarith [Pa.hPlo, hsq]

theorem HeartZcShiftedLine
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (ε c_h C_z : ℝ)
    (Zc : ℂ → ℂ) (p : ℝ → ℝ) (δ : ℝ)
    (hzc : Work.FIArea6Road.heartZcHyp Pa chi m d ε c_h C_z Zc)
    (hc_h : 0 < c_h)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))
    (hδ : δ = Work.FIArea6Hecke.deltaC Pa d ε c_h)
    (hmT : |(m : ℝ)| + 3 ≤ Work.FIArea6Hecke.heightT Pa)
    (hL100 : 100 ≤ Real.log Pa.N) :
    ‖∫ y in (-(Work.FIArea6Hecke.heightT Pa))..(Work.FIArea6Hecke.heightT Pa),
        mellin (fun u : ℝ => (p u : ℂ)) (((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          * Zc (((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ Real.pi * (10 ^ 7 * (C_z * (d : ℝ)) * (4 * Real.log Pa.N) ^ (6 : ℕ))
            * (Pa.N ^ (1 - δ) * Pa.C ^ δ)
        + 2 * ((10 ^ 7 * (C_z * (d : ℝ)) * (4 * Real.log Pa.N) ^ (6 : ℕ))
            * (1 / Work.FIArea6Hecke.heightT Pa)
            * (Pa.N * (δ + Real.exp 1 / Real.log Pa.N))) := by
  obtain ⟨hCzpos, hZeq, hZan, hZbd1, hZbd2⟩ := hzc
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hLpos0 : 0 < Real.log Pa.N := by linarith
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := heart_theta_le_one Pa
  have hCpos : (0 : ℝ) < Pa.C := by linarith [Pa.hC1]
  have hT10 : 10 ≤ Work.FIArea6Hecke.heightT Pa := hzc_heightT_ge Pa
  have hT1 : (1 : ℝ) ≤ Work.FIArea6Hecke.heightT Pa := by linarith
  have hlogPz2 : 2 < Real.log (Pa.Pz : ℝ) := hzc_logPz_gt_two Pa hL100
  by_cases hd0 : (d : ℝ) = 0
  · -- the degenerate case `d = 0`: clause 4 of `heartZcHyp` forces `Zc ≡ 0` on the line
    have hZc0 : ∀ y : ℝ,
        Zc (((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 := by
      intro y
      set s : ℂ := ((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I with hsdef
      have hsre : s.re = 1 + 1 / Real.log Pa.N := by rw [hsdef]; simp
      have h1 : 1 < s.re := by
        rw [hsre]; have := one_div_pos.mpr hLpos0; linarith
      have h2 : s.re ≤ 1 + 1 / Real.log Pa.N := le_of_eq hsre
      have h3 : s.re ≤ 2 := by
        rw [hsre]
        have h : 1 / Real.log Pa.N ≤ 1 := by rw [div_le_one hLpos0]; linarith
        linarith
      have h4 := hZbd2 s h1 h2 h3
      have h4' : ‖Zc s‖ ≤ 0 := by simpa [hd0] using h4
      exact norm_eq_zero.mp (le_antisymm h4' (norm_nonneg _))
    have hfun : (fun y : ℝ => mellin (fun u : ℝ => (p u : ℂ))
          (((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          * Zc (((1 + 1 / Real.log Pa.N : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = fun _ => 0 := by
      funext y; rw [hZc0 y, mul_zero]
    rw [hfun, intervalIntegral.integral_zero, norm_zero]
    simp [hd0]
  · have hdpos : 0 < (d : ℝ) := by
      have hdn : d ≠ 0 := by intro h; exact hd0 (by simp [h])
      exact_mod_cast (Nat.pos_of_ne_zero hdn)
    have hDpos : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdpos ε
    set L : ℝ := Real.log Pa.N with hLdef
    set T : ℝ := Work.FIArea6Hecke.heightT Pa with hTdef
    set σr : ℝ := 1 + 1 / L with hσrdef
    set σ₀ : ℝ := 1 - δ with hσ₀def
    set KZ : ℝ := 10 ^ 7 * (C_z * (d : ℝ)) * (4 * L) ^ (6 : ℕ) with hKZdef
    set G : ℂ → ℂ := fun s => mellin (fun u : ℝ => (p u : ℂ)) s * Zc s with hGdef
    have hLpos : 0 < L := by rw [hLdef]; linarith
    have hL100' : 100 ≤ L := by rw [hLdef]; exact hL100
    have hTpos : 0 < T := by rw [hTdef]; linarith
    -- ## the arithmetic of `δ = min(…)`
    have hδeq : δ = min (c_h / (2 * (d : ℝ) ^ ε * (Real.log T + 1)))
        (1 / Real.log (Pa.Pz : ℝ)) := by
      rw [hδ, hTdef]; rfl
    have hδlePz : δ ≤ 1 / Real.log (Pa.Pz : ℝ) := by rw [hδeq]; exact min_le_right _ _
    have hδlecap : δ ≤ c_h / (2 * (d : ℝ) ^ ε * (Real.log T + 1)) := by
      rw [hδeq]; exact min_le_left _ _
    have hδnonneg : 0 ≤ δ := by
      rw [hδeq]
      refine le_min ?_ (div_nonneg zero_le_one (le_of_lt (by linarith)))
      exact div_nonneg hc_h.le
        (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) ε))
          (by have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith))
    have hδlt : δ < 1 / 2 := by
      have h1 : 1 / Real.log (Pa.Pz : ℝ) < 1 / 2 :=
        one_div_lt_one_div_of_lt (by norm_num) hlogPz2
      linarith [hδlePz, h1]
    have hσ₀half : 1 / 2 < σ₀ := by rw [hσ₀def]; linarith
    have hσ₀le1 : σ₀ ≤ 1 := by rw [hσ₀def]; linarith
    have hσ₀gePz : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ σ₀ := by rw [hσ₀def]; linarith
    have hσ₀σr : σ₀ ≤ σr := by
      rw [hσ₀def, hσrdef]; have := one_div_pos.mpr hLpos; linarith
    have hσr1 : 1 < σr := by
      rw [hσrdef]; have := one_div_pos.mpr hLpos; linarith
    have hσr2 : σr ≤ 2 := by
      rw [hσrdef]
      have h : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
      linarith
    -- ## the region condition, hence the continuation bound on the rectangle
    have hhorn : ∀ y : ℝ, |y| ≤ T →
        1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |y| + 3)) < σ₀ := by
      intro y hy
      have hloglt : Real.log (|(m : ℝ)| + |y| + 3) < Real.log T + 1 := by
        rw [hTdef]
        exact hzc_log_arg_lt Pa m y hT1 hmT hy
      have hargpos : 0 < Real.log (|(m : ℝ)| + |y| + 3) := Real.log_pos (by
        have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg y; linarith)
      have hlt : c_h / (2 * (d : ℝ) ^ ε * (Real.log T + 1))
          < c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |y| + 3)) := by
        refine div_lt_div_of_pos_left hc_h ?_ ?_
        · exact mul_pos (mul_pos (by norm_num) hDpos) hargpos
        · exact mul_lt_mul_of_pos_left hloglt (mul_pos (by norm_num) hDpos)
      rw [hσ₀def]
      linarith [hδlecap, hlt]
    -- ## the logarithmic factor is `≤ 4 log N`
    have hlogV : ∀ y : ℝ, |y| ≤ T →
        (Real.log Pa.N + Real.log (|(m : ℝ)| + |y| + 3) + 2) ^ (6 : ℕ) ≤ (4 * L) ^ (6 : ℕ) := by
      intro y hy
      have hTle15 : T ≤ 15 * Real.exp (Real.sqrt L) := by
        rw [hTdef, hLdef, Work.FIArea6Hecke.heightT]
        have hone : (1 : ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) :=
          Real.one_le_exp (Real.sqrt_nonneg _)
        linarith
      have hlog15 : Real.log 15 ≤ 14 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 15); linarith
      have hlogT_le : Real.log T + 1 ≤ 15 + Real.sqrt L := by
        have hlog : Real.log T ≤ Real.log (15 * Real.exp (Real.sqrt L)) :=
          Real.log_le_log hTpos hTle15
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
        linarith
      have hsqrt_le : Real.sqrt L ≤ L := by
        have h1 : Real.sqrt L * Real.sqrt L = L := by simpa [pow_two] using Real.sq_sqrt hLpos.le
        have h2 : (1 : ℝ) ≤ Real.sqrt L := by
          have h := Real.sqrt_le_sqrt (by linarith [hL100'] : (1 : ℝ) ≤ L)
          rwa [Real.sqrt_one] at h
        calc Real.sqrt L = Real.sqrt L * 1 := (mul_one _).symm
          _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg L)
          _ = L := h1
      have hlog_arg : Real.log (|(m : ℝ)| + |y| + 3) ≤ Real.log T + 1 := by
        rw [hTdef]; exact heart_log_arg_le Pa m y hmT hy hT1
      apply pow_le_pow_left₀ ?_ ?_ 6
      · have h1 : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
        have h2 : 0 ≤ Real.log (|(m : ℝ)| + |y| + 3) := Real.log_nonneg (by
          have ha := abs_nonneg (m : ℝ); have hb := abs_nonneg y; linarith)
        linarith
      · rw [show Real.log Pa.N = L from hLdef.symm]
        linarith [hlog_arg, hlogT_le, hsqrt_le, hL100']
    -- ## the continuation bound on the shifted line
    have hZc₀ : ∀ y : ℝ, |y| ≤ T →
        ‖Zc ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * L) ^ (6 : ℕ) := by
      intro y hy
      set s : ℂ := (σ₀ : ℂ) + (y : ℂ) * Complex.I with hsdef
      have hsre : s.re = σ₀ := by rw [hsdef]; simp
      have hsim : s.im = y := by rw [hsdef]; simp
      have h1 : 1 / 2 < s.re := by rw [hsre]; exact hσ₀half
      have h2 : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re := by rw [hsre]; exact hσ₀gePz
      have h3 : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re := by
        rw [hsre, hsim]; exact hhorn y hy
      have h4 : s.re ≤ 1 := by rw [hsre]; exact hσ₀le1
      have h5 := hZbd1 s h1 h2 h3 h4
      rw [hsre, hsim] at h5
      refine h5.trans (mul_le_mul_of_nonneg_left (hlogV y hy) ?_)
      exact mul_nonneg (mul_nonneg hCzpos.le (Nat.cast_nonneg d)) (Real.rpow_nonneg hCpos.le _)
    -- ## differentiability of `G` on the rectangle
    have hGbox : DifferentiableOn ℂ G (Set.uIcc σ₀ σr ×ℂ Set.uIcc (-T) T) := by
      have hmellin : DifferentiableOn ℂ (mellin (fun u : ℝ => (p u : ℂ)))
          (Set.uIcc σ₀ σr ×ℂ Set.uIcc (-T) T) := by
        intro s hs
        have hsre := (Complex.mem_reProdIm.mp hs).1
        rw [Set.uIcc_of_le hσ₀σr, Set.mem_Icc] at hsre
        exact (hzc_mellin_diffAt p Pa.N Pa.θ hNpos hθ0 hθ1 hpC hp0 hp1 hpsupp s
          (by linarith [hsre.1, hσ₀half])).differentiableWithinAt
      have hZcd : DifferentiableOn ℂ Zc (Set.uIcc σ₀ σr ×ℂ Set.uIcc (-T) T) := by
        refine hZan.differentiableOn.mono ?_
        intro s hs
        obtain ⟨hsre, hsim⟩ := Complex.mem_reProdIm.mp hs
        rw [Set.uIcc_of_le hσ₀σr, Set.mem_Icc] at hsre
        rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] at hsim
        have hsim' : |s.im| ≤ T := by rw [abs_le]; exact ⟨hsim.1, hsim.2⟩
        exact ⟨by linarith [hsre.1, hσ₀half], lt_of_lt_of_le (hhorn s.im hsim') hsre.1⟩
      exact hmellin.mul hZcd
    -- ## the shifted-line estimate `HeartZcVertLine`
    have hVert : ‖∫ y in (-T)..T, G ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.pi * KZ * (Pa.N ^ σ₀ * Pa.C ^ δ) := by
      have hKnn : (0 : ℝ) ≤ C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * L) ^ (6 : ℕ) :=
        mul_nonneg (mul_nonneg (mul_nonneg hCzpos.le (Nat.cast_nonneg d))
          (Real.rpow_nonneg hCpos.le _)) (by positivity)
      have hD := HeartZcVertLine Pa p Zc σ₀ (C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * L) ^ (6 : ℕ))
        hpC hp0 hp1 hpsupp hpd (le_of_lt hσ₀half) (by linarith [hσ₀σr, hσr2]) hKnn hZc₀
      have hKZeq : Real.pi * (10 ^ 7 * (C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * L) ^ (6 : ℕ)))
            * Pa.N ^ σ₀
          = Real.pi * KZ * (Pa.N ^ σ₀ * Pa.C ^ δ) := by
        have hCeq : Pa.C ^ (1 - σ₀) = Pa.C ^ δ := by rw [hσ₀def]; congr 1; ring
        rw [hKZdef, hCeq]; ring
      calc ‖∫ y in (-T)..T, G ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ Real.pi * (10 ^ 7 * (C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * L) ^ (6 : ℕ)))
              * Pa.N ^ σ₀ := hD
        _ = Real.pi * KZ * (Pa.N ^ σ₀ * Pa.C ^ δ) := hKZeq
    -- ## the horizontal estimates
    have hsub1 : Set.uIcc σ₀ 1 ⊆ Set.uIcc σ₀ σr := by
      intro x hx
      rw [Set.uIcc_of_le hσ₀le1, Set.mem_Icc] at hx
      rw [Set.uIcc_of_le hσ₀σr, Set.mem_Icc]
      exact ⟨hx.1, le_trans hx.2 (le_of_lt hσr1)⟩
    have hsub2 : Set.uIcc (1 : ℝ) (1 + 1 / L) ⊆ Set.uIcc σ₀ σr := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith [one_div_pos.mpr hLpos] : (1 : ℝ) ≤ 1 + 1 / L),
        Set.mem_Icc] at hx
      rw [Set.uIcc_of_le hσ₀σr, Set.mem_Icc]
      exact ⟨le_trans hσ₀le1 hx.1, by rw [hσrdef]; exact hx.2⟩
    have horiz : ∀ y : ℝ, |y| = T →
        ‖∫ x in σr..σ₀, G ((x : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L)) := by
      intro y hy
      have hyT : |y| ≤ T := le_of_eq hy
      -- the two pointwise continuation bounds
      have hleft : ∀ x : ℝ, σ₀ ≤ x → x ≤ 1 →
          ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ C_z * (d : ℝ) * Pa.C ^ (1 - x) * (4 * L) ^ (6 : ℕ) := by
        intro x hx0 hx1
        set s : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hsdef
        have hsre : s.re = x := by rw [hsdef]; simp
        have hsim : s.im = y := by rw [hsdef]; simp
        have h1 : 1 / 2 < s.re := by rw [hsre]; exact lt_of_lt_of_le hσ₀half hx0
        have h2 : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re := by rw [hsre]; exact le_trans hσ₀gePz hx0
        have h3 : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re := by
          rw [hsre, hsim]; exact lt_of_lt_of_le (hhorn y hyT) hx0
        have h4 : s.re ≤ 1 := by rw [hsre]; exact hx1
        have h5 := hZbd1 s h1 h2 h3 h4
        rw [hsre, hsim] at h5
        refine h5.trans (mul_le_mul_of_nonneg_left (hlogV y hyT) ?_)
        exact mul_nonneg (mul_nonneg hCzpos.le (Nat.cast_nonneg d)) (Real.rpow_nonneg hCpos.le _)
      have hright : ∀ x : ℝ, 1 ≤ x → x ≤ 1 + 1 / L →
          ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C_z * (d : ℝ) * (4 * L) ^ (6 : ℕ) := by
        intro x hx1 hx2
        rcases eq_or_lt_of_le hx1 with hx | hx
        · -- `x = 1`: clause 3 still applies (the region contains `re s = 1`)
          subst hx
          set s : ℂ := ((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I with hsdef
          have hsre : s.re = (1 : ℝ) := by rw [hsdef]; simp
          have hsim : s.im = y := by rw [hsdef]; simp
          have hargpos : 0 < Real.log (|(m : ℝ)| + |y| + 3) := Real.log_pos (by
            have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg y; linarith)
          have h1 : 1 / 2 < s.re := by rw [hsre]; norm_num
          have h2 : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re := by
            rw [hsre]
            have hpz : 0 < Real.log (Pa.Pz : ℝ) := by linarith [hlogPz2]
            have hnn : 0 ≤ 1 / Real.log (Pa.Pz : ℝ) := div_nonneg zero_le_one hpz.le
            linarith
          have h3 : 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re := by
            rw [hsre, hsim]
            have hpos : 0 < c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |y| + 3)) :=
              div_pos hc_h (mul_pos (mul_pos (by norm_num) hDpos) hargpos)
            linarith
          have h4 : s.re ≤ 1 := le_of_eq hsre
          have h5 := hZbd1 s h1 h2 h3 h4
          rw [hsre, hsim, show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one] at h5
          refine h5.trans (mul_le_mul_of_nonneg_left (hlogV y hyT) ?_)
          exact mul_nonneg hCzpos.le (Nat.cast_nonneg d)
        · -- `1 < x ≤ 1 + 1/log N`: clause 4 applies
          set s : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hsdef
          have hsre : s.re = x := by rw [hsdef]; simp
          have hsim : s.im = y := by rw [hsdef]; simp
          have h3 : x ≤ 2 := by
            have h2 : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
            linarith
          have h5 := hZbd2 s (by rw [hsre]; exact hx) (by rw [hsre]; exact hx2) (by rw [hsre]; exact h3)
          rw [hsim] at h5
          refine h5.trans (mul_le_mul_of_nonneg_left (hlogV y hyT) ?_)
          exact mul_nonneg hCzpos.le (Nat.cast_nonneg d)
      -- interval integrability of the horizontal path
      have hphi_cont : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
      have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
          (Set.uIcc σ₀ σr) (Set.uIcc σ₀ σr ×ℂ Set.uIcc (-T) T) := by
        intro x hx
        have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
        have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
        rw [Complex.mem_reProdIm, hre, him]
        exact ⟨hx, by
          rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc]
          exact abs_le.mp hyT⟩
      have hpath : ContinuousOn (fun x : ℝ => G ((x : ℂ) + (y : ℂ) * Complex.I))
          (Set.uIcc σ₀ σr) :=
        hGbox.continuousOn.comp hphi_cont.continuousOn hmaps
      have hint1 : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + (y : ℂ) * Complex.I)) volume σ₀ 1 :=
        (hpath.mono hsub1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + (y : ℂ) * Complex.I)) volume 1 σr :=
        (hpath.mono hsub2).intervalIntegrable
      have hLf := HeartZcHorizLeft Pa p Zc σ₀ d C_z y hpC hp0 hp1 hpsupp hpd hy
        (le_of_lt hσ₀half) hσ₀le1 hleft
      have hRf := HeartZcHorizRight Pa p Zc d C_z y hpC hp0 hp1 hpsupp hpd hy hL100 hright
      rw [intervalIntegral.integral_symm, norm_neg]
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add hLf hRf).trans ?_
      refine le_of_eq ?_
      rw [hKZdef, hTdef, hLdef, hσ₀def]
      ring
    -- ## Cauchy on the rectangle, with `σ₀` and `σr` interchanged
    have hcauchy := norm_int_shift_le (G := G) (σ₀ := σr) (σ := σ₀) (T := T)
      (by rw [Set.uIcc_comm]; exact hGbox)
    have hfinal : ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.pi * KZ * (Pa.N ^ σ₀ * Pa.C ^ δ)
          + 2 * (KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L))) := by
      have h := hcauchy
      have hyT_neg : |(-T)| = T := by rw [abs_neg, abs_of_pos hTpos]
      have hyT_pos : |T| = T := abs_of_pos hTpos
      have h2 := horiz (-T) hyT_neg
      have h3 := horiz T hyT_pos
      linarith [h, hVert, h2, h3]
    change ‖∫ y in (-T)..T, G ((σr : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.pi * KZ * (Pa.N ^ (1 - δ) * Pa.C ^ δ)
          + 2 * (KZ * (1 / T) * (Pa.N * (δ + Real.exp 1 / L)))
    exact hfinal

end

end Work.FIArea6Road
