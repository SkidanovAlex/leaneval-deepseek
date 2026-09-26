/-
# The `r`-seminorm bound for the `low` piece of the CKMRV layer on the cusp-`±1` tiles

See `Submission/Work/Asymptotics/Tile/tileLayerAux.lean` for the auxiliary estimates.

`layerLow ℓ d σ x = sinSq x · ∫_0^1 K(σ, it) e^{-πx²t} dt`.  Write `y = Im w ≤ 1/2` and split
`(0,1] = (0, y/2] ∪ [y/2, 1]`: on `(0, y/2]` the kernel is flat at the cusp `0`
(`Kaxis_tile_flat_below_pole`); on `[y/2, 1]` it equals the translate pole
`(n/2π)/(it-w)` up to `C (scale w)^N` (`TilePPWindow`), and the pole against the derivative of
the Gaussian is handled by the signed pole integral (`ppLayerDeriv_bound`).
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.Kaxis_tile_flat_below_pole
import Submission.Work.Asymptotics.tile_pole_integral_decay
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.Tile.tileIntervalDeriv
import Submission.Work.Asymptotics.Tile.tileLayerAux

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics.Tile

/-- `‖(t i - w)‖⁻¹ ≤ |Re w|⁻¹` for `Re w ≠ 0`. -/
lemma inv_norm_le_inv_abs_re {t : ℝ} {w : ℂ} (hre : w.re ≠ 0) :
    ‖(t:ℂ)*Complex.I - w‖⁻¹ ≤ |w.re|⁻¹ := by
  have h := Complex.abs_re_le_norm ((t:ℂ)*Complex.I - w)
  have h2 : ((t:ℂ)*Complex.I - w).re = -w.re := by simp [Complex.sub_re, Complex.mul_re]
  rw [h2, abs_neg] at h
  have h1 : (0:ℝ) < |w.re| := abs_pos.mpr hre
  exact (inv_le_inv₀ (lt_of_lt_of_le h1 h) h1).mpr h

theorem layerLow_tile_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hpp : Work.Asymptotics.TilePPWindow ℓ d) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ n : ℤ,
        (n = 1 ∨ n = -1) → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layerLow ℓ d ((n : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨Cpp, Npp, hCpp, hNpp, hpp'⟩ := hpp
  intro k l
  obtain ⟨c0, N0, hc0, hN0, hflat⟩ := Kaxis_tile_flat_below_pole ℓ d hd (k+l+1) (by positivity)
  obtain ⟨Γ, hΓ0, hΓ⟩ := sinSq_gauss_seminorm k l
  obtain ⟨Cppl, Nppl, hCppl0, hNppl0, hPPl⟩ := ppLayerDeriv_bound k l
  obtain ⟨Cdec, hCdec0, hdecb⟩ := layerDeriv_gauss_bound l
  refine ⟨c0*Γ + Cpp*Γ*(2:ℝ)^(k+l) + Cppl,
    max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl, by positivity, by positivity, ?_⟩
  intro w hw hre n hn r
  set K : UpperHalfPlane → UpperHalfPlane → ℂ := Kfun ℓ d with hK
  have hopR : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hsinAt : ∀ (m : ℕ) (x : ℝ),
      ContDiffAt ℝ (↑m : ℕ∞) (fun x' : ℝ => Work.Asymptotics.sinSq x') x := by
    intro m x
    rw [show (fun x' : ℝ => Work.Asymptotics.sinSq x') = fun x' : ℝ => 2
        - Complex.exp (-((-Complex.I * Real.pi) * (x' : ℂ) ^ 2))
        - Complex.exp (-((Complex.I * Real.pi) * (x' : ℂ) ^ 2)) by
      funext x'; exact Work.Asymptotics.sinSq_eq_complex x']
    exact ((contDiffAt_const.sub (contDiffAt_gaussExp m (-Complex.I * Real.pi) x)).sub
      (contDiffAt_gaussExp m (Complex.I * Real.pi) x))
  -- the flatness bound with a *natural* exponent
  have hflatN : ∀ (w' : UpperHalfPlane) (n' : ℤ), (n' = 1 ∨ n' = -1) → w' ∈ KEpsilon →
      ∀ t : ℝ, 0 < t → t ≤ w'.im/2 →
      ‖Kaxis K ((n':ℝ) +ᵥ w') t‖ ≤ c0 * (scale w')^N0 * t^(k+l+1) := by
    intro w' n' hn' hw' t ht0 ht1
    have h := hflat w' n' hn' hw' t ht0
      (by rw [min_eq_right (by linarith [tile_im_le_half hw'])]; exact ht1)
    rw [show (↑k + ↑l + 1 : ℝ) = ((k+l+1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
    exact h
  have hy : 0 < w.im := w.im_pos
  have hyhalf : w.im ≤ 1/2 := tile_im_le_half hw
  have hy2 : w.im/2 ≤ 1 := by linarith
  have hmm : min 1 (w.im/2) = w.im/2 := min_eq_right hy2
  have hsc1 : (1:ℝ) ≤ scale w := one_le_scale w
  set σ : UpperHalfPlane := (n:ℝ) +ᵥ w with hσ
  -- a bound for the kernel on the whole window `(0,1]`
  have hKbd : ∃ Kbd : ℝ, 0 ≤ Kbd ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ‖Kaxis K σ t‖ ≤ Kbd := by
    refine ⟨max (c0 * (scale w)^N0)
      (Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|)), ?_, ?_⟩
    · exact le_max_of_le_left (by positivity)
    · intro t ht0 ht1
      rcases le_or_gt t (w.im/2) with hc | hc
      · have h := hflatN w n hn hw t ht0 hc
        rw [← hσ] at h
        refine le_trans h ?_
        have h1 : (scale w)^N0 * t^(k+l+1) ≤ (scale w)^N0 :=
          mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt (scale_pos w)) _)
            (pow_le_one₀ ht0.le ht1)
        calc c0 * (scale w)^N0 * t^(k+l+1) = c0 * ((scale w)^N0 * t^(k+l+1)) := by ring
          _ ≤ c0 * (scale w)^N0 := mul_le_mul_of_nonneg_left h1 hc0
          _ ≤ max (c0 * (scale w)^N0) (Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|)) :=
              le_max_left _ _
      · have h := hpp' w hw n hn t (le_of_lt hc) ht1
        rw [← hσ] at h
        have hPP : ‖((n:ℂ)/(2*(Real.pi:ℂ)))*((((t:ℂ)*Complex.I - (w:ℂ)))⁻¹)‖
            ≤ (1/(2*Real.pi)) * (1/|w.re|) := by
          have hn1 : ‖(n:ℂ)‖ ≤ 1 := by rcases hn with h | h <;> rw [h] <;> simp
          have hden : |w.re| ≤ ‖(t:ℂ)*Complex.I - (w:ℂ)‖ := by
            have h := Complex.abs_re_le_norm ((t:ℂ)*Complex.I - (w:ℂ))
            have h2 : ((t:ℂ)*Complex.I - (w:ℂ)).re = -w.re := by
              simp [Complex.sub_re, Complex.mul_re]
            rw [h2, abs_neg] at h
            exact h
          have h2pinv : ‖((2*(Real.pi:ℂ)))‖ = 2*Real.pi := by
            rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
              norm_ofReal_complex, abs_of_nonneg (by positivity)]
          rw [norm_mul, norm_div, norm_inv, h2pinv, div_eq_mul_inv]
          calc ‖(n:ℂ)‖ * (2*Real.pi)⁻¹ * ‖(t:ℂ)*Complex.I - (w:ℂ)‖⁻¹
              ≤ 1 * (2*Real.pi)⁻¹ * (|w.re|)⁻¹ := by
                refine mul_le_mul (mul_le_mul hn1 le_rfl (by positivity) (by norm_num)) ?_
                  (by positivity) (by positivity)
                exact inv_norm_le_inv_abs_re (w := (w:ℂ)) hre
            _ = (1/(2*Real.pi)) * (1/|w.re|) := by rw [inv_eq_one_div, inv_eq_one_div]; ring
        have htri : ‖Kaxis K ((n:ℝ)+ᵥw) t‖
            ≤ Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|) := by
          have heq : Kaxis K ((n:ℝ)+ᵥw) t
              = (Kaxis K ((n:ℝ)+ᵥw) t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹))
                + ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) := by ring
          rw [heq]
          exact le_trans (norm_add_le _ _) (add_le_add h hPP)
        exact le_trans htri (le_max_right _ _)
  obtain ⟨Kbd, hKbd0, hKbdle⟩ := hKbd
  -- the layer as an integral of `kfun`
  set kfun : ℝ → ℝ → ℂ := fun x t =>
    Kaxis K σ t * (Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x) with hkfun
  have hmeas : ∀ x : ℝ, Measurable (fun t : ℝ => kfun x t) := by
    intro x
    have h1 : (fun t : ℝ => kfun x t) = fun t : ℝ => (Kaxis K σ t *
        Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) * Work.Asymptotics.sinSq x := by
      funext t; rw [hkfun]; ring
    rw [h1]
    exact (((measurable_Kaxis_of_measurable K σ (measurable_Kfun_snd_all ℓ d hd σ)).mul
      (by fun_prop))).mul_const _
  have hsinSmooth : ContDiff ℝ ∞ (fun x : ℝ => Work.Asymptotics.sinSq x) := by
    rw [show (fun x : ℝ => Work.Asymptotics.sinSq x) = fun x : ℝ => 2
        - Complex.exp (-((-Complex.I * Real.pi) * (x : ℂ) ^ 2))
        - Complex.exp (-((Complex.I * Real.pi) * (x : ℂ) ^ 2)) by
      funext x; exact Work.Asymptotics.sinSq_eq_complex x]
    fun_prop
  have hsmooth : ∀ t : ℝ, ContDiff ℝ ∞ (fun x : ℝ => kfun x t) := by
    intro t
    have h1 : (fun x : ℝ => kfun x t) = fun x : ℝ => Kaxis K σ t *
        (Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x) := by
      funext x; rw [hkfun]
    rw [h1]
    have hexp : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) := by
      have hcd : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
      refine hcd.comp ?_
      exact ((contDiff_const.mul (hopR.pow 2)).mul contDiff_const).neg
    exact contDiff_const.mul (hexp.mul hsinSmooth)
  have hdom : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc 0 1) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ∀ x : ℝ,
        ‖iteratedDeriv j (fun x' : ℝ => kfun x' t) x‖ ≤ bd t := by
    intro j hj
    obtain ⟨Γj, hΓj0, hΓj⟩ := sinSq_gauss_seminorm 0 j
    refine ⟨fun _ => max (c0 * (scale w)^N0 * Γj) (Kbd * Γj * (2 / w.im)^j), ?_, ?_⟩
    · exact integrableOn_const (by simp)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      intro x
      have hstep : iteratedDeriv j (fun x' : ℝ => kfun x' t) x
          = Kaxis K σ t * iteratedDeriv j (fun x' : ℝ =>
              Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') x := by
        have h1 : (fun x' : ℝ => kfun x' t) = fun x' : ℝ => Kaxis K σ t *
            (Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') := by
          funext x'; rw [hkfun]
        rw [h1]
        refine iteratedDeriv_const_mul (Kaxis K σ t) ?_
        have hcd : ContDiffAt ℝ (↑j : ℕ∞) (fun x' : ℝ =>
            Complex.exp (-((Real.pi * (t:ℂ)) * (x':ℂ)^2))) x :=
          contDiffAt_gaussExp j (Real.pi * (t:ℂ)) x
        have heq : (fun x' : ℝ => Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) *
              Work.Asymptotics.sinSq x')
            = fun x' : ℝ => Complex.exp (-((Real.pi * (t:ℂ)) * (x':ℂ)^2)) *
              Work.Asymptotics.sinSq x' := by
          funext x'; congr 1; ring
        rw [heq]
        exact hcd.mul (hsinAt j x)
      rw [hstep, norm_mul]
      have hb2 : ‖iteratedDeriv j (fun x' : ℝ =>
            Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') x‖
          ≤ Γj * (t^j)⁻¹ := by
        have hcomm : (fun x' : ℝ => Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) *
            Work.Asymptotics.sinSq x') = fun x' : ℝ => Work.Asymptotics.sinSq x' *
            Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) := by
          funext x'; ring
        rw [hcomm]
        simpa using hΓj t ht0 ht1 x
      rcases le_or_gt t (w.im/2) with hc | hc
      · have hka := hflatN w n hn hw t ht0 hc
        rw [← hσ] at hka
        have htj : (t^j)⁻¹ ≤ (t^(k+l+1))⁻¹ := by
          rw [← inv_pow, ← inv_pow]
          exact pow_le_pow_right₀ ((one_le_inv₀ ht0).mpr ht1) (by omega)
        have hfin : c0 * (scale w)^N0 * t^(k+l+1) * (Γj * (t^j)⁻¹) ≤ c0 * (scale w)^N0 * Γj := by
          have h1 : t^(k+l+1) * (t^j)⁻¹ = t^(k+l+1-j) := by
            rw [← pow_sub₀ t (ne_of_gt ht0) (by omega : j ≤ k+l+1)]
          have h2 : t^(k+l+1) * (t^j)⁻¹ ≤ 1 := by
            rw [h1]; exact pow_le_one₀ ht0.le ht1
          have h3 : (0:ℝ) ≤ c0 * (scale w)^N0 * Γj := by positivity
          calc c0 * (scale w)^N0 * t^(k+l+1) * (Γj * (t^j)⁻¹)
              = c0 * (scale w)^N0 * Γj * (t^(k+l+1) * (t^j)⁻¹) := by ring
            _ ≤ c0 * (scale w)^N0 * Γj * 1 := mul_le_mul_of_nonneg_left h2 h3
            _ = c0 * (scale w)^N0 * Γj := by ring
        calc ‖Kaxis K σ t‖ * ‖iteratedDeriv j (fun x' : ℝ =>
              Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') x‖
            ≤ (c0 * (scale w)^N0 * t^(k+l+1)) * (Γj * (t^j)⁻¹) :=
              mul_le_mul hka hb2 (by positivity) (by positivity)
          _ ≤ c0 * (scale w)^N0 * Γj := hfin
          _ ≤ max (c0 * (scale w)^N0 * Γj) (Kbd * Γj * (2 / w.im)^j) := le_max_left _ _
      · have hka := hKbdle t ht0 ht1
        have htj : (t^j)⁻¹ ≤ (2 / w.im)^j := by
          have hstep : (t)⁻¹ ≤ (w.im/2)⁻¹ :=
            (inv_le_inv₀ ht0 (by linarith)).mpr (le_of_lt hc)
          rw [← inv_pow, show (2/w.im) = (w.im/2)⁻¹ by rw [inv_div]]
          exact pow_le_pow_left₀ (by positivity) hstep j
        calc ‖Kaxis K σ t‖ * ‖iteratedDeriv j (fun x' : ℝ =>
              Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') x‖
            ≤ Kbd * (Γj * (t^j)⁻¹) := mul_le_mul hka hb2 (by positivity) hKbd0
          _ ≤ Kbd * (Γj * (2 / w.im)^j) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htj hΓj0) hKbd0
          _ = Kbd * Γj * (2 / w.im)^j := by ring
          _ ≤ max (c0 * (scale w)^N0 * Γj) (Kbd * Γj * (2 / w.im)^j) := le_max_right _ _
  have hlayer : (fun s : ℝ => Work.Asymptotics.layerLow ℓ d σ s)
      = fun x : ℝ => ∫ t in (0:ℝ)..1, kfun x t := by
    funext x
    rw [Work.Asymptotics.layerLow, hkfun]
    have h1 : (fun t : ℝ => Kaxis K σ t *
          (Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x))
        = fun t : ℝ => (Kaxis K σ t *
          Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) * Work.Asymptotics.sinSq x := by
      funext t; ring
    rw [h1, intervalIntegral.integral_mul_const]
    ring
  set Dl : ℝ → ℂ := fun t => iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
      Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r with hDldef
  have hDl : ∀ t : ℝ, iteratedDeriv l (fun x' : ℝ => kfun x' t) r = Kaxis K σ t * Dl t := by
    intro t
    have h1 : (fun x' : ℝ => kfun x' t) = fun x' : ℝ => Kaxis K σ t *
        (Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') := by
      funext x'; rw [hkfun]
    rw [h1, hDldef]
    have hcd : ContDiffAt ℝ (↑l : ℕ∞) (fun x' : ℝ =>
        Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) * Work.Asymptotics.sinSq x') r := by
      have hcd0 : ContDiffAt ℝ (↑l : ℕ∞) (fun x' : ℝ =>
          Complex.exp (-((Real.pi * (t:ℂ)) * (x':ℂ)^2))) r :=
        contDiffAt_gaussExp l (Real.pi * (t:ℂ)) r
      have heq : (fun x' : ℝ => Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) *
            Work.Asymptotics.sinSq x')
          = fun x' : ℝ => Complex.exp (-((Real.pi * (t:ℂ)) * (x':ℂ)^2)) *
            Work.Asymptotics.sinSq x' := by
        funext x'; congr 1; ring
      rw [heq]
      exact hcd0.mul (hsinAt l r)
    rw [iteratedDeriv_const_mul (Kaxis K σ t) hcd]
    have heq2 : (fun x' : ℝ => Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) *
          Work.Asymptotics.sinSq x')
        = fun x' : ℝ => Work.Asymptotics.sinSq x' *
          Complex.exp (-(Real.pi * (x':ℂ)^2 * (t:ℂ))) := by
      funext x'; ring
    rw [heq2]
  have hmain : iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d σ s) r
      = ∫ t in (0:ℝ)..1, Kaxis K σ t * Dl t := by
    rw [hlayer, iteratedDeriv_intervalIntegral_of_meas_bound kfun l hmeas hsmooth hdom l le_rfl]
    simp only []
    congr 1 with t
    exact hDl t
  rw [show iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d ((n:ℝ) +ᵥ w) s) r
      = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d σ s) r from by rw [hσ],
    hmain]
  -- integrability on the two pieces
  have hI1 : IntervalIntegrable (fun t : ℝ => Kaxis K σ t * Dl t) volume 0 (w.im/2) := by
    refine intervalIntegrable_iff.mpr (IntegrableOn.of_bound ?_ ?_
      (Kbd * (Cdec * (1+|r|)^l)) ?_)
    · rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ w.im/2), Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact ((measurable_Kaxis_of_measurable K σ (measurable_Kfun_snd_all ℓ d hd σ)).mul
        (hdecb r).1).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [min_eq_left (by positivity : (0:ℝ) ≤ w.im/2)] at ht0
      rw [max_eq_right (by positivity : (0:ℝ) ≤ w.im/2)] at ht1
      rw [norm_mul, hDldef]
      exact mul_le_mul (hKbdle t ht0 (le_trans ht1 hy2))
        ((hdecb r).2 t ht0 (le_trans ht1 hy2)) (norm_nonneg _) hKbd0
  have hI2 : IntervalIntegrable (fun t : ℝ => Kaxis K σ t * Dl t) volume (w.im/2) 1 := by
    refine intervalIntegrable_iff.mpr (IntegrableOn.of_bound ?_ ?_
      (Kbd * (Cdec * (1+|r|)^l)) ?_)
    · rw [Set.uIoc_of_le hy2, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact ((measurable_Kaxis_of_measurable K σ (measurable_Kfun_snd_all ℓ d hd σ)).mul
        (hdecb r).1).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [min_eq_left hy2] at ht0
      rw [max_eq_right hy2] at ht1
      rw [norm_mul, hDldef]
      exact mul_le_mul (hKbdle t (lt_trans (by linarith [hy]) ht0) ht1)
        ((hdecb r).2 t (lt_trans (by linarith [hy]) ht0) ht1) (norm_nonneg _) hKbd0
  -- piece 1
  have hpiece1 : |r|^k * ‖∫ t in (0:ℝ)..(w.im/2), Kaxis K σ t * Dl t‖
      ≤ c0 * Γ * (scale w)^N0 := by
    have hb : ∀ t ∈ Set.uIoc (0:ℝ) (w.im/2),
        ‖(((|r|^k : ℝ)) : ℂ) • (Kaxis K σ t * Dl t)‖ ≤ c0 * (scale w)^N0 * Γ * (w.im/2) := by
      intro t ht
      have hu : Set.uIoc (0:ℝ) (w.im/2) = Set.Ioc 0 (w.im/2) := Set.uIoc_of_le (by positivity)
      rw [hu] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have hk := hflatN w n hn hw t ht0 ht1
      rw [← hσ] at hk
      have hD := hΓ t ht0 (le_trans ht1 hy2) r
      rw [norm_smul, norm_ofReal_complex, abs_of_nonneg (by positivity), hDldef, norm_mul]
      calc |r|^k * (‖Kaxis K σ t‖ * ‖iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
              Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r‖)
          = ‖Kaxis K σ t‖ * (|r|^k * ‖iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
              Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r‖) := by ring
        _ ≤ (c0 * (scale w)^N0 * t^(k+l+1)) * (Γ * (t^(k+l))⁻¹) :=
            mul_le_mul hk hD (by positivity) (by positivity)
        _ ≤ c0 * (scale w)^N0 * Γ * (w.im/2) := by
            have hpow : t^(k+l+1) * (t^(k+l))⁻¹ = t := by
              rw [← pow_sub₀ t (ne_of_gt ht0) (by omega : k+l ≤ k+l+1),
                show k+l+1 - (k+l) = 1 by omega, pow_one]
            have h3 : (0:ℝ) ≤ c0 * (scale w)^N0 * Γ := by positivity
            calc (c0 * (scale w)^N0 * t^(k+l+1)) * (Γ * (t^(k+l))⁻¹)
                = c0 * (scale w)^N0 * Γ * (t^(k+l+1) * (t^(k+l))⁻¹) := by ring
              _ = c0 * (scale w)^N0 * Γ * t := by rw [hpow]
              _ ≤ c0 * (scale w)^N0 * Γ * (w.im/2) := mul_le_mul_of_nonneg_left ht1 h3
    calc |r|^k * ‖∫ t in (0:ℝ)..(w.im/2), Kaxis K σ t * Dl t‖
        = ‖∫ t in (0:ℝ)..(w.im/2), (((|r|^k : ℝ)) : ℂ) • (Kaxis K σ t * Dl t)‖ := by
          rw [intervalIntegral.integral_smul, norm_smul, norm_ofReal_complex]
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |r|^k)]
      _ ≤ (c0 * (scale w)^N0 * Γ * (w.im/2)) * |(w.im/2) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = c0 * (scale w)^N0 * Γ * (w.im/2) * (w.im/2) := by
          rw [sub_zero, abs_of_nonneg (by positivity)]
      _ ≤ c0 * Γ * (scale w)^N0 := by
          have h4 : (w.im/2) * (w.im/2) ≤ 1 := by nlinarith [hyhalf, hy]
          have h5 : (0:ℝ) ≤ c0 * (scale w)^N0 * Γ := by positivity
          calc c0 * (scale w)^N0 * Γ * (w.im/2) * (w.im/2)
              = c0 * (scale w)^N0 * Γ * ((w.im/2) * (w.im/2)) := by ring
            _ ≤ c0 * (scale w)^N0 * Γ * 1 := mul_le_mul_of_nonneg_left h4 h5
            _ = c0 * Γ * (scale w)^N0 := by ring
  -- piece 2: split the kernel into remainder + pole
  have hRmeas : AEStronglyMeasurable (fun t : ℝ =>
      (Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)
      (volume.restrict (Set.uIoc (w.im/2) 1)) :=
    (((measurable_Kaxis_of_measurable K σ (measurable_Kfun_snd_all ℓ d hd σ)).sub
      (by fun_prop : Measurable (fun t : ℝ =>
        ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)))).mul
        (hdecb r).1).aestronglyMeasurable
  have hRbdd : ∀ᵐ t ∂(volume.restrict (Set.uIoc (w.im/2) 1)),
      ‖(Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t‖
        ≤ (Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|)) * (Cdec * (1+|r|)^l) := by
    rw [Set.uIoc_of_le hy2]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h := hpp' w hw n hn t (le_of_lt ht0) ht1
    rw [← hσ] at h
    rw [norm_mul, hDldef]
    have h1 : ‖Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)‖
        ≤ Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|) :=
      le_trans h (le_add_of_nonneg_right (by positivity : (0:ℝ) ≤ (1/(2*Real.pi)) * (1/|w.re|)))
    exact mul_le_mul h1 ((hdecb r).2 t (lt_trans (by linarith [hy]) ht0) ht1)
      (norm_nonneg _) (by positivity)
  have hIR : IntervalIntegrable (fun t : ℝ =>
      (Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)
      volume (w.im/2) 1 :=
    intervalIntegrable_iff.mpr
      (IntegrableOn.of_bound (by rw [Set.uIoc_of_le hy2, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        hRmeas ((Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|)) * (Cdec * (1+|r|)^l)) hRbdd)
  have hIPP : IntervalIntegrable (fun t : ℝ =>
      ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t) volume (w.im/2) 1 := by
    refine intervalIntegrable_iff.mpr (IntegrableOn.of_bound ?_ ?_
      ((Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|)) * (Cdec * (1+|r|)^l)) ?_)
    · rw [Set.uIoc_of_le hy2, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (((by fun_prop : Measurable (fun t : ℝ =>
        ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹))).mul (hdecb r).1)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [min_eq_left hy2] at ht0
      rw [max_eq_right hy2] at ht1
      rw [norm_mul, hDldef]
      have hden : |w.re| ≤ ‖(t:ℂ)*Complex.I - (w:ℂ)‖ := by
        have h := Complex.abs_re_le_norm ((t:ℂ)*Complex.I - (w:ℂ))
        have h2 : ((t:ℂ)*Complex.I - (w:ℂ)).re = -w.re := by
          simp [Complex.sub_re, Complex.mul_re]
        rw [h2, abs_neg] at h
        exact h
      have hn1 : ‖(n:ℂ)‖ ≤ 1 := by rcases hn with h | h <;> rw [h] <;> simp
      have h2pinv : ‖((2*(Real.pi:ℂ)))‖ = 2*Real.pi := by
        rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
          norm_ofReal_complex, abs_of_nonneg (by positivity)]
      have hPPn : ‖((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)‖
          ≤ (1/(2*Real.pi)) * (1/|w.re|) := by
        rw [norm_mul, norm_div, norm_inv, h2pinv, div_eq_mul_inv]
        calc ‖(n:ℂ)‖ * (2*Real.pi)⁻¹ * ‖(t:ℂ)*Complex.I - (w:ℂ)‖⁻¹
            ≤ 1 * (2*Real.pi)⁻¹ * (|w.re|)⁻¹ := by
              refine mul_le_mul (mul_le_mul hn1 le_rfl (by positivity) (by norm_num)) ?_
                (by positivity) (by positivity)
              exact inv_norm_le_inv_abs_re (w := (w:ℂ)) hre
          _ = (1/(2*Real.pi)) * (1/|w.re|) := by rw [inv_eq_one_div, inv_eq_one_div]; ring
      have h1 : ‖((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)‖
          ≤ Cpp * (scale w)^Npp + (1/(2*Real.pi)) * (1/|w.re|) :=
        le_trans hPPn (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ Cpp * (scale w)^Npp))
      exact mul_le_mul h1 ((hdecb r).2 t (lt_trans (by linarith [hy]) ht0) ht1)
        (norm_nonneg _) (by positivity)
  have hpiece2 : |r|^k * ‖∫ t in (w.im/2)..1, Kaxis K σ t * Dl t‖
      ≤ Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ)) + Cppl * (scale w)^Nppl := by
    have hsplit2 : (∫ t in (w.im/2)..1, Kaxis K σ t * Dl t)
        = (∫ t in (w.im/2)..1, (Kaxis K σ t -
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)
          + (∫ t in (w.im/2)..1, ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t) := by
      rw [← intervalIntegral.integral_add hIR hIPP]
      congr 1
      funext t; ring
    have hR : |r|^k * ‖∫ t in (w.im/2)..1, (Kaxis K σ t -
          ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t‖
        ≤ Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ)) := by
      have hb : ∀ t ∈ Set.uIoc (w.im/2) 1,
          ‖(((|r|^k : ℝ)) : ℂ) • ((Kaxis K σ t -
            ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)‖
          ≤ Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ := by
        intro t ht
        have hu : Set.uIoc (w.im/2) 1 = Set.Ioc (w.im/2) 1 := Set.uIoc_of_le hy2
        rw [hu] at ht
        obtain ⟨ht0, ht1⟩ := ht
        have h := hpp' w hw n hn t (le_of_lt ht0) ht1
        rw [← hσ] at h
        have hD := hΓ t (lt_of_le_of_lt (by linarith [hy]) ht0) ht1 r
        rw [norm_smul, norm_ofReal_complex, abs_of_nonneg (by positivity), norm_mul]
        calc |r|^k * (‖Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)‖ *
              ‖iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
                Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r‖)
            = ‖Kaxis K σ t - ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)‖ *
              (|r|^k * ‖iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
                Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r‖) := by ring
          _ ≤ (Cpp * (scale w)^Npp) * (Γ * (t^(k+l))⁻¹) :=
              mul_le_mul h hD (by positivity) (by positivity)
          _ ≤ Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ := by
              have h3 : (0:ℝ) ≤ Cpp * (scale w)^Npp * Γ := by positivity
              have h4 : (t^(k+l))⁻¹ ≤ ((w.im/2)^(k+l))⁻¹ :=
                (inv_le_inv₀ (pow_pos (lt_trans (by linarith [hy]) ht0) _)
                  (pow_pos (by linarith [hy]) _)).mpr
                  (pow_le_pow_left₀ (by linarith [hy]) (le_of_lt ht0) _)
              calc (Cpp * (scale w)^Npp) * (Γ * (t^(k+l))⁻¹)
                  = Cpp * (scale w)^Npp * Γ * (t^(k+l))⁻¹ := by ring
                _ ≤ Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ :=
                    mul_le_mul_of_nonneg_left h4 h3
      calc |r|^k * ‖∫ t in (w.im/2)..1, (Kaxis K σ t -
            ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t‖
          = ‖∫ t in (w.im/2)..1, (((|r|^k : ℝ)) : ℂ) • ((Kaxis K σ t -
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)‖ := by
            rw [intervalIntegral.integral_smul, norm_smul, norm_ofReal_complex]
            rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |r|^k)]
        _ ≤ (Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹) * |1 - w.im/2| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hb
        _ ≤ Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ := by
            have h6 : |1 - w.im/2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
            have h3 : (0:ℝ) ≤ Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ := by positivity
            calc (Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹) * |1 - w.im/2|
                ≤ (Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹) * 1 :=
                  mul_le_mul_of_nonneg_left h6 h3
              _ = Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹ := by ring
        _ ≤ Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ)) := by
            have hinv : ((w.im/2)^(k+l))⁻¹ ≤ (2:ℝ)^(k+l) * (scale w)^(k+l) := by
              rw [show ((w.im/2)^(k+l))⁻¹ = (2/w.im)^(k+l) by rw [← inv_pow, inv_div],
                div_pow, div_eq_mul_inv, ← inv_pow]
              have h7 : (w.im)⁻¹ ≤ scale w := inv_im_le_scale w
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h7 _)
                (by positivity)
            have h3 : (0:ℝ) ≤ Cpp * (scale w)^Npp * Γ := by positivity
            calc Cpp * (scale w)^Npp * Γ * ((w.im/2)^(k+l))⁻¹
                ≤ Cpp * (scale w)^Npp * Γ * ((2:ℝ)^(k+l) * (scale w)^(k+l)) :=
                  mul_le_mul_of_nonneg_left hinv h3
              _ = Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ)) := by
                  rw [Real.rpow_add (scale_pos w), Real.rpow_natCast]
                  ring
    have hPP : |r|^k * ‖∫ t in (w.im/2)..1,
          ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t‖
        ≤ Cppl * (scale w)^Nppl := by
      have hconst : (∫ t in (w.im/2)..1,
          ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t)
          = ((n:ℂ)/(2*(Real.pi:ℂ))) * (∫ t in (w.im/2)..1,
              (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) * Dl t) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        rw [hDldef]
        ring
      have hn1 : ‖(n:ℂ)/(2*(Real.pi:ℂ))‖ = 1/(2*Real.pi) := by
        rw [norm_div, show ‖((2*(Real.pi:ℂ)))‖ = 2*Real.pi by
          rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
            norm_ofReal_complex, abs_of_nonneg (by positivity)]]
        have hn1' : ‖(n:ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> simp
        rw [hn1']
      rw [hconst, norm_mul, hn1]
      calc |r|^k * ((1/(2*Real.pi)) * ‖∫ t in (w.im/2)..1,
            (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) * Dl t‖)
          = (1/(2*Real.pi)) * (|r|^k * ‖∫ t in (w.im/2)..1, (1:ℂ)/((t:ℂ)*Complex.I - (w:ℂ)) *
              iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
                Complex.exp (-(Real.pi * (x:ℂ)^2 * (t:ℂ)))) r‖) := by
            simp only [hDldef]; ring
        _ ≤ (1/(2*Real.pi)) * (Cppl * (scale w)^Nppl) :=
            mul_le_mul_of_nonneg_left (hPPl w hw hre r) (by positivity)
        _ ≤ Cppl * (scale w)^Nppl := by
            have h3 : (0:ℝ) ≤ Cppl * (scale w)^Nppl := by positivity
            calc (1/(2*Real.pi)) * (Cppl * (scale w)^Nppl) ≤ 1 * (Cppl * (scale w)^Nppl) :=
                  mul_le_mul_of_nonneg_right (by rw [one_div]; exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])) h3
              _ = Cppl * (scale w)^Nppl := by ring
    calc |r|^k * ‖∫ t in (w.im/2)..1, Kaxis K σ t * Dl t‖
        = |r|^k * ‖(∫ t in (w.im/2)..1, (Kaxis K σ t -
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t)
            + (∫ t in (w.im/2)..1,
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t)‖ := by rw [hsplit2]
      _ ≤ |r|^k * (‖∫ t in (w.im/2)..1, (Kaxis K σ t -
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t‖
            + ‖∫ t in (w.im/2)..1,
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t‖) := by
          refine mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = |r|^k * ‖∫ t in (w.im/2)..1, (Kaxis K σ t -
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹)) * Dl t‖
            + |r|^k * ‖∫ t in (w.im/2)..1,
              ((n:ℂ)/(2*(Real.pi:ℂ)))*(((t:ℂ)*Complex.I - (w:ℂ))⁻¹) * Dl t‖ := by ring
      _ ≤ Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ)) + Cppl * (scale w)^Nppl :=
          add_le_add hR hPP
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  calc |r|^k * ‖(∫ t in (0:ℝ)..(w.im/2), Kaxis K σ t * Dl t)
        + (∫ t in (w.im/2)..1, Kaxis K σ t * Dl t)‖
      ≤ |r|^k * (‖∫ t in (0:ℝ)..(w.im/2), Kaxis K σ t * Dl t‖
          + ‖∫ t in (w.im/2)..1, Kaxis K σ t * Dl t‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = |r|^k * ‖∫ t in (0:ℝ)..(w.im/2), Kaxis K σ t * Dl t‖
          + |r|^k * ‖∫ t in (w.im/2)..1, Kaxis K σ t * Dl t‖ := by ring
    _ ≤ c0 * Γ * (scale w)^N0 + (Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ))
          + Cppl * (scale w)^Nppl) := add_le_add hpiece1 hpiece2
    _ ≤ (c0*Γ + Cpp*Γ*(2:ℝ)^(k+l) + Cppl) * (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) := by
        have hsc0 : (0:ℝ) < scale w := scale_pos w
        have e0 : (scale w)^N0 ≤ (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (le_trans (le_max_left _ _) (le_max_left _ _))
        have e1 : (scale w)^(Npp + ((k+l : ℕ) : ℝ))
            ≤ (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (le_trans (le_max_right _ _) (le_max_left _ _))
        have e2 : (scale w)^Nppl ≤ (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)
        have h0 : (0:ℝ) ≤ c0*Γ := by positivity
        have h1 : (0:ℝ) ≤ Cpp*Γ*(2:ℝ)^(k+l) := by positivity
        have h2 : (0:ℝ) ≤ Cppl := hCppl0
        have hT : (0:ℝ) ≤ (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) :=
          Real.rpow_nonneg (le_of_lt hsc0) _
        calc c0 * Γ * (scale w)^N0 + (Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(Npp + ((k+l : ℕ) : ℝ))
              + Cppl * (scale w)^Nppl)
            ≤ c0 * Γ * (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl)
              + (Cpp * Γ * (2:ℝ)^(k+l) * (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl)
              + Cppl * (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl)) := by
              gcongr
          _ = (c0*Γ + Cpp*Γ*(2:ℝ)^(k+l) + Cppl)
                * (scale w)^(max (max N0 (Npp + ((k+l : ℕ) : ℝ))) Nppl) := by ring

end Work.Asymptotics.Tile
