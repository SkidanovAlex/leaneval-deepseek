import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.AERadial
import Submission.ProfileEq1D
import Submission.SndClassify
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior classification of radial weak-harmonic functions (Layer 3)

**Theorem** (`exterior_harmonic_classification`): let `w : ℝ³ → ℝ` be radial,
locally integrable, weakly harmonic in the exterior region `{x | R ≤ ‖x‖}`
(`∫ w·Δφ = 0` for every smooth compactly supported `φ` with
`tsupport φ ⊆ {x | R ≤ ‖x‖}`), and decaying at infinity
(`Tendsto w (cocompact ℝ³) (𝓝 0)`), with `R > 0`.  Then there is a constant
`c : ℝ` with

    ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖ .

This is the rigorous content of "among radial locally integrable weak
solutions of `Δω = 0` outside the support decaying at infinity, the only one
is `c/‖x‖`", and is the main step of the scattering fact
`omega_outside_support` (the constant is later identified with `a v` by a
flux/Gauss identity using the *full* scattering equation).

## Proof route

1. **1D reduction.**  With `f := radialProfile w` and `u(r) := r · f r`:
   - `profile_second_annihilates_R` (Submission.ProfileEq1D) turns exterior
     weak harmonicity into
     `∫ r in Ioi R, u r * deriv (deriv χ) r = 0` for every `χ ∈ C∞c((R,∞))`;
   - `profile_mul_locallyIntegrableOn` (Submission.ProfileLocInt) gives
     `u ∈ LocallyIntegrableOn (Ioi R)`.
2. **Classification.**  `SndClassify.affine_ae_of_snd_annihilates` gives
   `⟨A, B, hcl⟩` with `∀ᵐ r : ℝ, R < r → u r = A + B * r`.
3. **The slope vanishes.**  `radialProfile_tendsto_zero`
   (Submission.ProfileTendsto, from `hwlim`) gives `f r → 0` as `r → ∞`.
   Since `u r = r · f r` pointwise, if `B ≠ 0` then for every `ε > 0` there
   are points `r ≥ M` (arbitrarily far out, avoiding the null set where the
   affine identity fails) with `|A + B·r| = |u r| ≤ r·ε`, forcing
   `|B| ≤ 2ε` (take two such radii), contradiction.  Hence `B = 0`, so
   `∀ᵐ r, R < r → u r = A`, i.e. `f r = A / r` for almost every `r > R`
   (divide by `r`, using `u r = r·f r` and `r > 0`).
   [Implemented as `affine_slope_zero_of_tendsto_and_ae` below: one good
   radius `r` beyond all thresholds with `|f r| < |B|/2` and `|A|/r < |B|/2`
   gives `|B| < 2·(|B|/2) = |B|` from `|A + B·r| = r·|f r|` and the triangle
   inequality — the "two radii" trick reduced to one sufficiently large.]
4. **Back to 3D.**  Let `c := A`.  The 1D a.e. statement
   `∀ᵐ r, R < r → radialProfile w r = c / r`, the radiality of `w`
   (`w x = radialProfile w ‖x‖`) and the nullness of the sphere
   `{x | ‖x‖ = R}` give the 3D claim by the measure-transfer lemma
   `ae_eq_div_norm_of_radial_profile_ae` (Submission.AERadial).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If almost everywhere on `(R, ∞)` a function `u` is affine
`u x = A + B · x`, and `u x = x · f x` with `f x → 0` as `x → ∞`
(`R > 0`), then the slope `B` vanishes. -/
lemma affine_slope_zero_of_tendsto_and_ae {R A B : ℝ} {f u : ℝ → ℝ} (hR : 0 < R)
    (hu : ∀ r : ℝ, u r = r * f r)
    (hf : Tendsto f atTop (𝓝 0))
    (hucl : ∀ᵐ x : ℝ, R < x → u x = A + B * x) : B = 0 := by
  by_contra hBne
  have hBabs : 0 < |B| := abs_pos.mpr hBne
  let ε : ℝ := |B| / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  -- |f r| < ε eventually
  have hev : ∀ᶠ r in atTop, |f r| < ε := by
    have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
    have hf' : ∀ᶠ r in atTop, f r ∈ Metric.ball (0 : ℝ) ε := hf hball
    filter_upwards [hf'] with r hr
    simpa [Real.norm_eq_abs, dist_zero_right] using hr
  rcases Filter.mem_atTop_sets.mp hev with ⟨M, hM⟩
  have hbdd : ∀ r : ℝ, M ≤ r → |f r| < ε := by
    intro r hr
    exact hM r hr
  -- a single radius beyond every threshold, on which the affine identity holds
  let L : ℝ := max R (max M (|A| / ε)) + 1
  have hL1 : |A| / ε < L := by
    dsimp [L]
    have h1 : |A| / ε ≤ max M (|A| / ε) := le_max_right M (|A| / ε)
    have h2 : max M (|A| / ε) ≤ max R (max M (|A| / ε)) := le_max_right R (max M (|A| / ε))
    linarith
  have hL2 : R < L := by
    dsimp [L]
    have hle : R ≤ max R (max M (|A| / ε)) := le_max_left _ _
    linarith
  have hL3 : M < L := by
    dsimp [L]
    have hle1 : M ≤ max M (|A| / ε) := le_max_left _ _
    have hle2 : max M (|A| / ε) ≤ max R (max M (|A| / ε)) := le_max_right R (max M (|A| / ε))
    linarith
  have hgood : ∃ r : ℝ, L < r ∧ (R < r → u r = A + B * r) := by
    -- otherwise `Ioi L` would be contained in the null exceptional set
    by_contra h
    have hsub : Set.Ioi L ⊆ {x : ℝ | ¬ (R < x → u x = A + B * x)} := by
      intro r hr hQ
      exact h ⟨r, hr, hQ⟩
    have hmeas : (volume : Measure ℝ) (Set.Ioi L) ≤
        (volume : Measure ℝ) {x : ℝ | ¬ (R < x → u x = A + B * x)} := measure_mono hsub
    have hz : (volume : Measure ℝ) {x : ℝ | ¬ (R < x → u x = A + B * x)} = 0 :=
      (MeasureTheory.ae_iff.mp hucl)
    have hle : (volume : Measure ℝ) (Set.Ioi L) ≤ 0 := hmeas.trans (le_of_eq hz)
    have hLne : (volume : Measure ℝ) (Set.Ioi L) ≠ 0 := by
      rw [Real.volume_Ioi]
      exact ENNReal.top_ne_zero
    exact hLne (le_antisymm hle bot_le)
  rcases hgood with ⟨r, hrL, hrgood⟩
  have hRr : R < r := lt_trans hL2 hrL
  have hMr : M ≤ r := le_of_lt (lt_trans hL3 hrL)
  have hAr : |A| / ε < r := lt_trans hL1 hrL
  have hrf : |f r| < ε := hbdd r hMr
  have huc : u r = A + B * r := hrgood hRr
  have hufact : u r = r * f r := hu r
  have hR0r : 0 < r := lt_trans hR hRr
  -- |A + B·r| = |u r| = r·|f r| < r·ε
  have hmain : |A + B * r| < r * ε := by
    have h1 : |A + B * r| = |u r| := by rw [huc]
    have h2 : |u r| = r * |f r| := by
      rw [hufact, abs_mul]
      rw [abs_of_pos hR0r]
    calc
      |A + B * r| = |u r| := h1
      _ = r * |f r| := h2
      _ < r * ε := mul_lt_mul_of_pos_left hrf hR0r
  -- ... while `|B|·r − |A| ≤ |A + B·r|` by the triangle inequality
  have htriang := abs_add_le (A + B * r) (-A)
  have hBr : |B * r| ≤ |A + B * r| + |A| := by
    simpa [sub_eq_add_neg, abs_neg, add_assoc, add_comm, add_left_comm] using htriang
  have hle2 : |B * r| - |A| ≤ |A + B * r| := by linarith
  have hineq : |B| * r - |A| < r * ε := by
    have h3 : |B * r| = |B| * r := by
      rw [abs_mul]
      rw [abs_of_pos hR0r]
    calc
      |B| * r - |A| = |B * r| - |A| := by rw [h3]
      _ ≤ |A + B * r| := hle2
      _ < r * ε := hmain
  have hdiv : |B| < (r * ε + |A|) / r := by
    rw [lt_div_iff₀ hR0r]
    linarith
  have hdiv2 : |B| < ε + |A| / r := by
    have hcalc : (r * ε + |A|) / r = ε + |A| / r := by
      field_simp [ne_of_gt hR0r]
    rwa [hcalc] at hdiv
  have hAr2 : |A| / r < ε := by
    have h : |A| < ε * r := by simpa [mul_comm] using ((div_lt_iff₀ hε).mp hAr)
    exact (div_lt_iff₀ hR0r).mpr h
  have hfin : |B| < 2 * ε := by linarith
  have h2e : 2 * ε = |B| := by dsimp [ε]; ring
  exact (lt_irrefl |B| (by rwa [h2e] at hfin))

/-- Exterior classification: a radial, locally integrable, weakly-harmonic
outside `{x | R ≤ ‖x‖}`, decaying function is `c/‖x‖` a.e. on the exterior. -/
theorem exterior_harmonic_classification {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (hwli : LocallyIntegrable w)
    (hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖} → (∫ x : ℝ³, w x * (Δ φ) x) = 0)
    (hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)) :
    ∃ c : ℝ, ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖ := by
  let f : ℝ → ℝ := radialProfile w
  let u : ℝ → ℝ := fun r : ℝ => r * f r
  -- u is locally integrable on (R,∞) and annihilates second derivatives
  have huLI : MeasureTheory.LocallyIntegrableOn u (Set.Ioi R) volume := by
    simpa [u, f] using profile_mul_locallyIntegrableOn (w := w) (R := R) hR hrad hwli
  have huann : ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → R < r) →
      (∫ x : ℝ in Set.Ioi R, u x * deriv (deriv χ) x) = 0 := by
    intro χ hχc hχcomp hχsup
    simpa [u, f] using profile_second_annihilates_R (w := w) (R := R) hR hrad hwli hwh χ hχc hχcomp hχsup
  -- 1D classification: u is affine a.e. on (R,∞)
  rcases affine_ae_of_snd_annihilates huLI huann with ⟨A, B, hcl⟩
  -- decay of f at infinity
  have hftend : Tendsto f atTop (𝓝 0) := by
    simpa [f] using radialProfile_tendsto_zero hrad hwlim
  have hu_eq : ∀ r : ℝ, u r = r * f r := by intro r; rfl
  -- the slope vanishes
  have hB0 : B = 0 := affine_slope_zero_of_tendsto_and_ae (R := R) (A := A) (B := B)
    (f := f) (u := u) hR hu_eq hftend hcl
  -- u = A a.e. on (R,∞), hence radialProfile w r = A / r a.e. on (R,∞)
  have hclA : ∀ᵐ x : ℝ, R < x → u x = A := by
    filter_upwards [hcl] with x hx hRx
    have hx' : u x = A + B * x := hx hRx
    simpa [hB0] using hx'
  have hfA : ∀ᵐ r : ℝ, R < r → radialProfile w r = A / r := by
    filter_upwards [hclA] with r hr hRr
    have hR0r : 0 < r := lt_trans hR hRr
    have hrne : r ≠ 0 := ne_of_gt hR0r
    have huAr : r * radialProfile w r = A := by simpa [u, f] using (hr hRr)
    rw [eq_div_iff hrne, mul_comm]
    exact huAr
  -- transfer the 1D a.e. statement to the 3D exterior (Submission.AERadial)
  refine ⟨A, ?_⟩
  exact ae_eq_div_norm_of_radial_profile_ae (w := w) (R := R) hR hrad hfA

end Submission.BoseGases
