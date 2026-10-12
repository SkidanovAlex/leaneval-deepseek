import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.KernelFibreBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-261 — the `|Ŵ₁| ≤ C₀·(a v)` mass leaf (`SmallBoxBogWS1Bound.lean`)

FS eq:WSestimate (`0 ≤ ∫W₁ ≤ C a`, final_v2.tex ll.1152–1160 & 1525:
`Since 0 ≤ ∫ W₁ ≤ C a …`, `I := ∫ W₁(y)ω(y) ≤ C a`) bounds the total mass
of the χ-renormalised one-body kernel `W₁ = g₀/(χ⋆χ(·/ℓ))`.  In the corpus
transcription `W₁ = wScaled ℓ (g0 v h)` (`Submission.KernelIds.wScaled`),
and the Fourier-side bound `|Ŵ₁(p)| ≤ Ŵ₁(0) = ∫W₁` that the per-mode Fock
assembly consumes (`ℬ(p) := Ŵ₁(p)`, `|ℬ| ≤ C₀·(a v)`) reduces — since
`W₁ ≥ 0` a.e. — to the real-space mass bound

    ∫_z |wScaled ℓ (g0 v h) z| ≤ 16π·(a v)        (C₀ := 16π)

valid in the dilute regime `R ≤ ℓ·chiR0` (then `(χ⋆χ)_ℓ ≥ 1/2` on the
support `ball 0 R` of `g₀`, so `|wScaled| ≤ 2|g₀|` a.e. — `KernelMean.
wScaled_abs_le_two` — and `∫|g₀| = ∫g₀ = 8π·a v` —
`ScatKernelChosen.g0_integral` + a.e.-nonnegativity).

The module certifies (namespace `Submission.BoseGases`), for the standing
chosen-branch hypotheses `hR : 0 < R`, `hv_nonneg : 0 ≤ v`,
`hvrad : IsRadial v`, `hv_supp : tsupport v ⊆ ball 0 R`,
`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`:
  * `g0_abs_integral`          — `∫|g₀| = 8π·(a v)` (needs `g0_nonneg_ae`);
  * `g0_support_of_norm_ge`    — pointwise wrapper of `g0_zero_of_norm_ge`;
  * `wScaled_g0_integrable`    — `∫`-integrability of `wScaled ℓ (g0 v h)`
                                (via `KernelFibreBound.wScaled_integrable_ae`);
  * `wScaled_g0_nonneg_ae`     — `0 ≤ wScaled ℓ (g0 v h)` a.e.
                                (`g₀ ≥ 0` a.e. + `convScale ≥ 0`);
  * `wScaled_g0_abs_integral_le` — **`∫|W₁| ≤ 16π·(a v)`**;
  * `wScaled_g0_mass_le`       — **`∫W₁ ≤ 16π·(a v)`** (= the abs-bound, since
                                `W₁ ≥ 0` a.e.); the C₀ = 16π instance of
                                FS's `0 ≤ ∫W₁ ≤ Ca`;
  * `wScaled_g0_mass_nonneg`   — `0 ≤ ∫W₁` (the other side of the sandwich).

and the `g₂`-twin for the W₂/Q₂ side (FS eq:w2int, `g2_integral_bounds`):
  * `g2_support_of_norm_ge`, `wScaled_g2_integrable`, `wScaled_g2_nonneg_ae`,
  * `g2_abs_integral_le` — `∫|g₂| ≤ 16π·(a v)`,
  * `wScaled_g2_abs_integral_le` — **`∫|W₂| ≤ 32π·(a v)`** (C₀ := 32π),
  * `wScaled_g2_mass_le` / `wScaled_g2_mass_nonneg` — `0 ≤ ∫W₂ ≤ 32π·(a v)`.

Next: the per-mode Fock2Mode assembly multiplies this leaf by the
mode-count factors at the box-mode `𝒜(k)` coefficients (per the
SmallBoxDesignNote Session-260 roadmap).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
set_option autoImplicit false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Mass of `|g₀|`**: `∫|g₀| = ∫g₀ = 8π·(a v)` (a.e.-nonnegativity of
`g₀` + `ScatKernelChosen.g0_integral`). -/
lemma g0_abs_integral {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ z : ℝ³, |g0 v h z|) = 8 * π * a v := by
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hcongr : (fun z : ℝ³ => |g0 v h z|) =ᵐ[volume] (fun z : ℝ³ => g0 v h z) := by
    filter_upwards [hg0nn] with z hz
    exact abs_of_nonneg hz
  rw [MeasureTheory.integral_congr_ae hcongr]
  exact g0_integral hR hv_supp h

/-- Pointwise `g₀`-support wrapper: `g₀` vanishes for `R ≤ ‖z‖`. -/
lemma g0_support_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    g0 v h x = 0 := g0_zero_of_norm_ge (v := v) (R := R) hv_supp hx h

/-- Integrability of the renormalised kernel `wScaled ℓ (g0 v h)` (dilute
regime `R ≤ ℓ·chiR0`; from `KernelFibreBound.wScaled_integrable_ae`). -/
lemma wScaled_g0_integrable {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    MeasureTheory.Integrable (fun z : ℝ³ => wScaled ℓ (g0 v h) z) := by
  apply wScaled_integrable_ae hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
  intro z hz
  exact g0_support_of_norm_ge hv_supp hz h

/-- `W₁ := wScaled ℓ (g0 v h)` is nonnegative a.e. (`g₀ ≥ 0` a.e. and
`convScale ≥ 0` pointwise). -/
lemma wScaled_g0_nonneg_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ z : ℝ³, 0 ≤ wScaled ℓ (g0 v h) z := by
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  filter_upwards [hg0nn] with z hz
  dsimp [wScaled]
  exact mul_nonneg hz (inv_nonneg.mpr (convScale_nonneg ℓ z))

/-- **FS eq:WSestimate, C₀ := 16π**: `∫|W₁| ≤ 16π·(a v)` — the
`|Ŵ₁(p)| ≤ ∫|W₁| ≤ C₀·(a v)` real-space side of the per-mode Fock
`|ℬ(p)| ≤ C₀·(a v)` bound (`|wScaled| ≤ 2|g₀|` on the dilute regime +
`∫|g₀| = 8π·(a v)`). -/
lemma wScaled_g0_abs_integral_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, |wScaled ℓ (g0 v h) z|) ≤ 16 * π * a v := by
  have hwi : MeasureTheory.Integrable (fun z : ℝ³ => wScaled ℓ (g0 v h) z) :=
    wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hgi : MeasureTheory.Integrable (fun z : ℝ³ => |g0 v h z|) :=
    (g0_integrable hR hv_supp h).abs
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³),
      |wScaled ℓ (g0 v h) z| ≤ 2 * |g0 v h z| := by
    refine ae_of_all _ ?_
    intro z
    simpa [Real.norm_eq_abs] using
      (wScaled_abs_le_two hℓ hR.le hRℓ (fun z hz => g0_support_of_norm_ge hv_supp hz h) z)
  have hle : (∫ z : ℝ³, |wScaled ℓ (g0 v h) z|)
      ≤ ∫ z : ℝ³, 2 * |g0 v h z| := by
    exact MeasureTheory.integral_mono_ae hwi.abs (hgi.const_mul 2) hdom
  calc
    (∫ z : ℝ³, |wScaled ℓ (g0 v h) z|) ≤ ∫ z : ℝ³, 2 * |g0 v h z| := hle
    _ = 2 * (∫ z : ℝ³, |g0 v h z|) := by rw [MeasureTheory.integral_const_mul]
    _ = 2 * (8 * π * a v) := by rw [g0_abs_integral hR hv_nonneg hvrad hv_supp h]
    _ = 16 * π * a v := by ring

/-- **FS `∫W₁ ≤ C a`**: `∫ wScaled ℓ (g0 v h) ≤ 16π·(a v)` (the abs-bound
with `W₁ ≥ 0` a.e.). -/
lemma wScaled_g0_mass_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, wScaled ℓ (g0 v h) z) ≤ 16 * π * a v := by
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ wScaled ℓ (g0 v h) z :=
    wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hcongr : (fun z : ℝ³ => |wScaled ℓ (g0 v h) z|) =ᵐ[volume]
      (fun z : ℝ³ => wScaled ℓ (g0 v h) z) := by
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  calc
    (∫ z : ℝ³, wScaled ℓ (g0 v h) z) = ∫ z : ℝ³, |wScaled ℓ (g0 v h) z| := by
      rw [MeasureTheory.integral_congr_ae hcongr]
    _ ≤ 16 * π * a v := wScaled_g0_abs_integral_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ

/-- **FS `0 ≤ ∫W₁`**: the mass of `wScaled ℓ (g0 v h)` is nonnegative. -/
lemma wScaled_g0_mass_nonneg {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ (∫ z : ℝ³, wScaled ℓ (g0 v h) z) := by
  exact MeasureTheory.integral_nonneg_of_ae (wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)

/-! ## The `g₂`-twin (`W₂ = wScaled ℓ (g2 v h)`, the Q2-mass side)

FS eq:w2int (`∬w₂ = ½∫g₂(1+ω)`) and the Q₂ one-body mass treatment need the
mass of the `W₂`-kernel: from `g2_integral_bounds` (`∫g₂ ≤ 16π·(a v)`) and
`g2_nonneg_ae`, the same `|wScaled| ≤ 2|g₂|`-route gives
`∫|W₂| = ∫W₂ ≤ 32π·(a v)` (C₀ := 32π). -/

/-- Pointwise `g₂`-support wrapper: `g₂` vanishes for `R ≤ ‖z‖`. -/
lemma g2_support_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    g2 v h x = 0 := g2_zero_of_norm_ge (v := v) (R := R) hv_supp hx h

/-- Integrability of `wScaled ℓ (g2 v h)` (dilute regime; from
`KernelFibreBound.wScaled_integrable_ae` + `g2_integrable`). -/
lemma wScaled_g2_integrable {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    MeasureTheory.Integrable (fun z : ℝ³ => wScaled ℓ (g2 v h) z) := by
  apply wScaled_integrable_ae hℓ hR.le hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
  intro z hz
  exact g2_support_of_norm_ge hv_supp hz h

/-- `W₂ := wScaled ℓ (g2 v h)` is nonnegative a.e. (`g₂ ≥ 0` a.e. and
`convScale ≥ 0` pointwise). -/
lemma wScaled_g2_nonneg_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ z : ℝ³, 0 ≤ wScaled ℓ (g2 v h) z := by
  have hg2nn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  filter_upwards [hg2nn] with z hz
  dsimp [wScaled]
  exact mul_nonneg hz (inv_nonneg.mpr (convScale_nonneg ℓ z))

/-- `∫|g₂| = ∫g₂ ≤ 16π·(a v)` (a.e.-nonnegativity + `g2_integral_bounds`). -/
lemma g2_abs_integral_le {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ z : ℝ³, |g2 v h z|) ≤ 16 * π * a v := by
  have hg2nn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hcongr : (fun z : ℝ³ => |g2 v h z|) =ᵐ[volume] (fun z : ℝ³ => g2 v h z) := by
    filter_upwards [hg2nn] with z hz
    exact abs_of_nonneg hz
  calc
    (∫ z : ℝ³, |g2 v h z|) = ∫ z : ℝ³, g2 v h z := by
      rw [MeasureTheory.integral_congr_ae hcongr]
    _ ≤ 16 * π * a v := (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).2

/-- **W₂ mass bound**: `∫|W₂| ≤ 32π·(a v)` (the `|wScaled| ≤ 2|g₂|`-route +
`∫|g₂| ≤ 16π·(a v)`). -/
lemma wScaled_g2_abs_integral_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, |wScaled ℓ (g2 v h) z|) ≤ 32 * π * a v := by
  have hwi : MeasureTheory.Integrable (fun z : ℝ³ => wScaled ℓ (g2 v h) z) :=
    wScaled_g2_integrable hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hgi : MeasureTheory.Integrable (fun z : ℝ³ => |g2 v h z|) :=
    (g2_integrable hR hv_nonneg hvrad hv_supp h).abs
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³),
      |wScaled ℓ (g2 v h) z| ≤ 2 * |g2 v h z| := by
    refine ae_of_all _ ?_
    intro z
    simpa [Real.norm_eq_abs] using
      (wScaled_abs_le_two hℓ hR.le hRℓ (fun z hz => g2_support_of_norm_ge hv_supp hz h) z)
  have hle : (∫ z : ℝ³, |wScaled ℓ (g2 v h) z|)
      ≤ ∫ z : ℝ³, 2 * |g2 v h z| := by
    exact MeasureTheory.integral_mono_ae hwi.abs (hgi.const_mul 2) hdom
  calc
    (∫ z : ℝ³, |wScaled ℓ (g2 v h) z|) ≤ ∫ z : ℝ³, 2 * |g2 v h z| := hle
    _ = 2 * (∫ z : ℝ³, |g2 v h z|) := by rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * (16 * π * a v) := mul_le_mul_of_nonneg_left (g2_abs_integral_le hR hv_nonneg hvrad hv_supp h) (by norm_num)
    _ = 32 * π * a v := by ring

/-- **`∫W₂ ≤ 32π·(a v)`** (the abs-bound with `W₂ ≥ 0` a.e.). -/
lemma wScaled_g2_mass_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, wScaled ℓ (g2 v h) z) ≤ 32 * π * a v := by
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ wScaled ℓ (g2 v h) z :=
    wScaled_g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hcongr : (fun z : ℝ³ => |wScaled ℓ (g2 v h) z|) =ᵐ[volume]
      (fun z : ℝ³ => wScaled ℓ (g2 v h) z) := by
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  calc
    (∫ z : ℝ³, wScaled ℓ (g2 v h) z) = ∫ z : ℝ³, |wScaled ℓ (g2 v h) z| := by
      rw [MeasureTheory.integral_congr_ae hcongr]
    _ ≤ 32 * π * a v := wScaled_g2_abs_integral_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ

/-- **`0 ≤ ∫W₂`**. -/
lemma wScaled_g2_mass_nonneg {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ (∫ z : ℝ³, wScaled ℓ (g2 v h) z) := by
  exact MeasureTheory.integral_nonneg_of_ae (wScaled_g2_nonneg_ae hR hv_nonneg hvrad hv_supp h)

end BoseGases
end Submission
