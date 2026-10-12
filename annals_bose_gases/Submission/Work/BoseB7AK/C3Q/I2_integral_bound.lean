import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal
import Submission.Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.C3Q.I2_integral_bound` — FS `eq:I2-integral` in momentum space

The target is FS's `eq:I2-integral` (`Papers/fournais_solovej/final_v2.tex`, lemma after
`eq:W1-g`, around line 864) at the corpus's conventions:

`|(2π)⁻³ ∫ p, Ŵ₁(p)²/(2‖p‖²) − ĝω(0)| ≤ C (R/ℓ)² ĝω(0)`,

with `W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g₀)`, `g₀ = Submission.BoseGases.g0 v h`,
`ω = Classical.choose h` the chosen radial scattering solution, `ĝω(0) = ∫ g₀ω`, for a
nonnegative radial `v` with `tsupport v ⊆ ball 0 R` in the dilute regime `R ≤ ℓ·chiR0`.

## Route

Write `I := ∫ x, g₀(x)ω(x) ≥ 0` and, for `w : ℝ³ → ℝ`,

`I2coul w := ∫⁻ z ∂(volume × volume), ofReal (w z.1 * w z.2 / ‖z.1 − z.2‖)`,

the Coulomb double lintegral in **product-measure** form (equal to the iterated `∫⁻` by
`MeasureTheory.lintegral_prod`, `I2coul_iterated`).

1. **Fourier ↔ x-space** (`Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal`, proved in the
   sibling file): with `W := W₁`,
   `(2π)⁻³ ∫ p, Ŵ(p)²/(2‖p‖²) = (1/(8π)) · (I2coul W).toReal`.
2. **The value at `g₀`** (`Work.BoseB7AK.C3Q.lintegral_double_eq_ofReal_newton`): the `∫⁻`
   Newton identity `I2coul g₀ = ofReal (8π I)` — the `∫⁻` companion of
   `Submission.BoseGases.chosen_newton_double_eq`; it also shows the double lintegral is
   finite.
3. **The sandwich** (`Work.BoseB7AK.C3Q.W1_sharp_ae_aux` for the upper bound and
   `I2_g0_le_W1fun_ae` for the lower one): `g₀ ≤ W₁ ≤ (1 + 2C₁(R/ℓ)²)g₀` a.e., where `C₁`
   is a global quadratic deviation constant of `(χ⋆χ)`
   (`Work.BoseB7AK.C3Q.conv3chi_dev_quad`).  Monotonicity of the double lintegral
   (`I2coul_mono_ae`, `I2coul_mono_ae_mul`) gives

   `ofReal (8π I) = I2coul g₀ ≤ I2coul W₁ ≤ (1 + 2C₁(R/ℓ)²)² · ofReal (8π I)`,

   so, after `.toReal` and division by `8π`,

   `I ≤ (2π)⁻³ ∫ p, Ŵ₁(p)²/(2‖p‖²) ≤ (1 + 2C₁(R/ℓ)²)² I`.
4. **Arithmetic**: `(1 + 2C₁(R/ℓ)²)² − 1 ≤ 4C₁(1 + C₁·chiR0²)(R/ℓ)²` (from
   `(R/ℓ)² ≤ chiR0²`, `I2_arith`), whence the bound with the absolute constant
   `C := 4C₁(1 + C₁·chiR0²)`.

The absolute value is removed using the *lower* bound `A ≥ I` (so `A − I ≥ 0`); no
`δ`-smallness hypothesis (`(R/ℓ)² ≤ 1`, `C₁(R/ℓ)² ≤ 1/2`, …) is needed anywhere, the
smallness being entirely contained in the dilute hypothesis `R ≤ ℓ·chiR0` through
`convScale_ge_half_ball`.
-/

noncomputable section
open MeasureTheory

namespace Work.BoseB7AK.C3Q

local notation "R3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The Coulomb double lintegral in product form -/

/-- The Coulomb double lintegral of `w`, on the product measure `volume × volume`:
`∫⁻ z, ofReal (w z.1 * w z.2 / ‖z.1 − z.2‖)`. -/
def I2coul (w : R3 → ℝ) : ENNReal :=
  ∫⁻ z : R3 × R3, ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖)

lemma I2coul_eq (w : R3 → ℝ) :
    I2coul w = ∫⁻ z : R3 × R3, ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖) := rfl

lemma aemeasurable_I2coul_integrand {w : R3 → ℝ} (hw : AEStronglyMeasurable w) :
    AEMeasurable (fun z : R3 × R3 => ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖))
      (volume.prod volume) := by
  have h1 : AEMeasurable (fun z : R3 × R3 => w z.1) (volume.prod volume) :=
    hw.aemeasurable.comp_fst
  have h2 : AEMeasurable (fun z : R3 × R3 => w z.2) (volume.prod volume) :=
    hw.aemeasurable.comp_snd
  have h3 : AEMeasurable (fun z : R3 × R3 => ‖z.1 - z.2‖) (volume.prod volume) :=
    ((measurable_fst.sub measurable_snd).norm).aemeasurable
  exact ((h1.mul h2).div h3).ennreal_ofReal

/-- The product-measure form is the iterated `∫⁻`. -/
lemma I2coul_iterated {w : R3 → ℝ} (hw : AEStronglyMeasurable w) :
    I2coul w = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (w x * w y / ‖x - y‖) :=
  MeasureTheory.lintegral_prod _ (aemeasurable_I2coul_integrand hw)

/-- Monotonicity of the double lintegral. -/
lemma I2coul_mono_ae {w w' : R3 → ℝ} (hw : AEStronglyMeasurable w) (hw' : AEStronglyMeasurable w')
    (hw0 : ∀ᵐ x, 0 ≤ w x) (hw0' : ∀ᵐ x, 0 ≤ w' x) (hle : ∀ᵐ x, w x ≤ w' x) :
    I2coul w ≤ I2coul w' := by
  rw [I2coul_eq, I2coul_eq]
  refine lintegral_mono_ae ?_
  have h1 : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), 0 ≤ w z.1 ∧ 0 ≤ w z.2 := by
    have a : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), 0 ≤ w z.1 :=
      Measure.quasiMeasurePreserving_fst.ae hw0
    have b : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), 0 ≤ w z.2 :=
      Measure.quasiMeasurePreserving_snd.ae hw0
    filter_upwards [a, b] with z hz1 hz2
    exact ⟨hz1, hz2⟩
  have h2 : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), w z.1 ≤ w' z.1 ∧ w z.2 ≤ w' z.2 := by
    have a : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), w z.1 ≤ w' z.1 :=
      Measure.quasiMeasurePreserving_fst.ae hle
    have b : ∀ᵐ z : R3 × R3 ∂(volume.prod volume), w z.2 ≤ w' z.2 :=
      Measure.quasiMeasurePreserving_snd.ae hle
    filter_upwards [a, b] with z hz1 hz2
    exact ⟨hz1, hz2⟩
  filter_upwards [h1, h2] with z hz1 hz2
  apply ENNReal.ofReal_le_ofReal
  have hmul : w z.1 * w z.2 ≤ w' z.1 * w' z.2 :=
    mul_le_mul hz2.1 hz2.2 hz1.2 (le_trans hz1.1 hz2.1)
  exact div_le_div_of_nonneg_right hmul (norm_nonneg _)

/-- Scaling the argument by a nonnegative constant scales the double lintegral by its
square. -/
lemma I2coul_const_mul {w : R3 → ℝ} {c : ℝ} (hc : 0 ≤ c) (hw : AEStronglyMeasurable w) :
    I2coul (fun x => c * w x) = ENNReal.ofReal (c * c) * I2coul w := by
  rw [I2coul_eq, I2coul_eq]
  have hpt : ∀ z : R3 × R3, ENNReal.ofReal ((c * w z.1) * (c * w z.2) / ‖z.1 - z.2‖)
      = ENNReal.ofReal (c * c) * ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c * c)]
    congr 1
    ring
  calc ∫⁻ z : R3 × R3, ENNReal.ofReal ((c * w z.1) * (c * w z.2) / ‖z.1 - z.2‖)
      = ∫⁻ z : R3 × R3, ENNReal.ofReal (c * c) * ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖) :=
        lintegral_congr hpt
    _ = ENNReal.ofReal (c * c) * ∫⁻ z : R3 × R3, ENNReal.ofReal (w z.1 * w z.2 / ‖z.1 - z.2‖) :=
        lintegral_const_mul'' _ (aemeasurable_I2coul_integrand hw)

/-- `w ≤ c·v` a.e. (all a.e. nonnegative) gives `I2coul w ≤ ofReal (c·c) · I2coul v`. -/
lemma I2coul_mono_ae_mul {w v : R3 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hw : AEStronglyMeasurable w) (hv : AEStronglyMeasurable v)
    (hw0 : ∀ᵐ x, 0 ≤ w x) (hv0 : ∀ᵐ x, 0 ≤ v x) (hle : ∀ᵐ x, w x ≤ c * v x) :
    I2coul w ≤ ENNReal.ofReal (c * c) * I2coul v := by
  have hmono : I2coul w ≤ I2coul (fun x => c * v x) :=
    I2coul_mono_ae hw (hv.const_mul c) hw0 (hv0.mono (fun x hx => mul_nonneg hc hx)) hle
  rw [I2coul_const_mul hc hv] at hmono
  exact hmono

/-! ## The two a.e. facts about `W₁` -/

/-- `W₁` is even. -/
lemma I2_W1fun_neg {v : R3 → ℝ} {ℓ : ℝ} (hvrad : _root_.BoseGases.IsRadial v)
    (h : Work.UBB.ScatSol v) (x : R3) :
    Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x := by
  show Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (-x)
      = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x
  rw [Submission.BoseGases.wScaled, Submission.BoseGases.wScaled,
    Submission.BoseGases.g0_even hvrad h, Submission.BoseGases.convScale_symm]

/-- `g₀ ≤ W₁` a.e.  On `ball 0 R` the renormalisation `(χ⋆χ)(·/ℓ)` is `≤ 1`, so dividing
`g₀ ≥ 0` by it can only increase it. -/
lemma I2_g0_le_W1fun_ae {v : R3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x, Submission.BoseGases.g0 v h x ≤ Work.BoseFixR.W1fun v h ℓ x := by
  filter_upwards [Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h] with x hgx
  by_cases hx0 : Submission.BoseGases.g0 v h x = 0
  · have h0 : Work.BoseFixR.W1fun v h ℓ x = 0 := by
      show Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x = 0
      rw [Submission.BoseGases.wScaled, hx0, zero_div]
    rw [hx0, h0]
  · have hxR : ‖x‖ < R :=
      lt_of_not_ge (fun hx => hx0 (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h))
    have hbhalf : 1 / 2 ≤ Submission.BoseGases.convScale ℓ x :=
      Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ (le_of_lt hxR)
    have hbpos : 0 < Submission.BoseGases.convScale ℓ x := lt_of_lt_of_le (by norm_num) hbhalf
    have hb1 : Submission.BoseGases.convScale ℓ x ≤ 1 := Submission.BoseGases.conv3chi_le_one _
    show Submission.BoseGases.g0 v h x
      ≤ Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x
    rw [Submission.BoseGases.wScaled, le_div_iff₀ hbpos]
    nlinarith [hgx, hb1]

/-! ## The scalar arithmetic -/

lemma I2_arith {C₁ k e : ℝ} (hC₁ : 0 ≤ C₁) (hk : 0 ≤ k) (hke : k ≤ e) :
    (1 + 2 * C₁ * k ^ 2) ^ 2 - 1 ≤ 4 * C₁ * (1 + C₁ * e ^ 2) * k ^ 2 := by
  have hk2 : k ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hk hke 2
  have hstep : C₁ ^ 2 * k ^ 2 * k ^ 2 ≤ C₁ ^ 2 * k ^ 2 * e ^ 2 :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  nlinarith [hstep, hC₁, hk]

/-! ## The target -/

theorem I2_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}, 0 < R → 0 < ℓ →
      (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball 0 R → (h : Work.UBB.ScatSol v) →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      |((2 * Real.pi) ^ 3)⁻¹
            * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))
          - ∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x|
        ≤ C * (R / ℓ) ^ 2 * (∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := conv3chi_dev_quad
  refine ⟨4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2), ?_, ?_⟩
  · have h1 : 0 ≤ 1 + C₁ * Submission.BoseGases.chiR0 ^ 2 := by
      nlinarith [hC₁0, sq_nonneg Submission.BoseGases.chiR0]
    nlinarith [hC₁0, h1]
  · intro v R ℓ hR hℓ hv_nonneg hvrad hv_supp h hRℓ
    obtain ⟨hrad, hw⟩ := Classical.choose_spec h
    set I : ℝ := ∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x with hIdef
    have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR hv_supp h
    have hgsupp : ∀ x, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
      fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
    have hg0 : ∀ᵐ x, 0 ≤ Submission.BoseGases.g0 v h x :=
      Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
    have hgω : MeasureTheory.Integrable
        (fun x => Submission.BoseGases.g0 v h x * Classical.choose h x) :=
      Submission.BoseGases.g0w0_integrable hR hv_nonneg hvrad hv_supp h
    have hgω0 : ∀ᵐ x, 0 ≤ Submission.BoseGases.g0 v h x * Classical.choose h x :=
      Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h
    have hrep : ∀ᵐ x, Classical.choose h x
        = (1 / (8 * Real.pi)) * ∫ y, Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹ := by
      have h0 := Submission.BoseGases.scattering_newton_representation (v := v)
        (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad hw
      filter_upwards [h0] with x hx
      simpa [Submission.BoseGases.g0] using hx
    have hI0 : 0 ≤ I := by
      rw [hIdef]
      exact integral_nonneg_of_ae hgω0
    have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
      Submission.BoseGases.wScaled_integrable_ae (h := Submission.BoseGases.g0 v h)
        hℓ hR.le hRℓ hgI hgsupp
    have hWaesm : AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := hWint.aestronglyMeasurable
    have hgaesm : AEStronglyMeasurable (Submission.BoseGases.g0 v h) := hgI.aestronglyMeasurable
    have hsharp := W1_sharp_ae_aux hR hℓ hC₁0 hC₁ hv_nonneg hvrad hv_supp h hRℓ
    have hW0 : ∀ᵐ x, 0 ≤ Work.BoseFixR.W1fun v h ℓ x := hsharp.mono (fun x hx => hx.1)
    have hWle : ∀ᵐ x, Work.BoseFixR.W1fun v h ℓ x
        ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x :=
      hsharp.mono (fun x hx => hx.2)
    have hWge : ∀ᵐ x, Submission.BoseGases.g0 v h x ≤ Work.BoseFixR.W1fun v h ℓ x :=
      I2_g0_le_W1fun_ae hR hℓ hv_nonneg hvrad hv_supp h hRℓ
    -- the exact value of the double lintegral at `g₀`
    have hQg : I2coul (Submission.BoseGases.g0 v h) = ENNReal.ofReal (8 * Real.pi * I) := by
      rw [I2coul_iterated hgaesm, hIdef]
      exact lintegral_double_eq_ofReal_newton hgI hg0 hgsupp hR.le hgω hgω0 hrep
    have hc0 : 0 ≤ 1 + 2 * C₁ * (R / ℓ) ^ 2 := by
      nlinarith [hC₁0, sq_nonneg (R / ℓ)]
    have hQle : I2coul (Submission.BoseGases.g0 v h) ≤ I2coul (Work.BoseFixR.W1fun v h ℓ) :=
      I2coul_mono_ae hgaesm hWaesm hg0 hW0 hWge
    have hQle' : I2coul (Work.BoseFixR.W1fun v h ℓ)
        ≤ ENNReal.ofReal ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
          * I2coul (Submission.BoseGases.g0 v h) :=
      I2coul_mono_ae_mul hc0 hWaesm hgaesm hW0 hg0 hWle
    have hQwtop : I2coul (Work.BoseFixR.W1fun v h ℓ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hQle'
      rw [hQg]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hlow : 8 * Real.pi * I ≤ (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal := by
      have h1 : ENNReal.ofReal (8 * Real.pi * I) ≤ I2coul (Work.BoseFixR.W1fun v h ℓ) := by
        rw [← hQg]
        exact hQle
      calc 8 * Real.pi * I = (ENNReal.ofReal (8 * Real.pi * I)).toReal := by
            rw [ENNReal.toReal_ofReal]
            positivity
        _ ≤ (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal := ENNReal.toReal_mono hQwtop h1
    have hup : (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal
        ≤ ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * (8 * Real.pi * I) := by
      have h2 : I2coul (Work.BoseFixR.W1fun v h ℓ)
          ≤ ENNReal.ofReal (((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
              * (8 * Real.pi * I)) := by
        calc I2coul (Work.BoseFixR.W1fun v h ℓ)
            ≤ ENNReal.ofReal ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
              * I2coul (Submission.BoseGases.g0 v h) := hQle'
          _ = ENNReal.ofReal ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
              * ENNReal.ofReal (8 * Real.pi * I) := by rw [hQg]
          _ = ENNReal.ofReal (((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
                * (8 * Real.pi * I)) := by
              rw [ENNReal.ofReal_mul (mul_nonneg hc0 hc0)]
      calc (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal
          ≤ (ENNReal.ofReal (((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2))
              * (8 * Real.pi * I))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
        _ = ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * (8 * Real.pi * I) := by
            rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hc0 hc0) (by positivity))]
    -- the momentum-space side
    have hA := chat_sq_div_eq_coulomb_toReal hWint hW0 (fun x => I2_W1fun_neg hvrad h x)
    have hA' : ((2 * Real.pi) ^ 3)⁻¹
          * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))
        = (1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal := by
      rw [hA, ← I2coul_iterated hWaesm]
    have h8 : (8 : ℝ) * Real.pi ≠ 0 := by positivity
    have hA_up : (1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal
        ≤ ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * I := by
      have hπ : 0 ≤ (1 / (8 * Real.pi)) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hup hπ
      have heq : (1 / (8 * Real.pi))
            * (((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * (8 * Real.pi * I))
          = ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * I := by
        field_simp
      linarith [hstep, heq.symm.le, heq.le]
    have hA_low : I ≤ (1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal := by
      have hπ : 0 ≤ (1 / (8 * Real.pi)) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hlow hπ
      have heq : (1 / (8 * Real.pi)) * (8 * Real.pi * I) = I := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ h8, one_mul]
      linarith [hstep, heq.symm.le, heq.le]
    have hgoal : |(1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal - I|
        ≤ (4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2)) * (R / ℓ) ^ 2 * I := by
      have hnonneg : 0 ≤ (1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal - I := by
        linarith [hA_low]
      rw [abs_of_nonneg hnonneg]
      have hkey : ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2) - 1) * I
          ≤ (4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2)) * (R / ℓ) ^ 2 * I := by
        have hk0 : 0 ≤ R / ℓ := by positivity
        have hke : R / ℓ ≤ Submission.BoseGases.chiR0 := by
          rw [div_le_iff₀ hℓ]
          linarith
        have hscal := I2_arith (C₁ := C₁) hC₁0 hk0 hke
        have hscal' : (1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2) - 1
            ≤ 4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2) * (R / ℓ) ^ 2 := by
          simpa [pow_two] using hscal
        exact mul_le_mul_of_nonneg_right hscal' hI0
      calc (1 / (8 * Real.pi)) * (I2coul (Work.BoseFixR.W1fun v h ℓ)).toReal - I
          ≤ ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2)) * I - I := by
            linarith [hA_up]
        _ = ((1 + 2 * C₁ * (R / ℓ) ^ 2) * (1 + 2 * C₁ * (R / ℓ) ^ 2) - 1) * I := by ring
        _ ≤ (4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2)) * (R / ℓ) ^ 2 * I := hkey
    rw [hA']
    exact hgoal

end Work.BoseB7AK.C3Q
