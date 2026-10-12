import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1fun_bounds_ae
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.C3Q.coulomb_W1fun_le`

The *Coulomb energy* form of FS `eq:I2-integral` (`final_v2.tex` around line 1500),
i.e. the x-space bound on the double integral of the renormalised kernel

    `W₁ := Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g₀)`,  `g₀ := Submission.BoseGases.g0 v h`:

    `∫∫ W₁(x)W₁(y)/‖x−y‖ dx dy ≤ (1 + C(R/ℓ)²) · 8π ∫ g₀(x)ω(x) dx`,   `ω = Classical.choose h`,

for a nonnegative radial `v` with `tsupport v ⊆ ball 0 R` in the dilute regime
`R ≤ ℓ·chiR0` (and any scattering solution `h : ScatSol v`).

The sources of the two sides are the corpus's Newtonian dictionary
(`Submission/NewtonCoulomb.lean`):

* the *position-space* version of the Newton identity,
  `chosen_newton_double_eq`: `∫∫ g₀(x)g₀(y)/‖x−y‖ = 8π ∫ g₀·ω`, i.e.
  `8π·J(g₀) = 8π·ĝω(0)` with `J(f) = (1/8π)∫∫f(x)f(y)/‖x−y‖`;
* the rectangular comparison `coulomb_rect_le`, which upgrades a.e. domination
  `A ≤ cA·g` to `∫∫AB/‖x−y‖ ≤ cA·cB·∫∫gg/‖x−y‖`.

The mathematical content is therefore the **sharp comparison** of `W₁` with `g₀`,

    `W₁ ≤ (1 + 2C₁(R/ℓ)²)·g₀`  a.e.,  `C₁` the global quadratic deviation constant
    of `(χ⋆χ)`, i.e. `|(χ⋆χ)(t) − 1| ≤ C₁‖t‖²` for all `t`
    (`Submission.BoseGases.conv3chi_second_order_bound`, repackaged below as
    `conv3chi_dev_quad`),

whose `(R/ℓ)²`-size is what makes the constant `C` of the statement an *absolute*
one: as `R/ℓ → 0` the bound tends to `8π∫g₀ω`.

## Proof of the sharp comparison (`W1_sharp_ae_aux`)

On the support of `g₀` (`‖x‖ < R`, from `g0_zero_of_norm_ge`), with
`b := convScale ℓ x = (χ⋆χ)(x/ℓ)`:

* `1/2 ≤ b` — `convScale_ge_half_ball`, from `R ≤ ℓ·chiR0`;
* `b ≤ 1` — `conv3chi_le_one`;
* `1 − b ≤ C₁‖x/ℓ‖² ≤ C₁(R/ℓ)²` — the deviation hypothesis at `x/ℓ`.

Then `1/b ≤ 1 + 2(1−b) ≤ 1 + 2C₁(R/ℓ)²`, whence `W₁ x = g₀ x/b ≤ (1+2C₁(R/ℓ)²)·g₀ x`.
Off the support both kernels vanish.  The a.e. form is forced: `g₀ ≥ 0` is only
known a.e. (`g0_nonneg_ae`).

## Assembly

`coulomb_of_sharp` performs the double-integral comparison for a kernel `W` that is
a.e. nonnegative and a.e. dominated by `(1+δ)g₀` (with `W` vanishing off `ball 0 R`),
using `coulomb_rect_le` and `chosen_newton_double_eq`, and gives
`∫∫WW/‖x−y‖ ≤ (1+δ)²·8π∫g₀ω`.  The final arithmetic
`(1+2C₁(R/ℓ)²)² ≤ 1 + 4C₁(1+C₁·chiR0²)(R/ℓ)²` uses `(R/ℓ)² ≤ chiR0²` (from
`R ≤ ℓ·chiR0`) and the nonnegativity of `∫g₀ω`
(`W1omegaNum_nonneg_ae`).

All statements are the corpus's own; no new definitions.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB7AK.C3Q

set_option linter.unusedVariables false

open scoped Real

/-! ## The global quadratic deviation of `(χ⋆χ)` -/

/-- **Global quadratic deviation of the self-convolution `(χ⋆χ)`**:
`∃ C ≥ 0, ∀ t, |(χ⋆χ)(t) − 1| ≤ C‖t‖²`.

`Submission.BoseGases.conv3chi_second_order_bound` gives the local bound on
`‖t‖ ≤ r₁` (`r₁ > 0`); outside it `0 ≤ (χ⋆χ) ≤ 1` gives `|(χ⋆χ)(t) − 1| ≤ 2`,
while `2 ≤ (2/r₁²)‖t‖²` there, so `C := max C (2/r₁²)` works globally. -/
theorem conv3chi_dev_quad :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨C, hC0, r₁, hr₁, hloc⟩ := Submission.BoseGases.conv3chi_second_order_bound
  refine ⟨max C (2 / r₁ ^ 2), le_trans hC0 (le_max_left C _), fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ r₁
  · calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := hloc t ht
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left C _) (sq_nonneg _)
  · have htr : r₁ < ‖t‖ := lt_of_not_ge ht
    have hnn : 0 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t :=
      Submission.BoseGases.conv3chi_nonneg t
    have h1 : Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one t
    have h2 : |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hsq : r₁ ^ 2 ≤ ‖t‖ ^ 2 := by nlinarith [norm_nonneg t]
    have hC2 : 2 / r₁ ^ 2 * r₁ ^ 2 = 2 := by field_simp
    have hkey : 2 ≤ 2 / r₁ ^ 2 * ‖t‖ ^ 2 := by
      have hpos : 0 ≤ 2 / r₁ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsq hpos
      linarith [this, hC2]
    calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
          ≤ 2 := h2
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            le_trans hkey (mul_le_mul_of_nonneg_right (le_max_right C _) (sq_nonneg _))

/-! ## The sharp a.e. comparison `W₁ ≤ (1 + 2C₁(R/ℓ)²)·g₀` -/

/-- **Sharp a.e. comparison of `W₁` with `g₀`** (FS `eq:W1-g` with the quadratic
tail).  For a nonnegative radial `v` of range `R`, `R ≤ ℓ·chiR0`, any scattering
solution `h : ScatSol v`, and any *global* quadratic deviation constant `C₁` of
`(χ⋆χ)`:

    `0 ≤ W₁ x`  and  `W₁ x ≤ (1 + 2C₁(R/ℓ)²)·g₀ x`  for a.e. `x`,

where `W₁ = wScaled ℓ (g₀)`.

On `supp g₀` (`‖x‖ < R`), `b := (χ⋆χ)(x/ℓ) ∈ [1/2, 1]` and `1 − b ≤ C₁(R/ℓ)²`,
so `1/b ≤ 1 + 2(1−b) ≤ 1 + 2C₁(R/ℓ)²`; off `supp g₀` both sides vanish. -/
theorem W1_sharp_ae_aux {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ C₁ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C₁ * ‖t‖ ^ 2)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.BoseFixR.W1fun v h ℓ x ∧
        Work.BoseFixR.W1fun v h ℓ x
          ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by
  filter_upwards [Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h] with x hgx
  constructor
  · rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]
    exact div_nonneg hgx (Submission.BoseGases.convScale_nonneg ℓ x)
  · by_cases hx0 : Submission.BoseGases.g0 v h x = 0
    · simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hx0]
    · have hxR : ‖x‖ < R :=
        lt_of_not_ge (fun hx => hx0 (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h))
      have hbhalf : 1 / 2 ≤ Submission.BoseGases.convScale ℓ x :=
        Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ (le_of_lt hxR)
      have hbpos : 0 < Submission.BoseGases.convScale ℓ x := lt_of_lt_of_le (by norm_num) hbhalf
      have hb1 : Submission.BoseGases.convScale ℓ x ≤ 1 :=
        Submission.BoseGases.conv3chi_le_one _
      have hdev : 1 - Submission.BoseGases.convScale ℓ x ≤ C₁ * (R / ℓ) ^ 2 := by
        have h1 := (abs_le.mp (hC₁ ((ℓ)⁻¹ • x))).1
        have hnorm : ‖(ℓ)⁻¹ • x‖ ≤ R / ℓ := by
          rw [norm_smul_of_nonneg (inv_nonneg.mpr (le_of_lt hℓ))]
          calc ℓ⁻¹ * ‖x‖ ≤ ℓ⁻¹ * R :=
                mul_le_mul_of_nonneg_left (le_of_lt hxR) (inv_nonneg.mpr (le_of_lt hℓ))
            _ = R / ℓ := by ring
        have h2 : C₁ * ‖(ℓ)⁻¹ • x‖ ^ 2 ≤ C₁ * (R / ℓ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hC₁0
        have h3 : Submission.BoseGases.convScale ℓ x
            = Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
                ((ℓ)⁻¹ • x) := rfl
        linarith [h1, h2, h3.symm.le, h3.le]
      have hkey : 1 / Submission.BoseGases.convScale ℓ x ≤ 1 + 2 * C₁ * (R / ℓ) ^ 2 := by
        have hstep : 1 / Submission.BoseGases.convScale ℓ x
            ≤ 1 + 2 * (1 - Submission.BoseGases.convScale ℓ x) := by
          rw [div_le_iff₀ hbpos]
          nlinarith [hb1, hbhalf]
        linarith [hstep, hdev]
      rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]
      rw [div_le_iff₀ hbpos]
      have hstep2 : 1 ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.convScale ℓ x :=
        (div_le_iff₀ hbpos).mp hkey
      nlinarith [hgx, hstep2]

/-! ## The double-integral comparison for an a.e.-dominated kernel -/

/-- **Coulomb double-integral comparison.**  If `W` is integrable, a.e. nonnegative,
supported in `ball 0 R`, and a.e. dominated by `(1+δ)·g₀`, then

    `∫∫ W(x)W(y)/‖x−y‖ ≤ (1+δ)² · 8π ∫ g₀(x)ω(x) dx`,

`ω = Classical.choose h`.  This is `coulomb_rect_le` (with `A = B = W`, `g = g₀`,
`cA = cB = 1+δ`) followed by the Newton identity `chosen_newton_double_eq`. -/
theorem coulomb_of_sharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 ≤ δ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hsh : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.BoseFixR.W1fun v h ℓ x ∧
        Work.BoseFixR.W1fun v h ℓ x ≤ (1 + δ) * Submission.BoseGases.g0 v h x) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y / ‖x - y‖)
      ≤ (1 + δ) ^ 2 * (8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h x * Classical.choose h x) := by
  have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0nn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hgsupp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  have hW0 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
    hsh.mono (fun x hx => hx.1)
  have hWle : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
      ≤ (1 + δ) * Submission.BoseGases.g0 v h x := hsh.mono (fun x hx => hx.2)
  have hWsupp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → Work.BoseFixR.W1fun v h ℓ x = 0 := by
    intro x hx
    rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hgsupp x hx, zero_div]
  have hconv_aesm : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.convScale ℓ x)⁻¹) := by
    have hmeas : Measurable
        (fun x : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.convScale ℓ x)⁻¹) := by
      refine Measurable.inv ?_
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.convScale ℓ x) := by
        dsimp [Submission.BoseGases.convScale]
        exact (Submission.BoseGases.conv_contDiff.continuous).comp (continuous_id.const_smul (ℓ⁻¹))
      exact hc.measurable
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  have hWmeas : AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
    have hprod : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h x * (Submission.BoseGases.convScale ℓ x)⁻¹) :=
      hgI.aestronglyMeasurable.mul hconv_aesm
    refine hprod.congr ?_
    filter_upwards with x
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
  have hWI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    refine MeasureTheory.Integrable.mono' (hgI.const_mul (1 + δ)) hWmeas ?_
    filter_upwards [hW0, hWle] with x hW0x hWlex
    rw [Real.norm_eq_abs, abs_of_nonneg hW0x]
    exact hWlex
  obtain ⟨hrad₀, hw₀⟩ := Classical.choose_spec h
  have hrep : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), Classical.choose h x
      = (1 / (8 * Real.pi)) * Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x := by
    have h0 := Submission.BoseGases.scattering_newton_representation (v := v)
      (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad₀ hw₀
    simpa [Submission.BoseGases.g0, Submission.BoseGases.coulPot] using h0
  have hVg_eq : (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.g0 v h x
        * Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x) =ᵐ[volume]
      (fun x : EuclideanSpace ℝ (Fin 3) => 8 * Real.pi
        * (Submission.BoseGases.g0 v h x * Classical.choose h x)) := by
    filter_upwards [hrep] with x hx
    have hc : (8 : ℝ) * Real.pi ≠ 0 := by positivity
    have hVx : Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x
        = (8 * Real.pi) * Classical.choose h x := by
      symm
      calc (8 * Real.pi) * Classical.choose h x
          = (8 * Real.pi) * ((1 / (8 * Real.pi))
              * Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x) := by rw [hx]
        _ = Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x := by
              rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
    calc Submission.BoseGases.g0 v h x
            * Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x
        = Submission.BoseGases.g0 v h x * ((8 * Real.pi) * Classical.choose h x) := by rw [hVx]
      _ = 8 * Real.pi * (Submission.BoseGases.g0 v h x * Classical.choose h x) := by ring
  have hgw0 : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.g0 v h x * Classical.choose h x) :=
    Submission.BoseGases.g0w0_integrable hR hv_nonneg hvrad hv_supp h
  have hVgInt : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.g0 v h x
        * Submission.BoseGases.coulPot (Submission.BoseGases.g0 v h) x) :=
    MeasureTheory.Integrable.congr (hgw0.const_mul (8 * Real.pi)) hVg_eq.symm
  have hrect := Submission.BoseGases.coulomb_rect_le (R := R)
    (A := Work.BoseFixR.W1fun v h ℓ) (B := Work.BoseFixR.W1fun v h ℓ)
    (g := Submission.BoseGases.g0 v h) (cA := 1 + δ) (cB := 1 + δ) hR hWI hWI hgI
    hWsupp hWsupp hgsupp hW0 hW0 hg0nn hWle hWle (by linarith) (by linarith) hVgInt
  have hnewt : (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹)
      = 8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h x * Classical.choose h x := by
    have h0 := Submission.BoseGases.chosen_newton_double_eq (v := v) (R := R) hR hvrad hv_supp h
    simpa [Submission.BoseGases.g0] using h0
  calc (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y / ‖x - y‖)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹ := by
        simp only [div_eq_mul_inv]
    _ ≤ (1 + δ) * (1 + δ) * (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹) := hrect
    _ = (1 + δ) ^ 2 * (8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h x * Classical.choose h x) := by
          rw [hnewt]; ring

/-! ## The target -/

theorem coulomb_W1fun_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}, 0 < R → 0 < ℓ →
      (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball 0 R → (h : Work.UBB.ScatSol v) →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      (∫ x, ∫ y, Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y / ‖x - y‖)
        ≤ (1 + C * (R / ℓ) ^ 2)
          * (8 * Real.pi * ∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := conv3chi_dev_quad
  refine ⟨4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2), ?_, ?_⟩
  · have h : 0 ≤ 1 + C₁ * Submission.BoseGases.chiR0 ^ 2 := by
      nlinarith [sq_nonneg Submission.BoseGases.chiR0, hC₁0]
    nlinarith [hC₁0, h]
  · intro v R ℓ hR hℓ hv hvrad hv_supp h hRℓ
    have hsh := W1_sharp_ae_aux hR hℓ hC₁0 hC₁ hv hvrad hv_supp h hRℓ
    have hδ0 : 0 ≤ 2 * C₁ * (R / ℓ) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hC₁0) (sq_nonneg _)
    have hmain := coulomb_of_sharp (v := v) (R := R) (ℓ := ℓ) (δ := 2 * C₁ * (R / ℓ) ^ 2)
      hR hδ0 hv hvrad hv_supp h hsh
    have hVle : (R / ℓ) ^ 2 ≤ Submission.BoseGases.chiR0 ^ 2 := by
      have h1 : R / ℓ ≤ Submission.BoseGases.chiR0 := by rw [div_le_iff₀ hℓ]; linarith
      exact pow_le_pow_left₀ (div_nonneg (le_of_lt hR) (le_of_lt hℓ)) h1 2
    have hV0 : 0 ≤ (R / ℓ) ^ 2 := sq_nonneg _
    have key : 4 * C₁ ^ 2 * ((R / ℓ) ^ 2) ^ 2
        ≤ 4 * C₁ ^ 2 * Submission.BoseGases.chiR0 ^ 2 * (R / ℓ) ^ 2 := by
      calc 4 * C₁ ^ 2 * ((R / ℓ) ^ 2) ^ 2
            = 4 * C₁ ^ 2 * (R / ℓ) ^ 2 * (R / ℓ) ^ 2 := by ring
        _ ≤ 4 * C₁ ^ 2 * (R / ℓ) ^ 2 * Submission.BoseGases.chiR0 ^ 2 :=
              mul_le_mul_of_nonneg_left hVle (by positivity)
        _ = 4 * C₁ ^ 2 * Submission.BoseGases.chiR0 ^ 2 * (R / ℓ) ^ 2 := by ring
    have hfac : (1 + 2 * C₁ * (R / ℓ) ^ 2) ^ 2
        ≤ 1 + (4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2)) * (R / ℓ) ^ 2 := by
      nlinarith [key, hC₁0, hV0, hVle]
    have hI0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.g0 v h x * Classical.choose h x :=
      MeasureTheory.integral_nonneg_of_ae
        (Work.BoseB7AK.W1rows.W1omegaNum_nonneg_ae hR hv hvrad hv_supp h)
    have hIπ : 0 ≤ 8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.g0 v h x * Classical.choose h x :=
      mul_nonneg (by positivity) hI0
    calc (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ y / ‖x - y‖)
        ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) ^ 2
            * (8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x) := hmain
      _ ≤ (1 + 4 * C₁ * (1 + C₁ * Submission.BoseGases.chiR0 ^ 2) * (R / ℓ) ^ 2)
            * (8 * Real.pi * ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x) :=
          mul_le_mul_of_nonneg_right hfac hIπ

end Work.BoseB7AK.C3Q
