import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1omega0_rows.lean`

**The `Ŵ₁ω(0)` row of the dilute-regime kernel bundle** (`Work.BoseFixR`'s
`RView`, the `W1omega0_nonneg`/`W1omega0_le` fields of `Q3Kernels`): for a
nonnegative radial potential `v` of range `R` in the FS dilute regime
`R ≤ ℓ·chiR0`, with a scattering solution `h : ScatSol v`, the zero-momentum
value of the χ-renormalised kernel

    `W₁ω = Work.BoseFixR.W1omegaFun v h ℓ
         = wScaled ℓ (x ↦ g₀(x)·ω(x))`,  `g₀ = v(1−ω)`, `ω = Classical.choose h`,

satisfies

    `0 ≤ Ŵ₁ω(0)`,   `Ŵ₁ω(0) ≤ C·(a v)`   (here `C = 16π`).

In other words the row asks exactly for FS's `0 ≤ ∫W₁ω ≤ C a` (final_v2.tex
line 1158 and `I := ∫W₁(y)ω(y) ≤ Ca`, line 1525) at the corpus's own kernel:
FS `eq:defW_12` has `W₁ = W(1−ω)`, so `W₁ω = W(1−ω)ω`, which in the corpus's
normalisation `W₁ = wScaled ℓ g₀`, `g₀ = v(1−ω)` (see `Work.BoseFixR.W1omegaFun`)
is the numerator `g₀ω = v(1−ω)ω`.  (The mass cancellation `ĝω(0) = ∫W₁ω`, on
which FS §9 `prop:FarAway` and §10 `lem:BogIntegral` rest, fails with the
factor `(1−ω)` in place of `ω`; see the `Work.BoseFixR.W1omegaFun` docstring.)

## Route (all ingredients are already in the corpus)

1. `chat_zero`: the `p`-convention Fourier transform (`Work.BoseFixR.chat`) at
   momentum `0` is the total mass, `Ŵ(0) = ∫W`.  (This is the `k = 0` case of
   `Work.BoseFixR.chat_zero_eq_pairW`, proved directly from `kinFT`.)

2. **Nonnegativity.**  `g₀ω = v(1−ω)ω` is nonnegative **almost everywhere**
   (`ScatGIntegrals.scat_gomega_ae_bounds`: the conjunction
   `0 ≤ (v(1−w))w ∧ (v(1−w))w ≤ v(1−w)`), and
   `(χ⋆χ)(·/ℓ) ≥ 0` pointwise (`Submission.BoseGases.convScale_nonneg`), hence
   `0 ≤ W₁ω` a.e., and `0 ≤ ∫W₁ω` by `integral_nonneg_of_ae`.

3. **Mass bound.**  `W1omega0_mass_le`: `scat_gomega_integral_bounds` gives
   `∫g₀ω ≤ ∫g₀`, and `∫g₀ = 8π·(a v)` (`ScatKernelChosen.g0_integral`).

   Then `|W₁ω| ≤ 2|g₀ω|` pointwise in the dilute regime
   (`KernelMean.wScaled_abs_le_two`, since the numerator vanishes for `‖z‖ ≥ R`)
   and `W₁ω ≥ 0` a.e., so `∫W₁ω = ∫|W₁ω| ≤ 2·8π·(a v) = 16π·(a v)`
   (`W1omega_abs_integral_le`).

The statement is unchanged; only helper lemmas are added above it.

## The numerator convention

`W1omegaNum v h = g₀·ω = v(1−ω)ω`.  This is the numerator of
`Work.BoseFixR.W1omegaFun` **after** the `Work.BoseFixR` owner's correction of
2026-10-04 (FS `eq:defW_12`: `W₁ = W(1−ω)`, so `W₁ω = W(1−ω)ω`, which in the
corpus's normalisation `W₁ = wScaled ℓ g₀` is `wScaled ℓ (g₀ω)`).  The *old*
numerator `g₀(1−ω) = v(1−ω)²` is `W₁(1−ω)`, **not** `W₁ω`: it makes the mass
cancellation `ĝω(0) = ∫W₁ω` false (see `Work.BoseFixR.W1omegaFun`'s docstring), so
downstream consumers that previously used it must switch to the API of this module:
`W1omegaNum_nonneg_ae` (a.e. nonnegativity, not pointwise),
`W1omegaFun_eq` (the definitional identity), `W1omegaFun_abs_le_two`,
`W1omegaNum_integrable` / `W1omegaFun_integrable`
(`Work.BoseB7AK.W1rows.W1omega_low_nonneg`).
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory

open scoped Real Topology

/-- The numerator of the `W₁ω` kernel: `g₀ω = v(1−ω)ω`
(`g₀ = Submission.BoseGases.g0 v h`, `ω = Classical.choose h`). -/
def W1omegaNum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => Submission.BoseGases.g0 v h z * Classical.choose h z

/-- `W₁ω` is the χ-renormalised version of `W1omegaNum`. -/
lemma W1omegaFun_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) :
    Work.BoseFixR.W1omegaFun v h ℓ = Submission.BoseGases.wScaled ℓ (W1omegaNum v h) := rfl

/-- `Ŵ(0) = ∫ W`: the `p`-convention Fourier transform at momentum `0` is the
total mass of `W`. -/
theorem chat_zero (W : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseFixR.chat W 0 = ∫ x, W x := by
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  have h : (∫ y : EuclideanSpace ℝ (Fin 3), ((W y : ℝ) : ℂ))
      = (((∫ y : EuclideanSpace ℝ (Fin 3), W y) : ℝ) : ℂ) := integral_ofReal
  rw [h]
  exact Complex.ofReal_re _

/-- The numerator `g₀ω = v(1−ω)ω` is nonnegative **almost everywhere**
(`scat_gomega_ae_bounds`). -/
lemma W1omegaNum_nonneg_ae {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    ∀ᵐ z ∂(volume : Measure ℝ³), 0 ≤ W1omegaNum v h z := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hb := Submission.BoseGases.scat_gomega_ae_bounds hR (fun x => hv_nonneg x)
    hvrad hv_supp hrad hw
  filter_upwards [hb.1] with x hx
  simpa [W1omegaNum, Submission.BoseGases.g0] using hx

/-- **FS `∫W₁ω ≤ Ca`**, the real-space side: `∫ g₀ω ≤ 8π·(a v)`.

`scat_gomega_integral_bounds` gives `∫g₀ω ≤ ∫g₀`, and `∫g₀ = 8π·(a v)`
(`ScatKernelChosen.g0_integral`). -/
lemma W1omega0_mass_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    (∫ z, W1omegaNum v h z) ≤ 8 * π * _root_.BoseGases.a v := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hb := (Submission.BoseGases.scat_gomega_integral_bounds hR (fun x => hv_nonneg x)
    hvrad hv_supp hrad hw).2
  have hgw : (∫ z : EuclideanSpace ℝ (Fin 3),
      (v z * (1 - Classical.choose h z)) * Classical.choose h z)
      = ∫ z, W1omegaNum v h z := rfl
  rw [hgw] at hb
  have hg0 : (∫ z : EuclideanSpace ℝ (Fin 3), v z * (1 - Classical.choose h z))
      = 8 * π * _root_.BoseGases.a v :=
    Submission.BoseGases.g0_integral hR hv_supp h
  linarith [hb, hg0]

/-- **The dilute-regime domination by the numerator**, in the form consumers use:
`|W₁ω(z)| ≤ 2|g₀ω(z)|` for a.e. `z` (the numerator vanishes for `‖z‖ ≥ R` and
`wScaled` divides by the convolution kernel, `KernelMean.wScaled_abs_le_two`). -/
lemma W1omegaFun_abs_le_two {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}
    (hR : 0 ≤ R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ z ∂(volume : Measure ℝ³),
      |Work.BoseFixR.W1omegaFun v h ℓ z| ≤ 2 * |W1omegaNum v h z| := by
  refine ae_of_all _ (fun z => ?_)
  have hsupp : ∀ w : EuclideanSpace ℝ (Fin 3), R ≤ ‖w‖ → W1omegaNum v h w = 0 :=
    fun w hw => by
      have hw0 : Submission.BoseGases.g0 v h w = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp hw h
      simp [W1omegaNum, hw0]
  rw [W1omegaFun_eq]
  exact Submission.BoseGases.wScaled_abs_le_two hℓ hR hRℓ hsupp z

/-- **FS `0 ≤ ∫W₁ω ≤ Ca`** in `L¹` form: `∫|W₁ω| ≤ 16π·(a v)`.

`|W₁ω| ≤ 2|g₀ω|` pointwise in the dilute regime
(`KernelMean.wScaled_abs_le_two`, the numerator vanishing for `‖z‖ ≥ R`), and
the mass of the numerator is `≤ 8π·(a v)` (`W1omega0_mass_le`). -/
lemma W1omega_abs_integral_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫ z, |Work.BoseFixR.W1omegaFun v h ℓ z|) ≤ 16 * π * _root_.BoseGases.a v := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hNil : MeasureTheory.Integrable (W1omegaNum v h) :=
    Submission.BoseGases.scat_gomega_integrable (fun x => hv_nonneg x) hvrad hv_supp hrad hw
  have hsupp : ∀ z, R ≤ ‖z‖ → W1omegaNum v h z = 0 := fun z hz => by
    have hz0 : Submission.BoseGases.g0 v h z = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    simp [W1omegaNum, hz0]
  have hWi : MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) := by
    rw [W1omegaFun_eq]
    exact Submission.BoseGases.wScaled_integrable_ae hℓ hR.le hRℓ hNil hsupp
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³),
      |Work.BoseFixR.W1omegaFun v h ℓ z| ≤ 2 * |W1omegaNum v h z| := by
    refine ae_of_all _ (fun z => ?_)
    rw [W1omegaFun_eq]
    exact Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hRℓ hsupp z
  have hle : (∫ z, |Work.BoseFixR.W1omegaFun v h ℓ z|) ≤ ∫ z, 2 * |W1omegaNum v h z| :=
    MeasureTheory.integral_mono_ae hWi.abs (hNil.abs.const_mul 2) hdom
  have hNnn : ∀ᵐ z ∂(volume : Measure ℝ³), 0 ≤ W1omegaNum v h z :=
    W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h
  calc (∫ z, |Work.BoseFixR.W1omegaFun v h ℓ z|) ≤ ∫ z, 2 * |W1omegaNum v h z| := hle
    _ = 2 * (∫ z, |W1omegaNum v h z|) := by rw [MeasureTheory.integral_const_mul]
    _ = 2 * (∫ z, W1omegaNum v h z) := by
        congr 1
        exact MeasureTheory.integral_congr_ae (hNnn.mono (fun z hz => abs_of_nonneg hz))
    _ ≤ 2 * (8 * π * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left (W1omega0_mass_le hR hv_nonneg hvrad hv_supp h) (by norm_num)
    _ = 16 * π * _root_.BoseGases.a v := by ring

theorem W1omega0_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ 0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0
      ∧ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0 ≤ C * _root_.BoseGases.a v := by
  have hWnn : ∀ᵐ z ∂(volume : Measure ℝ³), 0 ≤ Work.BoseFixR.W1omegaFun v h ℓ z := by
    filter_upwards [W1omegaNum_nonneg_ae hR hv_nonneg hvrad hv_supp h] with z hz
    rw [W1omegaFun_eq]
    dsimp only [Submission.BoseGases.wScaled]
    rw [div_eq_mul_inv]
    exact mul_nonneg hz (inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg ℓ z))
  refine ⟨16 * π, by positivity, ?_, ?_⟩
  · rw [chat_zero]
    exact MeasureTheory.integral_nonneg_of_ae hWnn
  · rw [chat_zero]
    calc (∫ z, Work.BoseFixR.W1omegaFun v h ℓ z)
        = ∫ z, |Work.BoseFixR.W1omegaFun v h ℓ z| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hWnn] with z hz
          exact (abs_of_nonneg hz).symm
      _ ≤ 16 * π * _root_.BoseGases.a v :=
          W1omega_abs_integral_le hR hℓ hv_nonneg hvrad hv_supp h hRℓ

end

end Work.BoseB7AK.W1rows
