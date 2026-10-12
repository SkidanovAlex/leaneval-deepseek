import Mathlib
import ChallengeDeps
import Submission.KernelMean
import Submission.Q0Chosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — pointwise fibre bounds of the χ-renormalized kernels

FS `lm:potapp` (`eq:app1bd` and the `eq:Q'app1/2`/`eq:Q'app` family,
final_v2.tex ~1130–1230) bounds the one-body and mixed-sector potential
terms by constants times `a·μ·n`, `a·n²/ℓ³`, … using three elementary
kernel facts:

  1. the **fibre bound**: with `K := sup‖χ‖` and the dilute regime
     `R ≤ ℓ·chiR0` (where `(χ⋆χ)_ℓ ≥ 1/2` on the support of `h`,
     `ChiWitness.convScale_ge_half_ball`),

         |∫_y wPair(ℓ,h)(x,y) dy| ≤ (2·K²)·∫|h|                     (fibre bound)

     (`wPair(ℓ,h)(x,y) = χ_ℓ(x)χ_ℓ(y)·h(x−y)/(χ⋆χ)_ℓ(x−y)`;
     `|h/(χ⋆χ)_ℓ| ≤ 2|h|` = `wScaled_abs_le_two`, `|χ_ℓ| ≤ K` =
     `abs_chiScale_le`; `∫|h(x−·)| = ∫|h|` by translation);
  2. the **positivity** of `wPair(ℓ,h)` when `h ≥ 0` a.e.
     (`χ_ℓ ≥ 0`, `(χ⋆χ)_ℓ ≥ 0` everywhere);
  3. the **one-body expectation bound**: for continuous `Φ`,

         |Σ_i ∫_{abox}(P_iΦ)²·(∫_y wPair(xᵢ,y))| ≤ (2K²∫|h|)·Σ_i∫(P_iΦ)² .

  All statements are written with `h` merely **integrable** (no `Measurable`
  hypothesis), matching the chosen numerators `g₀ = v(1−w₀)`,
  `g₂ = g₀(1+w₀)` (`ScatKernelChosen`), which are only integrable.

  `K := chiSup = (∫χ²)⁻¹/²` is the pointwise sup-bound of `χ`
  (`chi_le_sqrt_inv`, `abs_chiScale_le` in `KernelIds`).

## Route notes (for the child)

* Start from `KernelMean.wScaled_abs_le_two` (`|wScaled ℓ h z| ≤ 2|h z|`),
  `KernelIds.abs_chiScale_le`, `KernelMean.km_measurePreserving_sub_left`
  (translation), and integrability of `wScaled`/`χℓ·wScaled` (build
  `wScaled_integrable_ae` and `kernel_fibre_integrable_ae`, mirroring
  `KernelMean.wScaled_integrable`/`kernel_fibre_integrable` but with
  `Integrable h` instead of `Measurable h`: use
  `MeasureTheory.Integrable.aestronglyMeasurable` and the `.mk`-route of
  `Submission.AeValue` if needed).
* `fibre_integral_abs_le`: split `wPair = χ_ℓ(x)·χ_ℓ(y)·wScaled(x−y)`; take
  `|·|` inside; bound `|χ_ℓ(x)|,|χ_ℓ(y)| ≤ chiSup`; substitute
  `z := x−y` (`y ↦ x−y` measure-preserving) and use the domination.
* `fibre_acube_abs_le`: `mean_kernel_full` identifies the cube integral with
  the full-space integral (valid once the full-space fibre is integrable).
* `fibre_integral_nonneg_of_ae`: from `0 ≤ h` a.e., `χ_ℓ ≥ 0` everywhere
  (`chiScale_nonneg`), `(χ⋆χ)_ℓ ≥ 0` everywhere (`conv3chi_nonneg`), and
  `(χ⋆χ)_ℓ ≥ 1/2` on the support of `h` (dilute regime), the integrand is
  `≥ 0` a.e.; use `integral_nonneg_of_ae` / `setIntegral_nonneg_ae`.
* Chosen instantiations: `g₀ ≥ 0` a.e. and `g₂ ≥ 0` a.e. with the standing
  chosen-branch hypotheses (`ScatT3.scattering_bounds_ae`,
  `ScatT3.scattering_g_nonneg`, `ScatKernelChosen.g0_integral`:
  `∫g₀ = 8πa v`, `g2_integral_bounds`: `8πa v ≤ ∫g₂ ≤ 16πa v`,
  `g0_zero_of_norm_ge`/`g2_zero_of_norm_ge`, and `0 ≤ a v` from
  `chosen_av_bounds_weak`); `∫|g₀| = ∫g₀` etc. by a.e.-nonnegativity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise sup-bound of `χ`: `K := (∫χ²)⁻¹/² > 0`. -/
noncomputable def chiSup : ℝ := (Real.sqrt chiNormSq)⁻¹

/-- `0 < chiSup`. -/
lemma chiSup_pos : 0 < chiSup := by
  unfold chiSup
  exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)

/-- `|χ_ℓ x| ≤ chiSup`. -/
lemma abs_chiScale_le_chiSup (ℓ : ℝ) (x : ℝ³) : |chiScale ℓ x| ≤ chiSup := by
  unfold chiSup
  exact abs_chiScale_le ℓ x


/-- Pulling back an a.e. statement along the measure-preserving reflection
`y ↦ x − y`. -/
lemma ae_comp_sub_left {p : ℝ³ → Prop} (hp : ∀ᵐ z ∂(volume : Measure ℝ³), p z) (x : ℝ³) :
    ∀ᵐ y ∂(volume : Measure ℝ³), p (x - y) := by
  rw [MeasureTheory.ae_iff]
  let T : ℝ³ → ℝ³ := fun y => x - y
  let N : Set ℝ³ := {z : ℝ³ | ¬ p z}
  have hN : (volume : Measure ℝ³) N = 0 := MeasureTheory.ae_iff.mp hp
  have hNm : MeasureTheory.NullMeasurableSet N (volume : Measure ℝ³) :=
    MeasureTheory.NullMeasurableSet.of_null hN
  have hset : {y : ℝ³ | ¬ p (x - y)} = T ⁻¹' N := by
    ext y
    simp [T, N]
  rw [hset]
  have hmap : (volume : Measure ℝ³).map T = (volume : Measure ℝ³) :=
    (km_measurePreserving_sub_left x).map_eq
  rw [MeasureTheory.Measure.measure_preimage_of_map_eq_self (μ := (volume : Measure ℝ³)) hmap
    (km_measurePreserving_sub_left x).measurable.aemeasurable hNm]
  exact hN

/-- A.e.-version of `wScaled`-integrability: `h` integrable (not necessarily
measurable) with the dilute-regime support hypotheses. -/
lemma wScaled_integrable_ae {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) :
    MeasureTheory.Integrable (wScaled ℓ h) := by
  have hWm : AEStronglyMeasurable (wScaled ℓ h) := by
    have hinvmeas : Measurable (fun z : ℝ³ => (convScale ℓ z)⁻¹) := by
      have hinv : Measurable fun t : ℝ => t⁻¹ := by fun_prop
      exact hinv.comp (convScale_continuous ℓ).measurable
    have hAEinv : AEStronglyMeasurable (fun z : ℝ³ => (convScale ℓ z)⁻¹) :=
      hinvmeas.aestronglyMeasurable
    have hEq : wScaled ℓ h = fun z : ℝ³ => h z * (convScale ℓ z)⁻¹ := by
      funext z
      dsimp [wScaled]
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hi.aestronglyMeasurable.mul hAEinv
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³), ‖wScaled ℓ h z‖ ≤ 2 * |h z| := by
    refine ae_of_all _ ?_
    intro z
    simpa [Real.norm_eq_abs] using wScaled_abs_le_two hℓ hR hRℓ hsupp z
  exact Integrable.mono' (hi.abs.const_mul (2 : ℝ)) hWm hdom

/-- A.e.-version: the `y`-fibre `χ_ℓ(y)·wScaled(x−y)` is integrable. -/
lemma kernel_fibre_integrable_ae {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (x : ℝ³) :
    MeasureTheory.Integrable (fun y : ℝ³ => chiScale ℓ y * wScaled ℓ h (x - y)) := by
  exact kernel_fibre_integrable hℓ hwi x

/-- **Fibre bound** (full space): `|∫_y wPair(ℓ,h)(x,y)dy| ≤ 2·chiSup²·∫|h|`. -/
lemma fibre_integral_abs_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (x : ℝ³) :
    |∫ y : ℝ³, wPair ℓ h x y| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|) := by
  have hdompt : ∀ y : ℝ³, |wPair ℓ h x y| ≤ chiSup ^ 2 * 2 * |h (x - y)| := by
    intro y
    calc
      |wPair ℓ h x y|
          = |chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y| := rfl
      _ = (|chiScale ℓ x| * |wScaled ℓ h (x - y)|) * |chiScale ℓ y| := by
          rw [abs_mul, abs_mul]
      _ ≤ (chiSup * (2 * |h (x - y)|)) * chiSup := by
          have hinner : |chiScale ℓ x| * |wScaled ℓ h (x - y)|
              ≤ chiSup * (2 * |h (x - y)|) :=
            mul_le_mul (abs_chiScale_le_chiSup ℓ x)
              (wScaled_abs_le_two hℓ hR hRℓ hsupp (x - y))
              (abs_nonneg _) (le_of_lt chiSup_pos)
          exact mul_le_mul hinner (abs_chiScale_le_chiSup ℓ y) (abs_nonneg _)
            (mul_nonneg (le_of_lt chiSup_pos) (mul_nonneg (by norm_num) (abs_nonneg _)))
      _ = chiSup ^ 2 * 2 * |h (x - y)| := by ring
  have hwi : MeasureTheory.Integrable (wScaled ℓ h) := wScaled_integrable_ae hℓ hR hRℓ hi hsupp
  have hwPair_int : MeasureTheory.Integrable (fun y : ℝ³ => wPair ℓ h x y) := by
    have hfib_int := kernel_fibre_integrable hℓ hwi x
    have hcm := hfib_int.const_mul (chiScale ℓ x)
    have hEq : (fun y : ℝ³ => wPair ℓ h x y)
        = fun y : ℝ³ => chiScale ℓ x * (chiScale ℓ y * wScaled ℓ h (x - y)) := by
      funext y
      dsimp [wPair]
      ring
    rw [hEq]
    exact hcm
  have hg : MeasureTheory.Integrable (fun y : ℝ³ => chiSup ^ 2 * 2 * |h (x - y)|) := by
    have hs := km_integrable_comp_sub_left (f := fun z : ℝ³ => |h z|) hi.abs x
    exact hs.const_mul (chiSup ^ 2 * 2)
  calc
    |∫ y : ℝ³, wPair ℓ h x y|
        ≤ ∫ y : ℝ³, |wPair ℓ h x y| := abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ³, chiSup ^ 2 * 2 * |h (x - y)| := by
        exact integral_mono hwPair_int.abs hg hdompt
    _ = chiSup ^ 2 * 2 * (∫ y : ℝ³, |h (x - y)|) := by
        rw [integral_const_mul]
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|) := by
        congr 1
        exact integral_comp_sub_left (fun z : ℝ³ => |h z|) x

/-- **Fibre bound** (over the centred cube, the form used in the box
expectations): `|∫_{acube ℓ} wPair(ℓ,h)(x,y)dy| ≤ 2·chiSup²·∫|h|`. -/
lemma fibre_acube_abs_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (x : ℝ³) :
    |∫ y in acube ℓ, wPair ℓ h x y| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|) := by
  have hwi : MeasureTheory.Integrable (wScaled ℓ h) := wScaled_integrable_ae hℓ hR hRℓ hi hsupp
  rw [mean_kernel_full hℓ hwi x]
  exact fibre_integral_abs_le hℓ hR hRℓ hi hsupp x

/-- **Fibre positivity**: `h ≥ 0` a.e. in the dilute regime makes the
`y`-integral of the kernel nonnegative (per `x`). -/
lemma fibre_integral_nonneg_of_ae {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hnn : ∀ᵐ z : ℝ³, 0 ≤ h z) (x : ℝ³) :
    0 ≤ ∫ y : ℝ³, wPair ℓ h x y := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_comp_sub_left hnn x] with y hy
  have hcsx : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  have hcsy : 0 ≤ chiScale ℓ y := chiScale_nonneg ℓ y
  have hdiv : 0 ≤ h (x - y) / convScale ℓ (x - y) :=
    div_nonneg hy (convScale_nonneg ℓ (x - y))
  dsimp [wPair, wScaled]
  exact mul_nonneg (mul_nonneg hcsx hdiv) hcsy

/-- **One-body expectation bound**: for continuous `Φ` over `abox N ℓ`,
`|Σ_i ∫(P_iΦ)²·(fibre wPair at xᵢ)| ≤ (2·chiSup²·∫|h|)·Σ_i∫(P_iΦ)²`. -/
lemma onebody_expect_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPair ℓ h (x i) y)|
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|)) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  let C : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num))
      (integral_nonneg (f := fun z : ℝ³ => |h z|) (by intro z; exact abs_nonneg _))
  have hbndfib : ∀ (i : Fin N) (x : X N),
      |∫ y in acube ℓ, wPair ℓ h (x i) y| ≤ C := by
    intro i x
    exact fibre_acube_abs_le hℓ hR hRℓ hi hsupp (x i)
  have hmain (i : Fin N) :
      |∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPair ℓ h (x i) y)|
        ≤ C * ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 := by
    let f : X N → ℝ := fun x => (aP ℓ i Φ x) ^ 2
    let g : X N → ℝ := fun x => ∫ y in acube ℓ, wPair ℓ h (x i) y
    have hf0 : ∀ x : X N, 0 ≤ f x := fun x => sq_nonneg _
    have hfg : ∀ x : X N, |f x * g x| = f x * |g x| := by
      intro x
      rw [abs_mul, abs_of_nonneg (hf0 x)]
    have hgi : MeasureTheory.Integrable (fun x : X N => f x * C)
        ((volume : Measure (X N)).restrict (abox N ℓ)) := by
      have hfI : MeasureTheory.Integrable f
          ((volume : Measure (X N)).restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using
          (integrableOn_sq_aP (N := N) hℓ i hΦc : IntegrableOn f (abox N ℓ) volume)
      have hcm := hfI.const_mul C
      simpa [mul_comm] using hcm
    calc
      |∫ x in abox N ℓ, f x * g x|
          ≤ ∫ x in abox N ℓ, |f x * g x| := by
            simpa using (abs_integral_le_integral_abs
              (f := fun x : X N => f x * g x)
              (μ := (volume : Measure (X N)).restrict (abox N ℓ)))
      _ = ∫ x in abox N ℓ, f x * |g x| := by
            apply integral_congr_ae
            exact ae_of_all _ hfg
      _ ≤ ∫ x in abox N ℓ, f x * C := by
            refine integral_mono_of_nonneg
              (μ := (volume : Measure (X N)).restrict (abox N ℓ))
              (f := fun x : X N => f x * |g x|)
              (g := fun x : X N => f x * C) ?_ hgi ?_
            · filter_upwards with x
              exact mul_nonneg (hf0 x) (abs_nonneg _)
            · filter_upwards with x
              exact mul_le_mul_of_nonneg_left (hbndfib i x) (hf0 x)
      _ = C * ∫ x in abox N ℓ, f x := by
            rw [integral_mul_const]
            ring
  calc
    |∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPair ℓ h (x i) y)|
        ≤ ∑ i : Fin N, |∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPair ℓ h (x i) y)| := by
          exact Finset.abs_sum_le_sum_abs (f := fun i : Fin N =>
            ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPair ℓ h (x i) y))
            (s := Finset.univ)
    _ ≤ ∑ i : Fin N, C * ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 := by
          exact Finset.sum_le_sum (fun i _ => hmain i)
    _ = (chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|)) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          rw [Finset.mul_sum]

/-- Chosen-branch headline: the `w₁ := wPair(g₀)` fibre is bounded by
`2·chiSup²·8πa v` (since `∫g₀ = 8πa v ≥ 0`). -/
lemma w1c_fibre_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y : ℝ³, wPair ℓ (g0 v h) x y| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  have hbnd := fibre_integral_abs_le (h := g0 v h) hℓ (le_of_lt hR) hRℓ
    (g0_integrable hR hv_supp h) (fun z hz => g0_zero_of_norm_ge hv_supp hz h) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g0 v h z|) = ∫ z : ℝ³, g0 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  rw [hEq, g0_integral hR hv_supp h] at hbnd
  exact hbnd

/-- Chosen-branch headline: the `w₂ := wPair(g₂)` fibre is bounded by
`2·chiSup²·16πa v` (since `∫g₂ ≤ 16πa v`). -/
lemma w2c_fibre_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y : ℝ³, wPair ℓ (g2 v h) x y| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
  have hbnd := fibre_integral_abs_le (h := g2 v h) hℓ (le_of_lt hR) hRℓ
    (g2_integrable hR hv_nonneg hvrad hv_supp h) (fun z hz => g2_zero_of_norm_ge hv_supp hz h) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g2 v h z|) = ∫ z : ℝ³, g2 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  have hleInt : (∫ z : ℝ³, g2 v h z) ≤ 16 * π * a v :=
    (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).2
  have hnnC : 0 ≤ chiSup ^ 2 * 2 := by
    exact mul_nonneg (sq_nonneg chiSup) (by norm_num)
  calc
    |∫ y : ℝ³, wPair ℓ (g2 v h) x y| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |g2 v h z|) := hbnd
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, g2 v h z) := by rw [hEq]
    _ ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
        exact mul_le_mul_of_nonneg_left hleInt hnnC

end BoseGases

end Submission
