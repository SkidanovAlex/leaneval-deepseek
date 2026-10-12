import ChallengeDeps
import Mathlib.Analysis.Convolution
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Conv3SmallGlobal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Executable eq:appw1sliding — the exact weighted sliding triple integral

(Work-in-progress module; Session-195.  Companion to `DLSmallKernels`.)

FS `final_v2.tex` eq:appw1sliding asserts the sliding identity
`∭w_{1,B(u)} = ℓ³∫g = 8πaℓ³`.  As recorded in SmallBoxDesignNote.md
(Session-194 scoping analysis) the EXACT computation in the corpus
transcription (u-integration first cancels the `(χ_M⋆χ_M)(·/(ℓd))`
denominator exactly, leaving `∫∫_xy χ_M(x/ℓ)χ_M(y/ℓ)g(x−y)`; then the
`w := x−y` substitution + ℓ-scaling `chiSmall_conv_fibre`) gives, EXACTLY,

    ∫_x∫_y∫_u wSmallPair M ℓ d u h x y
        = ℓ³ · ∫_w h(w)·(χ_M⋆χ_M)(w/ℓ) dw

— the `(χ_M⋆χ_M)(w/ℓ)` weight (at `w = 0` equal to `∫χ_M² = 1`, by
`chiSmall_L2`) survives because the surviving `x,y`-product has both
`χ_M`-factors at the BIG scale `ℓ` while the convolution from the `u`-sliding
appeared at the small scale `ℓd` and cancelled against the `W`-denominator.

This module machine-checks that exact weighted identity (the `h`-generic
form + the corpus `h := g₀`/`wSmall1Pair` specialisation):

  * `chiSmall_pair_double`:  the `u`-cancelled double integral
    `∫_x∫_y χ_M(x/ℓ)χ_M(y/ℓ)h(x−y) = ℓ³·∫h(w)(χ⋆χ)_M(w/ℓ)dw`
    (mirror of `kernel_double_integral` with the denominator
    cancelled — needs only `Integrable h`, no support regime);
  * `dlPair_triple_uInner`:  the full sliding triple (u innermost, corpus
    convention cf. `DLInfra.chiB_double_integral_u_sq`)
    `∫_x∫_y∫_u wSmallPair M ℓ d u h x y = ℓ³·∫h(w)(χ⋆χ)_M(w/ℓ)dw`
    under the `R ≤ (ℓd)/16` renormalisation regime (uses the Session-194
    cancellation `chiSmallB_w_pair_uint_cancel`);
  * `dlW1Pair_triple_uInner`: the `h := g₀` specialisation — the exact
    eq:appw1sliding form for the corpus one-body kernel `wSmall1Pair`.

The transcribed-FS conclusion `∭w_{1,B(u)} = 8πaℓ³` then follows from this
weighted form once the `(χ⋆χ)(w/ℓ)`-weight is estimated against `1` on the
support of `g₀` (an `O((R/ℓ)²)`-error lemma — next layer, see the design
note); note the weight is EXACTLY `1` at `w = 0` since `∫χ_M² = 1`
(`chiSmall_L2`) and `(χ⋆χ)` is even, so the error is quadratic, not
constant.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the dilation `x ↦ c⁻¹•x` is continuous (for `c ≠ 0`). -/
lemma chiSmall_dilation_continuous {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun x : ℝ³ => chiSmall M (c⁻¹ • x)) := by
  have hφ : Continuous (fun x : ℝ³ => c⁻¹ • x) :=
    (Homeomorph.smulOfNeZero (c⁻¹) (inv_ne_zero hc)).continuous
  exact (chiSmall_continuous hM).comp hφ

/-- the dilation `x ↦ c⁻¹•x` of the bump has compact support (for `c ≠ 0`). -/
lemma chiSmall_dilation_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (fun x : ℝ³ => chiSmall M (c⁻¹ • x)) := by
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.smulOfNeZero (c⁻¹) (inv_ne_zero hc)
  convert (chiSmall_hasCompactSupport hM).comp_homeomorph φ using 1
  ext x
  simp [φ, Homeomorph.smulOfNeZero]

/-- the dilated bump `x ↦ χ_M(c⁻¹•x)` is integrable on `ℝ³`. -/
lemma chiSmall_dilation_integrable {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun x : ℝ³ => chiSmall M (c⁻¹ • x)) := by
  exact Continuous.integrable_of_hasCompactSupport
    (chiSmall_dilation_continuous hM hc) (chiSmall_dilation_hasCompactSupport hM hc)

/-- The `(x,w)`-product integrand `(x,w) ↦ χ_M(x/ℓ)·χ_M((x−w)/ℓ)·h(w)` is
AE strongly measurable on `ℝ³ × ℝ³`. -/
lemma chiSmall_prod_AEStronglyMeasurable {M : ℕ} (hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ℝ³ → ℝ) (hh : MeasureTheory.Integrable h) :
    AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  let μ : Measure ℝ³ := volume
  have hc1 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1)) :=
    (chiSmall_dilation_continuous hM (ne_of_gt hℓ)).comp continuous_fst
  have hc2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • (p.1 - p.2))) :=
    (chiSmall_dilation_continuous hM (ne_of_gt hℓ)).comp (continuous_fst.sub continuous_snd)
  have hAE1 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1)) (μ.prod μ) :=
    hc1.aestronglyMeasurable (μ := μ.prod μ)
  have hAE2 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • (p.1 - p.2))) (μ.prod μ) :=
    hc2.aestronglyMeasurable (μ := μ.prod μ)
  have hAE0 : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2))) (μ.prod μ) :=
    hAE1.mul hAE2
  have hAEh : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => h p.2) (μ.prod μ) := by
    simpa [μ] using (hh.aestronglyMeasurable.comp_snd (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³)))
  have hF : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2)
      (μ.prod μ) :=
    hAE0.mul hAEh
  simpa [μ] using hF

/-- The `(x,w)`-product integrand is integrable on `ℝ³ × ℝ³`: dominated by
`((χ_M⋆χ_M)-bound · χ_M(x/ℓ)) · |h(w)|`, with `x ↦ χ_M(x/ℓ)` integrable
(`χ_M` continuous, compactly supported, dilated). -/
lemma chiSmall_prod_integrable {M : ℕ} (hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ℝ³ → ℝ) (hh : MeasureTheory.Integrable h) :
    MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  let μ : Measure ℝ³ := volume
  let D : ℝ := chiSmallDecay M
  have hDpos : 0 < D := by
    dsimp [D, chiSmallDecay, chiSmallNormFactor]
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (chiSmallNormSq_pos hM))) (pow_pos (by norm_num) M)
  have hsup : ∀ x : ℝ³, |chiSmall M (ℓ⁻¹ • x)| ≤ D := by
    intro x
    exact chiSmall_decay_coord_le_decay hM (ℓ⁻¹ • x)
  have hdom : ∀ p : ℝ³ × ℝ³,
      |chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2|
        ≤ (D * chiSmall M (ℓ⁻¹ • p.1)) * |h p.2| := by
    intro p
    calc
      |chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2|
          = |chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2))| * |h p.2| := by rw [abs_mul]
      _ = (|chiSmall M (ℓ⁻¹ • p.1)| * |chiSmall M (ℓ⁻¹ • (p.1 - p.2))|) * |h p.2| := by rw [abs_mul]
      _ = (chiSmall M (ℓ⁻¹ • p.1) * |chiSmall M (ℓ⁻¹ • (p.1 - p.2))|) * |h p.2| := by
          rw [abs_of_nonneg (chiSmall_nonneg M (ℓ⁻¹ • p.1))]
      _ ≤ (chiSmall M (ℓ⁻¹ • p.1) * D) * |h p.2| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsup (p.1 - p.2)) (chiSmall_nonneg M (ℓ⁻¹ • p.1)))
            (abs_nonneg (h p.2))
      _ ≤ (D * chiSmall M (ℓ⁻¹ • p.1)) * |h p.2| := by
          have heq : (chiSmall M (ℓ⁻¹ • p.1) * D) * |h p.2|
                    = (D * chiSmall M (ℓ⁻¹ • p.1)) * |h p.2| := by ring
          rw [heq]
  have hfg : Integrable
      (fun p : ℝ³ × ℝ³ => (D * chiSmall M (ℓ⁻¹ • p.1)) * |h p.2|) (μ.prod μ) := by
    have hχint : Integrable (fun x : ℝ³ => chiSmall M (ℓ⁻¹ • x)) μ := by
      simpa [μ] using chiSmall_dilation_integrable hM (ne_of_gt hℓ)
    have hf : Integrable (fun x : ℝ³ => D * chiSmall M (ℓ⁻¹ • x)) μ := hχint.const_mul D
    have hg : Integrable (fun z : ℝ³ => |h z|) μ := hh.abs
    exact hf.mul_prod hg
  refine Integrable.mono hfg (chiSmall_prod_AEStronglyMeasurable hM hℓ h hh) ?_
  filter_upwards with p
  simpa [D, abs_of_pos hDpos, abs_of_nonneg (chiSmall_nonneg M (ℓ⁻¹ • p.1)),
         mul_assoc, mul_left_comm, mul_comm] using hdom p

/-- **The `u`-cancelled double integral (exact weighted sliding atom)**:
for integrable `h` (no support regime needed),

    ∫_x∫_y χ_M(x/ℓ)·χ_M(y/ℓ)·h(x−y) dxdy = ℓ³·∫_w h(w)·(χ_M⋆χ_M)(w/ℓ) dw

Proof: substitute `w := x−y` in the `y`-integral (`integral_comp_sub_left`),
swap `x` and `w` (Fubini, `chiSmall_prod_integrable`), and evaluate the inner
fibre `∫_x χ_M(x/ℓ)χ_M((x−w)/ℓ) dx = ℓ³(χ_M⋆χ_M)(w/ℓ)`
(`chiSmall_conv_fibre`). -/
lemma chiSmall_pair_double {M : ℕ} (hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ℝ³ → ℝ) (hh : MeasureTheory.Integrable h) :
    (∫ x : ℝ³, ∫ y : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • y) * h (x - y))
      = ℓ ^ 3 * (∫ w : ℝ³, h w * conv3Small M (ℓ⁻¹ • w)) := by
  have hsub : ∀ x : ℝ³,
      (∫ y : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • y) * h (x - y))
        = ∫ w : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w := by
    intro x
    let Mf : ℝ³ → ℝ := fun y => chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • y) * h (x - y)
    calc
      (∫ y : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • y) * h (x - y))
          = ∫ y : ℝ³, Mf y := by rfl
      _ = ∫ w : ℝ³, Mf (x - w) := (integral_comp_sub_left (g := Mf) x).symm
      _ = ∫ w : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w := by
          apply integral_congr_ae
          exact ae_of_all _ (by
            intro w
            dsimp [Mf]
            rw [show x - (x - w) = w by abel])
  calc
    (∫ x : ℝ³, ∫ y : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • y) * h (x - y))
        = ∫ x : ℝ³, (∫ w : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w) := by
            apply integral_congr_ae
            exact ae_of_all _ (by intro x; exact hsub x)
    _ = ∫ w : ℝ³, (∫ x : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w) := by
            have hInt : Integrable
                (fun p : ℝ³ × ℝ³ => chiSmall M (ℓ⁻¹ • p.1) * chiSmall M (ℓ⁻¹ • (p.1 - p.2)) * h p.2)
                ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
              chiSmall_prod_integrable hM hℓ h hh
            have hswap := MeasureTheory.integral_integral_swap
              (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
              (f := fun x w : ℝ³ => chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w) hInt
            simpa [Function.uncurry] using hswap
    _ = ∫ w : ℝ³, ℓ ^ 3 * (h w * conv3Small M (ℓ⁻¹ • w)) := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro w
              have hz := chiSmall_conv_fibre hM hℓ w
              calc
                (∫ x : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w)
                    = h w * (∫ x : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w))) := by
                        have hpt : (fun x : ℝ³ => chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w)) * h w)
                                 = fun x : ℝ³ => h w * (chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - w))) := by
                          funext x
                          ring
                        rw [hpt, integral_const_mul]
                _ = h w * (ℓ ^ 3 * conv3Small M (ℓ⁻¹ • w)) := by rw [hz]
                _ = ℓ ^ 3 * (h w * conv3Small M (ℓ⁻¹ • w)) := by ring)
    _ = ℓ ^ 3 * (∫ w : ℝ³, h w * conv3Small M (ℓ⁻¹ • w)) := by
            rw [integral_const_mul]

/-- **The exact weighted sliding triple integral (u innermost, corpus
convention)** at the REPOINTED kernels: under the renormalisation regime
`R ≤ (ℓd)/16` (numerator `h` supported in `ball 0 R`) plus the `ℓ`-scale
regime needed for the corpus denominator (`R ≤ ℓr₀`, `(χ⋆χ) ≥ 1/2` on
`ball 0 r₀`),

    ∫_x∫_y∫_u wSmallPair M ℓ d u h x y = ℓ³·∫_w h w

(u-integration first: `chiSmallB_w_pair_uint_cancel` cancels the
`(χ_M⋆χ_M)(·/(ℓd))` denominator *and* produces the corpus renormalisation
`1/(χ⋆χ)(·/ℓ)`; the resulting double integral is the corpus global kernel
`wPairC ℓ h`, whose `χ`-renormalisation cancels exactly —
`kernel_double_integral`). -/
lemma dlPair_triple_uInner {M : ℕ} (hM : 1 ≤ M) {ℓ d R r₀ : ℝ} {h : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hh : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hR : R ≤ (ℓ * d) / 16)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    (∫ x : ℝ³, ∫ y : ℝ³, ∫ u : ℝ³, wSmallPair M ℓ d u h x y)
      = ℓ ^ 3 * (∫ w : ℝ³, h w) := by
  have hcancel (x y : ℝ³) :
      (∫ u : ℝ³, wSmallPair M ℓ d u h x y)
        = chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)) :=
    chiSmallB_w_pair_uint_cancel hM hℓ hd hsupp hR x y
  calc
    (∫ x : ℝ³, ∫ y : ℝ³, ∫ u : ℝ³, wSmallPair M ℓ d u h x y)
        = (∫ x : ℝ³, ∫ y : ℝ³,
            chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y))) := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro x
              apply integral_congr_ae
              exact ae_of_all _ (by intro y; exact hcancel x y))
    _ = ℓ ^ 3 * (∫ w : ℝ³, h w) :=
            kernel_double_integral h hℓ hh hsupp hr₀ hRℓ hC

/-- **The eq:appw1sliding weighted form for the corpus one-body kernel
`wSmall1Pair`** (numerator `g₀ = v(1−ω₀)`), at the repointed kernels: under
`tsupport v ⊆ ball 0 R0`, `0 < R0`, the regime `R0 ≤ (ℓd)/16` and the
`ℓ`-scale regime,

    ∫_x∫_y∫_u wSmall1Pair h M ℓ d u x y = ℓ³·∫_w g₀(w) dw . -/
lemma dlW1Pair_triple_uInner {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d r₀ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hr₀ : 0 < r₀) (hRℓ : R0 ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    (∫ x : ℝ³, ∫ y : ℝ³, ∫ u : ℝ³, wSmall1Pair h M ℓ d u x y)
      = ℓ ^ 3 * (∫ w : ℝ³, g0 v h w) := by
  unfold wSmall1Pair
  exact dlPair_triple_uInner (h := g0 v h) hM hℓ hd (g0_integrable hR0 hv_supp h)
    (fun z hz => g0_zero_of_norm_ge (v := v) (R := R0) hv_supp hz h) hR hr₀ hRℓ hC

/-- continuity of the cosine-M self-convolution (`χ_M⋆χ_M`): from
`HasCompactSupport.continuous_convolution_right` (χ_M continuous with
compact support). -/
lemma conv3Small_continuous {M : ℕ} (hM : 1 ≤ M) : Continuous (fun x : ℝ³ => conv3Small M x) := by
  have hf : MeasureTheory.LocallyIntegrable (chiSmall M) :=
    (chiSmall_continuous hM).locallyIntegrable
  have hc := HasCompactSupport.continuous_convolution_right
    (L := ContinuousLinearMap.mul ℝ ℝ) (f := chiSmall M) (g := chiSmall M)
    (μ := (volume : Measure ℝ³)) (chiSmall_hasCompactSupport hM) hf (chiSmall_continuous hM)
  have heq : (fun x : ℝ³ => conv3Small M x)
      = MeasureTheory.convolution (chiSmall M) (chiSmall M) (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure ℝ³) := by
    funext x
    unfold conv3Small
    rw [MeasureTheory.convolution_def]
    simp
  rwa [heq]

/-- **weight-deviation integrand bound** (UNCONDITIONAL since Session-264):
with the universal constant `convDevC M` of the global quadratic deviation
of the convolution weight (`convDevC_bound`, `3 ≤ M`), on the support of
`g₀` the weighted mass deviates from the unweighted one by at most
`|g₀|·convDevC M·(R0/ℓ)²` — pointwise everywhere.  (No `hdev`-hypothesis
and no support/regime restriction.) -/
lemma g0_weight_dev_pointwise {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 3 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ w : ℝ³, |g0 v h w * (conv3Small M (ℓ⁻¹ • w) - 1)|
      ≤ |g0 v h w| * (convDevC M * (R0 / ℓ) ^ 2) := by
  set C : ℝ := convDevC M with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; exact convDevC_nonneg M
  have hdev : ∀ t : ℝ³, ‖t‖ ≤ R0 / ℓ → ‖conv3Small M t - 1‖ ≤ C * ‖t‖ ^ 2 :=
    fun t _ => by rw [hCdef]; exact convDevC_bound hM t
  intro w
  by_cases hw0 : g0 v h w = 0
  · simp [hw0]
  · have hwR : ‖w‖ < R0 := by
      by_contra hnot
      have hge : R0 ≤ ‖w‖ := le_of_not_gt hnot
      exact hw0 (g0_zero_of_norm_ge (v := v) (R := R0) hv_supp hge h)
    have htw : ‖ℓ⁻¹ • w‖ ≤ R0 / ℓ := by
      calc
        ‖ℓ⁻¹ • w‖ = ℓ⁻¹ * ‖w‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
        _ = ‖w‖ / ℓ := by field_simp [ne_of_gt hℓ]
        _ ≤ R0 / ℓ := le_of_lt (div_lt_div_of_pos_right hwR hℓ)
    have hdev' : ‖conv3Small M (ℓ⁻¹ • w) - 1‖ ≤ C * (R0 / ℓ) ^ 2 := by
      have h1 := hdev (ℓ⁻¹ • w) htw
      have hnorm0 : 0 ≤ ‖ℓ⁻¹ • w‖ := norm_nonneg _
      have hsq : ‖ℓ⁻¹ • w‖ ^ 2 ≤ (R0 / ℓ) ^ 2 :=
        pow_le_pow_left₀ hnorm0 htw 2
      have hmul : C * ‖ℓ⁻¹ • w‖ ^ 2 ≤ C * (R0 / ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hC
      exact le_trans h1 hmul
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdev' (abs_nonneg _)

/-- **mass gap of the weighted `g₀`-mass** (UNCONDITIONAL since Session-264):
using the global quadratic deviation `‖(χ_M⋆χ_M)(t) − 1‖ ≤ convDevC M·‖t‖²`
(`convDevC_bound`) restricted to the corpus range,

    |∫_w g₀(w)·(χ_M⋆χ_M)(w/ℓ) − ∫_w g₀(w)| ≤ convDevC M·(R0/ℓ)²·8π·a v . -/
lemma g0_weight_mass_gap {v : ℝ³ → ℝ} {R0 : ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 3 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    |(∫ w : ℝ³, g0 v h w * conv3Small M (ℓ⁻¹ • w)) - (∫ w : ℝ³, g0 v h w)|
      ≤ convDevC M * (R0 / ℓ) ^ 2 * (8 * π * a v) := by
  set C : ℝ := convDevC M with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; exact convDevC_nonneg M
  have hdev : ∀ t : ℝ³, ‖t‖ ≤ R0 / ℓ → ‖conv3Small M t - 1‖ ≤ C * ‖t‖ ^ 2 :=
    fun t _ => by rw [hCdef]; exact convDevC_bound hM t
  let c : ℝ := C * (R0 / ℓ) ^ 2
  have hc0 : 0 ≤ c := by dsimp [c]; exact mul_nonneg hC (sq_nonneg _)
  let F : ℝ³ → ℝ := fun w => g0 v h w * (conv3Small M (ℓ⁻¹ • w) - 1)
  have hg0meas : AEStronglyMeasurable (g0 v h) := (g0_integrable hR0 hv_supp h).aestronglyMeasurable
  have hφ : Continuous (fun w : ℝ³ => ℓ⁻¹ • w) :=
    (Homeomorph.smulOfNeZero (ℓ⁻¹) (inv_ne_zero (ne_of_gt hℓ))).continuous
  have hwmeas : AEStronglyMeasurable (fun w : ℝ³ => conv3Small M (ℓ⁻¹ • w)) :=
    ((conv3Small_continuous (by omega : 1 ≤ M)).comp hφ).aestronglyMeasurable
  have hconst1 : AEStronglyMeasurable (fun _ : ℝ³ => (1 : ℝ)) :=
    continuous_const.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable F := by
    dsimp [F]
    exact hg0meas.mul (hwmeas.sub hconst1)
  have hFabsMeas : AEStronglyMeasurable (fun w : ℝ³ => |F w|) := by
    have hn : AEStronglyMeasurable (fun w : ℝ³ => ‖F w‖) := hFmeas.norm
    simpa [Real.norm_eq_abs] using hn
  have hpt : ∀ w : ℝ³, |F w| ≤ |g0 v h w| * c := by
    intro w
    dsimp [F, c]
    exact g0_weight_dev_pointwise hv_supp h hM hℓ w
  have hpt2 : ∀ w : ℝ³, |F w| ≤ c * |g0 v h w| := by
    intro w
    simpa [mul_comm] using hpt w
  have hg0int : Integrable (fun w : ℝ³ => |g0 v h w|) := (g0_integrable hR0 hv_supp h).abs
  have hg0cL : Integrable (fun w : ℝ³ => c * |g0 v h w|) := hg0int.const_mul c
  have hFabs : Integrable (fun w : ℝ³ => |F w|) := by
    refine Integrable.mono' hg0cL ?hmeas ?hbd
    · exact hFabsMeas
    · filter_upwards with w
      simpa [Real.norm_eq_abs] using hpt2 w
  have hAint : Integrable (fun w : ℝ³ => g0 v h w * conv3Small M (ℓ⁻¹ • w)) := by
    have hbd : ∀ᵐ w : ℝ³, ‖g0 v h w * conv3Small M (ℓ⁻¹ • w)‖ ≤ (1 + c) * |g0 v h w| := by
      filter_upwards with w
      have htri : |g0 v h w * conv3Small M (ℓ⁻¹ • w)| ≤ |F w| + |g0 v h w| := by
        have h : g0 v h w * conv3Small M (ℓ⁻¹ • w) = F w + g0 v h w := by dsimp [F]; ring
        rw [h]
        exact abs_add_le _ _
      have hb : |F w| ≤ c * |g0 v h w| := hpt2 w
      rw [Real.norm_eq_abs]
      nlinarith [htri, hb, mul_nonneg hc0 (abs_nonneg (g0 v h w))]
    have hg0c1 : Integrable (fun w : ℝ³ => (1 + c) * |g0 v h w|) := hg0int.const_mul (1 + c)
    have hAmeas : AEStronglyMeasurable (fun w : ℝ³ => g0 v h w * conv3Small M (ℓ⁻¹ • w)) :=
      hg0meas.mul hwmeas
    exact Integrable.mono' hg0c1 hAmeas hbd
  have hsub : (∫ w : ℝ³, g0 v h w * conv3Small M (ℓ⁻¹ • w)) - (∫ w : ℝ³, g0 v h w)
      = ∫ w : ℝ³, F w := by
    have h1 := MeasureTheory.integral_sub (μ := (volume : Measure ℝ³))
      (f := fun w : ℝ³ => g0 v h w * conv3Small M (ℓ⁻¹ • w)) (g := g0 v h) hAint
      (g0_integrable hR0 hv_supp h)
    rw [← h1]
    apply integral_congr_ae
    exact ae_of_all _ (by intro w; dsimp [F]; ring)
  have hg0nn : ∀ᵐ w : ℝ³, 0 ≤ g0 v h w := g0_nonneg_ae hR0 hv_nonneg hvrad hv_supp h
  have hcongr : (fun w : ℝ³ => |g0 v h w|) =ᵐ[volume] (fun w : ℝ³ => g0 v h w) := by
    filter_upwards [hg0nn] with w hw
    exact abs_of_nonneg hw
  calc
    |(∫ w : ℝ³, g0 v h w * conv3Small M (ℓ⁻¹ • w)) - (∫ w : ℝ³, g0 v h w)|
        = |∫ w : ℝ³, F w| := by rw [hsub]
    _ ≤ ∫ w : ℝ³, |F w| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ w : ℝ³, c * |g0 v h w| := by
            exact MeasureTheory.integral_mono_ae hFabs hg0cL (by filter_upwards with w; exact hpt2 w)
    _ = c * (∫ w : ℝ³, |g0 v h w|) := by rw [MeasureTheory.integral_const_mul]
    _ = c * (∫ w : ℝ³, g0 v h w) := by rw [MeasureTheory.integral_congr_ae hcongr]
    _ = c * (8 * π * a v) := by rw [g0_integral hR0 hv_supp h]
    _ = C * (R0 / ℓ) ^ 2 * (8 * π * a v) := by simp [c]


/-- **eq:appw1sliding with the quadratic weight error (corpus form)** at the
REPOINTED kernels: the sliding triple integral of the one-body kernel
`wSmall1Pair` (`w_{1,B(u)}`) satisfies

    | ∭_u,x,y w_{1,B(u)} − 8π(a v)·ℓ³ | ≤ convDevC M·(R0/ℓ)²·8π(a v)·ℓ³ ,

i.e. FS's `∭w_{1,B(u)} = ℓ³∫g = 8πaℓ³`.  At the repointed kernels the
renormalisation makes the identity EXACT (`dlW1Pair_triple_uInner` gives
`∭w₁ = ℓ³∫g₀` and `g0_integral` gives `∫g₀ = 8πa v`), so the left-hand side
is `0` and the stated (corpus) bound holds with the quadratic weight term as
a slack. -/
lemma dlW1Pair_triple_mass_gap {v : ℝ³ → ℝ} {R0 : ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 3 ≤ M) {ℓ d r₀ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hr₀ : 0 < r₀) (hRℓ : R0 ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    |(∫ x : ℝ³, ∫ y : ℝ³, ∫ u : ℝ³, wSmall1Pair h M ℓ d u x y) - 8 * π * a v * ℓ ^ 3|
      ≤ convDevC M * (R0 / ℓ) ^ 2 * (8 * π * a v) * ℓ ^ 3 := by
  have htri := dlW1Pair_triple_uInner (v := v) (R0 := R0) hv_supp hR0 h
    (M := M) (by omega : 1 ≤ M) hℓ hd hR hr₀ hRℓ hC
  have hgi := g0_integral hR0 hv_supp h
  have ha0 : 0 ≤ 8 * π * a v := by
    rw [← hgi]
    exact integral_nonneg_of_ae (g0_nonneg_ae hR0 hv_nonneg hvrad hv_supp h)
  have hrhs : 0 ≤ convDevC M * (R0 / ℓ) ^ 2 * (8 * π * a v) * ℓ ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (convDevC_nonneg M) (sq_nonneg _)) ha0)
      (pow_nonneg hℓ.le 3)
  have hzero : (∫ x : ℝ³, ∫ y : ℝ³, ∫ u : ℝ³, wSmall1Pair h M ℓ d u x y)
      - 8 * π * a v * ℓ ^ 3 = 0 := by
    rw [htri, hgi]
    ring
  rw [hzero, abs_zero]
  exact hrhs

end BoseGases

end Submission
