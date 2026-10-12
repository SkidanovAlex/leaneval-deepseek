import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Q0Value
import Submission.ScatKernelChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — instantiating the Q0 kernels with the chosen scattering solution

The Q0 expectation identities (`Q0Value.q0_expect`, `pair_value`, `one_value`)
are stated for abstract measurable kernels `w1,w2` integrable on
`acube ℓ ×ˢ acube ℓ`.  In the Fournais--Solovej analysis these kernels are
the χ-renormalized localized two-body kernels built from the chosen
scattering solution `w₀` (`ScatKernelChosen.g0 := v(1−w₀)`, `g2 := g0(1+w₀)`):

    w_pair(ℓ,h)(x,y) := χ_ℓ(x) · (h(x−y)/C_ℓ(x−y)) · χ_ℓ(y)   (h = g0 or g2)

(`KernelIds.wPair` with `C_ℓ := (χ⋆χ)(·/ℓ)`).  This module proves the
properties needed to feed them into `Q0Value`:

  * support: `wPair ℓ h (x,y) ≠ 0 ⟹ x,y ∈ acube ℓ` (each `χ_ℓ` factor
    vanishes off `acube ℓ`; `Q0Value.chiScale_mem_acube`);
  * measurability and integrability on `acube ℓ ×ˢ acube ℓ` (in the dilute
    regime `R ≤ ℓ·chiR0`, where `C_ℓ ≥ 1/2` on the support of `h`);
  * the double-integral values over `acube ℓ ×ˢ acube ℓ`:

        ∬ w_pair(g0) = ℓ³·∫g0 = 8π·a v·ℓ³                      (eq:DefU)
        ∬ w_pair(g2) = ℓ³·∫g2   ∈ [8π·a v·ℓ³, 16π·a v·ℓ³]      (eq:w2int)

  obtained by combining `Q0Value.prod_integral_eq_full` (support) with the
  full-space values `ScatKernelChosen.kernel_box_g0/g2`.

## Route notes (for the child)

* Vanishing: `wPair ℓ h x y = χ_ℓ x·(h/C)(x−y)·χ_ℓ y`; a nonzero product of
  reals forces each factor nonzero (`mul_ne_zero` etc.), so `χ_ℓ x ≠ 0` and
  `χ_ℓ y ≠ 0`, then `chiScale_support_le` (`KernelIds`) gives
  `‖x‖ ≤ ℓ/2, ‖y‖ ≤ ℓ/2` and `CentreBox.mem_acube_of_norm_le` finishes.
* Integrability: on `‖x−y‖ ≤ R` (where `h(x−y) ≠ 0` may happen) and under
  `R ≤ ℓ·chiR0`, `ChiWitness.convScale_ge_half_ball` gives `1/2 ≤ C_ℓ(x−y)`
  hence `|h/C| ≤ 2|h|`; off that ball `h = 0` (`g0_zero_of_norm_ge` /
  `g2_zero_of_norm_ge`) so `wPair = 0`.  `χ` is bounded (`chi_le_sqrt_inv`
  in `KernelIds` or direct); then `∫∫_{acube²}|wPair| ≤ C·vol·∫|h|` by
  Tonelli/Fubini (the difference map `(x,y) ↦ x−y` and `Integrable h`).
* Values: `Q0Value.prod_integral_eq_full` reduces the acube²-integral to
  the full ℝ³×ℝ³ double integral, which equals the iterated full-space
  integral (`∫ x, ∫ y, wPair ℓ h x y`) by Fubini; then
  `ScatKernelChosen.kernel_box_g0`/`kernel_box_g2` (which give
  `(1/2)ℓ^(-6:ℤ)·(∫x∫y χχ·h/C) = (1/2)ℓ^(-3:ℤ)·∫h`) and
  `g0_integral`/`g2_integral_bounds` finish.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The uncurried χ-renormalized pair kernel with numerator `h`. -/
def wPairU (ℓ : ℝ) (h : ℝ³ → ℝ) (p : ℝ³ × ℝ³) : ℝ := wPair ℓ h p.1 p.2

/-- A nonzero value of the χ-renormalized pair kernel forces both arguments
into the centred cube. -/
lemma wPair_vanishes_off_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} {x y : ℝ³}
    (hw : wPair ℓ h x y ≠ 0) : x ∈ acube ℓ ∧ y ∈ acube ℓ := by
  have hx : chiScale ℓ x ≠ 0 := by
    intro hx0
    apply hw
    simp [wPair, hx0]
  have hy : chiScale ℓ y ≠ 0 := by
    intro hy0
    apply hw
    simp [wPair, hy0]
  exact ⟨chiScale_mem_acube hℓ hx, chiScale_mem_acube hℓ hy⟩

/-- The χ-renormalized pair kernel is measurable as a function on
`ℝ³ × ℝ³` (for measurable `h`). -/
lemma wPairU_measurable {ℓ : ℝ} {h : ℝ³ → ℝ} (hh : Measurable h) :
    Measurable (wPairU ℓ h) := by
  have h1 : Measurable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1) :=
    (chiScale_continuous ℓ).measurable.comp measurable_fst
  have h2 : Measurable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
    (chiScale_continuous ℓ).measurable.comp measurable_snd
  have hsub : Measurable (fun p : ℝ³ × ℝ³ => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hk : Measurable (fun p : ℝ³ × ℝ³ => wScaled ℓ h (p.1 - p.2)) := by
    change Measurable (fun p : ℝ³ × ℝ³ => (h / convScale ℓ) (p.1 - p.2))
    exact ((hh.div (convScale_continuous ℓ).measurable).comp hsub)
  exact (h1.mul hk).mul h2

/-! ## The difference-map measure theory -/

/-- `y ↦ x − y` preserves Lebesgue measure on `ℝ³`. -/
lemma measurePreserving_sub_left (x : ℝ³) :
    MeasurePreserving (fun y : ℝ³ => x - y) volume volume := by
  have hneg : MeasurePreserving (fun y : ℝ³ => -y) volume volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ³)
  have hadd : MeasurePreserving (fun z : ℝ³ => x + z) volume volume :=
    measurePreserving_add_left volume x
  change MeasurePreserving (fun y : ℝ³ => x + (-y)) volume volume
  exact hadd.comp hneg

/-- `y ↦ x − y` is a measurable embedding of `ℝ³`. -/
lemma measurableEmbedding_sub_left (x : ℝ³) :
    MeasurableEmbedding (fun y : ℝ³ => x - y) := by
  let H : ℝ³ ≃ₜ ℝ³ :=
    { toEquiv := { toFun := fun y => x - y, invFun := fun y => x - y,
                   left_inv := by intro y; simp,
                   right_inv := by intro y; simp },
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop }
  have hemb : MeasurableEmbedding (⇑H) := Homeomorph.measurableEmbedding H
  simpa [H] using hemb

/-- Preimages of null sets under `(x,y) ↦ x−y` are null for the product measure. -/
lemma measure_sub_preimage_null (A : Set ℝ³)
    (hA : (volume : Measure ℝ³) A = 0) :
    ((volume : Measure ℝ³).prod (volume : Measure ℝ³))
        ((fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' A) = 0 := by
  let μ : Measure ℝ³ := volume
  let T : Set ℝ³ := toMeasurable μ A
  have hT : MeasurableSet T := measurableSet_toMeasurable μ A
  have hAT : A ⊆ T := subset_toMeasurable μ A
  have hT0 : μ T = 0 := by
    simpa [T] using (measure_toMeasurable (μ := μ) A).trans hA
  have hsub : Measurable (fun p : ℝ³ × ℝ³ => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hpre : MeasurableSet ((fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' T) := hsub hT
  have hslice : ∀ x : ℝ³, μ {y : ℝ³ | x - y ∈ T} = 0 := by
    intro x
    have hmp := measurePreserving_sub_left x
    have hemb := measurableEmbedding_sub_left x
    calc
      μ {y : ℝ³ | x - y ∈ T} = μ ((fun y : ℝ³ => x - y) ⁻¹' T) := by rfl
      _ = μ T := MeasurePreserving.measure_preimage_emb hmp hemb T
      _ = 0 := hT0
  have hprod : (μ.prod μ) ((fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' T) = 0 := by
    rw [Measure.prod_apply hpre]
    apply lintegral_eq_zero_of_ae_eq_zero
    · exact ae_of_all _ (by intro x; exact hslice x)
  have hsubA : (fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' A ⊆
      (fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' T := by
    intro p hp
    exact hAT hp
  exact measure_mono_null hsubA hprod

/-- A.e. equality of functions lifts to their difference precomposition. -/
lemma ae_eq_comp_sub_left {h g : ℝ³ → ℝ} (hg : h =ᵐ[volume] g) :
    (fun p : ℝ³ × ℝ³ => h (p.1 - p.2)) =ᵐ[(volume : Measure ℝ³).prod (volume : Measure ℝ³)]
      fun p : ℝ³ × ℝ³ => g (p.1 - p.2) := by
  have hg' : ∀ᵐ z : ℝ³ ∂(volume : Measure ℝ³), h z = g z := by
    simpa [EventuallyEq] using hg
  change (∀ᵐ p : ℝ³ × ℝ³ ∂(volume : Measure ℝ³).prod (volume : Measure ℝ³),
      h (p.1 - p.2) = g (p.1 - p.2))
  rw [ae_iff] at hg' ⊢
  change ((volume : Measure ℝ³).prod (volume : Measure ℝ³))
      ((fun p : ℝ³ × ℝ³ => p.1 - p.2) ⁻¹' {z : ℝ³ | ¬ h z = g z}) = 0
  exact measure_sub_preimage_null {z : ℝ³ | ¬ h z = g z} hg'

/-- `wPairU ℓ h` is a.e. strongly measurable for the product measure, given
merely integrability of `h`. -/
lemma aesm_wPairU_prod {ℓ : ℝ} {h : ℝ³ → ℝ} (hhi : MeasureTheory.Integrable h) :
    AEStronglyMeasurable (wPairU ℓ h)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  let μ : Measure ℝ³ := volume
  let τ : Measure (ℝ³ × ℝ³) := μ.prod μ
  let hh : AEStronglyMeasurable h μ := hhi.aestronglyMeasurable
  let h' : ℝ³ → ℝ := AEStronglyMeasurable.mk h hh
  have hh'm : Measurable h' := hh.stronglyMeasurable_mk.measurable
  have hWm : Measurable (wPairU ℓ h') := wPairU_measurable hh'm
  have hWh : AEStronglyMeasurable (wPairU ℓ h') τ := hWm.aestronglyMeasurable
  have h_eq : h' =ᵐ[μ] h := hh.ae_eq_mk.symm
  have hcomp_eq : (fun p : ℝ³ × ℝ³ => h' (p.1 - p.2)) =ᵐ[τ]
      fun p : ℝ³ × ℝ³ => h (p.1 - p.2) := by
    have hcc := ae_eq_comp_sub_left (h := h') (g := h) h_eq
    simpa [τ, μ] using hcc
  have hW_eq : wPairU ℓ h' =ᵐ[τ] wPairU ℓ h := by
    filter_upwards [hcomp_eq] with p hp
    unfold wPairU wPair wScaled
    rw [hp]
  simpa [τ, μ] using (AEStronglyMeasurable.congr hWh hW_eq)

/-- `wPairU ℓ h` is a.e. strongly measurable for the product of cube-restricted
measures, given merely integrability of `h`. -/
lemma aesm_wPairU_restrict {ℓ : ℝ} {h : ℝ³ → ℝ} (hhi : MeasureTheory.Integrable h) :
    AEStronglyMeasurable (wPairU ℓ h)
      (((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure ℝ³).restrict (acube ℓ))) := by
  have hfull := aesm_wPairU_prod (ℓ := ℓ) hhi
  have hle : ((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure ℝ³).restrict (acube ℓ)) ≤
      (volume : Measure ℝ³).prod (volume : Measure ℝ³) := by
    exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  exact hfull.mono_measure hle


/-- `y ↦ |h (x − y)|` is integrable (full space) if `h` is. -/
lemma integrable_abs_shift_full {h : ℝ³ → ℝ} (hhi : MeasureTheory.Integrable h) (x : ℝ³) :
    MeasureTheory.Integrable (fun y : ℝ³ => |h (x - y)|) := by
  have hmp := measurePreserving_sub_left x
  have hg : AEStronglyMeasurable (fun z : ℝ³ => |h z|) volume :=
    hhi.aestronglyMeasurable.norm
  have hb := hmp.integrable_comp hg
  change Integrable ((fun z : ℝ³ => |h z|) ∘ fun y : ℝ³ => x - y)
  exact hb.mpr hhi.abs

/-- `y ↦ |h (x − y)|` is integrable on the cube if `h` is integrable. -/
lemma integrable_abs_shift_restrict {h : ℝ³ → ℝ} (hhi : MeasureTheory.Integrable h) (x : ℝ³)
    (ℓ : ℝ) : Integrable (fun y : ℝ³ => |h (x - y)|)
      ((volume : Measure ℝ³).restrict (acube ℓ)) := by
  exact (integrable_abs_shift_full hhi x).restrict

/-- pointwise bound of the wPair kernel by a product of a bounded χ and |h|. -/
lemma wPair_abs_bound {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0) (x y : ℝ³) :
    |wPair ℓ h x y| ≤ chiScale ℓ x * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := by
  have hk : |wScaled ℓ h (x - y)| ≤ 2 * |h (x - y)| := by
    have hb := abs_kRat_le (h := h) (ℓ := ℓ) (R := R) (r₀ := chiR0) hℓ hsupp hRℓ chiR0_half (x - y)
    simpa [wScaled, kRat] using hb
  have hS : |chiScale ℓ y| ≤ (Real.sqrt chiNormSq)⁻¹ := abs_chiScale_le ℓ y
  calc
    |wPair ℓ h x y| = |chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y| := by rfl
    _ = |chiScale ℓ x * wScaled ℓ h (x - y)| * |chiScale ℓ y| := by rw [abs_mul]
    _ = (chiScale ℓ x * |wScaled ℓ h (x - y)|) * |chiScale ℓ y| := by
        rw [abs_mul, abs_of_nonneg (chiScale_nonneg ℓ x)]
    _ ≤ (chiScale ℓ x * (2 * |h (x - y)|)) * |chiScale ℓ y| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hk (chiScale_nonneg ℓ x)) (abs_nonneg _)
    _ ≤ (chiScale ℓ x * (2 * |h (x - y)|)) * (Real.sqrt chiNormSq)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hS
          (mul_nonneg (chiScale_nonneg ℓ x) (mul_nonneg (by norm_num) (abs_nonneg _)))
    _ = chiScale ℓ x * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := by ring

/-- `wPairU ℓ h` is integrable over the full product space when `h` is
integrable and supported in `ball 0 R` with `R ≤ ℓ·chiR0`. -/
lemma integrable_wPairU_full {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hhi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0) :
    MeasureTheory.Integrable (wPairU ℓ h) := by
  let μ : Measure ℝ³ := volume
  let S : ℝ := (Real.sqrt chiNormSq)⁻¹
  have hSpos : 0 ≤ S := by
    dsimp [S]
    exact inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))
  let a : ℝ := 2 * S
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) hSpos
  let hAbs : ℝ³ → ℝ := fun z => |h z|
  have hAbsI : Integrable hAbs μ := hhi.abs
  let H0 : ℝ := ∫ z : ℝ³, |h z|
  have hH00 : 0 ≤ H0 := integral_nonneg (by intro z; exact abs_nonneg _)
  -- a.e.-strong measurability
  have h1f : AEStronglyMeasurable (wPairU ℓ h) (μ.prod μ) := by
    simpa [μ] using aesm_wPairU_prod (ℓ := ℓ) hhi
  -- slice integrability for all x
  have hslice : ∀ x : ℝ³, Integrable (fun y : ℝ³ => wPair ℓ h x y) μ := by
    intro x
    let M : ℝ³ → ℝ := fun y => (chiScale ℓ x * a) * |h (x - y)|
    have hMg : Integrable M μ := by
      have hg := integrable_abs_shift_full hhi x
      have hc := hg.const_mul (chiScale ℓ x * a)
      simpa [M] using hc
    have hf : AEStronglyMeasurable (fun y : ℝ³ => wPair ℓ h x y) μ := by
      -- slice = (fun _ => χ(x)) * (fun y => wScaled ℓ h (x−y)) * (fun y => χ(y))
      have h1 : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ x) μ := aestronglyMeasurable_const
      have h2 : AEStronglyMeasurable (fun y : ℝ³ => wScaled ℓ h (x - y)) μ := by
        -- wScaled h z = h z * (convScale ℓ z)⁻¹
        have hsh : AEStronglyMeasurable (fun y : ℝ³ => h (x - y)) μ := by
          have hq : Measure.QuasiMeasurePreserving (fun y : ℝ³ => x - y) μ μ := by
            simpa [μ] using (measurePreserving_sub_left x).quasiMeasurePreserving
          simpa [μ, Function.comp_def] using hhi.aestronglyMeasurable.comp_quasiMeasurePreserving hq
        have hinv : AEStronglyMeasurable (fun y : ℝ³ => (convScale ℓ (x - y))⁻¹) μ := by
          have hmeas : Measurable (fun t : ℝ => t⁻¹) := by fun_prop
          have hcont : Continuous (fun y : ℝ³ => convScale ℓ (x - y)) :=
            (convScale_continuous ℓ).comp (continuous_const.sub continuous_id)
          exact (hmeas.comp hcont.measurable).aestronglyMeasurable
        have hmul := hsh.mul hinv
        have hEq : (fun y : ℝ³ => h (x - y) * (convScale ℓ (x - y))⁻¹)
            = fun y : ℝ³ => wScaled ℓ h (x - y) := by
          funext y
          dsimp [wScaled]
          rw [div_eq_mul_inv]
        exact AEStronglyMeasurable.congr hmul (ae_of_all _ (by intro y; exact congrFun hEq y))
      have h3 : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y) μ :=
        (chiScale_continuous ℓ).aestronglyMeasurable
      have hprod : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ x * wScaled ℓ h (x - y)) μ := h1.mul h2
      have hprod2 : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y) μ :=
        hprod.mul h3
      simpa [wPair, μ] using hprod2
    have hdom : ∀ᵐ y ∂μ, ‖wPair ℓ h x y‖ ≤ M y := by
      refine ae_of_all _ ?_
      intro y
      have hb := wPair_abs_bound (ℓ := ℓ) (R := R) hℓ hsupp hRℓ x y
      change |wPair ℓ h x y| ≤ M y
      calc
        |wPair ℓ h x y| ≤ chiScale ℓ x * (2 * (Real.sqrt chiNormSq)⁻¹) * |h (x - y)| := hb
        _ = M y := by
          simp [M, a, S]
    exact Integrable.mono' hMg hf hdom
  have hslice_ae : ∀ᵐ x ∂μ, Integrable (fun y : ℝ³ => wPairU ℓ h (x, y)) μ := by
    refine ae_of_all _ ?_
    intro x
    exact hslice x
  -- slice mean
  let J : ℝ³ → ℝ := fun x => ∫ y : ℝ³, |wPair ℓ h x y|
  have hJae : AEStronglyMeasurable J μ := by
    dsimp [J]
    have hnorm : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => ‖wPairU ℓ h p‖) (μ.prod μ) := h1f.norm
    exact hnorm.integral_prod_right'
  have hJdom : ∀ᵐ x ∂μ, |J x| ≤ (a * H0) * chiScale ℓ x := by
    refine ae_of_all _ ?_
    intro x
    dsimp [J]
    have hstep1 : (∫ y : ℝ³, |wPair ℓ h x y|) ≤ ∫ y : ℝ³, (chiScale ℓ x * a) * |h (x - y)| := by
      have hJint : Integrable (fun y : ℝ³ => |wPair ℓ h x y|) μ := (hslice x).abs
      have hMint : Integrable (fun y : ℝ³ => (chiScale ℓ x * a) * |h (x - y)|) μ := by
        have hg := integrable_abs_shift_full hhi x
        simpa [a, mul_assoc] using hg.const_mul (chiScale ℓ x * a)
      apply integral_mono_ae hJint hMint
      refine ae_of_all _ ?_
      intro y
      have hb := wPair_abs_bound (ℓ := ℓ) (R := R) hℓ hsupp hRℓ x y
      change |wPair ℓ h x y| ≤ (chiScale ℓ x * (2 * (Real.sqrt chiNormSq)⁻¹)) * |h (x - y)|
      simpa [a, S] using hb
    have hstep2eq : (∫ y : ℝ³, (chiScale ℓ x * a) * |h (x - y)|) = (a * H0) * chiScale ℓ x := by
      calc
        (∫ y : ℝ³, (chiScale ℓ x * a) * |h (x - y)|)
            = (chiScale ℓ x * a) * (∫ y : ℝ³, |h (x - y)|) := by
              rw [integral_const_mul]
        _ = (chiScale ℓ x * a) * H0 := by
              congr 1
              dsimp [H0]
              exact integral_comp_sub_left (fun z : ℝ³ => |h z|) x
        _ = (a * H0) * chiScale ℓ x := by ring
    have hstep2 : (∫ y : ℝ³, (chiScale ℓ x * a) * |h (x - y)|) ≤ (a * H0) * chiScale ℓ x := le_of_eq hstep2eq
    have hbnd : |(∫ y : ℝ³, |wPair ℓ h x y|)| ≤ a * H0 * chiScale ℓ x := by
      -- nonneg so norm is itself
      have hnonneg : 0 ≤ ∫ y : ℝ³, |wPair ℓ h x y| := integral_nonneg (by intro y; exact abs_nonneg _)
      have hnonneg2 : 0 ≤ (a * H0) * chiScale ℓ x := by
        exact mul_nonneg (mul_nonneg ha0 hH00) (chiScale_nonneg ℓ x)
      rw [abs_of_nonneg hnonneg]
      exact le_trans hstep1 hstep2
    exact hbnd
  have hJg : Integrable (fun x : ℝ³ => (a * H0) * chiScale ℓ x) μ := by
    have hχI : Integrable (chiScale ℓ) μ :=
      Continuous.integrable_of_hasCompactSupport (chiScale_continuous ℓ)
        (chiScale_hasCompactSupport (ne_of_gt hℓ))
    exact hχI.const_mul (a * H0)
  have hJ : Integrable J μ := Integrable.mono' hJg hJae hJdom
  -- assemble
  have hiff := MeasureTheory.integrable_prod_iff (f := wPairU ℓ h) (μ := μ) (ν := μ) h1f
  -- hiff : Integrable f (μ.prod μ) ↔ (∀ᵐ x, Integrable (fun y => f (x,y)) μ) ∧ Integrable (x ↦ ∫ ‖f(x,y)‖) μ
  have hRHS : (∀ᵐ x ∂μ, Integrable (fun y : ℝ³ => wPairU ℓ h (x, y)) μ) ∧
      Integrable (fun x : ℝ³ => ∫ y : ℝ³, ‖wPairU ℓ h (x, y)‖ ∂μ) μ := by
    constructor
    · simpa [wPairU] using hslice_ae
    · have hJeq : J = fun x : ℝ³ => ∫ y : ℝ³, ‖wPairU ℓ h (x, y)‖ ∂μ := by
        funext x
        dsimp [J, wPairU]
      simpa [hJeq] using hJ
  have hmain := hiff.2 hRHS
  -- goal measure volume on product = μ.prod μ
  rw [show (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod (volume : Measure ℝ³) by
        exact Measure.volume_eq_prod ℝ³ ℝ³]
  simpa [μ] using hmain

/-- `wPairU ℓ h` is integrable on `acube ℓ ×ˢ acube ℓ` when `h` is integrable
and supported in `ball 0 R` with `R ≤ ℓ·chiR0`. -/
lemma integrableOn_wPairU_of {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hhi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (_hR : 0 ≤ R) (hRℓ : R ≤ ℓ * chiR0) :
    IntegrableOn (wPairU ℓ h) (acube ℓ ×ˢ acube ℓ) := by
  have hfull := integrable_wPairU_full (ℓ := ℓ) (R := R) hℓ hhi hsupp hRℓ
  exact hfull.restrict


/-- The χ-renormalized pair kernel is integrable over `acube ℓ ×ˢ acube ℓ` in the dilute regime
(`h` integrable, vanishing outside `ball 0 R`, `R ≤ ℓ·chiR0`). -/
lemma integrableOn_wPairU_acube {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (_hh : Measurable h) (hhi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) :
    IntegrableOn (wPairU ℓ h) (acube ℓ ×ˢ acube ℓ) := by
  exact integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hhi hsupp hR hRℓ

/-- Specialised: `wPair(g0)` is integrable over the product cube (chosen
branch, `0 < R`, support of `v` in `ball 0 R`, dilute regime). -/
lemma integrableOn_w1c_acube {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    IntegrableOn (wPairU ℓ (g0 v h)) (acube ℓ ×ˢ acube ℓ) := by
  let g : ℝ³ → ℝ := g0 v h
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using g0_integrable hR hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    simpa [g] using g0_zero_of_norm_ge hv_supp hz h
  simpa [g] using integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ

/-- Specialised: `wPair(g2)` is integrable over the product cube. -/
lemma integrableOn_w2c_acube {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    IntegrableOn (wPairU ℓ (g2 v h)) (acube ℓ ×ˢ acube ℓ) := by
  let g : ℝ³ → ℝ := g2 v h
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using g2_integrable hR hv_nonneg hvrad hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    simpa [g] using g2_zero_of_norm_ge hv_supp hz h
  simpa [g] using integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ

/-- Support-based transfer of a one-variable integral from the cube to all space. -/
lemma integral_cube_eq_full_of_support {ℓ : ℝ} {f : ℝ³ → ℝ}
    (hsupp : ∀ y : ℝ³, f y ≠ 0 → y ∈ acube ℓ) :
    (∫ y in acube ℓ, f y) = ∫ y : ℝ³, f y := by
  calc
    (∫ y in acube ℓ, f y) = ∫ y : ℝ³, (acube ℓ).indicator f y := by
      rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
    _ = ∫ y : ℝ³, f y := by
      apply integral_congr_ae
      refine ae_of_all _ ?_
      intro y
      by_cases hy : y ∈ acube ℓ
      · simp [Set.indicator, hy]
      · have hf0 : f y = 0 := by
          by_contra hf
          exact hy (hsupp y hf)
        simp [Set.indicator, hy, hf0]

/-- If `x ∉ acube ℓ` then the `y`-integral of `wPair ℓ h x y` vanishes. -/
lemma wPair_integral_zero_of_not_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} {x : ℝ³}
    (hx : x ∉ acube ℓ) : (∫ y : ℝ³, wPair ℓ h x y) = 0 := by
  have hfun : (fun y : ℝ³ => wPair ℓ h x y) = fun _ : ℝ³ => 0 := by
    funext y
    by_contra hw
    exact hx (wPair_vanishes_off_acube hℓ hw).1
  rw [hfun]
  simp

/-- Restricted Fubini: the product-set integral over the centred cube pair equals
the iterated cube integrals (outer variable first). -/
lemma prod_setIntegral_eq_iter_outer {ℓ : ℝ} {w : ℝ³ × ℝ³ → ℝ}
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in acube ℓ, ∫ y in acube ℓ, w (x, y)) = ∫ p in acube ℓ ×ˢ acube ℓ, w p := by
  have hInt : Integrable w (((volume : Measure ℝ³).restrict (acube ℓ)).prod
      ((volume : Measure ℝ³).restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hwi
  have hF := MeasureTheory.integral_prod
    (μ := (volume : Measure ℝ³).restrict (acube ℓ))
    (ν := (volume : Measure ℝ³).restrict (acube ℓ)) (f := w) hInt
  rw [← hF]
  rw [← prod_measure_eq ℓ]

/-- Pointwise: `wPair` is a rearrangement of the `kernel_double_integral`
integrand. -/
lemma wPair_eq_kernel {ℓ : ℝ} {h : ℝ³ → ℝ} (x y : ℝ³) :
    wPair ℓ h x y = chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)) := by
  unfold wPair wScaled
  ring

/-- The full double integral of `wPair ℓ h` is `ℓ³·∫h`. -/
lemma wPair_double_full_integral {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hhi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ h x y) = ℓ ^ 3 * (∫ z : ℝ³, h z) := by
  have hmain := kernel_double_integral (h := h) (ℓ := ℓ) (R := R) (r₀ := chiR0) hℓ hhi hsupp
    chiR0_pos hRℓ chiR0_half
  calc
    (∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ h x y)
        = ∫ x : ℝ³, ∫ y : ℝ³, chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)) := by
          apply integral_congr_ae
          refine ae_of_all _ ?_
          intro x
          apply integral_congr_ae
          refine ae_of_all _ ?_
          intro y
          exact wPair_eq_kernel (ℓ := ℓ) (h := h) x y
    _ = ℓ ^ 3 * (∫ z : ℝ³, h z) := hmain

/-- The `acube²`-integral of `wPairU ℓ h` reduces to the full iterated integral. -/
lemma wPairU_cube_integral_eq_full {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hwi : IntegrableOn (wPairU ℓ h) (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ h p) = ∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ h x y := by
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ h p)
        = ∫ x in acube ℓ, ∫ y in acube ℓ, wPairU ℓ h (x, y) := by
          exact (prod_setIntegral_eq_iter_outer (w := wPairU ℓ h) hwi).symm
    _ = ∫ x in acube ℓ, ∫ y : ℝ³, wPair ℓ h x y := by
          apply integral_congr_ae
          refine ae_of_all _ ?_
          intro x
          exact integral_cube_eq_full_of_support (ℓ := ℓ)
            (f := fun y : ℝ³ => wPair ℓ h x y)
            (by intro y hy; exact (wPair_vanishes_off_acube hℓ hy).2)
    _ = ∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ h x y := by
          exact integral_cube_eq_full_of_support (ℓ := ℓ)
            (f := fun x : ℝ³ => ∫ y : ℝ³, wPair ℓ h x y)
            (by intro x hx; by_contra hxc; exact hx (wPair_integral_zero_of_not_mem hℓ (x := x) hxc))

/-- **eq:DefU on the centred cube**: `∬_{acube²} wPair(g0) = 8π·a v·ℓ³`. -/
lemma w1c_acube_integral {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p) = ℓ ^ 3 * (8 * π * a v) := by
  let g : ℝ³ → ℝ := g0 v h
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using g0_integrable hR hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    simpa [g] using g0_zero_of_norm_ge hv_supp hz h
  have hwi : IntegrableOn (wPairU ℓ g) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p)
        = ∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ g x y := by
          simpa [g] using wPairU_cube_integral_eq_full hℓ hwi
    _ = ℓ ^ 3 * (∫ z : ℝ³, g z) := wPair_double_full_integral (ℓ := ℓ) (R := R) hℓ hgI hgsupp hRℓ
    _ = ℓ ^ 3 * (8 * π * a v) := by
          rw [g0_integral hR hv_supp h]


/-- **eq:w2int on the centred cube**: `∬_{acube²} wPair(g2) = ℓ³·∫g2`. -/
lemma w2c_acube_integral {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) = ℓ ^ 3 * (∫ z : ℝ³, g2 v h z) := by
  let g : ℝ³ → ℝ := g2 v h
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using g2_integrable hR hv_nonneg hvrad hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    simpa [g] using g2_zero_of_norm_ge hv_supp hz h
  have hwi : IntegrableOn (wPairU ℓ g) (acube ℓ ×ˢ acube ℓ) :=
    integrableOn_wPairU_of (ℓ := ℓ) (R := R) hℓ hgI hgsupp (le_of_lt hR) hRℓ
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p)
        = ∫ x : ℝ³, ∫ y : ℝ³, wPair ℓ g x y := by
          simpa [g] using wPairU_cube_integral_eq_full hℓ hwi
    _ = ℓ ^ 3 * (∫ z : ℝ³, g z) := wPair_double_full_integral (ℓ := ℓ) (R := R) hℓ hgI hgsupp hRℓ
    _ = ℓ ^ 3 * (∫ z : ℝ³, g2 v h z) := by rfl

/-- Bounds for the `g2` double integral on the centred cube:
`8π·a v·ℓ³ ≤ ∬wPair(g2) ≤ 16π·a v·ℓ³`. -/
lemma w2c_acube_integral_bounds {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    8 * π * a v * ℓ ^ 3 ≤ (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) ∧
      (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g2 v h) p) ≤ 16 * π * a v * ℓ ^ 3 := by
  have hval := w2c_acube_integral hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hb := g2_integral_bounds hR hv_nonneg hvrad hv_supp h
  have hℓ3 : 0 ≤ ℓ ^ 3 := pow_nonneg (le_of_lt hℓ) 3
  constructor
  · rw [hval]
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hℓ3]
  · rw [hval]
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hℓ3]

end BoseGases
end Submission
