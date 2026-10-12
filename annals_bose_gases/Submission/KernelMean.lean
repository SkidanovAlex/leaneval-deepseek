import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ChallengeDeps
import Submission.ChiWitness
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — kernel fibre integrals and per-slot means (the `eq:Q1n0`-rewrite seeds)

The FS potential-decomposition rewrites (`lem:QDecompSimpler` `eq:Q1n0`,
`eq:Q2n0`) are driven by two elementary kernel facts on the analysis box:

  1. the *fibre integral* of the χ-renormalized pair kernel
     `w(x,y) := χℓ(x)·h(x−y)/Cℓ(x−y)·χℓ(y)` (`KernelIds.wPair`) factors as

         ∫_y w(x,y) dy = χℓ(x) · ∫_y χℓ(y)·wScaled ℓ h (x−y) dy ;        (kernel_fibre)

  2. the *per-slot mean*: multiplying a function `G` that is constant in
     slot `j` (e.g. `G = aP j Φ`) by the kernel and averaging over slot `j`
     pulls the mean out:

         ∫_y w(x_i,y)·G(x[j:=y]) dy = G(x)·∫_y w(x_i,y) dy ;             (mean_kernel)

  so that the FS operator `Σ_j P_j w₂(x_i,x_j) P_j` evaluates, at the
  configuration `x`, to `(∫_y w₂(x_i,y)dy)·(Σ_j P_j Φ x)` = the corpus-native
  `n0·(χℓ(W₂⋆χℓ)/ℓ³)(x_i)` factor (`sumPj_kernel_mean`).

The module also packages the boundedness of the renormalized kernel
(`|wScaled| ≤ 2|h|` on the support of `h` when `R ≤ ℓ·chiR0`) and its
consequent integrability — the standing "dilute regime" bookkeeping used
throughout the kernel calculus (`R ≤ ℓ·chiR0`).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- In the dilute regime the renormalized kernel is at most twice its
numerator: `|wScaled ℓ h z| ≤ 2·|h z|` whenever `h` vanishes outside
`ball 0 R` and `R ≤ ℓ·chiR0`. -/
lemma wScaled_abs_le_two {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ}
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (z : ℝ³) :
    |wScaled ℓ h z| ≤ 2 * |h z| := by
  have hk := abs_kRat_le (h := h) (r₀ := chiR0) hℓ hsupp hRℓ chiR0_half z
  simpa [wScaled, kRat] using hk



/-- `y ↦ x − y` is measure preserving on `ℝ³` (translation of negation). -/
lemma km_measurePreserving_sub_left (x : ℝ³) :
    MeasurePreserving (fun y : ℝ³ => x - y) volume volume := by
  have hneg : MeasurePreserving (fun y : ℝ³ => -y) volume volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ³)
  have hadd : MeasurePreserving (fun z : ℝ³ => x + z) volume volume :=
    measurePreserving_add_left volume x
  change MeasurePreserving (fun y : ℝ³ => x + (-y)) volume volume
  exact hadd.comp hneg

/-- Precomposing with the measure-preserving reflection `y ↦ x − y` preserves
integrability. -/
lemma km_integrable_comp_sub_left {f : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (x : ℝ³) : MeasureTheory.Integrable (fun y : ℝ³ => f (x - y)) := by
  have hmp := km_measurePreserving_sub_left x
  have hb := hmp.integrable_comp (g := f) hf.aestronglyMeasurable
  exact hb.mpr hf

/-- The a.e.-strong measurability of `y ↦ f (x − y)` transfers from `f`. -/
lemma km_aestronglyMeasurable_comp_sub_left {f : ℝ³ → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : ℝ³) :
    AEStronglyMeasurable (fun y : ℝ³ => f (x - y)) volume := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ℝ³ => x - y) volume volume :=
    (km_measurePreserving_sub_left x).quasiMeasurePreserving
  simpa [Function.comp_def] using hf.comp_quasiMeasurePreserving hq

/-- The renormalized kernel is integrable (dilute regime). -/
lemma wScaled_integrable {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hm : Measurable h)
    (hi : MeasureTheory.Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) :
    MeasureTheory.Integrable (wScaled ℓ h) := by
  have hWm : AEStronglyMeasurable (wScaled ℓ h) := by
    have hmeas : Measurable (wScaled ℓ h) := by
      change Measurable (fun z : ℝ³ => h z / convScale ℓ z)
      exact hm.div (convScale_continuous ℓ).measurable
    exact hmeas.aestronglyMeasurable
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³), ‖wScaled ℓ h z‖ ≤ 2 * |h z| := by
    refine ae_of_all _ ?_
    intro z
    simpa [Real.norm_eq_abs] using wScaled_abs_le_two hℓ hR hRℓ hsupp z
  exact Integrable.mono' (hi.abs.const_mul (2 : ℝ)) hWm hdom

/-- The `y`-fibre of the pair kernel is integrable, for `x` in the cube:
`χℓ(y)·wScaled(x−y)` is integrable (kernel present). -/
lemma kernel_fibre_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (x : ℝ³) :
    MeasureTheory.Integrable (fun y : ℝ³ => chiScale ℓ y * wScaled ℓ h (x - y)) := by
  let S : ℝ := (Real.sqrt chiNormSq)⁻¹
  have hS : 0 ≤ S := by
    dsimp [S]
    exact inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))
  have hshift : Integrable (fun y : ℝ³ => S * |wScaled ℓ h (x - y)|) := by
    have hs := km_integrable_comp_sub_left (f := fun z : ℝ³ => |wScaled ℓ h z|) hwi.abs x
    exact hs.const_mul S
  have hW : AEStronglyMeasurable (fun y : ℝ³ => wScaled ℓ h (x - y)) :=
    km_aestronglyMeasurable_comp_sub_left (f := wScaled ℓ h) hwi.aestronglyMeasurable x
  have hχ : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y) :=
    (chiScale_continuous ℓ).aestronglyMeasurable
  have haesm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y * wScaled ℓ h (x - y)) :=
    hχ.mul hW
  have hdom : ∀ᵐ y ∂(volume : Measure ℝ³),
      ‖chiScale ℓ y * wScaled ℓ h (x - y)‖ ≤ S * |wScaled ℓ h (x - y)| := by
    refine ae_of_all _ ?_
    intro y
    calc
      ‖chiScale ℓ y * wScaled ℓ h (x - y)‖
          = |chiScale ℓ y * wScaled ℓ h (x - y)| := Real.norm_eq_abs _
      _ ≤ |chiScale ℓ y| * |wScaled ℓ h (x - y)| := by rw [abs_mul]
      _ ≤ S * |wScaled ℓ h (x - y)| := by
          exact mul_le_mul_of_nonneg_right (abs_chiScale_le ℓ y) (abs_nonneg _)
  exact Integrable.mono' hshift haesm hdom

/-- **Fibre integral**: `∫_y w(x,y) dy = χℓ(x)·∫_y χℓ(y)·wScaled(x−y) dy`. -/
lemma kernel_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (x : ℝ³) :
    (∫ y : ℝ³, wPair ℓ h x y) =
      chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ h (x - y)) := by
  calc
    (∫ y : ℝ³, wPair ℓ h x y)
        = ∫ y : ℝ³, chiScale ℓ x * (chiScale ℓ y * wScaled ℓ h (x - y)) := by
            apply integral_congr_ae
            refine ae_of_all _ ?_
            intro y
            dsimp [wPair]
            ring
    _ = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ h (x - y)) := by
            rw [integral_const_mul]

/-- **Per-slot mean**: for `G` constant in slot `j` (in particular
`G = aP j Φ`), averaging the kernel times `G` over slot `j` pulls `G` out. -/
lemma mean_kernel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j : Fin N} {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (x : X N) (i : ℝ³) :
    (∫ y in acube ℓ, wPair ℓ h i y * aP ℓ j Φ (Function.update x j y)) =
      aP ℓ j Φ x * (∫ y in acube ℓ, wPair ℓ h i y) := by
  calc
    (∫ y in acube ℓ, wPair ℓ h i y * aP ℓ j Φ (Function.update x j y))
        = ∫ y in acube ℓ, wPair ℓ h i y * aP ℓ j Φ x := by
            apply integral_congr_ae
            refine ae_of_all _ ?_
            intro y
            exact congrArg (fun c : ℝ => wPair ℓ h i y * c) (aP_const_in_coord hℓ j hΦc x y)
    _ = (∫ y in acube ℓ, wPair ℓ h i y) * aP ℓ j Φ x := by
            rw [integral_mul_const]
    _ = aP ℓ j Φ x * (∫ y in acube ℓ, wPair ℓ h i y) := by ring

/-- The mean over slot `j` of the pair-kernel fibre is the whole-space
integral of the fibre (both vanish off the cube). -/
lemma mean_kernel_full {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (i : ℝ³) :
    (∫ y in acube ℓ, wPair ℓ h i y) = ∫ y : ℝ³, wPair ℓ h i y := by
  have hchi0 : ∀ y : ℝ³, y ∈ (acube ℓ)ᶜ → chiScale ℓ y = 0 := by
    intro y hy
    by_contra hz
    have hle := chiScale_support_le hℓ hz
    have hmem : y ∈ acube ℓ := mem_acube_of_norm_le (le_of_lt hℓ) hle
    exact hy hmem
  have hsup : ∀ y : ℝ³, y ∈ (acube ℓ)ᶜ → wPair ℓ h i y = 0 := by
    intro y hy
    dsimp [wPair]
    rw [hchi0 y hy]
    ring
  have hfun : (fun y : ℝ³ => wPair ℓ h i y) =
      (acube ℓ).indicator (fun y : ℝ³ => wPair ℓ h i y) := by
    funext y
    by_cases hy : y ∈ acube ℓ
    · simp [hy]
    · simp [hy, hsup y hy]
  calc
    (∫ y in acube ℓ, wPair ℓ h i y)
        = ∫ y : ℝ³, (acube ℓ).indicator (fun y : ℝ³ => wPair ℓ h i y) y := by
            rw [← integral_indicator (acube_measurable ℓ)]
    _ = ∫ y : ℝ³, wPair ℓ h i y := by
            rw [← hfun]

/-- **Sum over `j` of the `P_j`-mean** (FS `Σ_j P_j w₂(x_i,x_j) P_j` at `x`):
`Σ_j ∫_y w(x_i,y)·(P_jΦ)(x[j:=y]) = (∫_y w(x_i,y)dy)·Σ_j (P_jΦ)(x)`. -/
lemma sumPj_kernel_mean {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {h : ℝ³ → ℝ}
    (hwi : MeasureTheory.Integrable (wScaled ℓ h)) (x : X N) :
    (∑ j : Fin N, ∫ y in acube ℓ, wPair ℓ h (x i) y * aP ℓ j Φ (Function.update x j y)) =
      (∫ y in acube ℓ, wPair ℓ h (x i) y) * (∑ j : Fin N, aP ℓ j Φ x) := by
  let C : ℝ := ∫ y in acube ℓ, wPair ℓ h (x i) y
  calc
    (∑ j : Fin N, ∫ y in acube ℓ, wPair ℓ h (x i) y * aP ℓ j Φ (Function.update x j y))
        = ∑ j : Fin N, aP ℓ j Φ x * C := by
            apply Finset.sum_congr rfl
            intro j hj
            exact mean_kernel (ℓ := ℓ) hℓ (j := j) (Φ := Φ) hΦc (h := h) hwi x (x i)
    _ = C * (∑ j : Fin N, aP ℓ j Φ x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (∫ y in acube ℓ, wPair ℓ h (x i) y) * (∑ j : Fin N, aP ℓ j Φ x) := by
            rfl

end BoseGases

end Submission
