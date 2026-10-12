import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.KernelL2.integrable_coulomb_iter_g0
import Submission.Work.MGroupInput.SimpleA2Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.newtonianSharp` — the sharp Newtonian bound for `W₁ = wScaled s (g₀)`

Given the a.e. sharp comparison `W₁ ≤ (1+δ)·g₀` (`W₁ := wScaled s (g0 v h)`,
`g₀ := g0 v h`), the momentum-space Newtonian energy of `W₁` is finite and bounded by
`2(1+δ)²·∫ g₀·w₀` (`w₀ := Classical.choose h`):

`(2π)⁻³ ∫_q pairW W₁ q ²/‖q‖² dq ≤ 2(1+δ)² ∫_z g₀ z · w₀ z`,

which is the sharp form of FS's leading (`lm:appbogolubov`) mass term
`½(1+C(R/ℓ)²)ĝω(0)`: the position-space identity
`(2π)⁻³∫_q Ŵ(p)²/p² dp = (1/(4π))∬W(x)W(y)/‖x−y‖` turns the momentum integral into
`2 · ½(1/(8π))∬W₁W₁/‖x−y‖`, and the a.e. comparison `W₁ ≤ (1+δ)g₀` upgrades the double
integral to `(1+δ)²·8π·∫g₀w₀` (no `(R/ℓ)²`-Taylor tail is needed here: the comparison
is a hypothesis).

The three ingredients of the assembly (all on the shelf):

* `Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le`, packaged for the D1
  weight as `Submission.BoseGases.integral_pairW_sq_div_sq_le_newtonian_of_fin` (with the
  momentum-side integrability `Submission.BoseGases.integrable_pairW_sq_div`);
* the position-space rectangular comparison `Submission.BoseGases.coulomb_rect_le` (its
  `hVgInt` hypothesis is `Work.KernelL2.integrable_coulomb_iter_g0`, i.e.
  `∫g₀·coulPot g₀ = 8π∫g₀w₀ < ∞`);
* the Newton double-integral identity `Submission.BoseGases.chosen_newton_double_eq`,
  `∬g₀(x)g₀(y)/‖x−y‖ = 8π·∫g₀·w₀`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Helper 1 — `x ↦ g₀ x · coulPot g₀ x` is integrable

This is the `hVgInt` hypothesis of `coulomb_rect_le` for the scattering numerator; it is
the a.e. form of `8π·∫g₀·w₀ < ∞`. -/

lemma newtonianSharp_g0_coulPot_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    Integrable (fun x : ℝ³ => g0 v h x * coulPot (g0 v h) x) := by
  have h1 := Work.KernelL2.integrable_coulomb_iter_g0 (R := R) (v := v)
    hR hv_nonneg hvrad hv_supp h
  refine h1.congr ?_
  filter_upwards with x
  rw [coulPot]
  rw [show (fun y : ℝ³ => g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)
        = fun y : ℝ³ => g0 v h x * (g0 v h y * (‖x - y‖ : ℝ)⁻¹) from by funext y; ring]
  exact MeasureTheory.integral_const_mul _ _

/-! ## Helper 2 — the double Coulomb integrand of a nonnegative compactly supported `f`

If `f ∈ L¹`, `f ≥ 0` a.e., `f` vanishes outside `ball 0 R`, and the Coulomb energy
`∫f·coulPot f` is finite, then the *joint* (product-measure) integrand
`(x,y) ↦ f x f y ‖x−y‖⁻¹` is integrable.  This is a Tonelli computation: for a.e. `x` the
slice `y ↦ f y ‖x−y‖⁻¹` is integrable (`coulPot_abs_slice_integrable_ae`), so
`∫⁻y ofReal(f x f y /‖x−y‖) = ofReal(f x · coulPot f x)`, and the outer `∫⁻` is finite by
the integrability of `x ↦ f x · coulPot f x`. -/

lemma newtonianSharp_integrable_double_coulPot {f : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : Integrable f) (hf0 : ∀ᵐ x : ℝ³, 0 ≤ f x) (hfsupp : ∀ x : ℝ³, R ≤ ‖x‖ → f x = 0)
    (hfi : Integrable (fun x : ℝ³ => f x * coulPot f x)) :
    Integrable (fun p : ℝ³ × ℝ³ => f p.1 * f p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
  have hf_meas : AEMeasurable f := hf.aestronglyMeasurable.aemeasurable
  have hker_meas : Measurable (fun p : ℝ³ × ℝ³ => (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    ((measurable_fst.sub measurable_snd).norm).inv
  have hpair_meas : AEMeasurable (fun p : ℝ³ × ℝ³ => f p.1 * f p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)
      (volume.prod volume) :=
    (hf_meas.comp_fst.mul hf_meas.comp_snd).mul hker_meas.aemeasurable
  have hofReal_meas : AEMeasurable (Function.uncurry (fun x y : ℝ³ =>
      ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹))) (volume.prod volume) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    simpa [Function.uncurry] using hpair_meas
  -- a.e. integrability of the one-dimensional slices
  have hslice : ∀ᵐ x : ℝ³, Integrable (fun y : ℝ³ => f y * (‖x - y‖ : ℝ)⁻¹) := by
    filter_upwards [coulPot_abs_slice_integrable_ae (p := f) hf hfsupp hR] with x hx
    refine hx.congr ?_
    filter_upwards [hf0] with y hy
    rw [abs_of_nonneg hy]
  -- the collapse of the inner lintegral
  have hcollapse : ∀ᵐ x : ℝ³, (∫⁻ y : ℝ³, ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹))
      = ENNReal.ofReal (f x * coulPot f x) := by
    filter_upwards [hslice, hf0] with x hx hfx0
    have hIntMul : Integrable (fun y : ℝ³ => f x * (f y * (‖x - y‖ : ℝ)⁻¹)) :=
      hx.const_mul (f x)
    have hnn : 0 ≤ᵐ[volume] (fun y : ℝ³ => f x * (f y * (‖x - y‖ : ℝ)⁻¹)) := by
      filter_upwards [hf0] with y hy
      exact mul_nonneg hfx0 (mul_nonneg hy (inv_nonneg.mpr (norm_nonneg _)))
    have h1 : (∫⁻ y : ℝ³, ENNReal.ofReal (f x * (f y * (‖x - y‖ : ℝ)⁻¹)))
        = ENNReal.ofReal (∫ y : ℝ³, f x * (f y * (‖x - y‖ : ℝ)⁻¹)) :=
      (ofReal_integral_eq_lintegral_ofReal hIntMul hnn).symm
    have h2 : (∫ y : ℝ³, f x * (f y * (‖x - y‖ : ℝ)⁻¹)) = f x * coulPot f x := by
      rw [coulPot, MeasureTheory.integral_const_mul]
    have h3 : (∫⁻ y : ℝ³, ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹))
        = ∫⁻ y : ℝ³, ENNReal.ofReal (f x * (f y * (‖x - y‖ : ℝ)⁻¹)) := by
      apply lintegral_congr
      intro y
      congr 1
      ring
    rw [h3, h1, h2]
  have houter : (∫⁻ x : ℝ³, ENNReal.ofReal (f x * coulPot f x))
      = ENNReal.ofReal (∫ x : ℝ³, f x * coulPot f x) := by
    refine (ofReal_integral_eq_lintegral_ofReal hfi ?_).symm
    filter_upwards [hf0] with x hx
    exact mul_nonneg hx (coulPot_nonneg hf0 x)
  -- the pair lintegral is finite (Tonelli + the two collapses)
  have hlin : (∫⁻ p : ℝ³ × ℝ³,
      ENNReal.ofReal (f p.1 * f p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) ≠ ⊤ := by
    have hswap : (∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal (f p.1 * f p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹))
        = ∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹) :=
      (MeasureTheory.lintegral_lintegral (f := fun x y : ℝ³ =>
        ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹)) hofReal_meas).symm
    rw [hswap]
    have hc : (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (f x * f y * (‖x - y‖ : ℝ)⁻¹))
        = ∫⁻ x : ℝ³, ENNReal.ofReal (f x * coulPot f x) := lintegral_congr_ae hcollapse
    rw [hc, houter]
    exact ENNReal.ofReal_ne_top
  -- conclude integrability
  have hnn2 : 0 ≤ᵐ[volume.prod volume]
      (fun p : ℝ³ × ℝ³ => f p.1 * f p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
    have h1 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ f p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure ℝ³))).ae hf0
    have h2 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ f p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure ℝ³))).ae hf0
    filter_upwards [h1, h2] with p hp1 hp2
    exact mul_nonneg (mul_nonneg hp1 hp2) (inv_nonneg.mpr (norm_nonneg _))
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    hpair_meas.aestronglyMeasurable hnn2).mp hlin

/-! ## Helper 3 — the a.e. sharp comparison transfers the double integrability

If `0 ≤ W ≤ (1+δ)G` a.e. and the `G`-double integral is integrable, so is the
`W`-double integral. -/

lemma newtonianSharp_integrable_double_of_sharp {W G : ℝ³ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hW : Integrable W) (hW0 : ∀ᵐ x : ℝ³, 0 ≤ W x) (hWle : ∀ᵐ x : ℝ³, W x ≤ (1 + δ) * G x)
    (hG : Integrable (fun p : ℝ³ × ℝ³ => G p.1 * G p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :
    Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
  have h1 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ W p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³))).ae hW0
  have h2 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)), 0 ≤ W p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³))).ae hW0
  have h3 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)),
      W p.1 ≤ (1 + δ) * G p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³))).ae hWle
  have h4 : ∀ᵐ p ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)),
      W p.2 ≤ (1 + δ) * G p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³))).ae hWle
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) (volume.prod volume) := by
    have hk : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => (‖p.1 - p.2‖ : ℝ)⁻¹)
        (volume.prod volume) :=
      (((measurable_fst.sub measurable_snd).norm).inv).aemeasurable.aestronglyMeasurable
    exact (hW.aestronglyMeasurable.comp_fst.mul hW.aestronglyMeasurable.comp_snd).mul hk
  refine Integrable.mono' (hG.const_mul ((1 + δ) ^ 2)) hmeas ?_
  filter_upwards [h1, h2, h3, h4] with p hp1 hp2 hp3 hp4
  have hK : 0 ≤ (‖p.1 - p.2‖ : ℝ)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hp1 hp2) hK)]
  calc W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹
      ≤ ((1 + δ) * G p.1) * ((1 + δ) * G p.2) * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ hK
        exact mul_le_mul hp3 hp4 hp2 (le_trans hp1 hp3)
    _ = (1 + δ) ^ 2 * (G p.1 * G p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by ring

/-! ## The theorem -/

theorem newtonianSharp {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hsharp : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h) x
          ≤ (1 + δ) * Submission.BoseGases.g0 v h x) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.pairW (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) q) ^ 2
          / ‖q‖ ^ 2)
    ∧ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.pairW (Submission.BoseGases.wScaled s (Submission.BoseGases.g0 v h)) q) ^ 2
          / ‖q‖ ^ 2)
      ≤ 2 * (1 + δ) ^ 2 * (∫ z : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h z * Classical.choose h z) := by
  set W : ℝ³ → ℝ := wScaled s (g0 v h) with hWdef
  set G : ℝ³ → ℝ := g0 v h with hGdef
  change Integrable (fun q : ℝ³ => (pairW W q) ^ 2 / ‖q‖ ^ 2)
    ∧ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (pairW W q) ^ 2 / ‖q‖ ^ 2)
      ≤ 2 * (1 + δ) ^ 2 * (∫ z : ℝ³, G z * Classical.choose h z)
  have hsharpW : ∀ᵐ x : ℝ³, W x ≤ (1 + δ) * G x := by
    filter_upwards [hsharp] with x hx
    rw [hWdef, hGdef]
    exact hx
  have hWint : Integrable W := by
    rw [hWdef]
    exact integrable_wScaled_g0_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ hsharp
  have hGint : Integrable G := by
    rw [hGdef]
    exact g0_integrable hR hv_supp h
  have hG0 : ∀ᵐ x : ℝ³, 0 ≤ G x := by
    rw [hGdef]
    exact g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hGsupp : ∀ x : ℝ³, R ≤ ‖x‖ → G x = 0 := by
    intro x hx
    rw [hGdef]
    exact g0_zero_of_norm_ge hv_supp hx h
  have hW0 : ∀ᵐ x : ℝ³, 0 ≤ W x := by
    filter_upwards [hG0] with x hx
    rw [hWdef, wScaled]
    exact div_nonneg hx (convScale_nonneg s x)
  have hWsupp : ∀ x : ℝ³, R ≤ ‖x‖ → W x = 0 := by
    intro x hx
    rw [hWdef, wScaled, hGsupp x hx]
    simp
  have hWmeas : AEMeasurable W := hWint.aestronglyMeasurable.aemeasurable
  have hVgInt : Integrable (fun x : ℝ³ => G x * coulPot G x) := by
    have h1 := newtonianSharp_g0_coulPot_integrable (v := v) (R := R)
      hR hv_nonneg hvrad hv_supp h
    rw [← hGdef] at h1
    exact h1
  have hGjoint : Integrable (fun p : ℝ³ × ℝ³ => G p.1 * G p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    newtonianSharp_integrable_double_coulPot hR hGint hG0 hGsupp hVgInt
  have hWjoint : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    newtonianSharp_integrable_double_of_sharp hδ hWint hW0 hsharpW hGjoint
  refine ⟨?_, ?_⟩
  · exact integrable_pairW_sq_div hWint hW0 hWjoint
  · have hfin : (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ :=
      lintegral_lintegral_ne_top_of_integrable hW0 hWjoint
    have hM1 := integral_pairW_sq_div_sq_le_newtonian_of_fin (W := W) hWint hW0 hWmeas hfin
    have hrect := coulomb_rect_le (R := R) (A := W) (B := W) (g := G) (cA := 1 + δ) (cB := 1 + δ) hR
      hWint hWint hGint hWsupp hWsupp hGsupp hW0 hW0 hG0 hsharpW hsharpW
      (by linarith) (by linarith) hVgInt
    have hnewton : (∫ x : ℝ³, ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)
        = 8 * Real.pi * (∫ x : ℝ³, G x * Classical.choose h x) :=
      chosen_newton_double_eq hR hvrad hv_supp h
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (pairW W q) ^ 2 / ‖q‖ ^ 2)
        ≤ (1 / (4 * Real.pi)) * (∫ x : ℝ³, ∫ y : ℝ³, W x * W y * (‖x - y‖ : ℝ)⁻¹) := hM1
      _ ≤ (1 / (4 * Real.pi)) *
            ((1 + δ) * (1 + δ) * (∫ x : ℝ³, ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)) := by
          exact mul_le_mul_of_nonneg_left hrect (by positivity)
      _ = (1 / (4 * Real.pi)) *
            ((1 + δ) ^ 2 * (8 * Real.pi * (∫ x : ℝ³, G x * Classical.choose h x))) := by
          rw [hnewton]; ring
      _ = 2 * (1 + δ) ^ 2 * (∫ x : ℝ³, G x * Classical.choose h x) := by
          field_simp
          ring

end Work.MGroupInput
