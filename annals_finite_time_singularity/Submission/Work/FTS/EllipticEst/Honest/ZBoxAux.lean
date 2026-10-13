/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliaries for `HonZBoxPsiBound`

Support module for `Work.FTS.EllipticEst.Honest.HonZBoxPsiBound`.  For an *honest* solution
`(F,Ψ)` of `(PolarBSL)` (the class `Hon` of `Honest.Basic`) and `z > 0`, the goal of
`HonZBoxPsiBound` is the `θ`-integrability of

`θ ↦ (∫_{z/2}^{z} |∂_z²Ψ(u,θ)| du) · sin θ cos²θ`  on `Iθ = [0,π/2]`.

The two `θ`-endpoints are harmless because `sin θ cos²θ` vanishes there; the content is the
weighted `L²`-honesty `Hon.memA` of `A = z²∂_z²Ψ` against `σ = sin(2θ)^{-η}`, which controls
the *radial box average* of `∂_z²Ψ` by Tonelli.

## What is here

* `zhbT`, `zhbSigma` — the angular weights `sin(2θ)^η` and `sin(2θ)^{-η}`;
* `zhbA`, `zhbS`, `zhbG`, `zhbK2`, `zhbC` — the integrand `A`, its `ℋ⁰`-integrand, the angular
  integral of the latter, and the two constants of the majorant;
* the pointwise Young/AM–GM input `two_mul_abs_mul_le_rpow_amgm` is provided by the sibling
  module of the same name; the box Tonelli lemma `ZBoxLintegral` by its own sibling;
* `zhb_contOn_pzIter2`, `zhb_slice_cont`, `zhb_slice_cont_Icc` — joint/slice continuity of
  `∂_z²Ψ` on the open quadrant (from `Hon.sm`, via `Blocks.PzIterTwoContinuousOn`);
* `zhb_aesm_box` — continuity on the open quadrant upgrades to a.e. strong measurability for
  the product of the *box* restrictions `(volume↾[a,b]) ⊗ (volume↾Iθ)`;
* `zhb_S_eq`, `zhb_S_int`, `zhb_Tint` — the pointwise shape of the `ℋ⁰`-integrand and the
  slicewise integrability inputs.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The weights, the integrand and the majorant coefficient -/

/-- The angular weight `sin(2θ)^{-η}` (the `θ`-part of the `ℋ⁰`-weight `ρ`). -/
def zhbSigma (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The reciprocal angular weight `sin(2θ)^{η}`. -/
def zhbT (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ Work.Spaces.eta

/-- `A = z²∂_z²Ψ`, the quantity whose weighted `L²`-honesty is `Hon.memA`. -/
def zhbA (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ

/-- The `ℋ⁰`-integrand of `A`. -/
def zhbS (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun u θ => Work.Spaces.HkIntegrand α 0 (zhbA Ψ) u θ

/-- The angular integral of the `ℋ⁰`-integrand of `A`. -/
def zhbG (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun u => ∫ θ in Work.Spaces.Iθ, zhbS α Ψ u θ

/-- The angular integral of `sinCos2²·sin(2θ)^η`. -/
def zhbK2 : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ

/-- The coefficient of the pointwise majorant of the box average. -/
def zhbC (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun u =>
  (1 / 2) * ((1 / u ^ 2) * zhbG α Ψ u)
    + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2)) * zhbK2)

/-! ## Elementary facts about the angular data -/

/-- `sinCos2 θ = sin θ cos²θ` is nonnegative on `Iθ`. -/
lemma zhb_sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
    (sq_nonneg _)

/-- On `Iθ` the absolute value of `sinCos2` is `sinCos2` itself. -/
lemma zhb_abs_sinCos2 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| = Work.Elliptic.sinCos2 θ :=
  abs_of_nonneg (zhb_sinCos2_nonneg hθ)

/-- If `sin(2θ) = 0` then `sinCos2 θ = 0` (write `sin 2θ = 2 sin θ cos θ`). -/
lemma zhb_sin_two_zero_imp (θ : ℝ) (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  rw [Real.sin_two_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (by norm_num)
    · rw [Work.Elliptic.sinCos2, h2]; ring
  · rw [Work.Elliptic.sinCos2, h1]; ring

lemma zhb_eta_pos : 0 < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

lemma zhb_w_pos {u : ℝ} (hu : 0 < u) : 0 < Work.Spaces.w u := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hu 2)

lemma zhb_T_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ zhbT θ := by
  rw [zhbT]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-! ## The pointwise shape of the `ℋ⁰`-integrand and the slicewise integrability -/

/-- On `Iθ` the `ℋ⁰`-integrand of `A` is `(z²∂_z²Ψ)² w² σ`, the square of the weighted
profile. -/
lemma zhb_S_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {u θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    zhbS α Ψ u θ
      = (u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) ^ 2 * (Work.Spaces.w u) ^ 2 * zhbSigma θ := by
  change Work.Spaces.HkIntegrand α 0 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) u θ
      = (u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) ^ 2 * (Work.Spaces.w u) ^ 2 * zhbSigma θ
  rw [HkIntegrand_zero_eq α (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) u θ,
      sq_profile_eq (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) u θ
        (sin_two_nonneg_of_mem_Iθ hθ)]
  rfl

/-- `Hon.memA` gives the slicewise `σ`-integrability of the `ℋ⁰`-integrand of `A`. -/
lemma zhb_S_int {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {u : ℝ}
    (hu : u ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => zhbS α Ψ u θ) Work.Spaces.Iθ := by
  have hh := h.memA.1 u hu
  have hfun : (fun θ => zhbS α Ψ u θ)
      = (fun θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) := by
    funext θ; rfl
  rwa [hfun]

/-- The companion weight `sinCos2²·sin(2θ)^η` is integrable on `Iθ` (it is continuous and
bounded by `1`). -/
lemma zhb_Tint : IntegrableOn (fun θ => (Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)
    Work.Spaces.Iθ := by
  have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hTcont : Continuous zhbT := by
    change Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
    exact hsin.rpow_const (fun θ => Or.inr (le_of_lt zhb_eta_pos))
  have hsc : Continuous (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2) := by
    change Continuous (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ 2)
    fun_prop
  have hcont : ContinuousOn (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)
      (Set.Icc 0 (π / 2)) := hsc.continuousOn.mul hTcont.continuousOn
  rw [Work.Spaces.Iθ]
  exact ContinuousOn.integrableOn_Icc hcont

/-! ## Joint and slicewise continuity of `∂_z²Ψ` -/

/-- Joint continuity of `∂_z²Ψ` on the open quadrant, from `Hon.sm`. -/
lemma zhb_contOn_pzIter2 {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn (isOpen_Ioi.prod isOpen_Ioo) (h.sm 2)

/-- The `z`-slice of `∂_z²Ψ` at an interior angle is continuous. -/
lemma zhb_slice_cont {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun u => Work.Spaces.pzIter 2 Ψ u θ) (Set.Ioi 0) := by
  have hmaps : Set.MapsTo (fun u : ℝ => (u, θ)) (Set.Ioi 0)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun u hu => ⟨hu, hθ⟩
  have hinner : Continuous (fun u : ℝ => (u, θ)) := continuous_id.prodMk continuous_const
  have hcomp := (zhb_contOn_pzIter2 h).comp hinner.continuousOn hmaps
  have hfun : (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) ∘ (fun u : ℝ => (u, θ))
      = fun u => Work.Spaces.pzIter 2 Ψ u θ := by funext u; rfl
  rwa [hfun] at hcomp

/-- The same slice continuity restricted to a compact box `[a,b]` with `0 < a`. -/
lemma zhb_slice_cont_Icc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u => Work.Spaces.pzIter 2 Ψ u θ) (Set.Icc a b) :=
  (zhb_slice_cont h hθ).mono (fun _ hx => lt_of_lt_of_le ha hx.1)

/-! ## A.e. strong measurability on the box -/

/-- A function continuous on the open quadrant is a.e. strongly measurable for the product of
the restrictions to a box `[a,b]` (`0 < a`) and to `Iθ`.  The box differs from the open
quadrant only by the null lines `θ = 0`, `θ = π/2`. -/
lemma zhb_aesm_box {g : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo 0 (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  have hprod : ((Set.Icc a b) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Icc a b ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθ
  have hsub : (Set.Icc a b ×ˢ Set.Ioo 0 (π / 2))
      ⊆ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    exact ⟨lt_of_lt_of_le ha hu.1, ht⟩
  have hQm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hQm
  have hle : (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Icc a b ×ˢ Set.Ioo 0 (π / 2))
      ≤ (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  have h2 : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Icc a b ×ˢ Set.Ioo 0 (π / 2))) :=
    hmain.mono_measure hle
  rw [MeasureTheory.Measure.prod_restrict,
    MeasureTheory.Measure.restrict_congr_set hprod]
  exact h2

end Work.FTS.EllipticEst.Honest
