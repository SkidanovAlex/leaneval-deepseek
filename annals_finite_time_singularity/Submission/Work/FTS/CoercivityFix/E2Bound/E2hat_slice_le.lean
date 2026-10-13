/-
# The `θ`-slice bound for the `D_z`-commutator defect `Ê₂` (`E2hat_slice_le`)

`Ê₂ f = (2zf + 3z·D_θ f)/(1+z)² = φ(z)·(2f + 3D_θf)` with `φ(z) = z/(1+z)²` is the
`D_z`-commutator defect of the clean operator `Lhat` (`CoercivityFix.Basic`).  This file proves
the *sliced* `ℋⁿ`-bound

  `∫_θ HkIntegrand α n (Ê₂ f)(z,θ) ≤ C · (∫_θ HkIntegrand α n f(z,θ) + ∫_θ HkIntegrand α n (D_θf)(z,θ))`

with a constant `C` uniform in `z ∈ [0,∞)` and in `f`.

## Why two pointwise bounds are needed

Fix `z` and put `g₁ = HkIntegrand α n f`, `g₂ = HkIntegrand α n (D_θf)`,
`g₃ = HkIntegrand α n (Ê₂f)` (functions of `θ`).  The **forward** pointwise bound
`g₃ ≤ C₁(g₁ + g₂)` — from the Leibniz rule for the `z`-only multiplier `φ`, subadditivity and
homogeneity — gives the slice inequality *as soon as the dominating function is integrable*,
since `MeasureTheory.integral_mono_of_nonneg` needs the *upper* function integrable:

  `∫g₃ ≤ ∫C₁(g₁+g₂) = C₁(∫g₁ + ∫g₂)`  provided `g₁, g₂ ∈ L¹`.

But `HkMem α n f` only gives `g₁ ∈ L¹`, so we compare `∫g₃` with `C₁·(∫g₁ + ∫g₂)` by cases on
`IntegrableOn`:  if `g₂ ∈ L¹` the monotonicity step applies; if not, `∫g₂ = 0` by the
junk-value convention (`MeasureTheory.integral_undef`) and we must know that `∫g₃ = 0` too,
i.e. that `g₃ ∉ L¹`.  This is exactly what the **reverse** pointwise bound
`g₂ ≤ C₂(z)(g₃ + g₁)` gives: since `Ê₂ f = φ·G` with `G = 2f + 3D_θf` and `φ(z) ≠ 0` for
`z > 0`, the jet of `G` at the fixed `z` is a triangular (hence invertible) combination of
the jet of `Ê₂ f`, so `HkIntegrand α n G ≲ g₃` and `D_θf = (G − 2f)/3` yields `g₂ ≲ g₃ + g₁`.
Hence `g₃ ∈ L¹ ⟹ g₂ ∈ L¹`, and the `IntegrableOn` case split closes.

## The constants

`C₁ = 18·Cfw·(1+K)² + 1` is *uniform in `z`*: `Cfw` is the constant of
`SlotMul.HkIntegrand_zmul_uniform` (uniform in the point once a uniform bound `K` on the
`Zop`-iterates of the multiplier is given) and `K` is the uniform bound
`SlotMul.Zop_iterate_phiZ_bound` for the profile `φ`; the extra factor `18` absorbs
`HkIntegrand (2f + 3D_θf) ≤ 8g₁ + 18g₂` (subadditivity + homogeneity).
`C₂ = (2/9)Cz + 1` may depend on `z` (it is `≳ 1/φ(z)ⁿ`, unbounded as `z → 0⁺, ∞`); it is
used only to deduce the *integrability* of `g₂` from that of `g₁, g₃`, never in `C`.

## Layout

* `phiZ`, `auxG` — the multiplier `z/(1+z)²` and `G = 2f + 3D_θf`;
* the algebra `Ê₂ f = φ·G`, the vanishing of `HkIntegrand` on `z = 0`, and
  `restrict_Iθ_eq_Ioo`: `Iθ` and `(0,π/2)` carry the same restricted Lebesgue measure, so all
  estimates may be carried out on the open angle interval, where the data are `C^∞`;
* the measurability of the angular slices (needed for `Integrable.mono'`);
* the two pointwise bounds and the integral step.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkIntegrand_add_le
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zrev_at_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.CoercivityFix.E2Bound.SlotMul

/-! ## The multiplier `φ(z) = z/(1+z)²` and the auxiliary function `G = 2f + 3D_θf` -/

/-- The radial profile of the commutator defect: `φ(z) = z/(1+z)²`. -/
private def phiZ : ℝ → ℝ := fun z => z / (1 + z) ^ 2

/-- `G f = 2f + 3D_θf`, so that `Ê₂ f = φ · G f`. -/
private def auxG (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * f z θ + 3 * Work.Spaces.Dth f z θ

/-- `φ` is `C^∞` on `(-1,∞)` (a quotient with non-vanishing denominator). -/
private lemma phiZ_contDiffOn :
    ContDiffOn ℝ Work.Stability.smoothOrder phiZ (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z) (Set.Ioi (-1)) :=
    contDiff_id.contDiffOn
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2)
      (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiff_id.contDiffOn).pow 2
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (fun z : ℝ => (1 + z) ^ 2) z ≠ 0 := fun z hz => by
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have h : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
    hnum.div hden hne
  exact h

/-- `φ(z) ≠ 0` for `z > 0`. -/
private lemma phiZ_ne_zero {z : ℝ} (hz : 0 < z) : phiZ z ≠ 0 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  simp only [phiZ]
  positivity

/-- The algebraic identity `Ê₂ f = φ · G f` (valid for every real `z`: at the pole `z = -1`
both sides are `0` by the totalised division). -/
private lemma E2hat_eq_phiZ_mul (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.CoercivityFix.E2hat f z θ = phiZ z * auxG f z θ := by
  rw [Work.FTS.CoercivityFix.E2hat_eq, phiZ, auxG, div_mul_eq_mul_div]
  congr 1
  ring

/-- The same identity at the level of functions; used to rewrite `HkIntegrand` of `Ê₂ f`. -/
private lemma E2hat_eq_phiZ_auxG (f : ℝ → ℝ → ℝ) :
    Work.FTS.CoercivityFix.E2hat f = fun z θ => phiZ z * auxG f z θ := by
  funext z θ
  exact E2hat_eq_phiZ_mul f z θ

/-- `G f` is smooth on the open quadrant whenever `f` is. -/
private lemma auxG_smoothQuad {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (auxG f) := by
  have h1 : Work.FTS.LocData.SmoothQuad (fun z θ => 2 * f z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 hf
  have h2 : Work.FTS.LocData.SmoothQuad (fun z θ => 3 * Work.Spaces.Dth f z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul 3 (Work.FTS.LocData.SmoothQuad.DthIter hf 1)
  have h3 := Work.FTS.LocData.smoothQuad_add h1 h2
  exact h3

/-! ## Vanishing at `z = 0` -/

/-- `HkIntegrand` vanishes at `z = 0` (the weight `w 0 = 0` kills every summand). -/
private lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (n : ℕ) (h : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α n h 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have h1 : ∀ i : ℕ,
      (Work.Spaces.DzIter i h 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num)]
  have h2 : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i h 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0) = 0 := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      have hW : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, Work.Spaces.w]
      rw [hW, mul_zero, zero_pow (by norm_num)]
    · rw [if_neg hc]
  rw [Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => h2 i j)), add_zero]

/-! ## `Iθ` and `(0,π/2)` carry the same measure -/

/-- The two boundary points `{0, π/2}` are null, so `Iθ` and `(0,π/2)` carry the same
restricted Lebesgue measure. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := π / 2)).symm

/-! ## Measurability of the angular slices -/

/-- For a `SmoothQuad` datum and `z > 0`, the angular slice of the `ℋⁿ`-integrand is almost
everywhere strongly measurable on `(0,π/2)` (it is continuous there). -/
private lemma aestronglyMeasurable_slice_HkIntegrand (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
      ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
  have hQd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α n f p.1 p.2)
      Work.FTS.LocData.Qd :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n f hf
  have hmap : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α n f z θ)
      (Set.Ioo 0 (π / 2)) :=
    hQd.comp hmap (fun θ hθ => by
      simp only [Work.FTS.LocData.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hθ ⊢
      exact ⟨hz, hθ⟩)
  exact hcont.aestronglyMeasurable (μ := (volume : Measure ℝ)) measurableSet_Ioo

/-- A nonnegative function has nonnegative set integral (the junk value `0` included). -/
private lemma integral_nonneg_of_forall_nonneg {g : ℝ → ℝ} {s : Set ℝ}
    (hg : ∀ θ, 0 ≤ g θ) : 0 ≤ ∫ θ in s, g θ := by
  by_cases h : IntegrableOn g s
  · exact MeasureTheory.integral_nonneg (f := g) (fun θ => hg θ)
  · rw [MeasureTheory.integral_undef h]

/-! ## The slice inequality -/

theorem E2hat_slice_le (α : ℝ) (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f → Work.Spaces.HkMem α n f → ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ) ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)) := by
  obtain ⟨Cfw, hCfw, hFw⟩ := HkIntegrand_zmul_uniform α n
  obtain ⟨K, hKnn, hKbd⟩ := Zop_iterate_phiZ_bound n
  set C₁ : ℝ := 18 * Cfw * (1 + K) ^ 2 + 1 with hC₁def
  have hC₁pos : 0 < C₁ := by rw [hC₁def]; positivity
  refine ⟨C₁, hC₁pos, ?_⟩
  intro f hf hmem z hz
  rw [restrict_Iθ_eq_Ioo]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: every integrand vanishes
    subst hz0
    have hzero : ∀ g : ℝ → ℝ → ℝ,
        (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Spaces.HkIntegrand α n g 0 θ) = 0 := by
      intro g
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α n g 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => HkIntegrand_eq_zero_of_z_eq_zero α n g θ]
      simp
    rw [hzero (Work.FTS.CoercivityFix.E2hat f), hzero f, hzero (Work.Spaces.Dth f)]
    positivity
  · -- `z > 0`
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hzpos)
    have hGsm : Work.FTS.LocData.SmoothQuad (auxG f) := auxG_smoothQuad hf
    have hDthsm : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) :=
      Work.FTS.LocData.SmoothQuad.DthIter hf 1
    have hg1int : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n f z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) := by
      have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hmem.1 z hz
      rw [restrict_Iθ_eq_Ioo] at h
      exact h
    -- ### the forward pointwise bound, with the uniform constant `C₁`
    have hP1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ C₁ * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
      intro θ hθ
      have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hfw := hFw phiZ K hKnn (fun b hb z' hz' => hKbd b hb z' hz') phiZ_contDiffOn
        (auxG f) hGsm z hzpos θ hθ
      rw [← E2hat_eq_phiZ_auxG f] at hfw
      have hsplit : Work.Spaces.HkIntegrand α n
            (fun z θ => 2 * f z θ + 3 * Work.Spaces.Dth f z θ) z θ
          ≤ 8 * Work.Spaces.HkIntegrand α n f z θ
            + 18 * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ := by
        have h := Work.FTS.LocData.HkIntegrand_add_le α n
          (a := fun z θ => 2 * f z θ) (b := fun z θ => 3 * Work.Spaces.Dth f z θ)
          (Work.FTS.LocData.smoothQuad_const_mul 2 hf)
          (Work.FTS.LocData.smoothQuad_const_mul 3 hDthsm) hzIz hθIθ
        rw [Work.FTS.LocData.HkIntegrand_const_mul α n 2 f z θ,
          Work.FTS.LocData.HkIntegrand_const_mul α n 3 (Work.Spaces.Dth f) z θ] at h
        nlinarith [h]
      have hg1nn : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
        Work.Spaces.HkIntegrand_nonneg α n f z θ
      have hg2nn : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
      have hpos : 0 ≤ 10 * Cfw * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n f z θ := by
        have h1 : 0 ≤ Cfw := le_of_lt hCfw
        have h2 : 0 ≤ (1 + K) ^ 2 := sq_nonneg _
        positivity
      calc Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ Cfw * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n (auxG f) z θ := hfw
        _ ≤ Cfw * (1 + K) ^ 2
              * (8 * Work.Spaces.HkIntegrand α n f z θ
                  + 18 * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ ≤ C₁ * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
            rw [hC₁def]
            nlinarith [hg1nn, hg2nn, hpos]
    -- ### the reverse pointwise bound, with the (`z`-dependent) constant `(2/9)Cz + 1`
    obtain ⟨Cz, hCzpos, hCz⟩ :=
      HkIntegrand_zrev_at_z α n phiZ phiZ_contDiffOn z hzpos (phiZ_ne_zero hzpos)
    set Kc : ℝ := (2 / 9) * Cz + 1 with hKcdef
    have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
    have hP2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ
          ≤ Kc * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
            + Kc * Work.Spaces.HkIntegrand α n f z θ := by
      intro θ hθ
      have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      -- the reverse bound for `G`
      have hG : Work.Spaces.HkIntegrand α n (auxG f) z θ
          ≤ Cz * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ := by
        have h := hCz (auxG f) hGsm θ hθ
        rwa [← E2hat_eq_phiZ_auxG f] at h
      -- `D_θf = (1/3)·G − (2/3)·f`
      have hfun : Work.Spaces.Dth f
          = fun z θ => (1 / 3) * auxG f z θ + (-(2 / 3)) * f z θ := by
        funext z θ
        simp only [auxG]
        ring
      have hsplit : Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α n (fun z θ => (1 / 3) * auxG f z θ) z θ
            + 2 * Work.Spaces.HkIntegrand α n (fun z θ => (-(2 / 3)) * f z θ) z θ := by
        rw [hfun]
        exact Work.FTS.LocData.HkIntegrand_add_le α n
          (a := fun z θ => (1 / 3) * auxG f z θ) (b := fun z θ => (-(2 / 3)) * f z θ)
          (Work.FTS.LocData.smoothQuad_const_mul (1 / 3) hGsm)
          (Work.FTS.LocData.smoothQuad_const_mul (-(2 / 3)) hf) hzIz hθIθ
      rw [Work.FTS.LocData.HkIntegrand_const_mul α n (1 / 3) (auxG f) z θ,
        Work.FTS.LocData.HkIntegrand_const_mul α n (-(2 / 3)) f z θ] at hsplit
      have hg3nn : 0 ≤ Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ :=
        Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ
      have hg1nn : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
        Work.Spaces.HkIntegrand_nonneg α n f z θ
      have h29 : 0 ≤ (2 / 9) * Cz := by positivity
      have hpos1 : 0 ≤ (2 / 9) * (Cz * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ) :=
        mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hCzpos) hg3nn)
      have hpos2 : 0 ≤ (2 / 9) * Cz * Work.Spaces.HkIntegrand α n f z θ :=
        mul_nonneg h29 hg1nn
      calc Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ
          ≤ (2 / 9) * Work.Spaces.HkIntegrand α n (auxG f) z θ
              + (8 / 9) * Work.Spaces.HkIntegrand α n f z θ := by nlinarith [hsplit]
        _ ≤ (2 / 9) * (Cz * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
              + (8 / 9) * Work.Spaces.HkIntegrand α n f z θ := by
            have h := mul_le_mul_of_nonneg_left hG h29
            linarith
        _ ≤ Kc * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
              + Kc * Work.Spaces.HkIntegrand α n f z θ := by
            rw [hKcdef]
            nlinarith [hg3nn, hg1nn, hpos1, hpos2]
    -- ### the integral step
    by_cases h3 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        (Set.Ioo (0 : ℝ) (π / 2))
    · -- `g₂ ∈ L¹` by the reverse bound, then monotonicity of the integral
      have h2int : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
          (Set.Ioo (0 : ℝ) (π / 2)) :=
        Integrable.mono'
          (f := fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
          (g := fun θ => Kc * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
            + Kc * Work.Spaces.HkIntegrand α n f z θ)
          ((h3.const_mul Kc).add (hg1int.const_mul Kc))
          (aestronglyMeasurable_slice_HkIntegrand α n (f := Work.Spaces.Dth f) hDthsm hzpos)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)]
            exact hP2 θ hθ))
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (π / 2)))
        (f := fun θ => Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        (g := fun θ => C₁ * (Work.Spaces.HkIntegrand α n f z θ
            + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ))
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ((hg1int.add h2int).const_mul C₁)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hP1 θ hθ))
      refine hmono.trans_eq ?_
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hg1int h2int]
    · -- `g₃ ∉ L¹`: its integral is `0` by convention, and both remaining integrals are `≥ 0`
      rw [MeasureTheory.integral_undef h3]
      have hA : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Spaces.HkIntegrand α n f z θ :=
        integral_nonneg_of_forall_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α n f z θ)
      have hB : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
        integral_nonneg_of_forall_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)
      exact mul_nonneg (le_of_lt hC₁pos) (by linarith)

end Work.FTS.CoercivityFix.E2Bound
