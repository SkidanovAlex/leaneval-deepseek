/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H5/AngRad5/AngRadHkMem5` — the level-`5` angular `×` radial engine

This file proves `Work.FTS.StrongEps.H5.AngRad5.AngRadEngine5` (the interface fixed in
`H5/AngRad5/Engine5.lean`): for a separable product `(z,θ) ↦ a θ · r z` of a `θ`-only profile
`a` whose `D_θ`-iterates of orders `1..5` are dominated by `B1 · G` and a radial profile `r`
whose lift `(z,θ) ↦ r z` is `ℋ⁵`-honest with `HkNorm α 5 ≤ Crad`, the product is `ℋ⁵`-honest
and

`HkNorm α 5 (a·r) ≤ C · √(B0²·10⁴ + 5·B1²·M) · Crad`,  `M ≥ ∫_θ G(θ)²·sin(2θ)^{-γ}`,

with a universal `C` (the constant `1` works).

## The proof

The pointwise input is the already proven `H5.AngRad5.HkIntegrand_ang_rad_le5` (`n = 5`):
for every `z` and every `θ ∈ Iθ`,

`HkIntegrand α 5 (a·r) z θ ≤ Rint₅ r z · (B0²·smE θ + 5·B1²·G(θ)²·smG α θ)`,

where `Rint₅ r z = Σ_{i≤5}(D_z^i r z)²·w(z)²` is the level-`5` radial density and
`smE = sin(2θ)^{-η}`, `smG α = sin(2θ)^{-γ(α)}` are the two angular weights.  Writing
`AngMaj α B0 B1 G θ` for the second factor, there are two halves:

* **membership** (`HkMem`): the majorant criterion `LocData.HkMem_of_majorant`, with majorant
  `Rint₅ r z · AngMaj α B0 B1 G θ` (integrable in `θ` because `smE` is and `G²·smG` is by
  hypothesis, and in `z` because `Rint₅ r` is);
* **the norm bound**: integrate the pointwise bound in `θ` (`AngMaj` is `θ`-only, so the slice
  integral is `Rint₅ r z · ∫_θ AngMaj`), then in `z`.  The angular integral is
  `B0²·K_θ + 5·B1²·∫_θ G²·smG` with `K_θ = ∫_θ sin(2θ)^{-η} ≤ 10⁴`, so it is at most
  `B0²·10⁴ + 5·B1²·M`, and the `z`-integral of `Rint₅ r` is at most `HkSq α 5` of the radial
  lift (the exact value `HkSq_rad_eq5`: `HkSq α 5 (radial) = (∫_z Rint₅ r)·K_θ`, and `K_θ ≥ 1`).
  Hence `HkSq α 5 (a·r) ≤ (B0²·10⁴ + 5·B1²·M)·HkSq α 5 (radial)`, and taking square roots
  (using `HkNorm α 5 (radial) ≤ Crad`) gives the claim with `C = 1`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.H5.AngRad5.Engine5
import Submission.Work.FTS.StrongEps.H5.RadMem5
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngRad5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular majorant of the engine -/

/-- The angular majorant of the level-`5` engine:
`B0²·sin(2θ)^{-η} + 5·B1²·G(θ)²·sin(2θ)^{-γ(α)}`.  It is the `θ`-only factor produced by the
pointwise separation lemma `HkIntegrand_ang_rad_le5`. -/
def AngMaj (α B0 B1 : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + 5 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ

/-- The angular majorant is nonnegative on `Iθ`. -/
theorem AngMaj_nonneg {α B0 B1 : ℝ} {G : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ AngMaj α B0 B1 G θ := by
  have h1 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have h2 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  have h3 : 0 ≤ 5 * B1 ^ 2 * (G θ) ^ 2 := by positivity
  rw [AngMaj]
  exact add_nonneg (mul_nonneg (sq_nonneg B0) h1) (mul_nonneg h3 h2)

/-- Integrability in `θ` of the angular majorant on `Iθ`: `smE` is integrable
(`AuxAngRad.integrableOn_smE`) and `G²·smG` is integrable by hypothesis. -/
theorem integrableOn_AngMaj {α B0 B1 : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (AngMaj α B0 B1 G) Work.Spaces.Iθ := by
  have h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + (5 * B1 ^ 2) * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ :=
    (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul (B0 ^ 2)).add
      (hGint.const_mul (5 * B1 ^ 2))
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Icc
  rw [AngMaj]
  ring

/-- The `θ`-integral of the angular majorant splits into the two pieces
`B0²·K_θ + 5·B1²·∫_θ G²·smG`. -/
theorem integral_AngMaj {α B0 B1 : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      = B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth
        + 5 * B1 ^ 2 * (∫ θ in Work.Spaces.Iθ,
            G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hEq : (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      = ∫ θ in Work.Spaces.Iθ, (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + (5 * B1 ^ 2) * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [AngMaj]
    ring
  rw [hEq, MeasureTheory.integral_add
      (Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE.const_mul (B0 ^ 2))
      (hGint.const_mul (5 * B1 ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [Work.FTS.Nonlinear.RadialProd.Kth]

/-- The `θ`-integral of the angular majorant is at most `B0²·10⁴ + 5·B1²·M`, using
`K_θ ≤ 10⁴` (`StrongEps.H5.Kth_le_1e4`) and the mass bound `∫_θ G²·smG ≤ M`. -/
theorem integral_AngMaj_le {α B0 B1 M : ℝ} {G : ℝ → ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hmass : (∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) :
    (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ) ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M := by
  rw [integral_AngMaj hGint]
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := Work.FTS.StrongEps.H5.Kth_le_1e4
  have h1 : B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth ≤ B0 ^ 2 * 10 ^ 4 :=
    mul_le_mul_of_nonneg_left hKth (sq_nonneg B0)
  have h2 : 5 * B1 ^ 2 * (∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ 5 * B1 ^ 2 * M :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  linarith

/-! ## The pointwise separation -/

/-- The pointwise separation of the `ℋ⁵`-integrand of the product `a·r`, with the general
angular majorant `G` of the engine: the statement of `HkIntegrand_ang_rad_le5` with `n = 5`
and its angular factor replaced by `Rint₅ · AngMaj`. -/
theorem hkIntegrand_ang_le5 {α B0 B1 : ℝ} {a r G : ℝ → ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ := by
  have h := Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5 (n := 5) le_rfl
    (α := α) (a := a) (r := r) (G := G) (B0 := B0) (B1 := B1) (z := z) ha0 ha1 hθ
  simpa only [Work.FTS.StrongEps.H5.Rint5, AngMaj] using h

/-! ## The level-`5` radial density -/

/-- For a radial lift that is `ℋ⁵`-honest, the level-`5` radial density `Rint₅ r` is integrable
on `Iz` and its integral is at most `HkSq α 5` of the lift.  This is the exact value
`HkSq_rad_eq5` (`HkSq α 5 (radial) = (∫_z Rint₅ r)·K_θ`) together with `K_θ ≥ 1`. -/
theorem rint5_mem {α : ℝ} {r : ℝ → ℝ}
    (hrmem : Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z)) :
    MeasureTheory.IntegrableOn (Work.FTS.StrongEps.H5.Rint5 r) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
        ≤ Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one Work.FTS.Nonlinear.RadialProd.one_le_Kth)
  -- the `θ`-slice integral of the radial lift's integrand
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ)
      = Work.FTS.StrongEps.H5.Rint5 r z * Work.FTS.Nonlinear.RadialProd.Kth := by
    intro z
    have hkey : (fun θ : ℝ => Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
            * Work.FTS.Nonlinear.RadialProd.smE θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Work.Elliptic.HkIntegrand_rad α 5 r z hθ, Work.FTS.StrongEps.H5.Rint5,
        Finset.sum_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.smE]
    rw [MeasureTheory.integral_congr_ae hkey, MeasureTheory.integral_const_mul]
    rfl
  have h1 : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z) z θ) Work.Spaces.Iz := hrmem.2
  have h2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
        * Work.FTS.Nonlinear.RadialProd.Kth) Work.Spaces.Iz :=
    h1.congr (Filter.Eventually.of_forall hinner)
  refine ⟨?_, ?_⟩
  · have h3 := h2.div_const Work.FTS.Nonlinear.RadialProd.Kth
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    show Work.FTS.StrongEps.H5.Rint5 r z * Work.FTS.Nonlinear.RadialProd.Kth
      / Work.FTS.Nonlinear.RadialProd.Kth = Work.FTS.StrongEps.H5.Rint5 r z
    rw [mul_div_cancel_right₀ _ hKth]
  · have hSq : Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
        = (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * Work.FTS.Nonlinear.RadialProd.Kth := Work.FTS.StrongEps.H5.HkSq_rad_eq5 α r
    have hnn : 0 ≤ ∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z :=
      MeasureTheory.integral_nonneg (fun z => Work.FTS.StrongEps.H5.Rint5_nonneg r z)
    calc (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
        ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * Work.FTS.Nonlinear.RadialProd.Kth := by
          nth_rewrite 1 [← mul_one (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongEps.H5.Rint5 r z)]
          exact mul_le_mul_of_nonneg_left Work.FTS.Nonlinear.RadialProd.one_le_Kth hnn
      _ = Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := hSq.symm

/-! ## The engine -/

theorem AngRadHkMem5 : Work.FTS.StrongEps.H5.AngRad5.AngRadEngine5 := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα hα1 a r G B0 B1 M Crad ha hr hGnn hGint hB0 hB1 hM hCrad ha0 ha1 hmass
    hrmem hCradbd
  -- ### the angular data
  have hAi : MeasureTheory.IntegrableOn (AngMaj α B0 B1 G) Work.Spaces.Iθ :=
    integrableOn_AngMaj (α := α) (B0 := B0) (B1 := B1) (G := G) hGint
  have hAint : (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)
      ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M :=
    integral_AngMaj_le (α := α) (B0 := B0) (B1 := B1) (M := M) (G := G) hGint hmass hB0 hB1
  have hMAnn : 0 ≤ B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M :=
    add_nonneg (mul_nonneg (sq_nonneg B0) (by norm_num))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B1)) hM)
  -- ### the pointwise domination
  have hdom : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ
        ≤ Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ :=
    fun z _ θ hθ => hkIntegrand_ang_le5 (α := α) (B0 := B0) (B1 := B1) (a := a) (r := r)
      (G := G) ha0 ha1 hθ
  -- ### the radial data
  obtain ⟨hRint_int, hRint_le⟩ := rint5_mem (α := α) hrmem
  -- ### membership, by the majorant criterion
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha hr).continuousOn_HkIntegrand
      α 5).mono (fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hp.1, hp.2.1, hp.2.2⟩)
  have hmem : Work.Spaces.HkMem α 5 (fun z θ => a θ * r z) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 5 (f := fun z θ => a θ * r z)
      (M := fun z θ => Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
      hcont ?_ ?_ ?_
    · intro z _
      exact hAi.const_mul (Work.FTS.StrongEps.H5.Rint5 r z)
    · have hz : MeasureTheory.IntegrableOn
          (fun z : ℝ => Work.FTS.StrongEps.H5.Rint5 r z
            * (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ)) Work.Spaces.Iz :=
        hRint_int.mul_const _
      refine hz.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (MeasureTheory.integral_const_mul (Work.FTS.StrongEps.H5.Rint5 r z)
        (AngMaj α B0 B1 G)).symm
    · intro z hz θ hθ
      exact hdom z hz θ hθ
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hslices : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ)
        ≤ Work.FTS.StrongEps.H5.Rint5 r z * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) := by
    intro z hz
    have hAint' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
        Work.Spaces.Iθ := hAi.const_mul _
    have h1 := MeasureTheory.integral_mono_ae (hmem.1 z hz) hAint'
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hdom z hz θ hθ))
    have h2 : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.StrongEps.H5.Rint5 r z * AngMaj α B0 B1 G θ)
        = Work.FTS.StrongEps.H5.Rint5 r z
          * (∫ θ in Work.Spaces.Iθ, AngMaj α B0 B1 G θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hAint
      (Work.FTS.StrongEps.H5.Rint5_nonneg r z))
  have hSq : Work.Spaces.HkSq α 5 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
        * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by
    calc Work.Spaces.HkSq α 5 (fun z θ => a θ * r z)
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 5 (fun z θ => a θ * r z) z θ) := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) :=
          MeasureTheory.integral_mono_ae hmem.2 (hRint_int.mul_const _)
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslices)
      _ = (∫ z in Work.Spaces.Iz, Work.FTS.StrongEps.H5.Rint5 r z)
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) := MeasureTheory.integral_mul_const _ _
      _ ≤ Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
            * (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) :=
          mul_le_mul_of_nonneg_right hRint_le hMAnn
      _ = (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z) := by ring
  have hCrad' : Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) ≤ Crad := hCradbd
  have hnorm : Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => a θ * r z))
        ≤ Real.sqrt ((B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) := Real.sqrt_le_sqrt hSq
      _ = Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M)
            * Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) :=
          Real.sqrt_mul hMAnn _
      _ ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad :=
          mul_le_mul_of_nonneg_left hCrad' (Real.sqrt_nonneg _)
  calc Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := hnorm
    _ = 1 * Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad := by ring

end Work.FTS.StrongEps.H5.AngRad5
