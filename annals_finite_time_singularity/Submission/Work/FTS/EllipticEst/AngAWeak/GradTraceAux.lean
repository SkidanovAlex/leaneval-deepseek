/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak.GradTraceAux` — shared machinery for the a.e. `θ`-traces of `z ∂_z u`

The target `Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe` states that for almost every `z > 0`
the angular slice `θ ↦ z ∂_z u(z,θ)` tends to `0` at both endpoints `0⁺` and `(π/2)⁻`, for a
datum `AeData α u G` carrying the two *almost everywhere* honesties

* `hae` : for a.e. `z > 0` the slice `θ ↦ (z ∂_θ∂_z u(z,θ))² σ(θ)` is integrable on `Iθ`,
* `hint`: `z ↦ w(z)² ∫_θ (z ∂_θ∂_z u(z,θ))² σ(θ)` is integrable on `Iz`

with `σ θ = sin(2θ)^{-η}` and `w z = (1+z)²/z²`.

The proof runs the argument of
`Submission/Work/FTS/EllipticEst/H2W/SlotA/aeI1GradTraceLeft.lean` (the same statement under the
*global* honesty `HkMem α 0 (z ∂_θ∂_z u)`) simultaneously at the two endpoints, carrying the
exceptional null set of `z` along.

This module collects the pieces shared by the two ends:

* `sliceE` — the `σ`-weighted angular energy `∫_θ (∂_θ(z ∂_z u))² σ` of a slice;
* `clairautPoint`, `sliceE_eq` — Clairaut's theorem in the weighted square (it holds for every
  `z ∈ Iz` and every `θ ∈ Iθ`, the endpoints being killed by `σ`);
* `ae_integrableOn_sliceE_of_hae` — `hae` in terms of `∂_θ(z ∂_z u)`;
* `integrableOn_sliceE_of_hint`, `integrableOn_sqrtSliceE_of_hint` — the slice energy and its
  square root are locally integrable in `z`, from `hint`;
* `sliceBoundaryLeftRaw`, `sliceBoundaryRightRaw`, `sliceBoundaryLeft`, `sliceBoundaryRight` —
  `sliceBoundaryLimit` applied to the slice `θ ↦ z ∂_z u(z,θ)`;
* `boundU`, `integrableOn_boundU` — the dominating function of the dominated-convergence step;
* `pz_le_of_slice_bounds` — the resulting pointwise domination of `|∂_z u(z,θ)|`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. The `σ`-weighted angular energy of the slice `θ ↦ z ∂_z u(z,θ)` -/

/-- The `σ`-weighted angular energy `sliceE u z = ∫_θ (∂_θ(z ∂_z u)(z,θ))² σ(θ) dθ` of the slice
`θ ↦ z ∂_z u(z,θ)`; `σ θ = sin(2θ)^{-η}`. -/
def sliceE (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem sliceE_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceE u z :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

/-- `sEta` and `AngSecond.sig` are the same weight `sin(2θ)^{-η}`. -/
theorem sEta_eq_sig (θ : ℝ) :
    Work.FTS.EllipticEst.sEta θ = Work.FTS.EllipticEst.AngSecond.sig θ := rfl

/-- The angular weight is nonnegative on `Iθ`. -/
theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ σ θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The slice energy as an integral over the open interval (the endpoints are null). -/
theorem sliceE_eq_Ioo (u : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceE u z = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm

/-- **Clairaut's theorem in the weighted square.**  On the domain `Iz × Iθ` the two mixed
derivatives `z ∂_θ∂_z u` and `∂_θ(z ∂_z u)` have the same weighted square (at the endpoints
`θ = 0, π/2` both sides are killed by `σ`). -/
theorem clairautPoint {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ
      = (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta, hsin,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · by_cases hz0 : z = 0
    · subst hz0
      simp [Work.Spaces.Dz]
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hne0 : θ ≠ 0 := by intro hh; exact hsin (by subst hh; norm_num)
      have hne1 : θ ≠ Real.pi / 2 := by
        intro hh
        exact hsin (by rw [hh]; rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
      have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (Ne.symm hne0), lt_of_le_of_ne hθ.2 hne1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
        (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ'.1, hθ'.2⟩))
      have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
      simp only [Work.Spaces.Dz]
      rw [show σ θ = Work.FTS.EllipticEst.sEta θ from rfl, hcl]

/-- `sliceE` in terms of the mixed derivative `z ∂_θ∂_z u` (Clairaut). -/
theorem sliceE_eq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ}
    (hz : z ∈ Iz) :
    sliceE u z = ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => (clairautPoint hS hz hθ).symm)

/-! ## 2. The two a.e. honesties -/

/-- The slicewise honesty `hae` of the target, in terms of `∂_θ(z ∂_z u)`. -/
theorem ae_integrableOn_sliceE_of_hae {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iθ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ := by
  filter_upwards [hae, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
  exact MeasureTheory.IntegrableOn.congr_fun hz
    (fun θ hθ => clairautPoint (z := z) (θ := θ) hS
      (le_of_lt (show (0 : ℝ) < z from hzpos)) hθ) measurableSet_Icc

/-- The radial lower bound for `w ^ 2` on a compact subinterval of `(0,∞)`. -/
theorem w_sq_ge {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    (1 : ℝ) ≤ b ^ 4 * (Work.Spaces.w s) ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have h1 : s ^ 4 ≤ b ^ 4 * (1 + s) ^ 4 := by
    have hA : s ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hs0.le hs.2 4
    have hB : (1 : ℝ) ≤ (1 + s) ^ 4 := one_le_pow₀ (by linarith)
    have hC : (0 : ℝ) ≤ b ^ 4 := by positivity
    nlinarith [hA, hB, hC]
  rw [Work.Spaces.w]
  have hws : ((1 + s) ^ 2 / s ^ 2) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by ring
  rw [hws, mul_div_assoc', le_div_iff₀ (pow_pos hs0 4)]
  simpa using h1

/-- The slice energy is locally integrable in `z`, from the honest `hint`. -/
theorem integrableOn_sliceE_of_hint {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Iz := fun s hs => le_trans ha.le hs.1
  have hF : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.w s) ^ 2 * sliceE u s) (Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hint.mono_set hsub) (fun s hs => ?_)
      measurableSet_Icc
    rw [sliceE_eq hS (hsub hs)]
  have hnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ sliceE u s := fun s _ => sliceE_nonneg u s
  have hbound : ∀ s ∈ Set.Icc a b,
      ‖sliceE u s‖ ≤ b ^ 4 * ((Work.Spaces.w s) ^ 2 * sliceE u s) := by
    intro s hs
    have h0 := hnonneg s hs
    have h2 : (0 : ℝ) ≤ (Work.Spaces.w s) ^ 2 := sq_nonneg _
    have hkey : 1 * sliceE u s ≤ (b ^ 4 * (Work.Spaces.w s) ^ 2) * sliceE u s :=
      mul_le_mul_of_nonneg_right (w_sq_ge ha hs) h0
    simpa only [Real.norm_of_nonneg h0, one_mul, mul_assoc] using hkey
  have hcont : ContinuousOn (fun s : ℝ => ((Work.Spaces.w s) ^ 2)⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀
    · have hw : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Icc a b) := by
        rw [show (fun s : ℝ => Work.Spaces.w s) = fun s => (1 + s) ^ 2 / s ^ 2 from rfl]
        exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
          (fun s hs => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hs.1)))
      exact hw.pow 2
    · intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      rw [Work.Spaces.w]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hs0)))
  have haesm : AEStronglyMeasurable (sliceE u) (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    refine AEStronglyMeasurable.congr
      ((hcont.aestronglyMeasurable measurableSet_Icc).mul hF.1) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hwne : (Work.Spaces.w s) ^ 2 ≠ 0 := by
      rw [Work.Spaces.w]; positivity
    rw [Pi.mul_apply]
    exact inv_mul_cancel_left₀ hwne _
  exact Integrable.mono' (hF.const_mul (b ^ 4)) haesm (by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    simpa using hbound s hs)

/-- The square root of the slice energy is locally integrable in `z`. -/
theorem integrableOn_sqrtSliceE_of_hint {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (sliceE u s)) (Set.Icc a b) := by
  have hΦ := integrableOn_sliceE_of_hint hS hint ha hab
  have hnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ sliceE u s := fun s _ => sliceE_nonneg u s
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Integrable.mono' (hΦ.add hone) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hΦ.1
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h0 := hnonneg s hs
    have hle : Real.sqrt (sliceE u s) ≤ 1 + sliceE u s :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [h0, sq_nonneg (sliceE u s)]⟩
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Pi.add_apply]
    linarith [hle]

/-! ## 3. The two slices' one-sided limits, from `sliceBoundaryLimit` -/

/-- The first half of `sliceBoundaryLimit` (the limit at `0⁺`), in `∀ f` form. -/
theorem sliceBoundaryLeftRaw : ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
        ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ' := by
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  exact ⟨K, hKpos, fun f hf1 hfi => (hK f hf1 hfi).1⟩

/-- The second half of `sliceBoundaryLimit` (the limit at `(π/2)⁻`), in `∀ f` form. -/
theorem sliceBoundaryRightRaw : ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ' := by
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  exact ⟨K, hKpos, fun f hf1 hfi => (hK f hf1 hfi).2⟩

/-- The `θ`-slice of `D_z u` has derivative `D_z (∂_θ u)` on the open interval. -/
theorem deriv_Dz_slice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz u s θ') θ = Work.Spaces.Dz (Work.Spaces.pth u) s θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (s, θ) :=
    (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hθ.1, hθ.2⟩))
  have h1 : deriv (fun θ' => Work.Spaces.Dz u s θ') θ
      = s * Work.Spaces.pth (Work.Spaces.pz u) s θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pth, deriv_const_mul_field]
  rw [h1]
  show s * Work.Spaces.pth (Work.Spaces.pz u) s θ
    = s * Work.Spaces.pz (Work.Spaces.pth u) s θ
  exact congrArg (fun t => s * t) (Work.Spaces.pz_pth_comm (f := u) hcd).symm

/-- **The left boundary limit of the slice `θ ↦ z ∂_z u(z,θ)`.** -/
theorem sliceBoundaryLeft {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s K : ℝ} (hs : 0 < s) (hKnn : 0 ≤ K)
    (hraw : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
        ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
          ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
    (hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ) :
    ∃ c : ℝ, Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceE u s := by
  have hcont1 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.Dz u s θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip (fun n => (hS.Dz).forall n) hs 1
  have hsig : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => Work.Spaces.Dz u s θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hE.mono_set Set.Ioo_subset_Icc_self)
      (fun θ hθ => ?_) measurableSet_Ioo
    rw [deriv_Dz_slice hS hs hθ]
    rfl
  obtain ⟨c, hc, hb⟩ := hraw _ hcont1 hsig
  refine ⟨c, hc, fun θ hθ => ?_⟩
  have hE' : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hE.mono_set Set.Ioo_subset_Icc_self
  have hmono : (∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
      * Work.FTS.EllipticEst.sEta t) ≤ sliceE u s := by
    rw [sliceE_eq_Ioo u s]
    exact MeasureTheory.setIntegral_mono_set hE'
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
      (by
        filter_upwards with t ht
        exact ⟨ht.1, lt_trans ht.2 hθ.2⟩)
  have hbθ : (Work.Spaces.Dz u s θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
      ∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
        * Work.FTS.EllipticEst.sEta t := by
    have h := hb θ hθ
    rwa [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => by
        rw [deriv_Dz_slice hS hs ⟨ht.1, lt_trans ht.2 hθ.2⟩])] at h
  exact le_trans hbθ (mul_le_mul_of_nonneg_left hmono
    (mul_nonneg hKnn (Real.rpow_nonneg hθ.1.le _)))

/-- **The right boundary limit of the slice `θ ↦ z ∂_z u(z,θ)`.** -/
theorem sliceBoundaryRight {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {s K : ℝ} (hs : 0 < s) (hKnn : 0 ≤ K)
    (hraw : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
        ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (f θ - c) ^ 2
          ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
            ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2
              * Work.FTS.EllipticEst.thEta θ')
    (hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ) :
    ∃ c : ℝ, Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceE u s := by
  have hcont1 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.Dz u s θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip (fun n => (hS.Dz).forall n) hs 1
  have hsig : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => Work.Spaces.Dz u s θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hE.mono_set Set.Ioo_subset_Icc_self)
      (fun θ hθ => ?_) measurableSet_Ioo
    rw [deriv_Dz_slice hS hs hθ]
    rfl
  obtain ⟨c, hc, hb⟩ := hraw _ hcont1 hsig
  refine ⟨c, hc, fun θ hθ => ?_⟩
  have hE' : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hE.mono_set Set.Ioo_subset_Icc_self
  have hmono : (∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
      * Work.FTS.EllipticEst.sEta t) ≤ sliceE u s := by
    rw [sliceE_eq_Ioo u s]
    exact MeasureTheory.setIntegral_mono_set hE'
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
      (by
        filter_upwards with t ht
        exact ⟨lt_trans hθ.1 ht.1, ht.2⟩)
  have hbθ : (Work.Spaces.Dz u s θ - c) ^ 2
      ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) s t) ^ 2
          * Work.FTS.EllipticEst.sEta t := by
    have h := hb θ hθ
    rwa [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => by
        rw [deriv_Dz_slice hS hs ⟨lt_trans hθ.1 ht.1, ht.2⟩])] at h
  exact le_trans hbθ (mul_le_mul_of_nonneg_left hmono
    (mul_nonneg hKnn (Real.rpow_nonneg (by linarith [hθ.2]) _)))

/-! ## 4. The pointwise domination of `|∂_z u(z,θ)|` -/

/-- **The pointwise domination.**  If the slice `θ ↦ z ∂_z u(z,θ)` has a one-sided limit `c` at an
endpoint and satisfies the quadratic boundary bound at that endpoint, then `|∂_z u(z,θ)|` is
dominated by `|∂_z u(z,1)| + M √(sliceE u z)/z` with `M = √K + √(K (π/2)^{1+η})`. -/
theorem pz_le_of_slice_bounds {u : ℝ → ℝ → ℝ} {s θ c K : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : 0 < K) (hΦ : 0 ≤ sliceE u s)
    (h1 : (Work.Spaces.Dz u s 1 - c) ^ 2 ≤ K * sliceE u s)
    (h2 : (Work.Spaces.Dz u s θ - c) ^ 2
      ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) :
    |Work.Spaces.pz u s θ| ≤ |Work.Spaces.pz u s 1|
      + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := by
  have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hK.le hΦ
  have hKΦ' : 0 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s :=
    mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)) hΦ
  have hc0bd : |c| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
    have h2abs : |Work.Spaces.Dz u s 1 - c| ≤ Real.sqrt (K * sliceE u s) :=
      abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
    calc |c| = |c - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
      _ ≤ |c - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
      _ = |Work.Spaces.Dz u s 1 - c| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
      _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
      _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
  have h1abs : |Work.Spaces.Dz u s θ - c|
      ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by
    have hsq : (Work.Spaces.Dz u s θ - c) ^ 2
        ≤ (Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s)) ^ 2 := by
      rw [Real.sq_sqrt hKΦ']
      exact h2
    exact abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
  have hM1 : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
    Real.sqrt_mul hK.le _
  have hM2 : Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s)
      = Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) * Real.sqrt (sliceE u s) :=
    Real.sqrt_mul (by positivity) _
  have hDzbd : |Work.Spaces.Dz u s θ| ≤ |Work.Spaces.Dz u s 1|
      + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * Real.sqrt (sliceE u s) := by
    have h3 : |Work.Spaces.Dz u s θ| ≤ |c| + Real.sqrt
        (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by
      calc |Work.Spaces.Dz u s θ|
          = |Work.Spaces.Dz u s θ - c + c| := by ring_nf
        _ ≤ |Work.Spaces.Dz u s θ - c| + |c| := abs_add_le _ _
        _ ≤ _ := by linarith
    calc |Work.Spaces.Dz u s θ| ≤ |c| + Real.sqrt
          (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := h3
      _ ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) + Real.sqrt
          (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s) := by linarith
      _ = |Work.Spaces.Dz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s) := by rw [hM1, hM2]; ring
  have hDz : Work.Spaces.Dz u s θ = s * Work.Spaces.pz u s θ := rfl
  have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
  have h4 : |Work.Spaces.Dz u s θ| / s
      ≤ (|Work.Spaces.Dz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceE u s)) / s := div_le_div_of_nonneg_right hDzbd hs.le
  calc |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [hDz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    _ ≤ (|Work.Spaces.Dz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * Real.sqrt (sliceE u s)) / s := h4
    _ = |Work.Spaces.pz u s 1| + (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) := by
        rw [hDz1, abs_mul, abs_of_pos hs]; field_simp

/-! ## 5. The dominating function of the dominated-convergence step -/

/-- The dominating function `s ↦ |∂_z u(s,1)| + M √(sliceE u s)/s` of the DCT step. -/
def boundU (u : ℝ → ℝ → ℝ) (K : ℝ) (s : ℝ) : ℝ :=
  |Work.Spaces.pz u s 1|
    + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
      * (Real.sqrt (sliceE u s) / s)

/-- `boundU` is locally integrable on `(0,∞)`, from `hint`. -/
theorem integrableOn_boundU {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {K : ℝ} (hK : 0 < K) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) := by
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hMnn : 0 ≤ Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
    have := Real.sqrt_nonneg K
    have := Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
    linarith
  have hsqrt := integrableOn_sqrtSliceE_of_hint hS hint ha hab
  have hboundcont : ContinuousOn (fun s : ℝ => |Work.Spaces.pz u s 1|) (Set.Icc a b) :=
    (((hS.pz).curry_z hθ1).continuousOn.abs).mono (fun s hs => lt_of_lt_of_le ha hs.1)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hboundcont
  have hdom : ∀ s ∈ Set.Icc a b, boundU u K s ≤ C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : |Work.Spaces.pz u s 1| ≤ C₁ := by
      simpa only [Real.norm_eq_abs, abs_abs] using hC₁ s hs
    have h2 : Real.sqrt (sliceE u s) / s ≤ Real.sqrt (sliceE u s) / a := by
      gcongr
      exact hs.1
    have h4 : 0 ≤ Real.sqrt (sliceE u s) := Real.sqrt_nonneg _
    have h5 : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (by positivity)
    rw [boundU]
    have h6 : (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s)
        ≤ ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
          * Real.sqrt (sliceE u s) := by
      rw [show ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
            * Real.sqrt (sliceE u s)
          = (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / a) by ring]
      exact mul_le_mul_of_nonneg_left h2 hMnn
    linarith
  have haesm : AEStronglyMeasurable (boundU u K) (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun s : ℝ => |Work.Spaces.pz u s 1|)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hboundcont.aestronglyMeasurable measurableSet_Icc
    have hsqrt_ae : AEStronglyMeasurable (fun s => Real.sqrt (sliceE u s))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (integrableOn_sliceE_of_hint hS hint ha hab).1
    have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc a b) :=
      ContinuousOn.inv₀ continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1))
    have h2 : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (sliceE u s) * s⁻¹)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hsqrt_ae.mul (hinv.aestronglyMeasurable measurableSet_Icc)
    have h3 : AEStronglyMeasurable (fun s : ℝ => (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) * s⁻¹))
        (MeasureTheory.volume.restrict (Set.Icc a b)) := h2.const_mul _
    refine AEStronglyMeasurable.congr (h1.add h3) ?_
    filter_upwards with s
    simp only [Pi.add_apply, boundU]
    ring
  refine Integrable.mono' (g := fun s : ℝ => C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s)) ?_ haesm ?_
  · have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    simpa using (hone.const_mul C₁).add (hsqrt.const_mul
      ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h2 : 0 ≤ boundU u K s := by
      rw [boundU]
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (div_nonneg (Real.sqrt_nonneg _) hs0.le)
      linarith [abs_nonneg (Work.Spaces.pz u s 1)]
    rw [Real.norm_of_nonneg h2]
    exact hdom s hs

end Work.FTS.EllipticEst.AngAWeak
