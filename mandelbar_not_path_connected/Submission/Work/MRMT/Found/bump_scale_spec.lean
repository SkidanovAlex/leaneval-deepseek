/-
# Rescaled bump functions on `ℂ` with controlled Wirtinger derivatives

This file constructs the family of smoothing kernels used in the Ahlfors–Bers / measurable
Riemann mapping construction: a fixed `C^∞` bump `ρ` on `ℂ` (supported in the closed unit ball,
with total mass `1`) is rescaled to `η_r(u) = r⁻² • ρ(r⁻¹ • u)`.

For `r > 0` the rescaling

* keeps the total mass: `∫ η_r = ∫ ρ = 1`;
* shrinks the support: `support η_r ⊆ closedBall 0 r`;
* multiplies pointwise values by `r⁻²`: `‖η_r u‖ ≤ (sup ‖ρ‖) / r²`;
* multiplies the `L¹`-norms of the Wirtinger derivatives `∂η_r`, `∂̄η_r` by `r⁻¹`.

Everything is proved from the elementary scaling formula for the Lebesgue integral on the
finite dimensional real vector space `ℂ`, `MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`,
together with the unconditional chain rules `fderiv_comp_smul` and `fderiv_const_smul_field`.
-/
import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

noncomputable section

/-! ## The reference bump -/

/-- A fixed smooth bump at `0 : ℂ` with `rIn = 1/2` and `rOut = 1`, so that its support is
contained in the closed unit ball. -/
def bumpBase : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The reference bump `ρ`, viewed as a complex-valued function on `ℂ`. -/
abbrev refKernel : ℂ → ℂ := fun z => (bumpBase.normed (volume : Measure ℂ) z : ℂ)

theorem refKernel_contDiff :
    ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) refKernel := by
  have h : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞)
      (bumpBase.normed (volume : Measure ℂ)) :=
    bumpBase.contDiff_normed (μ := (volume : Measure ℂ)) (n := ⊤)
  exact Complex.ofRealCLM.contDiff.comp h

theorem refKernel_continuous : Continuous refKernel :=
  Complex.ofRealCLM.continuous.comp (bumpBase.continuous_normed (μ := (volume : Measure ℂ)))

theorem refKernel_hasCompactSupport : HasCompactSupport refKernel := by
  have h := bumpBase.hasCompactSupport_normed (μ := (volume : Measure ℂ))
  exact h.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

theorem refKernel_support_subset : Function.support refKernel ⊆ Metric.closedBall 0 1 := by
  have h1 : Function.support refKernel =
      Function.support (bumpBase.normed (volume : Measure ℂ)) := by
    ext z
    simp only [refKernel, Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  rw [h1, ContDiffBump.support_normed_eq]
  exact Metric.ball_subset_closedBall

theorem refKernel_integral : ∫ z, refKernel z = 1 := by
  have hint : Integrable (bumpBase.normed (volume : Measure ℂ)) (volume : Measure ℂ) :=
    bumpBase.integrable_normed (μ := (volume : Measure ℂ))
  have h := Complex.ofRealCLM.integral_comp_comm hint
  have h2 : (∫ z, refKernel z) =
      ((∫ z, (bumpBase.normed (volume : Measure ℂ)) z : ℝ) : ℂ) := by
    simpa using h
  rw [h2, bumpBase.integral_normed (μ := (volume : Measure ℂ))]
  simp

theorem refKernel_bounded : ∃ M : ℝ, ∀ z : ℂ, ‖refKernel z‖ ≤ M := by
  have hcomp : IsCompact (Set.range refKernel) :=
    refKernel_hasCompactSupport.isCompact_range refKernel_continuous
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hcomp.isBounded
  exact ⟨M, fun z => by
    have h := hM (Set.mem_range_self z)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩

/-! ## Wirtinger derivatives of a rescaled function -/

/-- Wirtinger `∂` of a rescaled function: `∂(c • ρ(s • ·))(u) = (c s) • ∂ρ(s u)`. -/
theorem dz_scale (ρ : ℂ → ℂ) (c s : ℝ) (u : ℂ) :
    dz (fun v => c • ρ (s • v)) u = (c * s) • dz ρ (s • u) := by
  have hA : fderiv ℝ (fun v => c • ρ (s • v)) u
      = c • fderiv ℝ (fun v => ρ (s • v)) u :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun v => ρ (s • v)) (c := c)) u
  have hB : fderiv ℝ (fun v => ρ (s • v)) u = s • fderiv ℝ ρ (s • u) :=
    fderiv_comp_smul (𝕜 := ℝ) (f := ρ) (x := u) (c := s)
  have h1 : fderiv ℝ (fun v => c • ρ (s • v)) u = (c * s) • fderiv ℝ ρ (s • u) := by
    rw [hA, hB, ← smul_smul]
  unfold dz
  rw [h1]
  simp only [smul_apply, RCLike.real_smul_eq_coe_mul]
  ring

/-- Wirtinger `∂̄` of a rescaled function: `∂̄(c • ρ(s • ·))(u) = (c s) • ∂̄ρ(s u)`. -/
theorem dzbar_scale (ρ : ℂ → ℂ) (c s : ℝ) (u : ℂ) :
    dzbar (fun v => c • ρ (s • v)) u = (c * s) • dzbar ρ (s • u) := by
  have hA : fderiv ℝ (fun v => c • ρ (s • v)) u
      = c • fderiv ℝ (fun v => ρ (s • v)) u :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun v => ρ (s • v)) (c := c)) u
  have hB : fderiv ℝ (fun v => ρ (s • v)) u = s • fderiv ℝ ρ (s • u) :=
    fderiv_comp_smul (𝕜 := ℝ) (f := ρ) (x := u) (c := s)
  have h1 : fderiv ℝ (fun v => c • ρ (s • v)) u = (c * s) • fderiv ℝ ρ (s • u) := by
    rw [hA, hB, ← smul_smul]
  unfold dzbar
  rw [h1]
  simp only [smul_apply, RCLike.real_smul_eq_coe_mul]
  ring

/-! ## The rescaled kernel -/

/-- The rescaling `η_r` of a kernel `ρ`: `η_r u = r⁻² • ρ(r⁻¹ • u)`. -/
abbrev scaleKernel (ρ : ℂ → ℂ) (r : ℝ) : ℂ → ℂ := fun u => (r ^ 2)⁻¹ • ρ (r⁻¹ • u)

theorem scaleKernel_dz (ρ : ℂ → ℂ) (r : ℝ) (u : ℂ) :
    dz (scaleKernel ρ r) u = ((r ^ 2)⁻¹ * r⁻¹) • dz ρ (r⁻¹ • u) := by
  simpa only [scaleKernel] using dz_scale ρ (r ^ 2)⁻¹ r⁻¹ u

theorem scaleKernel_dzbar (ρ : ℂ → ℂ) (r : ℝ) (u : ℂ) :
    dzbar (scaleKernel ρ r) u = ((r ^ 2)⁻¹ * r⁻¹) • dzbar ρ (r⁻¹ • u) := by
  simpa only [scaleKernel] using dzbar_scale ρ (r ^ 2)⁻¹ r⁻¹ u

theorem scaleKernel_contDiff {ρ : ℂ → ℂ} {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (r : ℝ) :
    ContDiff ℝ n (scaleKernel ρ r) := by
  have h1 : ContDiff ℝ n (fun u : ℂ => ρ (r⁻¹ • u)) := by
    have hlin : ContDiff ℝ n (fun u : ℂ => r⁻¹ • u) := by fun_prop
    exact hρ.comp hlin
  have h2 : ContDiff ℝ n (fun u : ℂ => (r ^ 2)⁻¹ • ρ (r⁻¹ • u)) := h1.const_smul ((r ^ 2)⁻¹)
  simpa only [scaleKernel] using h2

theorem support_scaleKernel_subset {ρ : ℂ → ℂ} {r R : ℝ} (hr : 0 < r)
    (hρ : Function.support ρ ⊆ Metric.closedBall 0 R) :
    Function.support (scaleKernel ρ r) ⊆ Metric.closedBall 0 (r * R) := by
  intro u hu
  rw [Function.mem_support] at hu
  rw [Metric.mem_closedBall, dist_zero_right]
  have hρu : ρ (r⁻¹ • u) ≠ 0 := by
    intro h
    have hz : scaleKernel ρ r u = 0 := by
      show (r ^ 2)⁻¹ • ρ (r⁻¹ • u) = 0
      rw [h, smul_zero]
    exact hu hz
  have hmem : r⁻¹ • u ∈ Function.support ρ := hρu
  have h1 : r⁻¹ * ‖u‖ ≤ R := by
    have h := hρ hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)] at h
    exact h
  calc ‖u‖ = r * (r⁻¹ * ‖u‖) := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    _ ≤ r * R := mul_le_mul_of_nonneg_left h1 hr.le

theorem scaleKernel_hasCompactSupport {ρ : ℂ → ℂ} {r R : ℝ} (hr : 0 < r)
    (hρ : Function.support ρ ⊆ Metric.closedBall 0 R) :
    HasCompactSupport (scaleKernel ρ r) := by
  have hsub := support_scaleKernel_subset hr hρ
  have hb : Bornology.IsBounded (Function.support (scaleKernel ρ r)) :=
    Metric.isBounded_closedBall.subset hsub
  simpa only [HasCompactSupport, tsupport] using hb.isCompact_closure

theorem scaleKernel_integral (ρ : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ u, scaleKernel ρ r u = ∫ u, ρ u := by
  have hsub : ∫ u, ρ (r⁻¹ • u) = r ^ 2 • ∫ u, ρ u := by
    have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure ℂ) ρ (R := r) hr.le
    simpa only [Complex.finrank_real_complex] using h
  have h1 : ∫ u, scaleKernel ρ r u = (r ^ 2)⁻¹ • ∫ u, ρ (r⁻¹ • u) := by
    simp only [scaleKernel]
    rw [MeasureTheory.integral_smul]
  rw [h1, hsub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_smul]

theorem norm_scaleKernel_le {ρ : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ u : ℂ, ‖ρ u‖ ≤ M) (u : ℂ) :
    ‖scaleKernel ρ r u‖ ≤ M / r ^ 2 := by
  have hpos : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  rw [scaleKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, div_eq_mul_inv]
  calc (r ^ 2)⁻¹ * ‖ρ (r⁻¹ • u)‖ ≤ (r ^ 2)⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hM _) hpos.le
    _ = M * (r ^ 2)⁻¹ := mul_comm _ _

theorem integral_norm_dz_scaleKernel_le (ρ : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ u, ‖dz (scaleKernel ρ r) u‖ ≤ (∫ u, ‖dz ρ u‖) / r := by
  have hconst : |(r ^ 2)⁻¹ * r⁻¹| * r ^ 2 = r⁻¹ := by
    rw [abs_of_pos (mul_pos (inv_pos.mpr (pow_pos hr 2)) (inv_pos.mpr hr)),
      mul_assoc, mul_comm r⁻¹ (r ^ 2), ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]
  have hpt : ∀ u : ℂ, ‖dz (scaleKernel ρ r) u‖
      = |(r ^ 2)⁻¹ * r⁻¹| * ‖dz ρ (r⁻¹ • u)‖ := by
    intro u
    rw [scaleKernel_dz, norm_smul, Real.norm_eq_abs]
  have hmain : ∫ u, ‖dz (scaleKernel ρ r) u‖
      = |(r ^ 2)⁻¹ * r⁻¹| * (r ^ 2 * ∫ u, ‖dz ρ u‖) := by
    calc ∫ u, ‖dz (scaleKernel ρ r) u‖
        = ∫ u, |(r ^ 2)⁻¹ * r⁻¹| * ‖dz ρ (r⁻¹ • u)‖ := by simp only [hpt]
      _ = |(r ^ 2)⁻¹ * r⁻¹| * ∫ u, ‖dz ρ (r⁻¹ • u)‖ := by
          rw [MeasureTheory.integral_const_mul]
      _ = |(r ^ 2)⁻¹ * r⁻¹| * (r ^ 2 * ∫ u, ‖dz ρ u‖) := by
          have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
            (volume : Measure ℂ) (fun u => ‖dz ρ u‖) (R := r) hr.le
          rw [h, Complex.finrank_real_complex, smul_eq_mul]
  rw [hmain, ← mul_assoc, hconst, div_eq_mul_inv]
  exact le_of_eq (mul_comm _ _)

theorem integral_norm_dzbar_scaleKernel_le (ρ : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ u, ‖dzbar (scaleKernel ρ r) u‖ ≤ (∫ u, ‖dzbar ρ u‖) / r := by
  have hconst : |(r ^ 2)⁻¹ * r⁻¹| * r ^ 2 = r⁻¹ := by
    rw [abs_of_pos (mul_pos (inv_pos.mpr (pow_pos hr 2)) (inv_pos.mpr hr)),
      mul_assoc, mul_comm r⁻¹ (r ^ 2), ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]
  have hpt : ∀ u : ℂ, ‖dzbar (scaleKernel ρ r) u‖
      = |(r ^ 2)⁻¹ * r⁻¹| * ‖dzbar ρ (r⁻¹ • u)‖ := by
    intro u
    rw [scaleKernel_dzbar, norm_smul, Real.norm_eq_abs]
  have hmain : ∫ u, ‖dzbar (scaleKernel ρ r) u‖
      = |(r ^ 2)⁻¹ * r⁻¹| * (r ^ 2 * ∫ u, ‖dzbar ρ u‖) := by
    calc ∫ u, ‖dzbar (scaleKernel ρ r) u‖
        = ∫ u, |(r ^ 2)⁻¹ * r⁻¹| * ‖dzbar ρ (r⁻¹ • u)‖ := by simp only [hpt]
      _ = |(r ^ 2)⁻¹ * r⁻¹| * ∫ u, ‖dzbar ρ (r⁻¹ • u)‖ := by
          rw [MeasureTheory.integral_const_mul]
      _ = |(r ^ 2)⁻¹ * r⁻¹| * (r ^ 2 * ∫ u, ‖dzbar ρ u‖) := by
          have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
            (volume : Measure ℂ) (fun u => ‖dzbar ρ u‖) (R := r) hr.le
          rw [h, Complex.finrank_real_complex, smul_eq_mul]
  rw [hmain, ← mul_assoc, hconst, div_eq_mul_inv]
  exact le_of_eq (mul_comm _ _)

/-! ## The main statement -/

theorem bump_scale_spec :
    ∃ (η : ℕ → ℂ → ℂ) (r : ℕ → ℝ),
      (∀ i, ContDiff ℝ 1 (η i)) ∧
      (∀ i, HasCompactSupport (η i)) ∧
      (∀ i, Function.support (η i) ⊆ Metric.closedBall 0 (r i)) ∧
      (∀ i, 0 < r i) ∧ Filter.Tendsto r Filter.atTop (nhds 0) ∧
      (∀ i, ∫ u, η i u = 1) ∧
      (∃ C : ℝ, ∀ i, ∫ u, ‖Work.MRMT.dzbar (η i) u‖ ≤ C / r i) ∧
      (∃ C : ℝ, ∀ i, ∫ u, ‖Work.MRMT.dz (η i) u‖ ≤ C / r i) ∧
      (∃ C : ℝ, ∀ i u, ‖η i u‖ ≤ C / r i ^ 2) := by
  obtain ⟨M, hM⟩ := refKernel_bounded
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  refine ⟨fun i => scaleKernel refKernel (1 / ((i : ℝ) + 1)),
    fun i => 1 / ((i : ℝ) + 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (scaleKernel_contDiff refKernel_contDiff (1 / ((i : ℝ) + 1))).of_le hle
  · intro i
    exact scaleKernel_hasCompactSupport (r := 1 / ((i : ℝ) + 1)) (R := 1)
      (by positivity) refKernel_support_subset
  · intro i
    have h := support_scaleKernel_subset (ρ := refKernel) (r := 1 / ((i : ℝ) + 1)) (R := 1)
      (by positivity) refKernel_support_subset
    simpa using h
  · intro i
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro i
    rw [scaleKernel_integral refKernel (r := 1 / ((i : ℝ) + 1)) (by positivity)]
    exact refKernel_integral
  · refine ⟨∫ u, ‖dzbar refKernel u‖, fun i => ?_⟩
    exact integral_norm_dzbar_scaleKernel_le refKernel (r := 1 / ((i : ℝ) + 1)) (by positivity)
  · refine ⟨∫ u, ‖dz refKernel u‖, fun i => ?_⟩
    exact integral_norm_dz_scaleKernel_le refKernel (r := 1 / ((i : ℝ) + 1)) (by positivity)
  · refine ⟨M, fun i u => ?_⟩
    exact norm_scaleKernel_le (ρ := refKernel) (M := M) (r := 1 / ((i : ℝ) + 1))
      (by positivity) hM u

end

end Work.MRMT.Found
