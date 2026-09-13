/-
# Savin's growth lemma (the "enlarge opening" lemma)

The `enlarge opening` lemma of the sliding-paraboloid method (Savin, CPDE 32 (2007); Cabre;
Imbert--Silvestre; Li--Li; Lian--Zhang arXiv:2405.07199; Fan arXiv:2509.01138, Lemma 2.2) states
that if a touching paraboloid of small opening `a` exists at a point `x₁ ∈ B_r(x₀)`, then the
contact set of the (universally) larger opening `M a` covers a definite fraction of `B_r(x₀)`.

This file proves the three steps of that lemma in the classical, concrete setting:

* `exists_below_of_supersolution` -- the *barrier* step: if `ψ` is a strict supersolution of the
  equation on the annulus `r/2 < ‖x - x₀‖ < r`, agrees with the touching paraboloid on
  `‖x - x₀‖ = r` and is strictly larger than `φ` at some interior point, then `φ - ψ` is negative
  somewhere in `closedBall x₀ (r/2)`.
* `growthBarrier_*` -- the concrete barrier of `Submission.Savin.Barrier` satisfies those
  hypotheses (`Fop` and `cofOp` estimates).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Barrier
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_sub_of_mem_nhds

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## The profile is positive below `1` -/

theorem growthProfile_pos {p t : ℝ} (hp : 0 < p) (ht : t < 1) : 0 < growthProfile p t := by
  have hcl : clampHalf t < 1 := by
    unfold clampHalf
    refine max_lt (lt_of_le_of_lt (min_le_left _ _) ht) (by norm_num)
  have hpos : 0 < clampHalf t := clampHalf_pos t
  have h1 : (1 : ℝ) ^ (-p) < (clampHalf t) ^ (-p) :=
    Real.rpow_lt_rpow_of_neg hpos hcl (by linarith)
  rw [Real.one_rpow] at h1
  simp only [growthProfile]
  have h2 : (0 : ℝ) < 1 / p := by positivity
  nlinarith

theorem growthBarrier_pos {p a r : ℝ} (hp : 0 < p) (ha : 0 < a) (hr : 0 < r)
    {x₀ x : ℝ⁴} (hx : ‖x - x₀‖ < r) : 0 < growthBarrier p a r x₀ x := by
  have ht : ‖x - x₀‖ / r < 1 := (div_lt_one hr).mpr hx
  unfold growthBarrier
  exact mul_pos (mul_pos ha (pow_pos hr 2)) (growthProfile_pos hp ht)

/-- The barrier function `z ↦ P(z) + a r² φ(‖z - x₀‖/r)` is `C²` inside the annulus. -/
theorem contDiffAt_parab_add_growthBarrier {p a c r : ℝ} {y x₀ x : ℝ⁴} (hr : 0 < r)
    (hx1 : r / 2 < ‖x - x₀‖) (hx2 : ‖x - x₀‖ < r) :
    ContDiffAt ℝ 2 (fun z => parab a y c z + growthBarrier p a r x₀ z) x := by
  have hpar : ContDiffAt ℝ 2 (parab a y c) x :=
    ((contDiff_parab a c y).contDiffAt).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have hxne : x ≠ x₀ := by
    intro h; rw [h, sub_self, norm_zero] at hx1; linarith
  have hne : r⁻¹ • (x - x₀) ≠ 0 := by
    rw [smul_ne_zero_iff, sub_ne_zero]
    exact ⟨inv_ne_zero (ne_of_gt hr), hxne⟩
  have hopen : IsOpen {z : ℝ⁴ | r / 2 < ‖z - x₀‖ ∧ ‖z - x₀‖ < r} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const |>.norm)).inter
      (isOpen_lt (continuous_id.sub continuous_const |>.norm) continuous_const)
  have hev : growthBarrier p a r x₀ =ᶠ[𝓝 x] barrierSmooth p a r x₀ := by
    filter_upwards [hopen.mem_nhds ⟨hx1, hx2⟩] with z hz
    have h1 : 1 / 2 ≤ ‖z - x₀‖ / r := by rw [le_div_iff₀ hr]; linarith [hz.1]
    have h2 : ‖z - x₀‖ / r ≤ 1 := by rw [div_le_one₀ hr]; exact hz.2.le
    exact (barrierSmooth_eq_growthBarrier (p := p) (a := a) hr h1 h2).symm
  have hsm : ContDiffAt ℝ 2 (barrierSmooth p a r x₀) x :=
    (contDiffAt_barrierKappa (a := a) (r := r) (norm_ne_zero_iff.mpr hne)).comp x
      ((contDiffAt_norm ℝ hne).comp x
        ((contDiffAt_id (x := x)).sub contDiffAt_const |>.const_smul (r⁻¹)))
  exact hpar.add (hsm.congr_of_eventuallyEq hev)

/-! ## The abstract barrier (comparison) step -/

/-- **Barrier step.**  Let `φ` be a classical solution of `Fop C ε (D²φ) = 0` on `ball 0 (3/2)`
and let `ψ` be a continuous function which is `C²` and a *strict* supersolution on the annulus
`r/2 < ‖x - x₀‖ < r`, with `C + ε • cofOp (D²ψ) ⪰ 0` there.  If `φ ≥ ψ` on the sphere
`‖x - x₀‖ = r` and `φ x₁ < ψ x₁` for some `x₁ ∈ ball x₀ r`, then `φ - ψ` is `≤ 0` somewhere in
`closedBall x₀ (r/2)`. -/
theorem exists_below_of_supersolution {φ ψ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {x₀ : ℝ⁴} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ ball 0 (3 / 2))
    (hψcont : Continuous ψ)
    (hψC2 : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r → ContDiffAt ℝ 2 ψ x)
    (hψF : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r → 0 < Fop C ε (hessOp ψ x))
    (hψcof : ∀ x, r / 2 < ‖x - x₀‖ → ‖x - x₀‖ < r →
      ∀ v : ℝ⁴, 0 ≤ ⟪(C + ε • cofOp (hessOp ψ x)) v, v⟫)
    (hsphere : ∀ z ∈ sphere x₀ r, 0 ≤ φ z - ψ z)
    {x₁ : ℝ⁴} (hx₁ : x₁ ∈ ball x₀ r) (hx₁neg : φ x₁ - ψ x₁ < 0) :
    ∃ x₂ ∈ closedBall x₀ (r / 2), φ x₂ - ψ x₂ ≤ 0 := by
  have hcontφ : ContinuousOn φ (closedBall x₀ r) :=
    (hφ.continuousOn).mono fun z hz => hsub hz
  obtain ⟨x₂, hx₂mem, hx₂min₀⟩ := (isCompact_closedBall x₀ r).exists_isMinOn
    ⟨x₀, mem_closedBall_self hr.le⟩ (hcontφ.sub hψcont.continuousOn)
  have hx₂min : ∀ z ∈ closedBall x₀ r, φ x₂ - ψ x₂ ≤ φ z - ψ z := by
    intro z hz
    exact hx₂min₀ hz
  have hx₂lt : ‖x₂ - x₀‖ < r := by
    rcases lt_or_eq_of_le (mem_closedBall.mp hx₂mem) with h | h
    · exact h
    · exfalso
      have h1 : 0 ≤ φ x₂ - ψ x₂ := hsphere x₂ (by
        rw [mem_sphere, dist_eq_norm]; exact h)
      have h2 : φ x₂ - ψ x₂ ≤ φ x₁ - ψ x₁ := hx₂min x₁ (mem_closedBall.mpr hx₁.le)
      linarith
  have hminneg : φ x₂ - ψ x₂ < 0 :=
    lt_of_le_of_lt (hx₂min x₁ (mem_closedBall.mpr hx₁.le)) hx₁neg
  have hfin : ‖x₂ - x₀‖ ≤ r / 2 := by
    by_contra hcon
    push_neg at hcon
    have hx₂ball : x₂ ∈ ball 0 (3 / 2) := hsub (mem_closedBall.mpr hx₂lt.le)
    have hφx : ContDiffAt ℝ 2 φ x₂ := hφ.contDiffAt (isOpen_ball.mem_nhds hx₂ball)
    have hψx : ContDiffAt ℝ 2 ψ x₂ := hψC2 x₂ hcon hx₂lt
    have hx₂b : x₂ ∈ ball x₀ r := by rw [mem_ball, dist_eq_norm]; exact hx₂lt
    have hloc : IsLocalMin (fun z => φ z - ψ z) x₂ :=
      hx₂min₀.isLocalMin (Filter.mem_of_superset (isOpen_ball.mem_nhds hx₂b)
        fun z hz => ball_subset_closedBall hz)
    have hnonneg : ∀ v : ℝ⁴,
        0 ≤ (fderiv ℝ (fderiv ℝ (fun z => φ z - ψ z)) x₂) v v := fun v =>
      Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin (hφx.sub hψx) hloc v
    have hsub2 : fderiv ℝ (fderiv ℝ (fun z => φ z - ψ z)) x₂
        = fderiv ℝ (fderiv ℝ φ) x₂ - fderiv ℝ (fderiv ℝ ψ) x₂ :=
      Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_sub_of_contDiffAt hφx hψx
    have hmono : ∀ v : ℝ⁴, 0 ≤ ⟪(hessOp φ x₂ - hessOp ψ x₂) v, v⟫ := by
      intro v
      have h := hnonneg v
      rw [hsub2] at h
      have h2 : ((fderiv ℝ (fderiv ℝ φ) x₂ - fderiv ℝ (fderiv ℝ ψ) x₂) v) v
          = ⟪(hessOp φ x₂ - hessOp ψ x₂) v, v⟫ := by
        rw [sub_apply, sub_apply, sub_apply, inner_sub_left]
        congr 1
        · exact (InnerProductSpace.continuousLinearMapOfBilin_apply
            (B := fderiv ℝ (fderiv ℝ φ) x₂) v v).symm
        · exact (InnerProductSpace.continuousLinearMapOfBilin_apply
            (B := fderiv ℝ (fderiv ℝ ψ) x₂) v v).symm
      rw [h2] at h
      exact h
    have hle := Fop_mono hC hε.le (hessOp_symm_of_contDiffAt hφx) (hessOp_symm_of_contDiffAt hψx)
      hmono (hψcof x₂ hcon hx₂lt)
    rw [heq x₂ hx₂ball] at hle
    linarith [hψF x₂ hcon hx₂lt]
  exact ⟨x₂, mem_closedBall.mpr hfin, hminneg.le⟩

end

end Submission
