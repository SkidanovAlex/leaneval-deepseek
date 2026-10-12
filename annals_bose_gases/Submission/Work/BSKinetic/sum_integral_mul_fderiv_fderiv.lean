import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BSKinetic.Defs
import Submission.Work.SmallBoxA0.acube_axis_ftoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Full-space kinetic integration by parts: `∑_k ∫ ψ ∂_k²ψ = - ∑_k ∫ (∂_kψ)²`

This file proves `Work.BSKinetic.sum_integral_mul_fderiv_fderiv`, the identity

    `∑_{k} ∫_{ℝ³} ψ(x) · (∂_k ∂_k ψ)(x) dx = - ∑_{k} ∫_{ℝ³} (∂_k ψ)(x)² dx`

for a smooth compactly supported `ψ : ℝ³ → ℝ`, where `∂_k` is the directional derivative in the
direction `kcStdBasis k` and `dSpace ψ = ∑_k ∫ (∂_k ψ)²` is the full-space Dirichlet word of
`Submission.Work.BSKinetic.Defs`.

The proof is the standard Green identity, organised as follows.

* `integral_fderiv_kcStdBasis_eq_zero` : the **divergence/FTC identity on `ℝ³`**,
  `∫_{ℝ³} ∂_k g = 0` for smooth compactly supported `g`.  It is obtained by choosing a centred cube
  `acube s` strictly containing the support of `g`, applying the axis fundamental theorem of
  calculus `Work.SmallBoxA0.acube_axis_ftoc` on the cube, and observing that both the integrand and
  the boundary face contributions vanish outside the cube.
* For each `k`, the product rule applied to `g_k = ψ · ∂_kψ` gives
  `∂_k g_k = (∂_kψ)² + ψ · ∂_k²ψ`; integrating and using the FTC identity yields
  `∫ ψ ∂_k²ψ = - ∫ (∂_kψ)²`.
* Summing over `k : Fin 3` gives the claim.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission.BoseGases

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The divergence / fundamental-theorem identity on `ℝ³`.**  For a smooth compactly supported
`g : ℝ³ → ℝ` and any coordinate direction `kcStdBasis j`, the integral of the partial derivative
vanishes:

    `∫_{ℝ³} ∂_j g = 0`.-/
theorem integral_fderiv_kcStdBasis_eq_zero {g : ℝ³ → ℝ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hcs : HasCompactSupport g) (j : Fin 3) :
    ∫ x : ℝ³, fderiv ℝ g x (kcStdBasis j) = 0 := by
  obtain ⟨r, hr⟩ := (show Bornology.IsBounded (tsupport g) from
    (show IsCompact (tsupport g) from hcs).isBounded).subset_closedBall (0 : ℝ³)
  have hr' : ∀ x ∈ tsupport g, ‖x‖ ≤ r := by
    intro x hx
    have h := hr hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  set s : ℝ := 2 * (max r 0 + 1) with hsdef
  have hs : 0 < s := by
    rw [hsdef]; have := le_max_right r (0 : ℝ); linarith
  have hs2 : 0 < s / 2 := by linarith
  have hrs : r < s / 2 := by
    rw [hsdef]; have := le_max_left r (0 : ℝ); linarith
  have face : ∀ z ∈ acube s, z j = s / 2 → g z = 0 := by
    intro z _ hzj
    have hnot : z ∉ tsupport g := by
      intro hzts
      have h1 : ‖z‖ ≤ r := hr' z hzts
      have h2 : s / 2 ≤ ‖z‖ := by
        have h3 : ‖z j‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
        have h4 : ‖z j‖ = s / 2 := by rw [hzj, Real.norm_eq_abs, abs_of_pos hs2]
        linarith
      linarith
    exact Function.notMem_support.mp (fun hmem => hnot (subset_tsupport g hmem))
  have face' : ∀ z ∈ acube s, z j = -(s / 2) → g z = 0 := by
    intro z _ hzj
    have hnot : z ∉ tsupport g := by
      intro hzts
      have h1 : ‖z‖ ≤ r := hr' z hzts
      have h2 : s / 2 ≤ ‖z‖ := by
        have h3 : ‖z j‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
        have h4 : ‖z j‖ = s / 2 := by rw [hzj, Real.norm_eq_abs, abs_neg, abs_of_pos hs2]
        linarith
      linarith
    exact Function.notMem_support.mp (fun hmem => hnot (subset_tsupport g hmem))
  have hcube : ∫ z in acube s, fderiv ℝ g z (kcStdBasis j) = 0 :=
    Work.SmallBoxA0.acube_axis_ftoc hs j hg face face'
  have hsub : tsupport g ⊆ acube s := by
    intro x hx
    have hxr : ‖x‖ ≤ r := hr' x hx
    have hxs : ‖x‖ < s / 2 := lt_of_le_of_lt hxr hrs
    intro m
    have h3 : ‖x m‖ ≤ ‖x‖ := PiLp.norm_apply_le x m
    rw [Real.norm_eq_abs] at h3
    rw [Set.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.mp (le_trans h3 (le_of_lt hxs))
    exact ⟨by linarith, h2⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := acube s)
      (f := fun z : ℝ³ => fderiv ℝ g z (kcStdBasis j)) (fun z hz => by
        have hzts : z ∉ tsupport g := fun h => hz (hsub h)
        rw [fderiv_of_notMem_tsupport ℝ hzts]
        simp)] at hcube
  exact hcube

/-- **Full-space kinetic integration by parts.**  For smooth compactly supported `ψ : ℝ³ → ℝ`,
summing the identity `∫ ψ ∂_k²ψ = -∫ (∂_kψ)²` over the three coordinate directions gives
`∑_k ∫ ψ ∂_k²ψ = - dSpace ψ`. -/
theorem sum_integral_mul_fderiv_fderiv {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3), ψ x *
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) x
          (Submission.BoseGases.kcStdBasis k)))
      = - Work.BSKinetic.dSpace ψ := by
  have hterm : ∀ k : Fin 3, (∫ x : ℝ³, ψ x *
        (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
      = - ∫ x : ℝ³, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2 := by
    intro k
    have hD_cd : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) :=
      (hψ.fderiv_right (by simp)).clm_apply contDiff_const
    have hD_cs : HasCompactSupport (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) :=
      hcs.fderiv_apply ℝ (kcStdBasis k)
    have hG_cd : ContDiff ℝ (⊤ : ENat)
        (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k)) := hψ.mul hD_cd
    have hG_cs : HasCompactSupport (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k)) :=
      hcs.mul_right (f' := fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k))
    have hFTC : ∫ x : ℝ³,
        fderiv ℝ (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k)) x (kcStdBasis k) = 0 :=
      integral_fderiv_kcStdBasis_eq_zero hG_cd hG_cs k
    have hpt : ∀ x : ℝ³,
        fderiv ℝ (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k)) x (kcStdBasis k)
        = (fderiv ℝ ψ x (kcStdBasis k)) ^ 2
          + ψ x * (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x
              (kcStdBasis k)) := by
      intro x
      have hfun : (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k))
          = ψ * (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) := by funext y; rfl
      rw [hfun, fderiv_mul (hψ.differentiable (by simp) x) (hD_cd.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul, pow_two]
      ring
    have hint1 : Integrable (fun x : ℝ³ => (fderiv ℝ ψ x (kcStdBasis k)) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (hD_cd.continuous.pow 2)
        (hD_cs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have hint2 : Integrable (fun x : ℝ³ =>
        ψ x * (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k))) :=
      Continuous.integrable_of_hasCompactSupport
        (hψ.continuous.mul ((hD_cd.continuous_fderiv (by simp)).clm_apply continuous_const))
        (hcs.mul_right (f' := fun x : ℝ³ =>
          fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x (kcStdBasis k)))
    have hcongr : (∫ x : ℝ³,
          fderiv ℝ (fun x : ℝ³ => ψ x * fderiv ℝ ψ x (kcStdBasis k)) x (kcStdBasis k))
        = ∫ x : ℝ³, ((fderiv ℝ ψ x (kcStdBasis k)) ^ 2
            + ψ x * (fderiv ℝ (fun y : ℝ³ => fderiv ℝ ψ y (kcStdBasis k)) x
                (kcStdBasis k))) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [hcongr, integral_add hint1 hint2] at hFTC
    linarith
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    show Work.BSKinetic.dSpace ψ
      = ∑ k : Fin 3, ∫ x : ℝ³, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2 from rfl,
    Finset.sum_neg_distrib]

end Work.BSKinetic
