/-
Copyright: work module for the Elgindi finite-time singularity project.

# The four basis entries of the second Fréchet derivative, at regularity `C²`

`Work.FTS.StrongLWP.Sobolev.eqc_fderiv_fderiv_basis_apply` expresses the four matrix entries
(on the standard basis of `ℝ × ℝ`) of the second Fréchet derivative of a *curried* function
`G` through the iterated slice derivatives `∂_z`, `∂_θ` — but it assumes `ContDiffOn ℝ ⊤`,
i.e. in this Mathlib pin *analyticity* of `G`.  The estimates of `FTS/StrongEps/LocUnif` feed
it a datum which is only `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`), so
analyticity is not available.  This module supplies the honest `C²` version, together with the
two derived facts used downstream:

* `Work.FTS.StrongEps.LocUnif.basis_apply_two` — the four entries at order `2`;
* `Work.FTS.StrongEps.LocUnif.norm_fderiv_fderiv_le_basis` — the operator norm of the second
  derivative dominated by the sum of the absolute values of the four entries;
* `Work.FTS.StrongEps.LocUnif.two_le_smoothOrder` — `(2 : ℕ∞ω) ≤ Work.Stability.smoothOrder`;
* `Work.FTS.StrongEps.LocUnif.contDiff_two_mul_of_contDiffOn_two` — a `C²` cutoff vanishing off
  a closed set `s`, multiplied by a function which is `C²` on an open `U ⊇ s`, is `C²`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasic
import Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 1000000

/-- `(2 : ℕ∞ω) ≤ Work.Stability.smoothOrder`: the honest smooth order `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`
dominates the finite order `2`. -/
lemma two_le_smoothOrder : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- The product of a `C²` cutoff `χ`, vanishing off a closed set `s`, with a function `g` which
is `C²` on an open set `U ⊇ s`, is `C²`.  (The `C²` version of
`Work.FTS.StrongLWP.Sobolev.eqc_contDiff_two_mul_of_forall_notMem_eq_zero`, whose hypothesis on
`g` is `ContDiffOn ℝ ⊤`, i.e. analyticity.) -/
lemma contDiff_two_mul_of_contDiffOn_two {χ g : ℝ × ℝ → ℝ} {s U : Set (ℝ × ℝ)}
    (hsc : IsClosed s) (hsU : s ⊆ U) (hU : IsOpen U) (hχ : ContDiff ℝ 2 χ)
    (hχ0 : ∀ x ∉ s, χ x = 0) (hg : ContDiffOn ℝ 2 g U) :
    ContDiff ℝ 2 (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hxR : x ∈ s := by
      have hsub : tsupport χ ⊆ s :=
        hsc.closure_subset_iff.mpr (Function.support_subset_iff'.mpr hχ0)
      exact hsub hx
    exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hsU hxR)))
  · have hev : (fun y => χ y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The four entries (on the standard basis of `ℝ × ℝ`) of the second Fréchet derivative of a
curried function `C²` on an open set, in terms of the iterated slice derivatives `∂_z`, `∂_θ`:
the order-`2` version of `Work.FTS.StrongLWP.Sobolev.eqc_fderiv_fderiv_basis_apply`. -/
lemma basis_apply_two {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) U) {z θ : ℝ} (hz : (z, θ) ∈ U) :
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = Work.Spaces.pzIter 2 G z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = Work.Spaces.pz (Work.Spaces.pth G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = Work.Spaces.pth (Work.Spaces.pz G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = Work.Spaces.pthIter 2 G z θ := by
  have hdat : ∀ y ∈ U, DifferentiableAt ℝ (Function.uncurry G) y := fun y hy =>
    (hG.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hfdOn : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry G)) U :=
    hG.fderiv_of_isOpen hU (by norm_num)
  have hdat2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ (Function.uncurry G)) y := fun y hy =>
    (hfdOn.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  set Az : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (1, 0) with hAzdef
  set Aθ : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (0, 1) with hAθdef
  have hAz_sm : ContDiffOn ℝ 1 (Function.uncurry Az) U := hfdOn.clm_apply contDiffOn_const
  have hAθ_sm : ContDiffOn ℝ 1 (Function.uncurry Aθ) U := hfdOn.clm_apply contDiffOn_const
  have hAz_diff : DifferentiableAt ℝ (Function.uncurry Az) (z, θ) :=
    (hAz_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hAθ_diff : DifferentiableAt ℝ (Function.uncurry Aθ) (z, θ) :=
    (hAθ_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hAz_eq : Set.EqOn (Function.uncurry Az) (Function.uncurry (Work.Spaces.pz G)) U := by
    intro y hy
    exact (Work.Spaces.pz_eq_fderiv (hdat y hy)).symm
  have hAθ_eq : Set.EqOn (Function.uncurry Aθ) (Function.uncurry (Work.Spaces.pth G)) U := by
    intro y hy
    exact (Work.Spaces.pth_eq_fderiv (hdat y hy)).symm
  have key : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y v) (z, θ)
        = (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip v := by
    intro v
    rw [fderiv_clm_apply (hdat2 (z, θ) hz) (differentiableAt_const v), fderiv_const_apply]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Az z θ := (Work.Spaces.pz_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pz G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAz_eq hz
      _ = Work.Spaces.pzIter 2 G z θ := rfl
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Aθ z θ := (Work.Spaces.pz_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pth G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAθ_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Az z θ := (Work.Spaces.pth_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
          Work.FTS.StrongLWP.Sobolev.eqc_pth_congr_of_isOpen hU hAz_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Aθ z θ := (Work.Spaces.pth_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pth G) z θ :=
          Work.FTS.StrongLWP.Sobolev.eqc_pth_congr_of_isOpen hU hAθ_eq hz
      _ = Work.Spaces.pthIter 2 G z θ := rfl

/-- The operator norm of the second Fréchet derivative of a curried `C²` function on an open set
is bounded by the sum of the absolute values of its four basis entries. -/
lemma norm_fderiv_fderiv_le_basis {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) U) {z θ : ℝ} (hz : (z, θ) ∈ U) :
    ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ≤
      |Work.Spaces.pzIter 2 G z θ| + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
        + |Work.Spaces.pth (Work.Spaces.pz G) z θ| + |Work.Spaces.pthIter 2 G z θ| := by
  obtain ⟨h1, h2, h3, h4⟩ := basis_apply_two hU hG hz
  have h := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum₂
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ))
  have e1 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
      = Work.Spaces.pzIter 2 G z θ := h1
  have e2 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
      = Work.Spaces.pz (Work.Spaces.pth G) z θ := h2
  have e3 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
      = Work.Spaces.pth (Work.Spaces.pz G) z θ := h3
  have e4 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
      = Work.Spaces.pthIter 2 G z θ := h4
  rw [e1, e2, e3, e4] at h
  exact h

end Work.FTS.StrongEps.LocUnif
