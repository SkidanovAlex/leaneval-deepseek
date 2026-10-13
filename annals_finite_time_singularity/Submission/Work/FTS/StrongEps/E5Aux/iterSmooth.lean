/-
Copyright: work module for the Elgindi finite-time singularity project.

# Finite-order smoothness of the partial derivatives and of the `D_z`/`D_θ` iterates

For the proof of `Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots` one needs to know
that the slots `D_zⁱD_θ^{j}F` (for `i + j ≤ 2`) of a function which is only `C²` on the open
quadrant are *continuous* there.  Mathlib's `Work.FTS.LocData.contDiffOn_pz` and friends are
stated for the genuine smooth order; here we record the finite-order bookkeeping:

* `∂_z` and `∂_θ` cost exactly one order of differentiability
  (`contDiffOn_uncurry_pz_succ`, `contDiffOn_uncurry_pth_succ`);
* `D_z` and `D_θ` likewise (`contDiffOn_uncurry_Dz_succ`, `contDiffOn_uncurry_Dth_succ`);
* consequently every slot of order `≤ 2` of a `C²` function on `Q0` is continuous
  (`contDiffOn_zero_mixed`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- `∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_pz_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => Work.Spaces.pz_eq_fderiv (hdiff p hp))

/-- `∂_θ` costs one order of differentiability. -/
theorem contDiffOn_uncurry_pth_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => Work.Spaces.pth_eq_fderiv (hdiff p hp))

/-- `D_z = z ∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dz_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (contDiffOn_fst).mul (contDiffOn_uncurry_pz_succ hV h)

/-- `D_θ = sin(2θ) ∂_θ` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dth_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul (contDiffOn_uncurry_pth_succ hV h)

/-- Every slot `D_zⁱD_θ^j` of order `i + j ≤ 2` of a `C²` function on `Q0` is continuous. -/
theorem contDiffOn_zero_mixed {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0) {j i : ℕ}
    (hji : j + i ≤ 2) :
    ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 := by
  have hQ : IsOpen (Work.FTS.EllipticEst.Q0) := Work.FTS.EllipticEst.isOpen_Q0
  have h11 : ((1 : ℕ∞ω) + 1) = 2 := by norm_num
  have h01 : ((0 : ℕ∞ω) + 1) = 1 := by norm_num
  have h2 : ContDiffOn ℝ ((1 : ℕ∞ω) + 1) (Function.uncurry G) Work.FTS.EllipticEst.Q0 :=
    by simpa only [h11] using h
  have h1G : ContDiffOn ℝ 1 (Function.uncurry G) Work.FTS.EllipticEst.Q0 := h.of_le (by norm_num)
  have h0G : ContDiffOn ℝ 0 (Function.uncurry G) Work.FTS.EllipticEst.Q0 := h.of_le (by norm_num)
  have hDz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Dz_succ hQ h2
  have hDth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dth G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Dth_succ hQ h2
  have hDz0 : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Dz_succ hQ (by simpa only [h01] using h1G)
  have hDth0 : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dth G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Dth_succ hQ (by simpa only [h01] using h1G)
  have hDzDz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_Dz_succ hQ (by simpa only [h01] using hDz1)
  have hDthDth : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth G)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_Dth_succ hQ (by simpa only [h01] using hDth1)
  have hDzDth : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth G)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_Dz_succ hQ (by simpa only [h01] using hDth1)
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  interval_cases j <;> interval_cases i <;>
    first
      | (exfalso; omega)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h0G)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hDz0)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hDth0)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hDzDz)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hDthDth)
      | (simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hDzDth)

end Work.FTS.StrongEps.E5Aux
