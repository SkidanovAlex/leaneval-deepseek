import Mathlib
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPV.tau_symplectic

/-!
# B5: the derivatives of the assembled family on the right half plane

For `x > 0` the assembled family `ℓ = lagPt W Γc Ac rho` is *by definition* the `τ_π`-image of
the reflected point,

`lagPt τ x t = tau π (lagPt τ (-x) (t - π))`,

because on the left half (`x ≤ 0`) `lagPt` is `basePt`; for `x > 0` the definition is
`tau π (basePt τ (-x) (t-π))` and `basePt τ (-x) · = lagPt τ (-x) ·` since `-x < 0`.

This file proves `Work.RPB.B5.lagPt_right_derivs`: the two partial derivatives of `ℓ` on the right
half are the `tauLinear π`-images of the corresponding derivatives of the reflected family.  The
proof is nothing but the chain rule applied to the identity above, together with the fact that
`tauLinear π` is the derivative of `tau π` at every point (`Work.RPV.fderiv_tau`) and the
one-sided congruence of `deriv` for functions agreeing on `(0, ∞)`.

The differentiability input is the hypothesis `hsm` (`ℓ τ` is `C¹` on the `τ`-slab `[0,1]`), from
which every slice is differentiable (`differentiableAt_slice_fst`/`_snd` of
`Submission.Work.RPB.B5.lagData_imm_aux`).
-/

open scoped ContDiff Topology

namespace Work.RPB.B5

noncomputable section

/-- `tau θ` is smooth (it is affine: a rotation of the `(q₁,p₁)`-plane plus a translation in the
angle coordinate). -/
private lemma contDiff_tau_pi_aux : ContDiff ℝ 1 (fun x : Work.RPV.PS => Work.RPV.tau Real.pi x) := by
  simp only [Work.RPV.tau]
  fun_prop

/-- The derivative of `tau π` at every point is its linear part `tauLinear π`
(`Work.RPV.fderiv_tau`), as a `HasFDerivAt` statement. -/
private lemma hasFDerivAt_tau_pi_aux (z : Work.RPV.PS) :
    HasFDerivAt (Work.RPV.tau Real.pi) (Work.RPV.tauLinear Real.pi) z := by
  have hdiff : DifferentiableAt ℝ (fun x : Work.RPV.PS => Work.RPV.tau Real.pi x) z :=
    (contDiff_tau_pi_aux.contDiffAt (x := z)).differentiableAt (by norm_num)
  rw [← Work.RPV.fderiv_tau Real.pi z]
  exact hdiff.hasFDerivAt

theorem lagPt_right_derivs (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, 0 < x → ∀ t : ℝ,
      deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t) x
        = Work.RPV.tauLinear Real.pi
            (-(deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) (-x)))
      ∧ deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s) t
        = Work.RPV.tauLinear Real.pi
            (deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) s) (t - Real.pi)) := by
  intro τ hτ x hx t
  -- `ℓ τ` is `C¹`, so every slice is differentiable
  have hcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) := hsm τ hτ
  have hdfst : ∀ u v : ℝ, DifferentiableAt ℝ (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y v) u :=
    fun u v => differentiableAt_slice_fst (hcd.contDiffAt (x := (u, v)))
  have hdsnd : ∀ u v : ℝ, DifferentiableAt ℝ (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ u s) v :=
    fun u v => differentiableAt_slice_snd (hcd.contDiffAt (x := (u, v)))
  constructor
  · -- ## the `x`-derivative
    -- on the right half `lagPt τ y t = tau π (lagPt τ (-y) (t-π))`
    have hev : (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t)
        =ᶠ[𝓝 x] (fun y : ℝ =>
          Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi))) := by
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) ?_
      intro y hy
      rw [Set.mem_Ioi] at hy
      change lagPt D.W D.Γc D.Ac D.rho τ y t
        = Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi))
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := y) (t := t) hy,
        lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -y) (t := t - Real.pi)
          (by linarith)]
    have hstep1 := hev.deriv_eq
    -- the chain rule for `y ↦ tau π (lagPt τ (-y) (t-π))`, whose inner part is `C¹`
    have hcomp : HasDerivAt (fun y : ℝ =>
          Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi)))
        (Work.RPV.tauLinear Real.pi
          (deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi)) x)) x := by
      have hg : HasDerivAt (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi))
          (deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi)) x) x :=
        (((hdfst (-x) (t - Real.pi)).comp x (differentiableAt_id.neg (x := x)))).hasDerivAt
      exact (hasFDerivAt_tau_pi_aux (lagPt D.W D.Γc D.Ac D.rho τ (-x) (t - Real.pi))).comp_hasDerivAt
        x hg
    -- `(y ↦ lagPt τ (-y) (t-π))' = -(lagPt τ · (t-π))'`
    have hneg : deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi)) x
        = -deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) (-x) :=
      deriv_comp_neg (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) x
    calc deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t) x
        = deriv (fun y : ℝ => Work.RPV.tau Real.pi
            (lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi))) x := hstep1
      _ = Work.RPV.tauLinear Real.pi
            (deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-y) (t - Real.pi)) x) :=
            hcomp.deriv
      _ = Work.RPV.tauLinear Real.pi
            (-(deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) (-x))) := by
            rw [hneg]
  · -- ## the `t`-derivative
    -- now `x` is fixed (`> 0`) and the identity is pointwise in `s`
    have hpt : ∀ s : ℝ, lagPt D.W D.Γc D.Ac D.rho τ x s
        = Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-x) (s - Real.pi)) := by
      intro s
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := x) (t := s) hx,
        lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -x) (t := s - Real.pi) (by linarith)]
    have hfun : (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s) = (fun s : ℝ =>
        Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-x) (s - Real.pi))) :=
      funext hpt
    have hcomp2 : HasDerivAt (fun s : ℝ =>
          Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho τ (-x) (s - Real.pi)))
        (Work.RPV.tauLinear Real.pi
          (deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) s) (t - Real.pi))) t := by
      have hg : HasDerivAt (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) (s - Real.pi))
          (deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) s) (t - Real.pi)) t :=
        (hdsnd (-x) (t - Real.pi)).hasDerivAt.comp_sub_const t Real.pi
      exact (hasFDerivAt_tau_pi_aux (lagPt D.W D.Γc D.Ac D.rho τ (-x) (t - Real.pi))).comp_hasDerivAt
        t hg
    rw [hfun, hcomp2.deriv]

end

end Work.RPB.B5
