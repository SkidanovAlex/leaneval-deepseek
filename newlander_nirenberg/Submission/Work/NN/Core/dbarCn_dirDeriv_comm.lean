import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# Commutation of `∂̄_{Jstd + A}` with a directional derivative

This file proves `Work.NN.Core.dbarCn_dirDeriv_comm`: for a `C²` function `u : ℂⁿ → ℂ`, a `C¹`
family of real endomorphisms `A`, a point `z`, vectors `v` and `e = Pi.single k 1`,

`∂̄_{Jstd + A}(y ↦ du_y(v))_z(e)
   = d_z(∂̄_{Jstd + A}u(·)(e))(v) - (I/2) · du_z (d_z(y ↦ A y e)(v))`.

The identity is the "second derivative" commutation underlying the linearisation of the chart
equation: writing `D = du` and `L = dD` (the symmetric second derivative), both sides reduce to
`(1/2)·(L e v + I·L (J z e) v)`, the left one by symmetry of `L`, the right one by the product rule
applied to `y ↦ D y (J y e)` and the fact that `J = Jstd + A` differs from the constant `Jstd`
by `A`, so that `d(J · e)_z = d(A · e)_z`.  The two agree because the extra term produced by the
product rule, `(I/2)·D_z(d(A·e)_z(v))`, is exactly the correction subtracted on the right.

## Main results

* `dbarCn_dirDeriv_comm_of_contDiffAt` — the identity under pointwise `C²`/`C¹` hypotheses;
* `dbarCn_dirDeriv_comm` — the same on an open set `Ω`, from `ContDiffOn ℝ 2 u Ω` and
  `ContDiff ℝ 1 A`.
-/

noncomputable section

open Set

namespace Work.NN.Core

variable {n : ℕ}

/-- **Commutation of `∂̄_{Jstd + A}` with a directional derivative**, pointwise form.

`hu` and `hA` are `C²`/`C¹` regularity of `u` and `A` at the point `z`. -/
lemma dbarCn_dirDeriv_comm_of_contDiffAt {u : Cn n → ℂ}
    {A : Cn n → Cn n →L[ℝ] Cn n} {z : Cn n}
    (hu : ContDiffAt ℝ 2 u z) (hA : ContDiffAt ℝ 1 A z) (v : Cn n) (k : Fin n) :
    dbarCn (JstdCn n + A) (fun y => fderiv ℝ u y v) z (Pi.single k (1:ℂ))
      = fderiv ℝ (fun y => dbarCn (JstdCn n + A) u y (Pi.single k (1:ℂ))) z v
        - (Complex.I / 2) * fderiv ℝ u z
            (fun l => fderiv ℝ (fun y => A y (Pi.single k (1:ℂ)) l) z v) := by
  set e : Cn n := Pi.single k (1:ℂ) with he
  -- regularity: `du` is `C¹` at `z`, `A` is differentiable, `y ↦ A y e` is differentiable
  have hDd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAd : DifferentiableAt ℝ A z := hA.differentiableAt (by norm_num)
  have hAe : DifferentiableAt ℝ (fun y => A y e) z := hAd.clm_apply (differentiableAt_const e)
  -- `J = Jstd + A` and `Jstd` is constant, so `d(J · e)_z = d(A · e)_z`
  have hW : fderiv ℝ (fun y => (JstdCn n + A) y e) z = fderiv ℝ (fun y => A y e) z := by
    have h2 : (fun y => (JstdCn n + A) y e) = fun y => Complex.I • e + A y e := by
      funext y; simp [JstdCn]
    rw [h2, fderiv_const_add]
  have hJed : DifferentiableAt ℝ (fun y => (JstdCn n + A) y e) z := by
    have h2 : (fun y => (JstdCn n + A) y e) = fun y => Complex.I • e + A y e := by
      funext y; simp [JstdCn]
    rw [h2]; exact hAe.const_add _
  -- symmetry of the second derivative of `u`
  have hsym : IsSymmSndFDerivAt ℝ u z := hu.isSymmSndFDerivAt (by norm_num)
  -- the derivative of `y ↦ A y e`, read through the coordinates of `ℂⁿ`
  have hpi : (fderiv ℝ (fun y => A y e) z) v = fun l => fderiv ℝ (fun y => A y e l) z v := by
    have hAll : ∀ l : Fin n, DifferentiableAt ℝ (fun y => A y e l) z :=
      differentiableAt_pi.mp hAe
    rw [show (fun y => A y e) = (fun y l => A y e l) from rfl]
    rw [fderiv_pi hAll]
    funext l
    rw [ContinuousLinearMap.pi_apply]
  -- ### the left-hand side
  rw [dbarCn_apply]
  rw [show fderiv ℝ (fun y => fderiv ℝ u y v) z = (fderiv ℝ (fderiv ℝ u) z).flip v from by
        rw [fderiv_clm_apply hDd (differentiableAt_const v)]; simp]
  simp only [ContinuousLinearMap.flip_apply]
  -- ### the right-hand side
  have hg1 : HasFDerivAt (fun y => fderiv ℝ u y e) ((fderiv ℝ (fderiv ℝ u) z).flip e) z := by
    have h := hDd.hasFDerivAt.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hg2 : HasFDerivAt (fun y => fderiv ℝ u y ((JstdCn n + A) y e))
      ((fderiv ℝ u z).comp (fderiv ℝ (fun y => A y e) z)
        + (fderiv ℝ (fderiv ℝ u) z).flip ((JstdCn n + A) z e)) z := by
    have h := hDd.hasFDerivAt.clm_apply (hJed.hasFDerivAt)
    rw [hW] at h
    exact h
  have hFG : HasFDerivAt
      (fun y => (1/2:ℂ) * (fderiv ℝ u y e + Complex.I * fderiv ℝ u y ((JstdCn n + A) y e)))
      ((1/2:ℂ) • ((fderiv ℝ (fderiv ℝ u) z).flip e
        + Complex.I • ((fderiv ℝ u z).comp (fderiv ℝ (fun y => A y e) z)
            + (fderiv ℝ (fderiv ℝ u) z).flip ((JstdCn n + A) z e)))) z :=
    (hg1.add (hg2.const_mul Complex.I)).const_mul (1/2:ℂ)
  have hF : fderiv ℝ (fun y => dbarCn (JstdCn n + A) u y e) z
      = (1/2:ℂ) • ((fderiv ℝ (fderiv ℝ u) z).flip e
        + Complex.I • ((fderiv ℝ u z).comp (fderiv ℝ (fun y => A y e) z)
            + (fderiv ℝ (fderiv ℝ u) z).flip ((JstdCn n + A) z e))) := by
    rw [show (fun y => dbarCn (JstdCn n + A) u y e)
        = fun y => (1/2:ℂ) * (fderiv ℝ u y e + Complex.I * fderiv ℝ u y ((JstdCn n + A) y e)) from by
          funext y; rw [dbarCn_apply]]
    exact hFG.fderiv
  rw [hF]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, add_apply]
  rw [hpi]
  -- the two extra second-order terms agree by symmetry of `d²u`, and the `(I/2)` corrections cancel
  rw [hsym.eq v e, hsym.eq v ((JstdCn n + A) z e)]
  ring

lemma dbarCn_dirDeriv_comm {n : ℕ} {Ω : Set (Work.NN.Core.Cn n)} (hΩ : IsOpen Ω)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n} (hA : ContDiff ℝ 1 A)
    (v : Work.NN.Core.Cn n) (k : Fin n) {z : Work.NN.Core.Cn n} (hz : z ∈ Ω) :
    Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => fderiv ℝ u y v) z (Pi.single k (1:ℂ))
      = fderiv ℝ (fun y => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u y (Pi.single k (1:ℂ))) z v
        - (Complex.I / 2) * fderiv ℝ u z
            (fun l => fderiv ℝ (fun y => A y (Pi.single k (1:ℂ)) l) z v) :=
  dbarCn_dirDeriv_comm_of_contDiffAt (hu.contDiffAt (hΩ.mem_nhds hz)) hA.contDiffAt v k

end Work.NN.Core
