import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

set_option autoImplicit false

/-! ## The Fréchet derivative of a two-variable function

For `g : ℝ → ℝ → ℝ` with `F = Function.uncurry g` differentiable at `(a,b)`, the Fréchet
derivative of `F` at `(a,b)` is the continuous linear functional `(u,v) ↦ u ∂_z g + v ∂_θ g`,
i.e. `ellCop (pz g a b) (pth g a b)` of `BoxRegAux.Defs`.  This is the linear-algebraic
counterpart of `Work.Spaces.pz_eq_fderiv` / `pth_eq_fderiv` (which identify the two partials
with the evaluations of `fderiv` on `(1,0)` and `(0,1)`). -/

theorem fderiv_uncurry_eq_ellCop {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry g) (a, b)) :
    fderiv ℝ (Function.uncurry g) (a, b)
      = Work.FTS_EllLimOK.ellCop (Work.Spaces.pz g a b) (Work.Spaces.pth g a b) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 : fderiv ℝ (Function.uncurry g) (a, b) ((1 : ℝ), (0 : ℝ)) = Work.Spaces.pz g a b :=
    (Work.Spaces.pz_eq_fderiv h).symm
  have h2 : fderiv ℝ (Function.uncurry g) (a, b) ((0 : ℝ), (1 : ℝ)) = Work.Spaces.pth g a b :=
    (Work.Spaces.pth_eq_fderiv h).symm
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  show fderiv ℝ (Function.uncurry g) (a, b) v = _
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, h1, h2, Work.FTS_EllLimOK.ellCop_apply]
  simp only [smul_eq_mul]

/-- **The operator norm of a first-order jet.**  If the Fréchet derivative of `F : ℝ × ℝ → ℝ`
at `x` is `ellCop A B`, then the norm of `iteratedFDeriv ℝ 1 F x` is at most `|A| + |B|`
(in fact it is equal, the norm on `ℝ × ℝ` being the sup norm). -/
theorem norm_iterDF1_le {F : ℝ × ℝ → ℝ} {x : ℝ × ℝ} {A B : ℝ}
    (hfd : fderiv ℝ F x = Work.FTS_EllLimOK.ellCop A B) :
    ‖iteratedFDeriv ℝ 1 F x‖ ≤ |A| + |B| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_one_apply, hfd, Real.norm_eq_abs, Fin.prod_univ_one]
  simp only [Work.FTS_EllLimOK.ellCop_apply]
  have h1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have h2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  calc |(m 0).1 * A + (m 0).2 * B|
      ≤ |(m 0).1 * A| + |(m 0).2 * B| := abs_add_le _ _
    _ = |(m 0).1| * |A| + |(m 0).2| * |B| := by rw [abs_mul, abs_mul]
    _ ≤ ‖m 0‖ * |A| + ‖m 0‖ * |B| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg A))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg B))
    _ = (|A| + |B|) * ‖m 0‖ := by ring

/-- **The operator norm of a second-order jet.**  If the second Fréchet derivative of
`F : ℝ × ℝ → ℝ` at `x` is the curried bilinear map with the four second partials `A2 B2 C2 D2`
(the `(∂_z∂_z, ∂_θ∂_z, ∂_z∂_θ, ∂_θ∂_θ)` entries), then the norm of `iteratedFDeriv ℝ 2 F x` is
at most the sum of their absolute values. -/
theorem norm_iterDF2_le {F : ℝ × ℝ → ℝ} {x : ℝ × ℝ} {A2 B2 C2 D2 : ℝ}
    (hfd2 : fderiv ℝ (fderiv ℝ F) x
      = Work.FTS_EllLimOK.copBilin.comp ((Work.FTS_EllLimOK.ellCop A2 B2).prod
          (Work.FTS_EllLimOK.ellCop C2 D2))) :
    ‖iteratedFDeriv ℝ 2 F x‖ ≤ |A2| + |B2| + |C2| + |D2| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_two_apply, hfd2, Real.norm_eq_abs, Fin.prod_univ_two]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Work.FTS_EllLimOK.copBilin_apply, Work.FTS_EllLimOK.ellCop_apply]
  have hh1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have hh2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  have hk1 : |(m 1).1| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 1)
  have hk2 : |(m 1).2| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 1)
  have hN1 : (0 : ℝ) ≤ ‖m 1‖ := norm_nonneg _
  have hX : |(m 0).1 * A2 + (m 0).2 * B2| ≤ ‖m 0‖ * (|A2| + |B2|) := by
    calc |(m 0).1 * A2 + (m 0).2 * B2|
        ≤ |(m 0).1 * A2| + |(m 0).2 * B2| := abs_add_le _ _
      _ = |(m 0).1| * |A2| + |(m 0).2| * |B2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖m 0‖ * |A2| + ‖m 0‖ * |B2| :=
          add_le_add (mul_le_mul_of_nonneg_right hh1 (abs_nonneg A2))
            (mul_le_mul_of_nonneg_right hh2 (abs_nonneg B2))
      _ = ‖m 0‖ * (|A2| + |B2|) := by ring
  have hY : |(m 0).1 * C2 + (m 0).2 * D2| ≤ ‖m 0‖ * (|C2| + |D2|) := by
    calc |(m 0).1 * C2 + (m 0).2 * D2|
        ≤ |(m 0).1 * C2| + |(m 0).2 * D2| := abs_add_le _ _
      _ = |(m 0).1| * |C2| + |(m 0).2| * |D2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖m 0‖ * |C2| + ‖m 0‖ * |D2| :=
          add_le_add (mul_le_mul_of_nonneg_right hh1 (abs_nonneg C2))
            (mul_le_mul_of_nonneg_right hh2 (abs_nonneg D2))
      _ = ‖m 0‖ * (|C2| + |D2|) := by ring
  have e1 : |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)|
      ≤ ‖m 1‖ * (‖m 0‖ * (|A2| + |B2|)) :=
    le_trans (le_of_eq (abs_mul _ _)) (mul_le_mul hk1 hX (abs_nonneg _) hN1)
  have e2 : |(m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)|
      ≤ ‖m 1‖ * (‖m 0‖ * (|C2| + |D2|)) :=
    le_trans (le_of_eq (abs_mul _ _)) (mul_le_mul hk2 hY (abs_nonneg _) hN1)
  calc |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)
        + (m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)|
      ≤ |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)|
        + |(m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)| := abs_add_le _ _
    _ ≤ ‖m 1‖ * (‖m 0‖ * (|A2| + |B2|)) + ‖m 1‖ * (‖m 0‖ * (|C2| + |D2|)) :=
        add_le_add e1 e2
    _ = (|A2| + |B2| + |C2| + |D2|) * (‖m 0‖ * ‖m 1‖) := by ring

/-- **The norm of the first two iterated Fréchet derivatives of a curried function is bounded
by the sums of the absolute values of its partial derivatives.**

For `f : ℝ → ℝ → ℝ` which is `C²` at `(z,θ)`, the operator norm of `iteratedFDeriv ℝ 1`
of `Function.uncurry f` at `(z,θ)` is at most `|∂_z f| + |∂_θ f|` (the norm on `ℝ × ℝ` is the
sup norm, so this is sharp), and the operator norm of `iteratedFDeriv ℝ 2` is at most the sum
of the absolute values of the four second-order partials `∂_z∂_z f`, `∂_θ∂_z f`,
`∂_z∂_θ f`, `∂_θ∂_θ f`. -/
theorem jet_fderiv_partial_bound {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hsm : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    ‖iteratedFDeriv ℝ 1 (Function.uncurry f) (z, θ)‖
        ≤ |Work.Spaces.pz f z θ| + |Work.Spaces.pth f z θ| ∧
      ‖iteratedFDeriv ℝ 2 (Function.uncurry f) (z, θ)‖
        ≤ |Work.Spaces.pz (Work.Spaces.pz f) z θ| + |Work.Spaces.pth (Work.Spaces.pz f) z θ|
          + |Work.Spaces.pz (Work.Spaces.pth f) z θ| + |Work.Spaces.pth (Work.Spaces.pth f) z θ| := by
  refine ⟨?_, ?_⟩
  · exact norm_iterDF1_le (fderiv_uncurry_eq_ellCop (g := f) (hsm.differentiableAt (by norm_num)))
  · -- an open neighbourhood of `(z,θ)` on which `Function.uncurry f` is `C²`
    have hsmU : ContDiffWithinAt ℝ 2 (Function.uncurry f) Set.univ (z, θ) := hsm
    obtain ⟨u, hu_open, hu_mem, hu_cd⟩ :=
      hsmU.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by intro h; simp at h)
    have hu_eq : insert (z, θ) Set.univ ∩ u = u := by ext x; simp
    rw [hu_eq] at hu_cd
    have hdiff_u : ∀ q ∈ u, DifferentiableAt ℝ (Function.uncurry f) q := fun q hq =>
      (hu_cd.contDiffAt (hu_open.mem_nhds hq)).differentiableAt (by norm_num)
    have h_ev_pz : Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (1, 0) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      exact Work.Spaces.pz_eq_fderiv (hdiff_u q hq)
    have h_ev_pth : Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (0, 1) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      exact Work.Spaces.pth_eq_fderiv (hdiff_u q hq)
    have hdF1 : ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry f)) (z, θ) :=
      hsm.fderiv_right (m := 1) (by norm_num)
    have hdiffF1 : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
      hdF1.differentiableAt (by norm_num)
    have hdA : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) (z, θ) :=
      (hdiffF1.clm_apply (differentiableAt_const ((1 : ℝ), (0 : ℝ)))).congr_of_eventuallyEq
        h_ev_pz
    have hdB : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
      (hdiffF1.clm_apply (differentiableAt_const ((0 : ℝ), (1 : ℝ)))).congr_of_eventuallyEq
        h_ev_pth
    have hA : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
          (Work.Spaces.pth (Work.Spaces.pz f) z θ)) (z, θ) :=
      hdA.hasFDerivAt.congr_fderiv (fderiv_uncurry_eq_ellCop (g := Work.Spaces.pz f) hdA)
    have hB : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
          (Work.Spaces.pth (Work.Spaces.pth f) z θ)) (z, θ) :=
      hdB.hasFDerivAt.congr_fderiv (fderiv_uncurry_eq_ellCop (g := Work.Spaces.pth f) hdB)
    have hg_ev : fderiv ℝ (Function.uncurry f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
          (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      rw [fderiv_uncurry_eq_ellCop (g := f) (hdiff_u q hq), Work.FTS_EllLimOK.copBilin_apply]
    have hpair : HasFDerivAt
        (fun q : ℝ × ℝ => (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ))) (z, θ) := hA.prodMk hB
    have hcomp : HasFDerivAt (fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
        (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
        (Work.FTS_EllLimOK.copBilin.comp
          ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
              (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
            (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
              (Work.Spaces.pth (Work.Spaces.pth f) z θ)))) (z, θ) :=
      (ContinuousLinearMap.hasFDerivAt Work.FTS_EllLimOK.copBilin).comp (z, θ) hpair
    have hfd2 : fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ)
        = Work.FTS_EllLimOK.copBilin.comp
          ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
              (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
            (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
              (Work.Spaces.pth (Work.Spaces.pth f) z θ))) :=
      hg_ev.fderiv_eq.trans hcomp.fderiv
    exact norm_iterDF2_le hfd2

end Work.FTS_EllLimOK.ProducerH.BoxAux
