import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.fderiv_curve_eq_VcoefC

namespace Work.WilE3.Frame

open Classical Topology Filter

/-- **Differentiation along a complex line.**  If `F` is differentiable near `u₀`, with derivative
`fderiv ℂ F v` at each nearby `v`, then the one-variable function `t ↦ F (u₀ + t • w)` has
derivative `fderiv ℂ F (u₀ + t • w) w` for every `t` near `0`.  This is the chain rule applied to
the affine line `t ↦ u₀ + t • w`, whose derivative is `ContinuousLinearMap.toSpanSingleton ℂ w`. -/
lemma deriv_comp_line {K : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → (Fin K → ℂ)) (u₀ w : E)
    (hF : ∀ᶠ v in 𝓝 u₀, HasFDerivAt F (fderiv ℂ F v) v) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      deriv (fun t' : ℂ => F (u₀ + t' • w)) t = fderiv ℂ F (u₀ + t • w) w := by
  have hline : ∀ t : ℂ, HasFDerivAt (fun t' : ℂ => u₀ + t' • w)
      (ContinuousLinearMap.toSpanSingleton ℂ w) t := fun t =>
    (ContinuousLinearMap.toSpanSingleton ℂ w).hasFDerivAt.const_add u₀
  have htend : Filter.Tendsto (fun t : ℂ => u₀ + t • w) (𝓝 0) (𝓝 u₀) := by
    have hc : Continuous fun t : ℂ => u₀ + t • w := by fun_prop
    simpa using hc.tendsto (0 : ℂ)
  filter_upwards [htend.eventually hF] with t ht
  have hcomp : HasFDerivAt (fun t' : ℂ => F (u₀ + t' • w))
      ((fderiv ℂ F (u₀ + t • w)).comp (ContinuousLinearMap.toSpanSingleton ℂ w)) t :=
    ht.comp t (hline t)
  show fderiv ℂ (fun t' : ℂ => F (u₀ + t' • w)) t 1 = fderiv ℂ F (u₀ + t • w) w
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]

/-- **The tangent of the straightened curve.**  Let `Ψ` straighten `{h = 0}` at `x`
(`IsStraightening`), and let `w : U k ι → ℝ` be a real direction.  Then, near `t = 0`, the curve
`t ↦ Ψ (u₀ + t • w_ℂ, 0)` (where `u₀ = uCoord k ι (toC x)` and `w_ℂ` is `w` viewed in `ℂ`) has
derivative `Σ_{l : U k ι} w_l • VcoefC c h ι l Z(t)`, i.e. the tangential frame field contracted
with `w`.

This is the chain rule applied to `Ψ ∘ (t ↦ (u₀ + t • w_ℂ, 0))`, using `fderiv_curve_eq_VcoefC`
(which computes `fderiv (fun v => Ψ (v, 0)) v (Pi.single l 1) = VcoefC c h ι l (Ψ (v, 0))` near `u₀`
under the hypothesis `hd`) and the linearity of `fderiv` in the direction: the direction
`w_ℂ` is `Σ_l w_l • Pi.single l 1`. -/
theorem curve_tangent {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : Work.WilE3.Frame.IsStraightening c h ι x Ψ)
    (hd : (Matrix.of fun a b => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c (ι b) (h a))
      (Work.WilE3.Frame.toC x)).det ≠ 0)
    (w : Work.WilE3.Frame.U k ι → ℝ) :
    ∀ᶠ t in nhds (0 : ℂ),
      deriv (fun t' : ℂ => Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
          t' • (fun i => (w i : ℂ)), 0)) t =
        ∑ l : Work.WilE3.Frame.U k ι, (w l : ℂ) • Work.WilE3.Frame.VcoefC c h ι l
          (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
            t • (fun i => (w i : ℂ)), 0)) := by
  classical
  let F : (U k ι → ℂ) → (Fin k → ℂ) := fun v => Ψ (v, 0)
  let u₀ : U k ι → ℂ := uCoord k ι (toC x)
  let wC : U k ι → ℂ := fun i => (w i : ℂ)
  change ∀ᶠ t in 𝓝 (0 : ℂ),
      deriv (fun t' : ℂ => F (u₀ + t' • wC)) t =
      ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l (F (u₀ + t • wC))
  -- `Ψ` is analytic, hence differentiable, on a neighbourhood of the base point `(u₀, 0)`, so the
  -- slice `v ↦ Ψ (v, 0)` is differentiable near `u₀`.
  have hslice : ∀ᶠ v in 𝓝 u₀, HasFDerivAt F (fderiv ℂ F v) v := by
    have hinl : Filter.Tendsto (fun v : U k ι → ℂ => (v, (0 : Fin j → ℂ)))
        (𝓝 u₀) (𝓝 (u₀, 0)) := by
      have hc : Continuous fun v : U k ι → ℂ => (v, (0 : Fin j → ℂ)) := by fun_prop
      simpa using hc.tendsto u₀
    have h1 : ∀ᶠ v in 𝓝 u₀, AnalyticAt ℂ Ψ (v, 0) :=
      hinl.eventually hΨ.2.1.eventually_analyticAt
    refine h1.mono fun v hv => ?_
    have hfun : (⇑(ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ))) =
        (fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ))) := by
      funext v'
      simp [ContinuousLinearMap.inl_apply]
    have hvd : HasFDerivAt (fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ)))
        (ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)) v := by
      have hh := (ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)).hasFDerivAt (x := v)
      rwa [hfun] at hh
    have hcomp := (hv.differentiableAt.hasFDerivAt).comp v hvd
    have hfun2 : (Ψ ∘ fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ))) =
        (fun v' : U k ι → ℂ => Ψ (v', 0)) := rfl
    rw [hfun2] at hcomp
    rw [← hcomp.fderiv] at hcomp
    simpa [F] using hcomp
  -- The fibrewise tangency: `fderiv` of the slice is the frame field, on a neighbourhood of `u₀`.
  have hall : ∀ᶠ v in 𝓝 u₀, ∀ l : U k ι,
      fderiv ℂ F v (Pi.single l 1) = VcoefC c h ι l (F v) :=
    (Filter.eventually_all (ι := U k ι)).mpr fun l =>
      fderiv_curve_eq_VcoefC c h ι x Ψ hΨ.2.2.1 hΨ.1 hΨ.2.1 hd l
  -- Hence `fderiv` of the slice, applied to `w_ℂ = Σ_l w_l • Pi.single l 1`, is the frame field
  -- contracted with `w` (linearity of `fderiv` in the direction).
  have hlin : ∀ᶠ v in 𝓝 u₀,
      fderiv ℂ F v wC = ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l (F v) := by
    refine hall.mono fun v hv => ?_
    have hwC : wC = ∑ l : U k ι, (w l : ℂ) • Pi.single l (1 : ℂ) := by
      rw [pi_eq_sum_univ' wC]
    rw [hwC, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hv l]
  -- Chain rule along the line `t ↦ u₀ + t • w_ℂ`, and the two eventual statements meet.
  have hline := deriv_comp_line F u₀ wC hslice
  have htend : Filter.Tendsto (fun t : ℂ => u₀ + t • wC) (𝓝 0) (𝓝 u₀) := by
    have hc : Continuous fun t : ℂ => u₀ + t • wC := by fun_prop
    simpa using hc.tendsto (0 : ℂ)
  filter_upwards [hline, htend.eventually hlin] with t h1 h2
  exact h1.trans h2

end Work.WilE3.Frame
