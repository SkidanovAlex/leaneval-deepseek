/-
# `Work.FTS.Physical.Pressure.vorticity_materialAccel_eq_zero_at`

**The material acceleration of a solution of Euler is curl-free**, i.e. the curl of the Euler
equation is the vorticity equation.  For a jointly `C²` velocity field `u` with

* `ω = ∇×u` (at every time: `hcurl`),
* `div u = 0` at time `t` (`hdivu`),
* the vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u` at time `t` (`hvort`),

the material acceleration `G = ∂ₜu + (u·∇)u` has vanishing curl at `(x,t)`:

  `∇×(∂ₜu + (u·∇)u)(x,t) = 0`.

This is the statement consumed by the pressure reconstruction of `Physical/Defs.lean`: the Euler
equation `G = -∇p` produces a pressure only if `G` is curl-free, and conversely the curl of the
Euler equation is exactly the vorticity equation — which is what identifies the pressure of the
reconstructed solution.

## Proof

The curl is a *continuous linear* function `curlCLM` of the Fréchet derivative
(`Work.FTS.Physical.Pressure.CurlCLM`), so it is additive:

`∇×G(x) = ∇×(∂ₜu(·,t))(x) + ∇×((u·∇)u)(x)`

(the two summands are differentiable at `x`: the first because near `x` it coincides with
`y ↦ Du(y,t)(0,1)`, a composition of the `C¹` map `y ↦ Du(y,t)` with a continuous linear map; the
second by the product rule for `HasFDerivAt.clm_apply` applied to the slice `u(·,t)`, which is `C²`
at `x`).

The two curls are the classical identities

* `∇×(∂ₜu(·,t))(x) = ∂ₜ(∇×u(·,t))(x)`: differentiating the parametrised derivative
  `s ↦ Du(x,s)` (Clairaut) and composing with the continuous linear `curlCLM`;
* `∇×((u·∇)u)(x) = (u·∇)(∇×u)(x) - ((∇×u)·∇)u(x)`: the product rule for the curl
  (`Work.FTS.Physical.Pressure.vorticity_materialAccel_eq`), using `tr Du(x) = div u = 0` and the
  symmetry of the second derivative.

Substituting `ω = ∇×u` and the vorticity equation `hvort` in the sum gives
`∂ₜω + (u·∇)ω - (ω·∇)u = 0`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Pressure.CurlCLM
import Submission.Work.FTS.Physical.Pressure.vorticity_materialAccel_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.Physical.Pressure

/-! ## Calculus lemmas for a jointly `C²` spacetime field `U : ℝ³ × ℝ → ℝ³` -/

/-- The spatial slice derivative is the spatial block of the joint derivative:
`D(U(·,t))(y) = DU(y,t) ∘ inl`. -/
lemma ma_slice_fderiv_eq {U : R3 × ℝ → R3} {y : R3} {t : ℝ} (hy : DifferentiableAt ℝ U (y, t)) :
    fderiv ℝ (fun z => U (z, t)) y
      = (fderiv ℝ U (y, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  have h4 : HasFDerivAt (fun z : R3 => (z, t)) (ContinuousLinearMap.inl ℝ R3 ℝ) y :=
    hasFDerivAt_prodMk_left y t
  have h5 : HasFDerivAt (U ∘ fun z : R3 => (z, t))
      ((fderiv ℝ U (y, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) y :=
    hy.hasFDerivAt.comp y h4
  have h6 : (U ∘ fun z : R3 => (z, t)) = (fun z : R3 => U (z, t)) := rfl
  rw [h6] at h5
  exact h5.fderiv

/-- The time derivative of a slice is the joint derivative evaluated on the time direction:
`∂ₛU(y,s)|ₛ₌ₜ = DU(y,t) (0,1)`. -/
lemma ma_deriv_slice_eq {U : R3 × ℝ → R3} {y : R3} {t : ℝ} (hy : DifferentiableAt ℝ U (y, t)) :
    deriv (fun s => U (y, s)) t = (fderiv ℝ U (y, t)) ((0 : R3), (1 : ℝ)) := by
  have h2 : HasFDerivAt (fun s : ℝ => (y, s)) (ContinuousLinearMap.inr ℝ R3 ℝ) t :=
    hasFDerivAt_prodMk_right y t
  have h3 : HasFDerivAt (U ∘ fun s : ℝ => (y, s))
      ((fderiv ℝ U (y, t)) ∘SL (ContinuousLinearMap.inr ℝ R3 ℝ)) t :=
    hy.hasFDerivAt.comp t h2
  have h4 := h3.hasDerivAt
  have h6 : (U ∘ fun s : ℝ => (y, s)) = (fun s : ℝ => U (y, s)) := rfl
  rw [h6] at h4
  rw [h4.deriv]
  simp

/-- The time slice `y ↦ U(y,t)` of a jointly `C²` field is `C²`. -/
lemma ma_contDiffAt_slice {U : R3 × ℝ → R3} {x : R3} {t : ℝ} (h : ContDiffAt ℝ 2 U (x, t)) :
    ContDiffAt ℝ 2 (fun y : R3 => U (y, t)) x := by
  have hC : ContDiffAt ℝ 2 (fun y : R3 => ((y : R3), t)) x :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have h1 : ContDiffAt ℝ 2 (U ∘ fun y : R3 => (y, t)) x := h.comp x hC
  have h2 : (U ∘ fun y : R3 => (y, t)) = (fun y : R3 => U (y, t)) := rfl
  rwa [h2] at h1

/-- A jointly `C²` field is differentiable on a neighbourhood of the point. -/
lemma ma_eventually_diff {U : R3 × ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 U (x, t)) :
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ U (y, t)) ∧ (∀ᶠ s in 𝓝 t, DifferentiableAt ℝ U (x, s)) := by
  have h1 : ∀ᶠ p in 𝓝 ((x, t) : R3 × ℝ), DifferentiableAt ℝ U p :=
    (h.eventually (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun p hp => hp.differentiableAt (by norm_num))
  exact ⟨(Continuous.prodMk_left t).continuousAt.eventually h1,
    (Continuous.prodMk_right x).continuousAt.eventually h1⟩

/-- Clairaut for the parametrised Fréchet derivative: the derivative at `t` of `s ↦ DU(x,s)` is
the second derivative `D²U(x,t)` evaluated on the time direction `(0,1)`. -/
lemma ma_hasDerivAt_fderiv_slice {U : R3 × ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 U (x, t)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ U (x, s))
      ((fderiv ℝ (fderiv ℝ U) (x, t)) ((0 : R3), (1 : ℝ))) t := by
  have hF : HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) (x, t)) (x, t) :=
    ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hj : HasDerivAt (fun s : ℝ => ((x, s) : R3 × ℝ)) ((0 : R3), (1 : ℝ)) t := by
    have h0 : HasDerivAt (fun s : ℝ => ((0 : R3), s)) ((0 : R3), (1 : ℝ)) t := by
      simpa using (hasDerivAt_id t).smul_const ((0 : R3), (1 : ℝ))
    simpa using h0.add_const ((x : R3), (0 : ℝ))
  exact hF.comp_hasDerivAt t hj

/-- For a fixed vector `v`, the map `y ↦ DU(y,t) v` has derivative
`(w ↦ D²U(x,t)(w,0)(v)) = (D²U(x,t) v) ∘ inl`. -/
lemma ma_hasFDerivAt_apply_const {U : R3 × ℝ → R3} {x : R3} {t : ℝ} {v : R3 × ℝ}
    (h : ContDiffAt ℝ 2 U (x, t)) :
    HasFDerivAt (fun y : R3 => (fderiv ℝ U (y, t)) v)
      ((ContinuousLinearMap.apply ℝ R3 v) ∘SL
        ((fderiv ℝ (fderiv ℝ U) (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ U) (x, t) :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hC : HasFDerivAt (fun y : R3 => (y, t)) (ContinuousLinearMap.inl ℝ R3 ℝ) x :=
    hasFDerivAt_prodMk_left x t
  have h1 : HasFDerivAt (fderiv ℝ U ∘ fun y : R3 => (y, t))
      ((fderiv ℝ (fderiv ℝ U) (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) x :=
    hD.hasFDerivAt.comp x hC
  have h2 : (fderiv ℝ U ∘ fun y : R3 => (y, t)) = (fun y : R3 => fderiv ℝ U (y, t)) := rfl
  rw [h2] at h1
  exact (ContinuousLinearMap.apply ℝ R3 v).hasFDerivAt.comp x h1

/-- Symmetry of the second derivative (Clairaut/Schwarz). -/
lemma ma_symm_snd_fderiv {U : R3 × ℝ → R3} {x : R3} {t : ℝ} (h : ContDiffAt ℝ 2 U (x, t))
    (a b : R3 × ℝ) :
    (fderiv ℝ (fderiv ℝ U) (x, t) a) b = (fderiv ℝ (fderiv ℝ U) (x, t) b) a :=
  (h.isSymmSndFDerivAt (by simp)).eq a b

/-- `(v ↦ D²U(x,t)(w,0)(v) = D²U(x,t)(v,0)(w)`: the symmetry of the second derivative, read on
continuous linear maps. -/
lemma ma_apply_comp_symm {U : R3 × ℝ → R3} {x : R3} {t : ℝ} (h : ContDiffAt ℝ 2 U (x, t))
    (v : R3 × ℝ) :
    (ContinuousLinearMap.apply ℝ R3 v) ∘SL
        ((fderiv ℝ (fderiv ℝ U) (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))
      = (fderiv ℝ (fderiv ℝ U) (x, t) v) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inl_apply]
  exact ma_symm_snd_fderiv h (y, 0) v

/-- **`∇×` commutes with `∂ₜ`.**  For a jointly `C²` field `U`,

  `∂ₜ(∇×U(·,t))(x) = ∇×((D²U(x,t) (0,1)) ∘ inl)`. -/
lemma ma_deriv_vorticity_slice {U : R3 × ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 U (x, t)) :
    deriv (fun s => vorticity (fun y => U (y, s)) x) t
      = curlCLM ((fderiv ℝ (fderiv ℝ U) (x, t) ((0 : R3), (1 : ℝ))) ∘SL
          (ContinuousLinearMap.inl ℝ R3 ℝ)) := by
  have hslice : (fun s => vorticity (fun y => U (y, s)) x) =ᶠ[𝓝 t]
      (fun s => curlCLM ((fderiv ℝ U (x, s)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))) := by
    filter_upwards [(ma_eventually_diff h).2] with s hs
    rw [vorticity_eq_curlCLM, ma_slice_fderiv_eq hs]
  have h3 : HasDerivAt
      (fun s : ℝ => curlCLM ((fderiv ℝ U (x, s)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)))
      (curlCLM ((fderiv ℝ (fderiv ℝ U) (x, t) ((0 : R3), (1 : ℝ))) ∘SL
        (ContinuousLinearMap.inl ℝ R3 ℝ))) t := by
    have hΦ := ma_hasDerivAt_fderiv_slice (U := U) h
    have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ U (x, s)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))
        ((fderiv ℝ (fderiv ℝ U) (x, t) ((0 : R3), (1 : ℝ))) ∘SL
          (ContinuousLinearMap.inl ℝ R3 ℝ)) t := by
      have hc := hΦ.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inl ℝ R3 ℝ))
      simpa using hc
    exact (ContinuousLinearMap.hasFDerivAt curlCLM).comp_hasDerivAt t h2
  rw [Filter.EventuallyEq.eq_of_nhds (Filter.EventuallyEq.deriv hslice), h3.deriv]

/-! ## Additivity and germ-invariance of the curl -/

/-- The curl is additive at a point where both fields are differentiable. -/
lemma ma_vorticity_add {f g : R3 → R3} {x : R3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    vorticity (f + g) x = vorticity f x + vorticity g x := by
  rw [vorticity_eq_curlCLM, vorticity_eq_curlCLM, vorticity_eq_curlCLM, fderiv_add hf hg,
    map_add]

/-- The curl depends only on the germ at the point. -/
lemma ma_vorticity_congr {F G : R3 → R3} {x : R3} (h : F =ᶠ[𝓝 x] G) :
    vorticity F x = vorticity G x := by
  rw [vorticity_eq_curlCLM, vorticity_eq_curlCLM, h.fderiv_eq]

/-! ## The theorem -/

theorem vorticity_materialAccel_eq_zero_at {u ω : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {x : Work.FTS.Physical.R3} {t : ℝ} (hcurl : ∀ y : Work.FTS.Physical.R3, ∀ s : ℝ, FiniteTimeSingularity.vorticity (fun z => u z s) y = ω y s) (hdivu : FiniteTimeSingularity.div (fun z => u z t) = 0) (hvort : ∀ y : Work.FTS.Physical.R3, FiniteTimeSingularity.timeDeriv ω y t + FiniteTimeSingularity.directionalDeriv ω u y t = FiniteTimeSingularity.directionalDeriv u ω y t) (hjoint : ContDiffAt ℝ 2 (fun q : Work.FTS.Physical.R3 × ℝ => u q.1 q.2) (x, t)) : FiniteTimeSingularity.vorticity (fun y => FiniteTimeSingularity.timeDeriv u y t + FiniteTimeSingularity.directionalDeriv u u y t) x = 0 := by
  have hslice2 : ContDiffAt ℝ 2 (fun y : R3 => u y t) x :=
    ma_contDiffAt_slice (U := fun q : R3 × ℝ => u q.1 q.2) hjoint
  -- the time-derivative slice coincides, near `x`, with `y ↦ DU(y,t)(0,1)`
  have htd_ev : (fun y : R3 => timeDeriv u y t) =ᶠ[𝓝 x]
      (fun y : R3 => (fderiv ℝ (fun q : R3 × ℝ => u q.1 q.2) (y, t)) ((0 : R3), (1 : ℝ))) := by
    filter_upwards [(ma_eventually_diff (U := fun q : R3 × ℝ => u q.1 q.2) hjoint).1]
      with y hy
    show deriv (fun s => (fun q : R3 × ℝ => u q.1 q.2) (y, s)) t = _
    exact ma_deriv_slice_eq (U := fun q : R3 × ℝ => u q.1 q.2) hy
  have htd : DifferentiableAt ℝ (fun y : R3 => timeDeriv u y t) x :=
    (Filter.EventuallyEq.differentiableAt_iff htd_ev).mpr
      ((ma_hasFDerivAt_apply_const (U := fun q : R3 × ℝ => u q.1 q.2)
        (v := ((0 : R3), (1 : ℝ))) hjoint).differentiableAt)
  -- the material-derivative slice is differentiable (product rule on the `C²` slice)
  have hmd : DifferentiableAt ℝ (fun y : R3 => directionalDeriv u u y t) x := by
    have hd1 : HasFDerivAt (fun y : R3 => u y t) (fderiv ℝ (fun y : R3 => u y t) x) x :=
      (hslice2.differentiableAt (by norm_num)).hasFDerivAt
    have hd2 : HasFDerivAt (fderiv ℝ (fun y : R3 => u y t))
        (fderiv ℝ (fderiv ℝ (fun y : R3 => u y t)) x) x :=
      ((hslice2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (hd2.clm_apply hd1).differentiableAt
  -- `∇×(∂ₜu(·,t))(x) = ∂ₜ(∇×u(·,t))(x)`
  have htime : vorticity (fun y : R3 => timeDeriv u y t) x
      = deriv (fun s => vorticity (fun y => u y s) x) t := by
    have hA : vorticity (fun y : R3 => timeDeriv u y t) x
        = curlCLM ((ContinuousLinearMap.apply ℝ R3 ((0 : R3), (1 : ℝ))) ∘SL
            ((fderiv ℝ (fderiv ℝ (fun q : R3 × ℝ => u q.1 q.2)) (x, t)) ∘SL
              (ContinuousLinearMap.inl ℝ R3 ℝ))) := by
      rw [ma_vorticity_congr htd_ev, vorticity_eq_curlCLM,
        (ma_hasFDerivAt_apply_const (U := fun q : R3 × ℝ => u q.1 q.2)
          (v := ((0 : R3), (1 : ℝ))) hjoint).fderiv]
    have hB := ma_apply_comp_symm (U := fun q : R3 × ℝ => u q.1 q.2) hjoint ((0 : R3), (1 : ℝ))
    have hC : deriv (fun s => vorticity (fun y => u y s) x) t
        = curlCLM ((fderiv ℝ (fderiv ℝ (fun q : R3 × ℝ => u q.1 q.2)) (x, t)
            ((0 : R3), (1 : ℝ))) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) :=
      ma_deriv_vorticity_slice (U := fun q : R3 × ℝ => u q.1 q.2) hjoint
    rw [hA, hB, ← hC]
  -- `∇×((u·∇)u)(x) = (u·∇)(∇×u)(x) - ((∇×u)·∇)u(x)`
  have hmat : vorticity (fun y : R3 => directionalDeriv u u y t) x
      = fderiv ℝ (fun y => vorticity (fun z => u z t) y) x (u x t)
        - fderiv ℝ (fun z => u z t) x (vorticity (fun z => u z t) x) :=
    vorticity_materialAccel_eq x hdivu hslice2
  calc vorticity (fun y : R3 => timeDeriv u y t + directionalDeriv u u y t) x
      = vorticity (fun y : R3 => timeDeriv u y t) x
          + vorticity (fun y : R3 => directionalDeriv u u y t) x :=
        ma_vorticity_add htd hmd
    _ = deriv (fun s => vorticity (fun y => u y s) x) t
          + (fderiv ℝ (fun y => vorticity (fun z => u z t) y) x (u x t)
              - fderiv ℝ (fun z => u z t) x (vorticity (fun z => u z t) x)) := by
        rw [htime, hmat]
    _ = 0 := by
        -- substitute `ω = ∇×u` and the vorticity equation
        have hω : (fun y => vorticity (fun z => u z t) y) = (fun y => ω y t) :=
          funext (fun y => hcurl y t)
        have h1 : fderiv ℝ (fun y => vorticity (fun z => u z t) y) x (u x t)
            = directionalDeriv ω u x t := by
          rw [hω]
          rfl
        have h2 : deriv (fun s => vorticity (fun y => u y s) x) t = timeDeriv ω x t := by
          rw [show (fun s => vorticity (fun y => u y s) x) = (fun s => ω x s)
            from funext (fun s => hcurl x s)]
          rfl
        have h3 : fderiv ℝ (fun z => u z t) x (vorticity (fun z => u z t) x)
            = directionalDeriv u ω x t := by
          rw [show vorticity (fun z => u z t) x = ω x t from hcurl x t]
          rfl
        rw [h1, h2, h3, ← hvort x]
        abel

end Work.FTS.Physical.Pressure
