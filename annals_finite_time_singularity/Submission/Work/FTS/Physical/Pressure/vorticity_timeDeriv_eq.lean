import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂ₜ (∇ × u(·,t)) = ∇ × (∂ₜ u)(·,t)` on `ℝ³`

The vorticity of a space-time velocity field commutes with the time derivative: if
`f = uncurry u : ℝ³ × ℝ → ℝ³` is `C²` near `(x,t)`, then

  `deriv (fun s => vorticity (fun y => u y s) x) t = vorticity (fun y => deriv (fun s => u y s) t) x`.

Both sides are the mixed second derivative `∂ₓ∂ₜ f` contracted with the curl
`∑ᵢ eᵢ ⨯₃ (·)`: the content of the lemma is exactly the symmetry of the second
derivative of `f` (`ContDiffAt.isSymmSndFDerivAt`) together with the two chain rules
that express `∂ₜ (fderiv ℝ f (x,·))` and `fderiv ℝ (∂ₜ f(·,t))` at the point `(x,t)`.

The curl `vorticity u x = ∑ᵢ eᵢ ⨯₃ (fderiv ℝ u x eᵢ)` is *linear* in `fderiv ℝ u x`, so
it is packaged here as the continuous linear map `curlCLMT` (built from `WithLp.toLp`,
`WithLp.ofLp` and the cross product, all of which are continuous linear in finite
dimension).  This lets the time derivative pass through the whole curl in one step.
-/

open scoped Matrix
open Filter Topology

namespace Work.FTS.Physical.Pressure

/-! ## Plumbing: the curl as a continuous linear map -/

/-- `WithLp.ofLp`, the identification `ℝ³ → (Fin 3 → ℝ)`, as a continuous linear map. -/
noncomputable def ofLpCLMT : R3 →L[ℝ] (Fin 3 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.toContinuousLinearMap

lemma ofLpCLMT_apply (x : R3) : ofLpCLMT x = x.ofLp := rfl

/-- `WithLp.toLp 2`, the identification `(Fin 3 → ℝ) → ℝ³`, as a continuous linear map. -/
noncomputable def toLpCLMT : (Fin 3 → ℝ) →L[ℝ] R3 :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.toContinuousLinearMap

lemma toLpCLMT_apply (x : Fin 3 → ℝ) : toLpCLMT x = WithLp.toLp 2 x := rfl

/-- The cross product with a fixed vector, as a continuous linear map. -/
noncomputable def crossCLMT (a : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (crossProduct a).toContinuousLinearMap

lemma crossCLMT_apply (a b : Fin 3 → ℝ) : crossCLMT a b = a ⨯₃ b := rfl

/-- **The curl as a continuous linear map.**  For a linear map `L : ℝ³ × ℝ →L ℝ³` (the spatial
derivative of a space-time velocity field), `curlCLMT L` is the curl of the spatial field `L(·, 0)`:

`curlCLMT L = ∑ᵢ eᵢ ⨯₃ (L (eᵢ, 0))`. -/
noncomputable def curlCLMT : (R3 × ℝ →L[ℝ] R3) →L[ℝ] R3 :=
  toLpCLMT.comp (∑ i : Fin 3, (crossCLMT (Pi.single i (1 : ℝ))).comp
    (ofLpCLMT.comp (ContinuousLinearMap.apply ℝ R3 ((FiniteTimeSingularity.e i), (0 : ℝ)))))

lemma curlCLMT_apply (L : R3 × ℝ →L[ℝ] R3) :
    curlCLMT L
      = WithLp.toLp 2
          (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i, 0))) := by
  simp [curlCLMT, crossCLMT_apply, ofLpCLMT_apply, toLpCLMT_apply, FiniteTimeSingularity.e]

/-- The defining formula for the vorticity, in terms of `WithLp.toLp`. -/
lemma vorticity_apply_eq (g : R3 → R3) (y : R3) :
    FiniteTimeSingularity.vorticity g y
      = WithLp.toLp 2 (∑ i : Fin 3,
          FiniteTimeSingularity.e i ⨯₃ (fderiv ℝ g y (FiniteTimeSingularity.e i))) := rfl

/-! ## The three analytic inputs -/

/-- The spatial derivative of the time slice is the spatial part of the space-time derivative. -/
lemma fderiv_uncurry_slice {f : R3 × ℝ → R3} {x : R3} {s : ℝ}
    (h : DifferentiableAt ℝ f (x, s)) (v : R3) :
    fderiv ℝ (fun y : R3 => f (y, s)) x v = fderiv ℝ f (x, s) (v, 0) := by
  have hg : HasFDerivAt (fun y : R3 => (y, s)) (ContinuousLinearMap.inl ℝ R3 ℝ) x :=
    hasFDerivAt_prodMk_left x s
  have hf : HasFDerivAt f (fderiv ℝ f (x, s)) (x, s) := h.hasFDerivAt
  have hcomp' : fderiv ℝ (fun y : R3 => f (y, s)) x
      = (fderiv ℝ f (x, s)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := (hf.comp x hg).fderiv
  rw [hcomp']
  simp [ContinuousLinearMap.inl_apply]

/-- **The time derivative of the spatial derivative.**  For `f` of class `C²` at `(x,t)` the map
`s ↦ fderiv ℝ f (x,s)` is differentiable at `t` with derivative the second derivative of `f`
evaluated in the time direction `(0,1)`. -/
lemma hasDerivAt_fderiv_slice {f : R3 × ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 f (x, t)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x, s)) (fderiv ℝ (fderiv ℝ f) (x, t) (0, 1)) t := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) (x, t) := h.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x, t)) (x, t) :=
    (hdf.differentiableAt (by norm_num)).hasFDerivAt
  have hgd : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t := by
    simpa using (hasFDerivAt_prodMk_right x t).hasDerivAt
  have hcomp := hfd.comp_hasDerivAt t hgd
  have hfun : ((fderiv ℝ f) ∘ fun s : ℝ => (x, s)) = fun s : ℝ => fderiv ℝ f (x, s) := rfl
  rw [hfun] at hcomp
  exact hcomp

/-- **The spatial derivative of the time derivative.**  For `f` of class `C²` at `(x,t)`, the
spatial derivative at `x` of `y ↦ ∂ₜ f(y,t)` is the second derivative of `f` evaluated once in the
spatial direction `(v,0)` and once in the time direction `(0,1)`. -/
lemma fderiv_deriv_slice {f : R3 × ℝ → R3} {x : R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 f (x, t)) (v : R3) :
    fderiv ℝ (fun y : R3 => deriv (fun s : ℝ => f (y, s)) t) x v
      = fderiv ℝ (fderiv ℝ f) (x, t) (v, 0) (0, 1) := by
  -- `f` is `C²` on a neighbourhood of `(x,t)`, hence `∂ₜ f(y,t) = fderiv ℝ f (y,t) (0,1)` for
  -- `y` near `x`.
  obtain ⟨U, hU, hCU⟩ := h.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  have hev : (fun y : R3 => deriv (fun s : ℝ => f (y, s)) t)
      =ᶠ[𝓝 x] (fun y : R3 => fderiv ℝ f (y, t) (0, 1)) := by
    filter_upwards [(Continuous.prodMk_left t).continuousAt.eventually
      (hWopen.mem_nhds hxW)] with y hy
    have hy2 : ContDiffAt ℝ 2 f (y, t) := (hCU.mono hWU).contDiffAt (hWopen.mem_nhds hy)
    have hd : HasFDerivAt f (fderiv ℝ f (y, t)) (y, t) :=
      (hy2.differentiableAt (by norm_num)).hasFDerivAt
    have hgd : HasDerivAt (fun s : ℝ => (y, s)) (0, 1) t := by
      simpa using (hasFDerivAt_prodMk_right y t).hasDerivAt
    have hcd := hd.comp_hasDerivAt t hgd
    have hfun : (f ∘ fun s : ℝ => (y, s)) = fun s : ℝ => f (y, s) := rfl
    rw [hfun] at hcd
    exact hcd.deriv
  rw [hev.fderiv_eq]
  -- chain rule: `y ↦ fderiv ℝ f (y,t) (0,1)` at `x`
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) (x, t) := h.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x, t)) (x, t) :=
    (hdf.differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun y : R3 => fderiv ℝ f (y, t))
      ((fderiv ℝ (fderiv ℝ f) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ)) x :=
    hfd.comp x (hasFDerivAt_prodMk_left x t)
  have h2 : HasFDerivAt (fun y : R3 => fderiv ℝ f (y, t) (0, 1))
      ((ContinuousLinearMap.apply ℝ R3 ((0 : R3), 1)).comp
        ((fderiv ℝ (fderiv ℝ f) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ))) x :=
    (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.apply ℝ R3 ((0 : R3), (1 : ℝ)))).comp x h1
  rw [h2.fderiv]
  simp [ContinuousLinearMap.inl_apply]

/-! ## The theorem -/

theorem vorticity_timeDeriv_eq {u : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3}
    {x : Work.FTS.Physical.R3} {t : ℝ}
    (h : ContDiffAt ℝ 2 (fun q : Work.FTS.Physical.R3 × ℝ => u q.1 q.2) (x, t)) :
    deriv (fun s => FiniteTimeSingularity.vorticity (fun y => u y s) x) t
      = FiniteTimeSingularity.vorticity (fun y => deriv (fun s => u y s) t) x := by
  set f : R3 × ℝ → R3 := fun q => u q.1 q.2 with hf
  have h' : ContDiffAt ℝ 2 f (x, t) := h
  -- the two mixed second derivatives of `f` at `(x,t)` agree
  have hsymm : IsSymmSndFDerivAt ℝ f (x, t) := h'.isSymmSndFDerivAt (by simp)
  have hA := hasDerivAt_fderiv_slice h'
  -- near `t`, the vorticity of the time slice is `curlCLMT` applied to `fderiv ℝ f (x,·)`
  have hgerm : (fun s : ℝ => FiniteTimeSingularity.vorticity (fun y => u y s) x) =ᶠ[𝓝 t]
      (fun s : ℝ => curlCLMT (fderiv ℝ f (x, s))) := by
    obtain ⟨U, hU, hCU⟩ := h'.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
    filter_upwards [(Continuous.prodMk_right x).continuousAt.eventually
      (hWopen.mem_nhds hxW)] with s hs
    have hcs : ContDiffAt ℝ 2 f (x, s) := (hCU.mono hWU).contDiffAt (hWopen.mem_nhds hs)
    rw [vorticity_apply_eq, curlCLMT_apply]
    apply congrArg (WithLp.toLp 2)
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun z => FiniteTimeSingularity.e i ⨯₃ z)
    exact congrArg WithLp.ofLp
      (fderiv_uncurry_slice (hcs.differentiableAt (by norm_num)) (FiniteTimeSingularity.e i))
  have key1 : deriv (fun s => FiniteTimeSingularity.vorticity (fun y => u y s) x) t
      = curlCLMT (fderiv ℝ (fderiv ℝ f) (x, t) (0, 1)) := by
    rw [hgerm.deriv_eq]
    have h2 : HasDerivAt (fun s : ℝ => curlCLMT (fderiv ℝ f (x, s)))
        (curlCLMT (deriv (fun s : ℝ => fderiv ℝ f (x, s)) t)) t :=
      (ContinuousLinearMap.hasFDerivAt curlCLMT).comp_hasDerivAt t hA.differentiableAt.hasDerivAt
    rw [h2.deriv, hA.deriv]
  have key2 : FiniteTimeSingularity.vorticity (fun y => deriv (fun s => u y s) t) x
      = curlCLMT (fderiv ℝ (fderiv ℝ f) (x, t) (0, 1)) := by
    change FiniteTimeSingularity.vorticity (fun y : R3 => deriv (fun s : ℝ => f (y, s)) t) x
      = curlCLMT (fderiv ℝ (fderiv ℝ f) (x, t) (0, 1))
    rw [vorticity_apply_eq, curlCLMT_apply]
    apply congrArg (WithLp.toLp 2)
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun z => FiniteTimeSingularity.e i ⨯₃ z)
    refine congrArg WithLp.ofLp
      ((fderiv_deriv_slice h' (FiniteTimeSingularity.e i)).trans ?_)
    exact (hsymm.eq (0, 1) (FiniteTimeSingularity.e i, 0)).symm
  rw [key1, key2]

end Work.FTS.Physical.Pressure
