import Mathlib
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped ContDiff Topology
open Filter

/-- **Clairaut (Schwarz) for the slice `fderiv`, continuous-linear-map valued.**

For `Φ : ℝ × V → G` which is `C²` at `(t₀, u₀)`, the function `s ↦ ∂₂Φ(s, ·)|_{u₀}` (a
continuous linear map `V →L G`) has derivative at `t₀` equal to `∂₂(∂₁Φ)(t₀, u₀)`, i.e.
`s ↦ deriv (fun s => Φ s y) t₀` differentiated in `y`.

This is the `(V →L G)`-valued form of `Work.Diff.T.clairaut_fderiv_apply`, which states the same
identity pointwise: for every `v : V`,
`HasDerivAt (fun s => fderiv ℝ (fun y => Φ (s,y)) u₀ v) (fderiv ℝ (fun y => deriv (fun s => Φ (s,y)) t₀) u₀ v) t₀`.
Both sides are the second Fréchet derivative of `Φ` at `(t₀,u₀)` evaluated on `(1,0)` and `(0,v)`,
which agree by symmetry of the second derivative (`ContDiffAt.isSymmSndFDerivAt`).

Proof sketch (mirroring `Work.Diff.T.clairaut_fderiv_apply`):
* `P := fderiv ℝ (fun p : ℝ × V => fderiv ℝ Φ p) (t₀,u₀)`; `P` is symmetric:
  `IsSymmSndFDerivAt.eq` gives `P (0,v) (1,0) = P (1,0) (0,v)`.
* `C : ((ℝ × V) →L G) →L (V →L G)`, `C T = T.comp (ContinuousLinearMap.inr ℝ ℝ V)`
  (build it as `(ContinuousLinearMap.apply ℝ (V →L G) (ContinuousLinearMap.inr ℝ ℝ V)).comp
  (ContinuousLinearMap.compL ℝ V (ℝ × V) G)`; use `compL_apply` and `apply_apply`).
* `hA : HasFDerivAt (fun p => fderiv ℝ Φ p) P (t₀,u₀)` (from `hΦ.fderiv_right` + `differentiableAt.hasFDerivAt`).
* `s ↦ fderiv ℝ Φ (s,u₀)` has fderiv `P.comp (ContinuousLinearMap.inl ℝ ℝ V)` (chain rule with
  `hasFDerivAt_prodMk_left`); composing with the CLM `C` gives a `HasFDerivAt` of
  `s ↦ (fderiv ℝ Φ (s,u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)`.  Transport along the eventual
  equality `fderiv ℝ (fun y => Φ (s,y)) u₀ = (fderiv ℝ Φ (s,u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)`
  (from `HasFDerivAt.comp` with `hasFDerivAt_prodMk_right`, true for all `s` with `Φ` differentiable
  at `(s,u₀)`, hence eventually) and evaluate the derivative on `1`: it is `(P (1,0)).comp inr`.
* Identify the claimed value: by `ContinuousLinearMap.ext v`, use `Work.Diff.T.clairaut_fderiv_apply`
  (which gives the derivative of `s ↦ fderiv ℝ (fun y => Φ (s,y)) u₀ v`) together with the previous
  bullet evaluated on `v`; both expressions are `P (1,0) (0,v)`. -/
theorem hasDerivAt_sliceFDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Φ : ℝ × V → G} {t₀ : ℝ} {u₀ : V} (hΦ : ContDiffAt ℝ 2 Φ (t₀, u₀)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : V => Φ (s, y)) u₀)
      (fderiv ℝ (fun y : V => deriv (fun s : ℝ => Φ (s, y)) t₀) u₀) t₀ := by
  -- The second Fréchet derivative of `Φ` at `(t₀, u₀)`, as a continuous bilinear map.
  set P : (ℝ × V) →L[ℝ] ((ℝ × V) →L[ℝ] G) :=
    fderiv ℝ (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) with hP
  have hA_cd : ContDiffAt ℝ 1 (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) :=
    hΦ.fderiv_right (m := 1) (by norm_num)
  have hA_has : HasFDerivAt (fun p : ℝ × V => fderiv ℝ Φ p) P (t₀, u₀) := by
    rw [hP]
    exact (hA_cd.differentiableAt (by simp)).hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ Φ (t₀, u₀) := hΦ.isSymmSndFDerivAt (by simp)
  have hsymm_eq : ∀ v : V, P (0, v) (1, 0) = P (1, 0) (0, v) := by
    intro v
    have := hsymm.eq (0, v) (1, 0)
    simpa only [hP] using this
  -- The continuous linear map `T ↦ T.comp inr`, extracting the `V`-slot.
  set C : ((ℝ × V) →L[ℝ] G) →L[ℝ] (V →L[ℝ] G) :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] G) (ContinuousLinearMap.inr ℝ ℝ V)).comp
      (ContinuousLinearMap.compL ℝ V (ℝ × V) G) with hCdef
  have hC_apply : ∀ T : (ℝ × V) →L[ℝ] G, C T = T.comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro T
    rw [hCdef]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply]
  -- ## Left-hand side: `s ↦ (fderiv ℝ Φ (s,u₀)).comp inr` has derivative `(P (1,0)).comp inr`.
  have hM : HasDerivAt (fun s : ℝ => (fderiv ℝ Φ (s, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V))
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) t₀ := by
    have hφ : HasFDerivAt (fun s : ℝ => (s, u₀)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ u₀
    have h1' : HasFDerivAt (fun s : ℝ => fderiv ℝ Φ (s, u₀))
        (P.comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ := hA_has.comp t₀ hφ
    have h2 : HasFDerivAt (fun s : ℝ => C (fderiv ℝ Φ (s, u₀)))
        (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) t₀ :=
      (ContinuousLinearMap.hasFDerivAt C).comp t₀ h1'
    have h3 := h2.hasDerivAt
    have hvalC : (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) 1
        = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      exact hC_apply (P (1, 0))
    simpa only [hC_apply, hvalC, Function.comp_def] using h3
  -- ## Transport to the actual slice `fderiv`, which agrees with it near `t₀`.
  have hDev : ∀ᶠ s in 𝓝 t₀, DifferentiableAt ℝ Φ (s, u₀) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Tendsto (fun s : ℝ => (s, u₀)) (𝓝 t₀) (𝓝 (t₀, u₀)) :=
      continuousAt_id.prodMk continuousAt_const
    exact hφtend.eventually hDeev
  have hEv : (fun s : ℝ => fderiv ℝ (fun y : V => Φ (s, y)) u₀)
      =ᶠ[𝓝 t₀] (fun s : ℝ => (fderiv ℝ Φ (s, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
    filter_upwards [hDev] with s hs
    have hψ : HasFDerivAt (fun y : V => (s, y)) (ContinuousLinearMap.inr ℝ ℝ V) u₀ :=
      hasFDerivAt_prodMk_right (𝕜 := ℝ) s u₀
    have h := (hs.hasFDerivAt.comp u₀ hψ).fderiv
    simpa only [Function.comp_def] using h
  have hF : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : V => Φ (s, y)) u₀)
      ((P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V)) t₀ := hM.congr_of_eventuallyEq hEv
  -- ## The claimed value, identified by the `u`-derivative of the `t`-partial.
  have hDev' : ∀ᶠ y in 𝓝 u₀, DifferentiableAt ℝ Φ (t₀, y) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Tendsto (fun y : V => (t₀, y)) (𝓝 u₀) (𝓝 (t₀, u₀)) :=
      continuousAt_const.prodMk continuousAt_id
    exact hφtend.eventually hDeev
  have hEv' : (fun y : V => deriv (fun s : ℝ => Φ (s, y)) t₀)
      =ᶠ[𝓝 u₀] (fun y : V => (fderiv ℝ Φ (t₀, y)) (1, 0)) := by
    filter_upwards [hDev'] with y hy
    have hφ : HasFDerivAt (fun s : ℝ => (s, y)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ y
    have h := (hy.hasFDerivAt.comp t₀ hφ).hasDerivAt
    have h' := h.deriv
    simp only [Function.comp_def] at h'
    rw [h']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hR : HasFDerivAt (fun y : V => (fderiv ℝ Φ (t₀, y)) (1, 0))
      ((ContinuousLinearMap.apply ℝ G (1, 0)).comp
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V))) u₀ := by
    have hψ : HasFDerivAt (fun y : V => (t₀, y)) (ContinuousLinearMap.inr ℝ ℝ V) u₀ :=
      hasFDerivAt_prodMk_right (𝕜 := ℝ) t₀ u₀
    have h1' : HasFDerivAt (fun y : V => fderiv ℝ Φ (t₀, y))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) u₀ := hA_has.comp u₀ hψ
    have h2 := (ContinuousLinearMap.apply ℝ G (1, 0)).hasFDerivAt.comp u₀ h1'
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2
  have hval : fderiv ℝ (fun y : V => deriv (fun s : ℝ => Φ (s, y)) t₀) u₀
      = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    rw [hEv'.fderiv_eq, hR.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inr_apply]
    exact hsymm_eq v
  rw [hval]
  exact hF

end Work.Diff.EXT
