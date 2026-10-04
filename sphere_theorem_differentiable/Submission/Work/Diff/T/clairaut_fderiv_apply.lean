import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open scoped ContDiff Topology
open Filter

/-- **Clairaut's theorem (Schwarz), mixed-partial form.**

For a map `Φ : ℝ × V → G` which is `C²` at `(t₀, u₀)`, the `t`-derivative at `t₀` of the
partial derivative in the `u`-direction (applied to a fixed vector `w`) equals the value on `w`
of the `u`-derivative at `u₀` of the partial derivative in the `t`-direction.

Both sides are the second derivative of `Φ` at `(t₀, u₀)` evaluated on `(1, 0)` and `(0, w)`;
they agree by symmetry of the second Fréchet derivative (`ContDiffAt.isSymmSndFDerivAt`). -/
theorem clairaut_fderiv_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Φ : ℝ × V → G} {t₀ : ℝ} {u₀ : V} (hΦ : ContDiffAt ℝ 2 Φ (t₀, u₀)) (w : V) :
    HasDerivAt (fun t ↦ fderiv ℝ (fun u : V ↦ Φ (t, u)) u₀ w)
      (fderiv ℝ (fun u : V ↦ deriv (fun t : ℝ ↦ Φ (t, u)) t₀) u₀ w) t₀ := by
  -- The second Fréchet derivative of `Φ` at `(t₀, u₀)`, as a continuous bilinear map.
  set P : (ℝ × V) →L[ℝ] ((ℝ × V) →L[ℝ] G) :=
    fderiv ℝ (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) with hP
  have hA_cd : ContDiffAt ℝ 1 (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) :=
    hΦ.fderiv_right (m := 1) (by norm_num)
  have hA_diff : DifferentiableAt ℝ (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) :=
    hA_cd.differentiableAt (by simp)
  have hA_has : HasFDerivAt (fun p : ℝ × V => fderiv ℝ Φ p) P (t₀, u₀) := by
    rw [hP]; exact hA_diff.hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ Φ (t₀, u₀) := hΦ.isSymmSndFDerivAt (by simp)
  have hsymm_eq : P (0, w) (1, 0) = P (1, 0) (0, w) := by
    have := hsymm.eq (0, w) (1, 0)
    simpa only [hP] using this
  -- First partial derivative in the `u`-direction, as a function of `t`.
  have hL : HasDerivAt (fun t : ℝ => (fderiv ℝ Φ (t, u₀)) (0, w)) (P (1, 0) (0, w)) t₀ := by
    have hφ : HasFDerivAt (fun t : ℝ => (t, u₀)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ u₀
    have h1' : HasFDerivAt (fun t : ℝ => fderiv ℝ Φ (t, u₀))
        (P.comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ := hA_has.comp t₀ hφ
    have h2 := (ContinuousLinearMap.apply ℝ G (0, w)).hasFDerivAt.comp t₀ h1'
    have h3 := h2.hasDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.apply_apply] using h3
  have hDev : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ Φ (t, u₀) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Tendsto (fun t : ℝ => (t, u₀)) (𝓝 t₀) (𝓝 (t₀, u₀)) :=
      continuousAt_id.prodMk continuousAt_const
    exact hφtend.eventually hDeev
  have hEv : (fun t : ℝ => fderiv ℝ (fun u : V => Φ (t, u)) u₀ w)
      =ᶠ[𝓝 t₀] (fun t : ℝ => (fderiv ℝ Φ (t, u₀)) (0, w)) := by
    filter_upwards [hDev] with t ht
    have hψ : HasFDerivAt (fun u : V => (t, u)) (ContinuousLinearMap.inr ℝ ℝ V) u₀ :=
      hasFDerivAt_prodMk_right (𝕜 := ℝ) t u₀
    have h := (ht.hasFDerivAt.comp u₀ hψ).fderiv
    simp only [Function.comp_def] at h
    rw [h]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hLHS : HasDerivAt (fun t : ℝ => fderiv ℝ (fun u : V => Φ (t, u)) u₀ w)
      (P (1, 0) (0, w)) t₀ := hL.congr_of_eventuallyEq hEv
  -- Second partial derivative in the `t`-direction, as a function of `u`.
  have hDev' : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ Φ (t₀, u) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Tendsto (fun u : V => (t₀, u)) (𝓝 u₀) (𝓝 (t₀, u₀)) :=
      continuousAt_const.prodMk continuousAt_id
    exact hφtend.eventually hDeev
  have hEv' : (fun u : V => deriv (fun t : ℝ => Φ (t, u)) t₀)
      =ᶠ[𝓝 u₀] (fun u : V => (fderiv ℝ Φ (t₀, u)) (1, 0)) := by
    filter_upwards [hDev'] with u hu
    have hφ : HasFDerivAt (fun t : ℝ => (t, u)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) t₀ u
    have h := (hu.hasFDerivAt.comp t₀ hφ).hasDerivAt
    have h' := h.deriv
    simp only [Function.comp_def] at h'
    rw [h']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hR : HasFDerivAt (fun u : V => (fderiv ℝ Φ (t₀, u)) (1, 0))
      ((ContinuousLinearMap.apply ℝ G (1, 0)).comp
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V))) u₀ := by
    have hψ : HasFDerivAt (fun u : V => (t₀, u)) (ContinuousLinearMap.inr ℝ ℝ V) u₀ :=
      hasFDerivAt_prodMk_right (𝕜 := ℝ) t₀ u₀
    have h1' : HasFDerivAt (fun u : V => fderiv ℝ Φ (t₀, u))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) u₀ := hA_has.comp u₀ hψ
    have h2 := (ContinuousLinearMap.apply ℝ G (1, 0)).hasFDerivAt.comp u₀ h1'
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2
  have hRval : fderiv ℝ (fun u : V => deriv (fun t : ℝ => Φ (t, u)) t₀) u₀ w
      = P (0, w) (1, 0) := by
    rw [hEv'.fderiv_eq, hR.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply]
  rw [hRval, hsymm_eq]
  exact hLHS

end Work.Diff.T
