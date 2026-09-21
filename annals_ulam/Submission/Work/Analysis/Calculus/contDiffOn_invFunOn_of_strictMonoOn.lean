import Mathlib

namespace Work.Analysis.Calculus

open Set Filter
open scoped Topology

/-- If `y` is `C^∞` on the open interval `(a,b)`, strictly monotone there, maps `(a,b)` onto
itself and has nonvanishing derivative, then its inverse on `(a,b)` is again `C^∞` and strictly
monotone there. -/
theorem contDiffOn_invFunOn_of_strictMonoOn {a b : ℝ} (hab : a < b) {y : ℝ → ℝ}
    (hy : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y (Set.Ioo a b))
    (hmono : StrictMonoOn y (Set.Ioo a b))
    (hsurj : Set.SurjOn y (Set.Ioo a b) (Set.Ioo a b))
    (hder : ∀ t ∈ Set.Ioo a b, deriv y t ≠ 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.invFunOn y (Set.Ioo a b)) (Set.Ioo a b) ∧
      StrictMonoOn (Function.invFunOn y (Set.Ioo a b)) (Set.Ioo a b) := by
  have hsub : a < b := hab
  set s := Set.Ioo a b with hs_def
  set n : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞) with hn_def
  have hne : n ≠ 0 := fun h => ENat.top_ne_zero (WithTop.coe_eq_coe.mp h)
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_Ioo
  have hinj : InjOn y s := hmono.injOn
  -- At each point of `s`, the global inverse `invFunOn y s` agrees with the local inverse
  -- delivered by the inverse function theorem, hence is `C^∞` there.
  have hkey : ∀ x ∈ s, ContDiffAt ℝ n (Function.invFunOn y s) x := by
    intro x hx
    obtain ⟨t, ht, hyt⟩ := hsurj hx
    have hct : ContDiffAt ℝ n y t := hy.contDiffAt (hsopen.mem_nhds ht)
    have hdiff : DifferentiableAt ℝ y t := hct.differentiableAt hne
    have hderiv : HasDerivAt y (deriv y t) t := hdiff.hasDerivAt
    have hc : deriv y t ≠ 0 := hder t ht
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv y t) hc)
    have hfe : HasFDerivAt y (e : ℝ →L[ℝ] ℝ) t := hderiv.hasFDerivAt_equiv hc
    have hsd : HasStrictFDerivAt y (e : ℝ →L[ℝ] ℝ) t := hct.hasStrictFDerivAt' hfe hne
    have hli : ContDiffAt ℝ n (hct.localInverse hfe hne) (y t) := hct.to_localInverse hfe hne
    rw [hyt] at hli
    have hright : ∀ᶠ z in 𝓝 x, y (hsd.localInverse y e t z) = z := by
      have h := hsd.eventually_right_inverse
      rwa [hyt] at h
    have hcont : ContinuousAt (hsd.localInverse y e t) x := by
      have h := hsd.localInverse_continuousAt
      rwa [hyt] at h
    have hli_at : hsd.localInverse y e t x = t := by
      have h := hsd.localInverse_apply_image
      rwa [hyt] at h
    have hmem : ∀ᶠ z in 𝓝 x, hsd.localInverse y e t z ∈ s :=
      hcont.tendsto.eventually (by rw [hli_at]; exact hsopen.mem_nhds ht)
    have hgerm : Function.invFunOn y s =ᶠ[𝓝 x] (hsd.localInverse y e t) := by
      filter_upwards [hmem, hright] with z hz_mem hz_y
      have hzex : ∃ w ∈ s, y w = z := ⟨hsd.localInverse y e t z, hz_mem, hz_y⟩
      exact hinj (Function.invFunOn_mem hzex) hz_mem (by rw [Function.invFunOn_eq hzex, hz_y])
    have hli' : ContDiffAt ℝ n (hsd.localInverse y e t) x := hli
    exact hli'.congr_of_eventuallyEq hgerm
  refine ⟨fun x hx => (hkey x hx).contDiffWithinAt, ?_⟩
  -- strict monotonicity of the inverse follows from strict monotonicity of `y`
  intro x1 hx1 x2 hx2 hlt
  obtain ⟨t1, ht1, hy1⟩ := hsurj hx1
  obtain ⟨t2, ht2, hy2⟩ := hsurj hx2
  have h1 : y (Function.invFunOn y s x1) = x1 := Function.invFunOn_eq ⟨t1, ht1, hy1⟩
  have h2 : y (Function.invFunOn y s x2) = x2 := Function.invFunOn_eq ⟨t2, ht2, hy2⟩
  have hm1 : Function.invFunOn y s x1 ∈ s := Function.invFunOn_mem ⟨t1, ht1, hy1⟩
  have hm2 : Function.invFunOn y s x2 ∈ s := Function.invFunOn_mem ⟨t2, ht2, hy2⟩
  have : y (Function.invFunOn y s x1) < y (Function.invFunOn y s x2) := by rw [h1, h2]; exact hlt
  exact (hmono.lt_iff_lt hm1 hm2).mp this

end Work.Analysis.Calculus
