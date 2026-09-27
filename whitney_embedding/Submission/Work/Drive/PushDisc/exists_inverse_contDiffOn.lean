import Mathlib

namespace Work.Drive.PushDisc

open Set Filter Function
open scoped Topology

/-- If `F : ℝ → ℝ` is smooth and `deriv F > 0` on `[a, b]`, then `F` has a smooth inverse
`σ` on `(F a, F b)`: `σ (F x) = x` for `x ∈ [a, b]`, `σ` is `C^∞` on `(F a, F b)`, and
`deriv σ y = (deriv F (σ y))⁻¹` for `y ∈ (F a, F b)`. -/
theorem exists_inverse_contDiffOn {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < deriv F x) :
    ∃ σ : ℝ → ℝ,
      (∀ x ∈ Set.Icc a b, σ (F x) = x) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ (Set.Ioo (F a) (F b)) ∧
      (∀ y ∈ Set.Ioo (F a) (F b),
        σ y ∈ Set.Ioo a b ∧ deriv σ y = (deriv F (σ y))⁻¹) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- `F` is strictly monotone on `[a, b]`, hence injective there.
  have hmono : StrictMonoOn F (Set.Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hF.continuous.continuousOn (by
      intro x hx
      rw [interior_Icc] at hx
      exact hpos x (Set.Ioo_subset_Icc_self hx))
  have hinj : Set.InjOn F (Set.Icc a b) := hmono.injOn
  -- the image covers `(F a, F b)` by the intermediate value theorem
  have himage : Set.Icc (F a) (F b) ⊆ F '' Set.Icc a b :=
    intermediate_value_Icc hab.le hF.continuous.continuousOn
  -- the candidate inverse
  let σ : ℝ → ℝ := Function.invFunOn F (Set.Icc a b)
  have hpre : ∀ y ∈ Set.Ioo (F a) (F b), σ y ∈ Set.Icc a b ∧ F (σ y) = y :=
    fun y hy => Function.invFunOn_pos (himage ⟨hy.1.le, hy.2.le⟩)
  have hpreIoo : ∀ y ∈ Set.Ioo (F a) (F b), σ y ∈ Set.Ioo a b := by
    intro y hy
    obtain ⟨hmem, hFy⟩ := hpre y hy
    refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
    · intro h
      rw [← h] at hFy
      exact absurd hFy (ne_of_lt hy.1)
    · intro h
      rw [h] at hFy
      exact absurd hFy (ne_of_gt hy.2)
  -- `σ` is a left inverse of `F` near every point of `(F a, F b)`
  have hleft : ∀ y ∈ Set.Ioo (F a) (F b), ∀ᶠ x' in 𝓝 (σ y), σ (F x') = x' := by
    intro y hy
    have hσIoo := hpreIoo y hy
    filter_upwards [Ioo_mem_nhds hσIoo.1 hσIoo.2] with x' hx'
    obtain ⟨hmem, hFx⟩ := Function.invFunOn_pos (f := F) (s := Set.Icc a b) (b := F x')
      ⟨x', Set.Ioo_subset_Icc_self hx', rfl⟩
    exact hinj hmem (Set.Ioo_subset_Icc_self hx') hFx
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- `σ ∘ F = id` on `[a, b]`
    intro x hx
    obtain ⟨hmem, hFx⟩ := Function.invFunOn_pos (f := F) (s := Set.Icc a b) (b := F x)
      ⟨x, hx, rfl⟩
    exact hinj hmem hx hFx
  · -- smoothness of `σ` on `(F a, F b)` by the inverse function theorem
    intro y hy
    rw [contDiffWithinAt_iff_contDiffAt (Ioo_mem_nhds hy.1 hy.2)]
    obtain ⟨hσmem, hFσ⟩ := hpre y hy
    have hne : deriv F (σ y) ≠ 0 := (hpos (σ y) hσmem).ne'
    have hsd : HasStrictDerivAt F (deriv F (σ y)) (σ y) := hF.hasStrictDerivAt hn
    let f' : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv F (σ y)) hne)
    have hfd : HasFDerivAt F (f' : ℝ →L[ℝ] ℝ) (σ y) :=
      (hsd.hasStrictFDerivAt_equiv hne).hasFDerivAt
    have h2 : HasStrictFDerivAt.localInverse F f' (σ y)
        ((hF.contDiffAt (x := σ y)).hasStrictFDerivAt' hfd hn) =
        (hF.contDiffAt (x := σ y)).localInverse hfd hn := rfl
    have huniq : σ =ᶠ[𝓝 y] (hF.contDiffAt (x := σ y)).localInverse hfd hn := by
      have h := ((hF.contDiffAt (x := σ y)).hasStrictFDerivAt' hfd hn).localInverse_unique
        (g := σ) (hleft y hy)
      rw [hFσ] at h
      rwa [h2] at h
    have hcont' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((hF.contDiffAt (x := σ y)).localInverse hfd hn) y := by
      simpa only [hFσ] using (hF.contDiffAt (x := σ y)).to_localInverse hfd hn
    exact hcont'.congr_of_eventuallyEq huniq
  · -- the derivative of `σ`
    intro y hy
    obtain ⟨hσmem, hFσ⟩ := hpre y hy
    have hne : deriv F (σ y) ≠ 0 := (hpos (σ y) hσmem).ne'
    have hsd : HasStrictDerivAt F (deriv F (σ y)) (σ y) := hF.hasStrictDerivAt hn
    have hderiv : HasStrictDerivAt σ (deriv F (σ y))⁻¹ (F (σ y)) :=
      hsd.to_local_left_inverse hne (hleft y hy)
    rw [hFσ] at hderiv
    exact ⟨hpreIoo y hy, hderiv.hasDerivAt.deriv⟩

end Work.Drive.PushDisc
