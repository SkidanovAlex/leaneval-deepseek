import Mathlib

namespace Work.Drive.Final

/-- Any nonzero continuous linear functional `F` on `ℝ × ℝ` can be transformed into
the first coordinate by a linear isomorphism: there is a bijective open linear map
`L` with `F (L a) = a.1` for all `a`. -/
theorem exists_linear_normalising (F : (ℝ × ℝ) →L[ℝ] ℝ) (hF : F ≠ 0) :
    ∃ L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), Function.Bijective L ∧
      (∀ a : ℝ × ℝ, F (L a) = a.1) ∧ IsOpenMap L := by
  -- The value of `F` in coordinates.
  have Fpair : ∀ a : ℝ × ℝ, F a = a.1 * F (1, 0) + a.2 * F (0, 1) := by
    intro a
    have h : a = (a.1 : ℝ) • ((1, 0) : ℝ × ℝ) + a.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc F a = F ((a.1 : ℝ) • ((1, 0) : ℝ × ℝ) + a.2 • ((0, 1) : ℝ × ℝ)) := congrArg F h
      _ = a.1 * F (1, 0) + a.2 * F (0, 1) := by simp only [map_add, map_smul, smul_eq_mul]
  -- `F` is nonzero, so some vector has nonzero value.
  have hx : ∃ x : ℝ × ℝ, F x ≠ 0 := by
    by_contra h
    exact hF (ContinuousLinearMap.ext (fun x => by
      by_contra hx
      exact h ⟨x, hx⟩))
  obtain ⟨x, hx⟩ := hx
  -- A vector `v` with `F v = 1`.
  obtain ⟨v, hFv⟩ : ∃ v : ℝ × ℝ, F v = 1 :=
    ⟨(F x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  -- A nonzero vector `u` in the kernel of `F`.
  obtain ⟨u, hu_mem, hu_ne⟩ : ∃ u : ℝ × ℝ, F u = 0 ∧ u ≠ 0 := by
    refine ⟨(F (0, 1), -(F (1, 0))), ?_, ?_⟩
    · rw [Fpair]; ring
    · intro hu
      refine hF (ContinuousLinearMap.ext (fun a => ?_))
      rw [Fpair a, zero_apply]
      have h1 : F (1, 0) = 0 := by
        have := congrArg Prod.snd hu
        simpa using this
      have h2 : F (0, 1) = 0 := by
        have := congrArg Prod.fst hu
        simpa using this
      rw [h1, h2]; ring
  -- The linear map `a ↦ a.1 • v + a.2 • u`.
  let f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight v + (LinearMap.snd ℝ ℝ ℝ).smulRight u
  have f_apply : ∀ a : ℝ × ℝ, f a = a.1 • v + a.2 • u := by
    intro a
    simp only [f, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
  have hFf : ∀ a : ℝ × ℝ, F (f a) = a.1 := by
    intro a
    rw [f_apply a, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hFv, hu_mem]
    ring
  -- `f` is injective.
  have hker : ∀ a : ℝ × ℝ, f a = 0 → a = 0 := by
    intro a ha
    have h1 : a.1 = 0 := by
      have h := hFf a
      rw [ha, map_zero] at h
      exact h.symm
    have h2 : a.2 = 0 := by
      have h : a.2 • u = 0 := by
        have h' := ha
        rw [f_apply a, h1, zero_smul, zero_add] at h'
        exact h'
      rcases (smul_eq_zero.mp h) with h' | h'
      · exact h'
      · exact absurd h' hu_ne
    ext <;> simp [h1, h2]
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have := hker (a - b) h
    exact sub_eq_zero.mp this
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, LinearMap.injective_iff_surjective.mp hf_inj⟩
  -- Package `f` as a continuous linear equivalence.
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofBijective f hf_bij
  let L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := e.toContinuousLinearEquiv
  have hL : ∀ a : ℝ × ℝ, (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) a = f a := by
    intro a
    have h1 : (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) a = e a := rfl
    rw [h1, LinearEquiv.ofBijective_apply]
  refine ⟨L, L.bijective, ?_, L.isOpenMap⟩
  intro a
  rw [hL a]
  exact hFf a

end Work.Drive.Final
