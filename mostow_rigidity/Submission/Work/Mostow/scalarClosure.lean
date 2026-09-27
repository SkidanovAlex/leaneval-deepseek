import Mathlib

namespace Work.Mostow

/-- If each member of a finite generating list `F` of an abelian family `𝓖` of linear isometries
acts on a subspace `P`, carrying a complex structure `J`, as a complex scalar `a + b J`, and `J`
commutes with every generator, then every element of `𝓖` acts on `P` as a complex scalar. -/
theorem scalarClosure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (𝓖 : Subgroup (V ≃ₗᵢ[ℝ] V)) {ι : Type*} [Fintype ι] (F : ι → V ≃ₗᵢ[ℝ] V) (hF : ∀ i, F i ∈ 𝓖)
    (hgen : 𝓖 ≤ Subgroup.closure (Set.range F)) (P : Submodule ℝ V) (J : V →ₗ[ℝ] V)
    (hJ2 : ∀ x ∈ P, J (J x) = -x) (hJmem : ∀ x ∈ P, J x ∈ P)
    (hJc : ∀ i : ι, ∀ x : V, J ((F i) x) = (F i) (J x))
    (hgenScal : ∀ i : ι, ∃ a b : ℝ, ∀ x ∈ P, (F i) x = a • x + b • (J x)) :
    ∀ T ∈ 𝓖, ∃ a b : ℝ, ∀ x ∈ P, T x = a • x + b • (J x) := by
  -- The set of linear isometries acting on `P` as a complex scalar `a + bJ` is a subgroup.
  let S : Subgroup (V ≃ₗᵢ[ℝ] V) :=
    { carrier := {g | ∃ a b : ℝ, ∀ x ∈ P, g x = a • x + b • (J x)}
      one_mem' := by
        refine ⟨1, 0, ?_⟩
        intro x _
        simp
      mul_mem' := by
        intro g h hg hh
        obtain ⟨a, b, hab⟩ := hg
        obtain ⟨c, d, hcd⟩ := hh
        -- `(a + bJ) ∘ (c + dJ) = (ca - db) + (cb + da)J` on `P`
        refine ⟨c * a - d * b, c * b + d * a, ?_⟩
        intro x hx
        have hxJ : J x ∈ P := hJmem x hx
        have h1 : (g * h) x = g (h x) := by simp
        rw [h1, hcd x hx, LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_smul,
            LinearIsometryEquiv.map_smul, hab x hx, hab (J x) hxJ, hJ2 x hx]
        module
      inv_mem' := by
        intro g hg
        obtain ⟨a, b, hab⟩ := hg
        by_cases h : a ^ 2 + b ^ 2 = 0
        · -- then `g` vanishes on `P`, forcing `P = ⊥`
          have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
          have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
          refine ⟨0, 0, ?_⟩
          intro x hx
          have hx0 : x = 0 := by
            have hgx : g x = 0 := by rw [hab x hx, ha, hb]; simp
            exact g.injective (by rw [hgx, map_zero])
          simp [hx0]
        · -- otherwise `a + bJ` is invertible on `P` with the usual complex inverse
          refine ⟨(a ^ 2 + b ^ 2)⁻¹ * a, -((a ^ 2 + b ^ 2)⁻¹ * b), ?_⟩
          intro x hx
          have hxJ : J x ∈ P := hJmem x hx
          have hgJx : g (J x) = a • (J x) - b • x := by
            rw [hab (J x) hxJ, hJ2 x hx]
            module
          have hinner : a • (a • x + b • (J x)) - b • (a • (J x) - b • x)
              = (a ^ 2 + b ^ 2) • x := by
            module
          have hgZ : g ((a ^ 2 + b ^ 2)⁻¹ • (a • x - b • (J x))) = x := by
            rw [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_sub,
                LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_smul, hab x hx, hgJx,
                hinner, smul_smul, inv_mul_cancel₀ h, one_smul]
          have hz : (g⁻¹ : V ≃ₗᵢ[ℝ] V) x = (a ^ 2 + b ^ 2)⁻¹ • (a • x - b • (J x)) := by
            rw [show (g⁻¹ : V ≃ₗᵢ[ℝ] V) x = g.symm x from rfl]
            exact (LinearIsometryEquiv.symm_apply_eq g).mpr hgZ.symm
          rw [hz]
          module }
  have hFS : Set.range F ⊆ (S : Set (V ≃ₗᵢ[ℝ] V)) := by
    rintro g ⟨i, rfl⟩
    exact hgenScal i
  have hcl : Subgroup.closure (Set.range F) ≤ S := (Subgroup.closure_le S).mpr hFS
  intro T hT
  exact hcl (hgen hT)

end Work.Mostow
