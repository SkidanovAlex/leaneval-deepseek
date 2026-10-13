import Mathlib

namespace Work.WilE2

open ContinuousLinearMap

/-- If `D : (Fin m → ℝ) →L[ℝ] (Fin (m-1) → ℝ)` is surjective and `e ≠ 0` lies in its kernel,
then the kernel is exactly the line spanned by `e`, and one can split
`(Fin m → ℝ)` as `ℝ • e ⊕ (Fin (m-1) → ℝ)` via a section of `D`. -/
theorem exists_linearEquiv_fst_eq_of_ker {m : ℕ} (D : (Fin m → ℝ) →L[ℝ] (Fin (m-1) → ℝ))
    (e : Fin m → ℝ) (hD : D.range = ⊤) (he : D e = 0) (he0 : e ≠ 0) :
    ∃ M : (ℝ × (Fin (m-1) → ℝ)) ≃L[ℝ] (Fin m → ℝ),
      M (1, 0) = e ∧ (∀ y, D (M (0, y)) = y) := by
  classical
  -- `m ≠ 0` because `e ≠ 0`
  have hm : 0 < m := by
    by_contra h
    rw [not_lt] at h
    have hm0 : m = 0 := Nat.le_zero.mp h
    subst hm0
    exact he0 (Subsingleton.elim e 0)
  -- a continuous linear section of `D`
  obtain ⟨g, hg⟩ := D.exists_rightInverse_of_surjective hD
  have hg' : ∀ y, D (g y) = y := fun y => by
    have h := DFunLike.congr_fun hg y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    exact h
  -- the candidate linear map `(x, y) ↦ x • e + g y`
  let φ : ℝ →ₗ[ℝ] (Fin m → ℝ) := LinearMap.toSpanSingleton ℝ (Fin m → ℝ) e
  let M₀ : ℝ × (Fin (m-1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) := φ.coprod g.toLinearMap
  have hM0 : ∀ v : ℝ × (Fin (m-1) → ℝ), M₀ v = v.1 • e + g v.2 := by
    intro v; simp [M₀, φ]
  have hDM : ∀ v, D (M₀ v) = v.2 := by
    intro v; rw [hM0 v]; simp [he, hg']
  -- injectivity
  have hinj : Function.Injective M₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h2 : v.2 = 0 := by
      have h := hDM v
      rw [hv, map_zero] at h
      exact h.symm
    have h1 : v.1 = 0 := by
      have hthis : v.1 • e = 0 := by
        have h := hv
        rw [hM0 v] at h
        simpa [h2] using h
      exact (smul_eq_zero.mp hthis).resolve_right he0
    exact Prod.ext h1 h2
  -- dimension count: `dim (ℝ × Fin (m-1) → ℝ) = dim (Fin m → ℝ)`
  have hrank : Module.finrank ℝ (ℝ × (Fin (m-1) → ℝ)) = Module.finrank ℝ (Fin m → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  refine ⟨(M₀.linearEquivOfInjective hinj hrank).toContinuousLinearEquiv, ?_, ?_⟩
  · simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearMap.linearEquivOfInjective_apply,
      hM0]
    simp
  · intro y
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearMap.linearEquivOfInjective_apply,
      hM0]
    simp [hg']

end Work.WilE2
