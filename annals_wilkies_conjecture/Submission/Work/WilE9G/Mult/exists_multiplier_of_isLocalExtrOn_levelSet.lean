import Mathlib

namespace Work.WilE9G.Mult

/-- Lagrange multipliers in the form needed for the Pfaffian transversality argument.

If `φ` has a local extremum on the level set `{y | ∀ i, f i y = f i z}` at `z`, all the `f i`
and `φ` are strictly differentiable at `z`, and the joint derivative `v ↦ (fun i => f' i v)`
maps `E` onto `ι → ℝ` (i.e. the constraint gradients are independent), then `φ'` is a genuine
linear combination `∑ i, c i * f' i` of the constraint differentials. -/
theorem exists_multiplier_of_isLocalExtrOn_levelSet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι] {φ : E → ℝ} {φ' : E →L[ℝ] ℝ}
    {f : ι → E → ℝ} {f' : ι → E →L[ℝ] ℝ} {z : E}
    (hextr : IsLocalExtrOn φ {y | ∀ i, f i y = f i z} z)
    (hf : ∀ i, HasStrictFDerivAt (f i) (f' i) z)
    (hφ : HasStrictFDerivAt φ φ' z)
    (hsurj : Function.Surjective (fun v : E => fun i : ι => f' i v)) :
    ∃ c : ι → ℝ, ∀ v : E, φ' v = ∑ i, c i * f' i v := by
  classical
  -- Mathlib's Lagrange multiplier theorem gives multipliers `Λ`, `Λ₀`, not both zero.
  obtain ⟨Λ, Λ₀, hΛne, hΛeq⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt hf hφ
  -- `hΛeq : ∑ i, Λ i • f' i + Λ₀ • φ' = 0`.
  -- We first show that surjectivity of `v ↦ (f' i v)` forces `Λ₀ ≠ 0`.
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    have hsumCLM : (∑ i, Λ i • f' i) = 0 := by
      simpa [h0] using hΛeq
    have hsum : ∀ v : E, ∑ i, Λ i * f' i v = 0 := by
      intro v
      have h := DFunLike.congr_fun hsumCLM v
      simpa only [sum_apply, smul_apply, smul_eq_mul, zero_apply] using h
    -- hence `Λ` vanishes against every vector of `ι → ℝ`
    have horth : ∀ w : ι → ℝ, ∑ i, Λ i * w i = 0 := by
      intro w
      obtain ⟨v, hv⟩ := hsurj w
      have hv' : ∀ i, f' i v = w i := fun i => congrFun hv i
      have h := hsum v
      rwa [show (∑ i, Λ i * f' i v) = ∑ i, Λ i * w i from
        Finset.sum_congr rfl (fun i _ => by rw [hv' i])] at h
    have hΛzero : Λ = 0 := by
      funext j
      have h := horth (Pi.single j (1 : ℝ))
      simpa [Pi.single_apply] using h
    exact hΛne (by simp [hΛzero, h0])
  -- From `∑ i, Λ i * f' i v + Λ₀ * φ' v = 0` we read off `φ' = ∑ i, (-Λ i / Λ₀) * f' i`.
  refine ⟨fun i => -(Λ i / Λ₀), fun v => ?_⟩
  have h := DFunLike.congr_fun hΛeq v
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at h
  have hphi : φ' v = -((∑ i, Λ i * f' i v)) / Λ₀ := by
    rw [eq_div_iff hΛ₀, mul_comm (φ' v) Λ₀]
    linarith [h]
  have hsum_eq : (∑ i, -(Λ i / Λ₀) * f' i v) = -((∑ i, Λ i * f' i v)) / Λ₀ := by
    have h1 : ∀ i, -(Λ i / Λ₀) * f' i v = -(1 / Λ₀) * (Λ i * f' i v) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum]
    ring
  rw [hphi, hsum_eq]

end Work.WilE9G.Mult
