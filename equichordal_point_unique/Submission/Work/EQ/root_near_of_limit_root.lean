import Mathlib

namespace Work.EQ

open Filter _root_.Topology

/-- **A root persists near a limit root.**  For `κ ≠ 0`, `k > 0`, a root `ζ₀` of the equation at
the centre `u₁`, and `ε > 0`, every parameter `u` close to `u₁` has a root within `ε` of `ζ₀`. -/
theorem root_near_of_limit_root {κ u₀ u₁ : ℂ} (hκ : κ ≠ 0) {k : ℕ} (hk : 0 < k)
    {ζ₀ : ℂ} (hζ₀ : u₀ + κ * ζ₀ ^ k = u₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℂ, dist u u₁ < ρ →
      ∃ ζ : ℂ, u₀ + κ * ζ ^ k = u ∧ dist ζ ζ₀ < ε := by
  -- The map `ζ ↦ u₀ + κ * ζ ^ k` is locally surjective at the point `ζ₀`.
  by_cases hζ : ζ₀ = 0
  · -- `ζ₀ = 0`: the equation at the centre is `u₀ + κ * 0 ^ k = u₁`, so `u₁ = u₀`; a root for `u`
    -- near `u₀` is any `k`-th root of `(u - u₀) / κ`, and the modulus bound is a consequence of
    -- `‖ζ ^ k‖ = ‖ζ‖ ^ k`.
    subst hζ
    have hu₁ : u₁ = u₀ := by
      rw [← hζ₀, zero_pow hk.ne', mul_zero, add_zero]
    refine ⟨‖κ‖ * ε ^ k, mul_pos (norm_pos_iff.mpr hκ) (pow_pos hε k), ?_⟩
    intro u hu
    rw [hu₁] at hu
    have hw : ‖(u - u₀) / κ‖ < ε ^ k := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hκ)]
      have hh : ‖u - u₀‖ < ‖κ‖ * ε ^ k := by
        rw [← dist_eq_norm]; exact hu
      linarith [hh]
    obtain ⟨ζ, hζk⟩ : ∃ ζ : ℂ, ζ ^ k = (u - u₀) / κ := IsAlgClosed.exists_pow_nat_eq _ hk
    refine ⟨ζ, ?_, ?_⟩
    · rw [hζk]
      field_simp
      ring
    · rw [dist_zero_right]
      have hnk : ‖ζ‖ ^ k = ‖(u - u₀) / κ‖ := by rw [← norm_pow, hζk]
      exact lt_of_pow_lt_pow_left₀ k (le_of_lt hε) (by rw [hnk]; exact hw)
  · -- `ζ₀ ≠ 0`: the derivative `κ * k * ζ₀ ^ (k - 1)` does not vanish, so the (strict) inverse
    -- function theorem makes the map a local homeomorphism, and the image of a small ball around
    -- `ζ₀` is a neighbourhood of `u₁`.
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have hderiv : κ * ((k : ℂ) * ζ₀ ^ (k - 1)) ≠ 0 :=
      mul_ne_zero hκ (mul_ne_zero hk' (pow_ne_zero _ hζ))
    let f : ℂ → ℂ := fun ζ => u₀ + κ * ζ ^ k
    have hp : HasStrictDerivAt (fun ζ : ℂ => ζ ^ k) ((k : ℂ) * ζ₀ ^ (k - 1)) ζ₀ := by
      simpa using hasStrictDerivAt_pow k ζ₀
    have h1 : HasStrictDerivAt (fun ζ : ℂ => κ * ζ ^ k) (κ * ((k : ℂ) * ζ₀ ^ (k - 1))) ζ₀ :=
      hp.const_mul κ
    have h2 : HasStrictDerivAt f (κ * ((k : ℂ) * ζ₀ ^ (k - 1))) ζ₀ := h1.const_add u₀
    have hfeq : f ζ₀ = u₁ := by simp only [f]; exact hζ₀
    have hmap : Filter.map f (𝓝 ζ₀) = 𝓝 u₁ := by
      have := h2.map_nhds_eq hderiv
      rw [this, hfeq]
    have hS : Metric.ball ζ₀ ε ∈ 𝓝 ζ₀ := Metric.ball_mem_nhds ζ₀ hε
    have hpre : f ⁻¹' (f '' Metric.ball ζ₀ ε) ∈ 𝓝 ζ₀ :=
      Filter.mem_of_superset hS (fun x hx => ⟨x, hx, rfl⟩)
    have himage : f '' Metric.ball ζ₀ ε ∈ 𝓝 u₁ := by
      rw [← hmap]; exact Filter.mem_map.mpr hpre
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp himage
    exact ⟨ρ, hρ, fun u hu => by
      obtain ⟨ζ, hζmem, hζeq⟩ := hsub (Metric.mem_ball.mpr hu)
      exact ⟨ζ, by simpa only [f] using hζeq, Metric.mem_ball.mp hζmem⟩⟩

end Work.EQ
