import Mathlib

namespace Work.ZeroFreeTables

/-- Derivative of the auxiliary function
`F y = y * (1 + 2 cos²y) - 3 sin y cos y`. -/
private lemma deriv_aux (x : ℝ) :
    deriv (fun y : ℝ => y * (1 + 2 * Real.cos y ^ 2) - 3 * Real.sin y * Real.cos y) x
      = 4 * Real.sin x * (Real.sin x - x * Real.cos x) := by
  change deriv ((fun y : ℝ => y * (1 + 2 * Real.cos y ^ 2)) -
      fun y : ℝ => 3 * Real.sin y * Real.cos y) x = _
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  have h1 : deriv (fun y : ℝ => y * (1 + 2 * Real.cos y ^ 2)) x
      = 1 + 2 * Real.cos x ^ 2 - 4 * x * Real.sin x * Real.cos x := by
    change deriv ((fun y : ℝ => y) * fun y : ℝ => 1 + 2 * Real.cos y ^ 2) x = _
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    have h : deriv (fun y : ℝ => 1 + 2 * Real.cos y ^ 2) x = -4 * Real.sin x * Real.cos x := by
      simp [Real.deriv_cos]; ring
    rw [h, deriv_id'']
    ring
  have h2 : deriv (fun y : ℝ => 3 * Real.sin y * Real.cos y) x
      = 3 * (Real.cos x ^ 2 - Real.sin x ^ 2) := by
    simp [Real.deriv_cos]; ring
  rw [h1, h2]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem tf71_trig_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    0 < θ * Real.tan θ + 3 * θ * (Real.tan θ)⁻¹ - 3 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθπ : θ < Real.pi := by linarith
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  -- auxiliary function: `F θ = sin θ * cos θ * (θ tan θ + 3 θ cot θ - 3)`
  set F : ℝ → ℝ := fun y => y * (1 + 2 * Real.cos y ^ 2) - 3 * Real.sin y * Real.cos y with hF
  have hF0 : F 0 = 0 := by simp [hF]
  -- `F` is strictly increasing on `[0, θ]` since `F' = 4 sin x (sin x - x cos x) > 0`
  have hderiv : ∀ x ∈ interior (Set.Icc (0:ℝ) θ), 0 < deriv F x := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hxθ⟩ := hx
    have hxπ2 : x < Real.pi / 2 := lt_trans hxθ hθ1
    have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [hπ])
    have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxπ2⟩
    have htx : x < Real.tan x := Real.lt_tan hx0 hxπ2
    have hxcs : x * Real.cos x < Real.sin x := by
      have h := mul_lt_mul_of_pos_right htx hcx
      rw [Real.tan_eq_sin_div_cos] at h
      rwa [div_mul_cancel₀ _ (ne_of_gt hcx)] at h
    have hd : deriv F x = 4 * Real.sin x * (Real.sin x - x * Real.cos x) := by
      rw [hF]; exact deriv_aux x
    rw [hd]
    have : 0 < Real.sin x - x * Real.cos x := by linarith
    exact mul_pos (mul_pos (by norm_num) hsx) this
  have hmono : StrictMonoOn F (Set.Icc 0 θ) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 θ) (by rw [hF]; fun_prop) hderiv
  have hθmem : θ ∈ Set.Icc (0:ℝ) θ := ⟨le_of_lt hθ0, le_refl θ⟩
  have h0mem : (0:ℝ) ∈ Set.Icc 0 θ := ⟨le_refl 0, le_of_lt hθ0⟩
  have hFpos : 0 < F θ := by
    have := hmono h0mem hθmem hθ0
    rwa [hF0] at this
  -- rewrite the target as `F θ / (sin θ * cos θ)`
  have hsc_pos : 0 < Real.sin θ * Real.cos θ := mul_pos hsin hcos
  have key : F θ = Real.sin θ * Real.cos θ *
      (θ * Real.tan θ + 3 * θ * (Real.tan θ)⁻¹ - 3) := by
    rw [hF, Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [key] at hFpos
  exact pos_of_mul_pos_right hFpos (le_of_lt hsc_pos)

end Work.ZeroFreeTables
