import Mathlib

namespace Work.Mostow.gapA

/-- For `x ≥ 0` one has `sinh x ≤ x * cosh x`. -/
lemma sinh_le_mul_cosh (x : ℝ) (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hderiv : ∀ y ∈ interior (Set.Ici 0),
      HasDerivWithinAt (fun y : ℝ => y * Real.cosh y - Real.sinh y) (y * Real.sinh y)
        (interior (Set.Ici 0)) y := by
    intro y hy
    have h : HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
      have h1 : HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y)
          (1 * Real.cosh y + y * Real.sinh y - Real.cosh y) y :=
        ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
      convert h1 using 1
      ring
    exact h.hasDerivWithinAt
  have hmono : MonotoneOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (by fun_prop) hderiv (by
      intro y hy
      rw [interior_Ici] at hy
      exact mul_nonneg (le_of_lt hy) (Real.sinh_nonneg_iff.mpr (le_of_lt hy)))
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at h
  linarith

/-- For `x ≥ 0` and `D ≥ 1` one has `D * sinh x ≤ sinh (D * x)`. -/
lemma sinh_mul_le (x : ℝ) (hx : 0 ≤ x) (D : ℝ) (hD : 1 ≤ D) :
    D * Real.sinh x ≤ Real.sinh (D * x) := by
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh (t * x) - t * Real.sinh x) (Set.Ici 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun t => Real.cosh (t * x) * x - Real.sinh x) (by fun_prop) ?_ ?_
    · intro t ht
      have h : HasDerivAt (fun t : ℝ => Real.sinh (t * x) - t * Real.sinh x)
          (Real.cosh (t * x) * x - Real.sinh x) t := by
        have h1 : HasDerivAt (fun t : ℝ => Real.sinh (t * x)) (Real.cosh (t * x) * (1 * x)) t :=
          ((hasDerivAt_id t).mul_const x).sinh
        have h2 : HasDerivAt (fun t : ℝ => t * Real.sinh x) (1 * Real.sinh x) t :=
          (hasDerivAt_id t).mul_const (Real.sinh x)
        have h3 := h1.sub h2
        convert h3 using 1
        ring
      exact h.hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have htx_nonneg : 0 ≤ t * x := mul_nonneg (by linarith) hx
      have hcosh : Real.cosh x ≤ Real.cosh (t * x) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg hx, abs_of_nonneg htx_nonneg]
        nlinarith
      have hsc := sinh_le_mul_cosh x hx
      nlinarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hD) hD
  simp at h
  linarith

/-- Auxiliary form of the screw-motion inequality, for a general angle `φ ∈ [0, π]`. -/
lemma screw_aux (l φ D : ℝ) (hl : 0 < l) (hφ0 : 0 ≤ φ) (hφπ : φ ≤ Real.pi) (hD : 1 ≤ D) :
    D ^ 2 * (Real.cosh l - Real.cos φ) + Real.cos φ ≤ Real.cosh (2 * (l + φ) * D) := by
  have hsinh_l_nonneg : 0 ≤ Real.sinh l := Real.sinh_nonneg_iff.mpr (le_of_lt hl)
  have hsinh_φ_nonneg : 0 ≤ Real.sinh φ := Real.sinh_nonneg_iff.mpr hφ0
  have hlp_nonneg : 0 ≤ l + φ := by linarith
  have hsinh_lp_nonneg : 0 ≤ Real.sinh (l + φ) := Real.sinh_nonneg_iff.mpr hlp_nonneg
  have hsin_φ_half_nonneg : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsinh_half_nonneg : 0 ≤ Real.sinh (l / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  -- `sinh l + sinh φ ≤ sinh (l+φ)`
  have h2ab : Real.sinh l + Real.sinh φ ≤ Real.sinh (l + φ) := by
    rw [Real.sinh_add]
    have e1 : Real.sinh l ≤ Real.sinh l * Real.cosh φ :=
      le_mul_of_one_le_right hsinh_l_nonneg (Real.one_le_cosh φ)
    have e2 : Real.sinh φ ≤ Real.cosh l * Real.sinh φ :=
      le_mul_of_one_le_left hsinh_φ_nonneg (Real.one_le_cosh l)
    linarith
  have hsl : Real.sinh (l / 2) ≤ Real.sinh l := Real.sinh_le_sinh.mpr (by linarith)
  have hsφ : Real.sin (φ / 2) ≤ Real.sinh φ := by
    have h1 : Real.sin (φ / 2) ≤ φ / 2 := Real.sin_le (by linarith)
    have h2 : φ / 2 ≤ Real.sinh φ := by
      have := Real.self_le_sinh_iff.mpr hφ0
      linarith
    linarith
  have hAB : Real.sinh (l / 2) + Real.sin (φ / 2) ≤ Real.sinh (l + φ) := by linarith
  have hABnonneg : 0 ≤ Real.sinh (l / 2) + Real.sin (φ / 2) := by linarith
  -- (P2)
  have hstep1 : (Real.sinh (l / 2)) ^ 2 + (Real.sin (φ / 2)) ^ 2 ≤ (Real.sinh (l + φ)) ^ 2 := by
    have hsq : (Real.sinh (l / 2) + Real.sin (φ / 2)) ^ 2 ≤ (Real.sinh (l + φ)) ^ 2 :=
      pow_le_pow_left₀ hABnonneg hAB 2
    have h2AB : (Real.sinh (l / 2)) ^ 2 + (Real.sin (φ / 2)) ^ 2
        ≤ (Real.sinh (l / 2) + Real.sin (φ / 2)) ^ 2 := by
      nlinarith [mul_nonneg hsinh_half_nonneg hsin_φ_half_nonneg]
    linarith
  -- (P1)
  have hscale : D * Real.sinh (l + φ) ≤ Real.sinh (D * (l + φ)) :=
    sinh_mul_le (l + φ) hlp_nonneg D hD
  have hstep2 : D ^ 2 * (Real.sinh (l + φ)) ^ 2 ≤ (Real.sinh (D * (l + φ))) ^ 2 := by
    have hbase : 0 ≤ D * Real.sinh (l + φ) := mul_nonneg (by linarith) hsinh_lp_nonneg
    have hmm := mul_self_le_mul_self hbase hscale
    calc D ^ 2 * (Real.sinh (l + φ)) ^ 2 = (D * Real.sinh (l + φ)) ^ 2 := by ring
      _ ≤ (Real.sinh (D * (l + φ))) ^ 2 := by simpa [pow_two] using hmm
  have hmain : D ^ 2 * (Real.sinh (l / 2)) ^ 2 + (D ^ 2 - 1) * (Real.sin (φ / 2)) ^ 2
      ≤ (Real.sinh (D * (l + φ))) ^ 2 := by
    have hB2 : 0 ≤ (Real.sin (φ / 2)) ^ 2 := sq_nonneg _
    have hD2nonneg : 0 ≤ D ^ 2 := sq_nonneg _
    have hmult : D ^ 2 * ((Real.sinh (l / 2)) ^ 2 + (Real.sin (φ / 2)) ^ 2)
        ≤ D ^ 2 * (Real.sinh (l + φ)) ^ 2 := mul_le_mul_of_nonneg_left hstep1 hD2nonneg
    calc D ^ 2 * (Real.sinh (l / 2)) ^ 2 + (D ^ 2 - 1) * (Real.sin (φ / 2)) ^ 2
        ≤ D ^ 2 * ((Real.sinh (l / 2)) ^ 2 + (Real.sin (φ / 2)) ^ 2) := by nlinarith
      _ ≤ D ^ 2 * (Real.sinh (l + φ)) ^ 2 := hmult
      _ ≤ (Real.sinh (D * (l + φ))) ^ 2 := hstep2
  -- reduction of the goal to `hmain`
  have hcosh_l : Real.cosh l = 1 + 2 * (Real.sinh (l / 2)) ^ 2 := by
    have h := Real.cosh_two_mul (l / 2)
    rw [show 2 * (l / 2) = l by ring, Real.cosh_sq] at h
    linarith [h]
  have hcos_φ : Real.cos φ = 1 - 2 * (Real.sin (φ / 2)) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    have hc : Real.cos (φ / 2) ^ 2 = 1 - Real.sin (φ / 2) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (φ / 2)]
    rw [h, hc]; ring
  have hcosh_arg : Real.cosh (2 * (l + φ) * D) = 1 + 2 * (Real.sinh (D * (l + φ))) ^ 2 := by
    rw [show 2 * (l + φ) * D = 2 * (D * (l + φ)) by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring
  rw [hcosh_l, hcos_φ, hcosh_arg]
  nlinarith [hmain]

theorem screwReal (l : ℝ) (hl : 0 < l) (M : ℕ) (hM : 0 < M) (D : ℝ) (hD : 1 ≤ D) :
    D ^ 2 * (Real.cosh l - Real.cos (Real.pi / M)) + Real.cos (Real.pi / M)
      ≤ Real.cosh (2 * (l + Real.pi / M) * D) := by
  have hφ0 : 0 ≤ Real.pi / M := div_nonneg (le_of_lt Real.pi_pos) (Nat.cast_nonneg M)
  have hφπ : Real.pi / M ≤ Real.pi := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    rw [div_le_iff₀ (Nat.cast_pos.mpr hM)]
    nlinarith [Real.pi_pos]
  exact screw_aux l (Real.pi / M) D hl hφ0 hφπ hD

end Work.Mostow.gapA
