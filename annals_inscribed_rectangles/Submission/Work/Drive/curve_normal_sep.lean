import Mathlib

namespace Work.Drive

/-- Uniform separation: a `2π`-periodic continuous curve `G : ℝ → ℝ × ℝ` that is injective modulo the
period meets the point `G 0` only near parameters congruent to `0 mod 2π`. -/
theorem curve_normal_sep (G : ℝ → ℝ × ℝ) (hcont : Continuous G)
    (hper : ∀ t : ℝ, G (t + 2 * Real.pi) = G t)
    (hinj : ∀ s t : ℝ, G s = G t → ∃ k : ℤ, s = t + 2 * Real.pi * k)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, ‖G x - G 0‖ < δ → ∃ k : ℤ, |x - 2 * Real.pi * k| < r := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi) ≠ 0 := ne_of_gt h2pi
  -- Periodicity for integer multiples of the period.
  have hper_int : ∀ (t : ℝ) (k : ℤ), G (t + 2 * Real.pi * k) = G t := by
    intro t k
    have hp : Function.Periodic G (2 * Real.pi) := hper
    have h := (hp.int_mul k) t
    rw [show t + 2 * Real.pi * (k : ℝ) = (t + (k : ℝ) * (2 * Real.pi)) by ring]
    exact h
  -- The "bad" set of parameters in one period that are far from `0 mod 2π`.
  set C : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ r ≤ x ∧ r ≤ |x - 2 * Real.pi|} with hCdef
  have hCeq : C = (Set.Icc 0 (2 * Real.pi) ∩ Set.Ici r) ∩
      (fun x : ℝ => |x - 2 * Real.pi|) ⁻¹' Set.Ici r := by
    rw [hCdef]; ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ici, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hCcompact : IsCompact C := by
    rw [hCeq]
    exact (isCompact_Icc.inter_right isClosed_Ici).inter_right (isClosed_Ici.preimage (by fun_prop))
  -- `G` avoids `G 0` on `C`.
  have hCnonzero : ∀ x ∈ C, (0 : ℝ) < ‖G x - G 0‖ := by
    intro x hx
    rw [hCdef] at hx
    simp only [Set.mem_ofPred_eq] at hx
    obtain ⟨hx0, hx2, hxr, hx2r⟩ := hx
    rcases lt_or_eq_of_le (norm_nonneg (G x - G 0)) with h | h
    · exact h
    · exfalso
      have hGx : G x = G 0 := sub_eq_zero.mp (norm_eq_zero.mp h.symm)
      obtain ⟨k, hk⟩ := hinj x 0 hGx
      simp only [zero_add] at hk
      -- `x = 2π k` with `0 ≤ x ≤ 2π` forces `k ∈ {0,1}`, and both are excluded from `C`.
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by nlinarith [hk, hx0, h2pi]
      have hk1 : (k : ℝ) ≤ 1 := by nlinarith [hk, hx2, h2pi]
      have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
      have hk1' : k ≤ 1 := by exact_mod_cast hk1
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with h0 | h1
      · rw [h0] at hk
        simp only [Int.cast_zero, mul_zero] at hk
        linarith [hk, hr, hxr]
      · rw [h1] at hk
        simp only [Int.cast_one, mul_one] at hk
        rw [hk] at hx2r
        simp only [sub_self, abs_zero] at hx2r
        linarith [hr, hx2r]
  -- A positive lower bound for `‖G · - G 0‖` on the compact set `C`.
  have hcont' : Continuous (fun x : ℝ => ‖G x - G 0‖) := (hcont.sub continuous_const).norm
  obtain ⟨δ, hδpos, hδle⟩ :=
    hCcompact.exists_forall_le' (f := fun x : ℝ => ‖G x - G 0‖) hcont'.continuousOn (a := 0)
      (fun b hb => hCnonzero b hb)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  -- Reduce `x` modulo `2π` to the window `[0, 2π)`.
  set m : ℤ := ⌊x / (2 * Real.pi)⌋ with hmdef
  set y : ℝ := x - 2 * Real.pi * (m : ℝ) with hydef
  have hy0 : 0 ≤ y := by
    rw [hydef, hmdef]
    have h := Int.floor_le (x / (2 * Real.pi))
    have h2 : (2 * Real.pi) * (x / (2 * Real.pi)) = x := mul_div_cancel₀ x h2pi_ne
    nlinarith [h, h2, h2pi]
  have hy2 : y < 2 * Real.pi := by
    rw [hydef, hmdef]
    have h := Int.lt_floor_add_one (x / (2 * Real.pi))
    have h2 : (2 * Real.pi) * (x / (2 * Real.pi)) = x := mul_div_cancel₀ x h2pi_ne
    nlinarith [h, h2, h2pi]
  have hGy : G x = G y := by
    have hxy : x = y + 2 * Real.pi * (m : ℝ) := by rw [hydef]; ring
    rw [hxy]; exact hper_int y m
  have hfy_lt : ‖G y - G 0‖ < δ := by rwa [← hGy]
  -- `y` is not in the bad set, so it lies in one of the two good arcs.
  have hyC : y ∉ C := by
    intro hy
    exact absurd (hδle y hy) (not_le.mpr hfy_lt)
  have hylim : y < r ∨ |y - 2 * Real.pi| < r := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact hyC (by rw [hCdef]; exact ⟨hy0, le_of_lt hy2, hcon.1, hcon.2⟩)
  rcases hylim with hyr | hy2r
  · exact ⟨m, by rw [show x - 2 * Real.pi * (m : ℝ) = y by rw [hydef], abs_of_nonneg hy0]; exact hyr⟩
  · exact ⟨m + 1, by
      rw [show x - 2 * Real.pi * ((m + 1 : ℤ) : ℝ) = y - 2 * Real.pi by
        rw [hydef]; push_cast; ring]
      exact hy2r⟩

end Work.Drive
