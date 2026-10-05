import Mathlib

namespace Work.RPA3

/-- A function which is periodic with period `c` only on the right is periodic with
every integer multiple of `c`. -/
private lemma periodic_int_mul {f : ℝ → ℝ} {c : ℝ} (h : ∀ t, f (t + c) = f t)
    (n : ℤ) (z : ℝ) : f (z + c * n) = f z := by
  have hf : Function.Periodic f c := h
  have := hf.int_mul n
  simpa [mul_comm] using this z

theorem exists_lower_of_periodic_of_std (X0 : ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (hcont : Continuous (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
    (hper : ∀ τ x t, g τ x (t + 2 * Real.pi) = g τ x t)
    (hpos : ∀ τ x t, 0 < g τ x t)
    (hstd : ∀ τ x t, X0 < |x| → g τ x t = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t, c ≤ g τ x t := by
  -- integer-shift periodicity of `g` in its last variable
  have hshift : ∀ (τ x : ℝ) (n : ℤ) (z : ℝ), g τ x (z + 2 * Real.pi * n) = g τ x z :=
    fun τ x n z => periodic_int_mul (fun t => hper τ x t) n z
  -- the compact slab over which we minimise
  set R : ℝ := |X0| + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (-2 : ℝ) 3 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) with hK
  have hKc : IsCompact K := by
    rw [hK]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKne : K.Nonempty := by
    refine ⟨(-2, 0, 0), ?_⟩
    rw [hK]
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩,
      ⟨by linarith, by linarith⟩, ⟨le_refl 0, by positivity⟩⟩
  obtain ⟨p0, hp0K, hp0min⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
  let m : ℝ := g p0.1 p0.2.1 p0.2.2
  have hmpos : 0 < m := hpos p0.1 p0.2.1 p0.2.2
  have hmle : ∀ p ∈ K, m ≤ g p.1 p.2.1 p.2.2 := by
    intro p hp
    show g p0.1 p0.2.1 p0.2.2 ≤ g p.1 p.2.1 p.2.2
    exact hp0min hp
  refine ⟨min m 1, lt_min hmpos one_pos, ?_⟩
  intro τ hτ x t
  by_cases hx : |x| ≤ X0
  · -- inside the strip: reduce `t` modulo `2π` into the compact slab
    have hxlt : |x| < R := by rw [hR]; linarith [le_abs_self X0]
    set t0 : ℝ := 2 * Real.pi * Int.fract (t / (2 * Real.pi)) with ht0
    have ht0nn : 0 ≤ t0 := by
      rw [ht0]
      exact mul_nonneg (by positivity) (Int.fract_nonneg _)
    have ht0le : t0 ≤ 2 * Real.pi := by
      rw [ht0]
      have h1 := Int.fract_lt_one (t / (2 * Real.pi))
      have h2p : 0 < 2 * Real.pi := by positivity
      have := mul_lt_mul_of_pos_left h1 h2p
      rw [mul_one] at this
      linarith
    have htdecomp : t = t0 + 2 * Real.pi * ⌊t / (2 * Real.pi)⌋ := by
      rw [ht0]
      have h := Int.fract_add_floor (t / (2 * Real.pi))
      have h2p : (2 * Real.pi) ≠ 0 := by positivity
      have hmul : 2 * Real.pi *
          (Int.fract (t / (2 * Real.pi)) + (⌊t / (2 * Real.pi)⌋ : ℝ)) = t := by
        rw [h, mul_div_cancel₀ t h2p]
      rw [mul_add] at hmul
      linarith
    have hmem : (τ, x, t0) ∈ K := by
      rw [hK]
      simp only [Set.mem_prod, Set.mem_Icc]
      exact ⟨hτ, ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩,
        ⟨ht0nn, ht0le⟩⟩
    have hge : m ≤ g τ x t0 := hmle (τ, x, t0) hmem
    have heq : g τ x t = g τ x t0 := by
      rw [htdecomp, hshift τ x ⌊t / (2 * Real.pi)⌋ t0]
    rw [heq]
    exact le_trans (min_le_left m 1) hge
  · -- outside the strip: `g = 1`
    rw [not_le] at hx
    rw [hstd τ x t hx]
    exact min_le_right m 1

end Work.RPA3
