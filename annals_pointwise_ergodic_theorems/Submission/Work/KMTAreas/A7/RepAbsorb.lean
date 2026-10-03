import Mathlib

namespace Work.KMTAreas.A7

open Filter

/-- Elementary bound: for `t ≥ 0`, `t ≤ 2 ^ t`.  (Exponential beats linear.) -/
lemma le_two_rpow_self (t : ℝ) (ht : 0 ≤ t) : t ≤ (2 : ℝ) ^ t := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : (1 : ℝ) ≤ 2 * Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  calc t = t * 1 := by ring
    _ ≤ t * (2 * Real.log 2) := mul_le_mul_of_nonneg_left hlog ht
    _ = 2 * (Real.log 2 * t) := by ring
    _ ≤ Real.exp (Real.log 2 * t) := Real.two_mul_le_exp

/-- **The absorption of the weight against the lacunary decay.**  Eventually (in `L`) the exponent
`A*(2^{ρL} + L) - 2^{L/C₀} + 2` is ≤ 0.  The proof writes `u = 2^{L/(4C₀)}`; then
`2^{L/C₀} = u⁴`, `2^{ρL} ≤ u` (as `ρ ≤ 1/(4C₀)`) and `L ≤ 4C₀·u` (as `t ≤ 2^t`), so it suffices
that `A(1+4C₀)·u + 2 ≤ u⁴`, which holds once `u ≥ max 2 (A(1+4C₀))`. -/
private lemma exponent_eventually_nonpos (A : ℝ) (hA : 0 ≤ A) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
      A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
        + (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ 0 := by
  have hC0R : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC0pos : (0 : ℝ) < (C₀ : ℝ) := by linarith
  have hden : (0 : ℝ) < 4 * (C₀ : ℝ) := by linarith
  -- the lacunary base
  have hr : (1 : ℝ) < (2 : ℝ) ^ (1 / (4 * (C₀ : ℝ))) :=
    Real.one_lt_rpow (by norm_num) (one_div_pos.mpr hden)
  have hbase : Tendsto (fun L : ℕ => ((2 : ℝ) ^ (1 / (4 * (C₀ : ℝ)))) ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have heq : (fun L : ℕ => ((2 : ℝ) ^ (1 / (4 * (C₀ : ℝ)))) ^ (L : ℝ))
      = fun L : ℕ => (2 : ℝ) ^ ((L : ℝ) / (4 * (C₀ : ℝ))) := by
    funext L
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  have hTend : Tendsto (fun L : ℕ => (2 : ℝ) ^ ((L : ℝ) / (4 * (C₀ : ℝ)))) atTop atTop := by
    rw [← heq]
    simpa [Real.rpow_natCast] using hbase
  have hm : (0 : ℝ) < 2 := by norm_num
  have hthreshold := hTend.eventually (Filter.eventually_ge_atTop (max (2 : ℝ) (A * (1 + 4 * (C₀ : ℝ)))))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hthreshold
  refine ⟨N, ?_⟩
  intro L hL
  have hu_ge : max (2 : ℝ) (A * (1 + 4 * (C₀ : ℝ))) ≤ (2 : ℝ) ^ ((L : ℝ) / (4 * (C₀ : ℝ))) :=
    hN L hL
  set u : ℝ := (2 : ℝ) ^ ((L : ℝ) / (4 * (C₀ : ℝ))) with hu
  have hu2 : (2 : ℝ) ≤ u := le_trans (le_max_left _ _) hu_ge
  have hc_le_u : A * (1 + 4 * (C₀ : ℝ)) ≤ u := le_trans (le_max_right _ _) hu_ge
  have hu_nonneg : (0 : ℝ) ≤ u := le_trans (by norm_num) hu2
  -- `2 ^ (ρ L) ≤ u`
  have hρL : ρ * (L : ℝ) ≤ (L : ℝ) / (4 * (C₀ : ℝ)) := by
    have h0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    calc ρ * (L : ℝ) ≤ (1 / (4 * (C₀ : ℝ))) * (L : ℝ) := mul_le_mul_of_nonneg_right hρle h0
      _ = (L : ℝ) / (4 * (C₀ : ℝ)) := by ring
  have h2ρL : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ u :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hρL
  -- `L ≤ 4 C₀ u`
  have hLle : (L : ℝ) ≤ 4 * (C₀ : ℝ) * u := by
    have ht : (0 : ℝ) ≤ (L : ℝ) / (4 * (C₀ : ℝ)) := div_nonneg (Nat.cast_nonneg L) hden.le
    have h1 : (L : ℝ) / (4 * (C₀ : ℝ)) ≤ u := by
      have h := le_two_rpow_self ((L : ℝ) / (4 * (C₀ : ℝ))) ht
      simpa [hu] using h
    have h2 : (L : ℝ) / (4 * (C₀ : ℝ)) * (4 * (C₀ : ℝ)) = (L : ℝ) := by
      rw [div_mul_cancel₀ _ hden.ne']
    calc (L : ℝ) = (L : ℝ) / (4 * (C₀ : ℝ)) * (4 * (C₀ : ℝ)) := h2.symm
      _ ≤ u * (4 * (C₀ : ℝ)) := mul_le_mul_of_nonneg_right h1 hden.le
      _ = 4 * (C₀ : ℝ) * u := by ring
  -- `u ^ 4 = 2 ^ (L / C₀)`
  have hpow4 : u ^ 4 = (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := by
    have h4 : (L : ℝ) / (4 * (C₀ : ℝ)) * ((4 : ℕ) : ℝ) = (L : ℝ) / (C₀ : ℝ) := by
      push_cast
      field_simp
    rw [← Real.rpow_natCast u 4, hu, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), h4]
  -- the two elementary estimates
  have hcu : A * (1 + 4 * (C₀ : ℝ)) * u ≤ u ^ 2 := by
    calc A * (1 + 4 * (C₀ : ℝ)) * u ≤ u * u := mul_le_mul_of_nonneg_right hc_le_u hu_nonneg
      _ = u ^ 2 := by ring
  have hsq : u ^ 2 + 2 ≤ u ^ 4 := by
    have h4u : (4 : ℝ) ≤ u ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu2 2
      norm_num at h
      exact h
    have h1 : (0 : ℝ) ≤ u ^ 2 - 2 := by linarith
    have h2 : (0 : ℝ) ≤ u ^ 2 + 1 := by nlinarith [sq_nonneg u]
    have hmul := mul_nonneg h1 h2
    nlinarith [hmul]
  have hAu : A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)) ≤ A * (1 + 4 * (C₀ : ℝ)) * u := by
    have h1 : (2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ) ≤ u + 4 * (C₀ : ℝ) * u := by
      linarith [h2ρL, hLle]
    calc A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)) ≤ A * (u + 4 * (C₀ : ℝ) * u) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ = A * (1 + 4 * (C₀ : ℝ)) * u := by ring
  have hcu4 : A * (1 + 4 * (C₀ : ℝ)) * u + 2 ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := by
    rw [← hpow4]
    linarith [hcu, hsq]
  have hmain : A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)) + 2 ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) :=
    le_trans (by linarith [hAu]) hcu4
  linarith [hmain]

theorem RepAbsorb (A : ℝ) (hA : 0 ≤ A) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ L : ℕ,
      (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ K := by
  obtain ⟨N, hN⟩ := exponent_eventually_nonpos A hA C₀ hC₀ ρ hρle
  refine ⟨max 1 ((2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) + 2)), le_max_left _ _, ?_⟩
  intro L
  have hval : (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
      = (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
          + (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
  rw [hval]
  rcases lt_or_ge L N with hLN | hLN
  · have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_lt hLN)
    have hmono : A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
        ≤ A * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      have h1 : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (ρ * (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ])
      linarith
    have hexp : A * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
          + (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
        ≤ A * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) + 2 := by
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := Real.rpow_nonneg (by norm_num) _
      linarith
    exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (le_max_right _ _)
  · have hkey := hN L hLN
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey) ?_
    rw [Real.rpow_zero]
    exact le_max_left _ _

end Work.KMTAreas.A7
