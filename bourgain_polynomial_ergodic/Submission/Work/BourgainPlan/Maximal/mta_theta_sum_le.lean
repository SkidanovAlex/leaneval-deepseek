import Mathlib

namespace Work.BourgainPlan.Maximal

/-- Rewrites the summand appearing in `mta_theta_sum_le` as a constant times the geometric
term `r ^ s.natAbs`, with `r = 2 ^ (-(θ / d))`. -/
private lemma theta_term_eq (C₂ B c : ℝ) (hC₂ : 0 < C₂) (d : ℕ) (θ : ℝ) (s : ℤ) :
    c * (C₂ * (2:ℝ) ^ (-((|s| : ℤ) : ℝ) / (d : ℝ))) ^ θ * B ^ (1 - θ)
      = c * C₂ ^ θ * B ^ (1 - θ) * ((2:ℝ) ^ (-(θ / (d:ℝ)))) ^ s.natAbs := by
  rw [Real.mul_rpow (le_of_lt hC₂) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-((|s| : ℤ) : ℝ)/(d:ℝ)) θ]
  rw [show (-((|s| : ℤ) : ℝ)/(d:ℝ)) * θ = (-(θ/(d:ℝ))) * ((|s|:ℤ):ℝ) by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(θ/(d:ℝ))) ((|s|:ℤ):ℝ)]
  rw [show ((|s|:ℤ):ℝ) = (s.natAbs:ℝ) by rw [← Int.natCast_natAbs s]; norm_num]
  rw [Real.rpow_natCast]
  ring

theorem mta_theta_sum_le (C₂ B c : ℝ) (hC₂ : 0 < C₂) (hB : 0 < B) (hc : 0 < c)
    (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ S : ℕ,
      ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
        c * (C₂ * (2:ℝ) ^ (-((|s| : ℤ) : ℝ) / (d : ℝ))) ^ θ * B ^ (1 - θ) ≤ A := by
  -- The summand is `K * r ^ s.natAbs` with `r = 2 ^ (-(θ/d)) ∈ (0,1)` geometric and `K > 0`.
  set r : ℝ := (2:ℝ) ^ (-(θ / (d:ℝ))) with hr
  have hd0 : (0:ℝ) < (d:ℝ) := by
    have : (0:ℕ) < d := lt_of_lt_of_le Nat.zero_lt_one hd
    exact_mod_cast this
  have hr_pos : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hr_lt : r < 1 := by
    rw [hr]
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (show -(θ / (d:ℝ)) < 0 by
        have : 0 < θ / (d:ℝ) := div_pos hθ0 hd0
        linarith)
    simpa using this
  have hr_norm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_lt
  -- Summability of the geometric majorant over `ℤ`.
  have hg : Summable (fun s : ℤ => r ^ s.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using summable_geometric_of_norm_lt_one hr_norm,
           by simpa using summable_geometric_of_norm_lt_one hr_norm⟩
  have hKpos : 0 < c * C₂ ^ θ * B ^ (1 - θ) := by positivity
  refine ⟨|(c * C₂ ^ θ * B ^ (1 - θ)) * (∑' s : ℤ, r ^ s.natAbs)| + 1, by positivity, ?_⟩
  intro S
  have key : ∀ s : ℤ, c * (C₂ * (2:ℝ) ^ (-((|s| : ℤ) : ℝ) / (d : ℝ))) ^ θ * B ^ (1 - θ)
      = (c * C₂ ^ θ * B ^ (1 - θ)) * (r ^ s.natAbs) := by
    intro s
    rw [hr, theta_term_eq C₂ B c hC₂ d θ s]
  have hsumle : ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), r ^ s.natAbs ≤ ∑' s : ℤ, r ^ s.natAbs :=
    Summable.sum_le_tsum _ (fun i _ => pow_nonneg (le_of_lt hr_pos) _) hg
  calc ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
          c * (C₂ * (2:ℝ) ^ (-((|s| : ℤ) : ℝ) / (d : ℝ))) ^ θ * B ^ (1 - θ)
      = ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), (c * C₂ ^ θ * B ^ (1 - θ)) * (r ^ s.natAbs) :=
        Finset.sum_congr rfl (fun s _ => key s)
    _ = (c * C₂ ^ θ * B ^ (1 - θ)) * ∑ s ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), r ^ s.natAbs := by
        rw [Finset.mul_sum]
    _ ≤ (c * C₂ ^ θ * B ^ (1 - θ)) * ∑' s : ℤ, r ^ s.natAbs :=
        mul_le_mul_of_nonneg_left hsumle (le_of_lt hKpos)
    _ ≤ |(c * C₂ ^ θ * B ^ (1 - θ)) * (∑' s : ℤ, r ^ s.natAbs)| + 1 := by
        have := le_abs_self ((c * C₂ ^ θ * B ^ (1 - θ)) * ∑' s : ℤ, r ^ s.natAbs)
        linarith

end Work.BourgainPlan.Maximal
