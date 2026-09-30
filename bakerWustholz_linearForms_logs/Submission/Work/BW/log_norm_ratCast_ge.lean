import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem log_norm_ratCast_ge {n v d : ℕ} (hd : 1 ≤ d) {b : Fin n → ℤ} {L : Fin 1 → Fin n → ℤ}
    (q : ℚ) (σ : ℝ) (hσ : 0 < σ)
    (hrel : ∀ i, (b i : ℚ) = q * (L 0 i : ℚ))
    (hb : ∃ i, b i ≠ 0)
    (hL : ∑ i, |((L 0 i : ℤ) : ℝ)| * (1 / (d : ℝ)) ≤ 2 ^ v * σ) :
    Real.log ‖(q : ℂ)‖ ≥ -((v : ℝ) * Real.log 2 + Real.log σ + Real.log d) := by
  obtain ⟨i, hi⟩ := hb
  -- Some coefficient L 0 i is nonzero, so the sum S is strictly positive.
  have hLi_ne : L 0 i ≠ 0 := by
    intro h
    have : (b i : ℚ) = 0 := by rw [hrel i, h]; simp
    exact hi (by exact_mod_cast this)
  have hrelR : (b i : ℝ) = (q : ℝ) * (L 0 i : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hrel i)
    push_cast at h
    exact h
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hSpos : 0 < ∑ j, |((L 0 j : ℤ) : ℝ)| := by
    have h1 : (0:ℝ) < |((L 0 i : ℤ) : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hLi_ne
    have hle : |((L 0 i : ℤ) : ℝ)| ≤ ∑ j, |((L 0 j : ℤ) : ℝ)| :=
      Finset.single_le_sum (f := fun j => |((L 0 j : ℤ) : ℝ)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hL' : (∑ j, |((L 0 j : ℤ) : ℝ)|) * (1 / (d:ℝ)) ≤ 2^v * σ := by
    rw [Finset.sum_mul]; exact hL
  have hdiv : (∑ j, |((L 0 j : ℤ) : ℝ)|) / (d:ℝ) ≤ 2^v * σ := by
    rw [div_eq_mul_one_div]; exact hL'
  have hSle : ∑ j, |((L 0 j : ℤ) : ℝ)| ≤ (d:ℝ) * 2^v * σ := by
    have h' := (div_le_iff₀ hdpos).mp hdiv
    calc ∑ j, |((L 0 j : ℤ) : ℝ)| ≤ (2^v * σ) * (d:ℝ) := h'
      _ = (d:ℝ) * 2^v * σ := by ring
  have hqS : 1 ≤ |(q:ℝ)| * (∑ j, |((L 0 j : ℤ) : ℝ)|) := by
    have hb1 : (1:ℝ) ≤ |(b i : ℝ)| := by
      have := Int.one_le_abs hi
      exact_mod_cast this
    have habs : |(b i : ℝ)| ≤ |(q:ℝ)| * (∑ j, |((L 0 j : ℤ) : ℝ)|) := by
      rw [hrelR, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun j => |((L 0 j : ℤ) : ℝ)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
    linarith
  have hq_lower : 1 / (∑ j, |((L 0 j : ℤ) : ℝ)|) ≤ |(q:ℝ)| := (div_le_iff₀ hSpos).mpr hqS
  have hd2s_pos : (0:ℝ) < (d:ℝ) * 2^v * σ := by positivity
  have hle2 : 1 / ((d:ℝ) * 2^v * σ) ≤ 1 / (∑ j, |((L 0 j : ℤ) : ℝ)|) :=
    one_div_le_one_div_of_le hSpos hSle
  have hbound : 1 / ((d:ℝ) * 2^v * σ) ≤ |(q:ℝ)| := le_trans hle2 hq_lower
  have hxpos : (0:ℝ) < 1 / ((d:ℝ) * 2^v * σ) := one_div_pos.mpr hd2s_pos
  have hlog : Real.log (1 / ((d:ℝ) * 2^v * σ)) ≤ Real.log |(q:ℝ)| :=
    Real.log_le_log hxpos hbound
  have hlhs : Real.log (1 / ((d:ℝ) * 2^v * σ)) =
      -((v:ℝ) * Real.log 2 + Real.log σ + Real.log d) := by
    have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdpos
    have hs0 : σ ≠ 0 := ne_of_gt hσ
    have h2v0 : (2:ℝ)^v ≠ 0 := by positivity
    calc Real.log (1 / ((d:ℝ) * 2^v * σ))
        = - Real.log ((d:ℝ) * 2^v * σ) := by rw [one_div, Real.log_inv]
      _ = - (Real.log ((d:ℝ) * 2^v) + Real.log σ) := by
            rw [Real.log_mul (x := (d:ℝ)*2^v) (y := σ) (by positivity) hs0]
      _ = - ((Real.log d + Real.log ((2:ℝ)^v)) + Real.log σ) := by
            rw [Real.log_mul (x := (d:ℝ)) (y := (2:ℝ)^v) hd0 h2v0]
      _ = -((v:ℝ) * Real.log 2 + Real.log σ + Real.log d) := by
            rw [Real.log_pow]; ring
  have hnorm : ‖(q:ℂ)‖ = |(q:ℝ)| := by
    rw [show (q:ℂ) = ((q:ℝ):ℂ) by norm_num]
    simp
  rw [hnorm, ← hlhs]
  exact hlog

end Work.BW
