import Mathlib

namespace Work.Analysis.Asymptotics

open Filter
open scoped Topology

theorem pow_dominates_linear (a : ℝ) (ha : 1 < a) (K L : ℝ) :
    ∃ N : ℕ, ∀ l : ℕ, N ≤ l → K * ((l : ℝ) + 1) + L ≤ a ^ l := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hlin : Tendsto (fun l : ℕ => (l : ℝ) / a ^ l) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 ha
  have hinv : Tendsto (fun l : ℕ => (a ^ l)⁻¹) atTop (𝓝 0) :=
    Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt ha)
  have h1 : Tendsto (fun l : ℕ => K * ((l : ℝ) / a ^ l) + (K + L) * (a ^ l)⁻¹) atTop (𝓝 0) := by
    have hK : Tendsto (fun l : ℕ => K * ((l : ℝ) / a ^ l)) atTop (𝓝 (K * 0)) :=
      Filter.Tendsto.const_mul K hlin
    have hL : Tendsto (fun l : ℕ => (K + L) * (a ^ l)⁻¹) atTop (𝓝 ((K + L) * 0)) :=
      Filter.Tendsto.const_mul (K + L) hinv
    simpa using hK.add hL
  have hmain : Tendsto (fun l : ℕ => (K * ((l : ℝ) + 1) + L) / a ^ l) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards with l
    rw [div_eq_mul_inv]
    ring
  have hev : ∀ᶠ l : ℕ in atTop, (K * ((l : ℝ) + 1) + L) / a ^ l < 1 :=
    (tendsto_order.1 hmain).2 1 zero_lt_one
  rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
  exact ⟨N, fun l hl => le_of_lt ((div_lt_one (pow_pos ha0 l)).1 (hN l hl))⟩

end Work.Analysis.Asymptotics
