import Mathlib
import Submission.Work.BMF.adi_descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset
theorem step_geom (p : ADIPar) (hp : ADIHyp p) :
    p.L ≤ p.x / 2 ∧ 3 * p.C₀ ^ 2 * p.L ≤ p.x / 2 ∧
    (∀ t ∈ Set.Icc (p.x / (p.a : ℝ)) ((p.x + p.L) / (p.a : ℝ)),
      |(p.a : ℝ) * t - p.x| ≤ p.L ∧ |(p.b : ℝ) * t - p.x| ≤ 3 * p.C₀ ^ 2 * p.L) := by
  rcases hp with ⟨hC0, _hdeg, _hL2, hN100, _hQm, hxpos, hNL, hxNL, _hb1, hba, _ha, hNa⟩
  have hC0pos : 0 < p.C₀ := lt_of_lt_of_le zero_lt_one hC0
  have hLpos : 0 < p.L := by
    have h : (2:ℝ) ≤ p.L := _hL2
    linarith
  have hC03 : (1:ℝ) ≤ p.C₀ ^ 3 := one_le_pow₀ hC0
  have hC02 : (1:ℝ) ≤ p.C₀ ^ 2 := one_le_pow₀ hC0
  -- key: 100 C₀^3 L ≤ x
  have h100 : 100 * p.C₀ ^ 3 * p.L ≤ p.x := by
    have h1 : p.L * (100 * p.C₀ ^ 4) ≤ p.L * p.N :=
      mul_le_mul_of_nonneg_left hN100 (le_of_lt hLpos)
    nlinarith [h1, hNL, hC0pos, hLpos]
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [h100, hC03, hLpos]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [h100, hC03, hLpos, hC0pos]
  · intro t ht
    obtain ⟨htlo, hthi⟩ := ht
    have hapos : (0:ℝ) < p.a := by
      have : 0 < p.a := by omega
      exact_mod_cast this
    have hb_le_a : (p.b : ℝ) ≤ (p.a : ℝ) := by exact_mod_cast le_of_lt hba
    have hab_nonneg : 0 ≤ (p.a : ℝ) - (p.b : ℝ) := by linarith
    have hat_lo : p.x ≤ (p.a : ℝ) * t := by
      have := (div_le_iff₀ hapos).mp htlo
      linarith
    have hat_hi : (p.a : ℝ) * t ≤ p.x + p.L := by
      have := (le_div_iff₀ hapos).mp hthi
      linarith
    have ht_pos : 0 < t := by
      have : 0 < p.x / (p.a : ℝ) := div_pos hxpos hapos
      linarith
    have hb0 : (0:ℝ) ≤ (p.b : ℝ) := Nat.cast_nonneg _
    -- key bound: x (a-b) / a ≤ C₀² L
    have hmul : p.x * ((p.a : ℝ) - (p.b : ℝ)) ≤ p.C₀ ^ 2 * p.L * p.a := by
      have h1 : p.x * ((p.a : ℝ) - (p.b : ℝ)) ≤ (p.C₀ * (p.N * p.L)) * ((p.a : ℝ) - (p.b : ℝ)) :=
        mul_le_mul_of_nonneg_right hxNL hab_nonneg
      have h3 : p.C₀ * p.L * (p.N * ((p.a : ℝ) - (p.b : ℝ))) ≤ p.C₀ * p.L * (p.C₀ * p.a) :=
        mul_le_mul_of_nonneg_left hNa (by positivity)
      nlinarith [h1, h3]
    have hkey : p.x * ((p.a : ℝ) - (p.b : ℝ)) / (p.a : ℝ) ≤ p.C₀ ^ 2 * p.L := by
      rw [div_le_iff₀ hapos]
      nlinarith [hmul]
    have hprod : 0 ≤ p.C₀ ^ 2 * p.L := mul_nonneg (sq_nonneg p.C₀) (le_of_lt hLpos)
    constructor
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_le]
      constructor
      · have h1 : (p.b : ℝ) * (p.x / (p.a : ℝ)) ≤ (p.b : ℝ) * t :=
          mul_le_mul_of_nonneg_left htlo hb0
        have h2 : (p.b : ℝ) * (p.x / (p.a : ℝ)) - p.x =
            -(p.x * ((p.a : ℝ) - (p.b : ℝ)) / (p.a : ℝ)) := by
          field_simp
          ring
        linarith [h1, h2, hkey, hprod]
      · have hbup : (p.b : ℝ) * t - p.x ≤ p.L := by
          nlinarith [hat_hi, hba, ht_pos]
        have hLle : p.L ≤ 3 * (p.C₀ ^ 2 * p.L) := by nlinarith [hC02, hLpos]
        linarith [hbup, hLle]

end Work.BMF
