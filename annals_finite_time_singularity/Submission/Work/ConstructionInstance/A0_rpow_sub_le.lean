import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Subadditivity of `x ↦ x ^ β` on `[0, ∞)` for exponents `β ∈ (0, 1]`. -/
private lemma rpow_add_le_add_rpow {β a b : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ β ≤ a ^ β + b ^ β := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hab | hab
  · have ha0 : a = 0 := le_antisymm (by linarith) ha
    have hb0 : b = 0 := le_antisymm (by linarith) hb
    simp [ha0, hb0, Real.zero_rpow hβ.ne']
  · have hpow : 0 ≤ (a + b) ^ β := Real.rpow_nonneg hab.le β
    have key : ∀ x : ℝ, 0 ≤ x → x ≤ a + b →
        (a + b) ^ β * (x / (a + b)) ≤ x ^ β := by
      intro x hx hxb
      have hxdiv_nonneg : 0 ≤ x / (a + b) := div_nonneg hx hab.le
      have hxdiv_le_one : x / (a + b) ≤ 1 := (div_le_one hab).mpr hxb
      have h1 : x / (a + b) ≤ (x / (a + b)) ^ β :=
        Real.self_le_rpow_of_le_one hxdiv_nonneg hxdiv_le_one hβ1
      calc (a + b) ^ β * (x / (a + b)) ≤ (a + b) ^ β * (x / (a + b)) ^ β :=
            mul_le_mul_of_nonneg_left h1 hpow
        _ = x ^ β := by
            rw [← Real.mul_rpow hab.le hxdiv_nonneg, mul_div_cancel₀ x hab.ne']
    have h := add_le_add (key a ha (by linarith)) (key b hb (by linarith))
    rw [← mul_add, ← add_div, div_self hab.ne', mul_one] at h
    exact h

lemma A0_rpow_sub_le {β t u : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    |t ^ β - u ^ β| ≤ |t - u| ^ β := by
  rcases le_total u t with h | h
  · have htu : u ^ β ≤ t ^ β := Real.rpow_le_rpow hu h hβ.le
    have hsub : 0 ≤ t - u := by linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ t ^ β - u ^ β), abs_of_nonneg hsub]
    have key := rpow_add_le_add_rpow hβ hβ1 hu hsub
    rw [show u + (t - u) = t by ring] at key
    linarith
  · have htu : t ^ β ≤ u ^ β := Real.rpow_le_rpow ht h hβ.le
    have hsub : 0 ≤ u - t := by linarith
    rw [abs_of_nonpos (by linarith : t ^ β - u ^ β ≤ 0), abs_sub_comm t u,
      abs_of_nonneg hsub]
    have key := rpow_add_le_add_rpow hβ hβ1 ht hsub
    rw [show t + (u - t) = u by ring] at key
    linarith

end Work.ConstructionInstance
