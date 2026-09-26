import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- The rational cast of an integer dot product, in coordinates. -/
lemma dot_cast (u v : V3) : ((V3.dot u v : ℤ) : ℚ) =
    (u.x : ℚ) * (v.x : ℚ) + (u.y : ℚ) * (v.y : ℚ) + (u.z : ℚ) * (v.z : ℚ) := by
  simp only [V3.dot]; push_cast; ring

/-- Two primitive vectors that are rational multiples of each other are equal up to sign. -/
theorem eq_pm_of_rat_smul {c z : V3} (hz : V3.Prim z) (hc : V3.Prim c) {q : ℚ}
    (h : (c.x : ℚ) = q * (z.x : ℚ) ∧ (c.y : ℚ) = q * (z.y : ℚ) ∧ (c.z : ℚ) = q * (z.z : ℚ)) :
    c = z ∨ c = V3.negate z := by
  obtain ⟨β, hβ⟩ := hc
  obtain ⟨γ, hγ⟩ := hz
  obtain ⟨hx, hy, hzz⟩ := h
  -- Primitivity of `c` gives `q * (β · z) = 1`, so `q` is the inverse of the integer `β · z`.
  have hqβ : q * ((V3.dot β z : ℤ) : ℚ) = 1 := by
    have A : ((V3.dot β c : ℤ) : ℚ) = 1 := by rw [hβ]; norm_num
    have B : ((V3.dot β c : ℤ) : ℚ) = q * ((V3.dot β z : ℤ) : ℚ) := by
      rw [dot_cast β c, dot_cast β z, hx, hy, hzz]; ring
    rwa [B] at A
  -- Primitivity of `z` gives `q = γ · c`, so `q` is an integer.
  have hqz : ((V3.dot γ z : ℤ) : ℚ) = 1 := by rw [hγ]; norm_num
  have hqγ : q = ((V3.dot γ c : ℤ) : ℚ) := by
    have B : ((V3.dot γ c : ℤ) : ℚ) = q * ((V3.dot γ z : ℤ) : ℚ) := by
      rw [dot_cast γ c, dot_cast γ z, hx, hy, hzz]; ring
    rw [hqz, mul_one] at B
    exact B.symm
  -- Hence the integer `(γ · c) * (β · z)` equals `1`, so `q = (±1)`.
  have hnm : (V3.dot γ c) * (V3.dot β z) = 1 := by
    have : ((V3.dot γ c : ℤ) : ℚ) * ((V3.dot β z : ℤ) : ℚ) = 1 := by
      rw [← hqγ]; exact hqβ
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with hq1 | hqneg
  · left
    have hq : q = 1 := by rw [hqγ, hq1]; norm_num
    have e1 : c.x = z.x := by
      have : (c.x : ℚ) = (z.x : ℚ) := by rw [hx, hq, one_mul]
      exact_mod_cast this
    have e2 : c.y = z.y := by
      have : (c.y : ℚ) = (z.y : ℚ) := by rw [hy, hq, one_mul]
      exact_mod_cast this
    have e3 : c.z = z.z := by
      have : (c.z : ℚ) = (z.z : ℚ) := by rw [hzz, hq, one_mul]
      exact_mod_cast this
    exact (V3.mk.injEq c.x c.y c.z z.x z.y z.z).mpr ⟨e1, e2, e3⟩
  · right
    have hq : q = -1 := by rw [hqγ, hqneg]; norm_num
    show c = ⟨-z.x, -z.y, -z.z⟩
    refine (V3.mk.injEq c.x c.y c.z (-z.x) (-z.y) (-z.z)).mpr ⟨?_, ?_, ?_⟩
    · have : (c.x : ℚ) = ((-z.x : ℤ) : ℚ) := by rw [hx, hq]; push_cast; ring
      exact_mod_cast this
    · have : (c.y : ℚ) = ((-z.y : ℤ) : ℚ) := by rw [hy, hq]; push_cast; ring
      exact_mod_cast this
    · have : (c.z : ℚ) = ((-z.z : ℤ) : ℚ) := by rw [hzz, hq]; push_cast; ring
      exact_mod_cast this

end Work.SGsep.hand
