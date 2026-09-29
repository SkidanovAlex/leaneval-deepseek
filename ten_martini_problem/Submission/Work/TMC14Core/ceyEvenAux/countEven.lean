import Mathlib

namespace Work.TMC14Core.ceyEvenAux

/-- Counting lemma: if `q = 2*m+2`, `a+b+c+e ≤ 2*m+1`, and `q` divides both
`a-b-m` and `c-e-m`, then `a = c = m` and `b = e = 0`. -/
theorem countEven (a b c e m q : ℕ) (hm : q = 2*m+2) (h1 : a + b + c + e ≤ 2*m+1)
    (h2 : (q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ)))
    (h3 : (q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ))) :
    a = m ∧ b = 0 ∧ c = m ∧ e = 0 := by
  obtain ⟨k, hk⟩ := h2
  obtain ⟨l, hl⟩ := h3
  have ha : a ≤ 2*m+1 := by omega
  have hb : b ≤ 2*m+1 := by omega
  have hc : c ≤ 2*m+1 := by omega
  have he : e ≤ 2*m+1 := by omega
  have hq : (q:ℤ) = 2*(m:ℤ) + 2 := by omega
  have hqpos : (0:ℤ) < (q:ℤ) := by omega
  have hu : (a:ℤ)-(b:ℤ)-(m:ℤ) ≤ (m:ℤ)+1 := by omega
  have hlow : -(3*(m:ℤ)+1) ≤ (a:ℤ)-(b:ℤ)-(m:ℤ) := by omega
  have hlt : (m:ℤ)+1 < (q:ℤ) := by omega
  have hk_le : k ≤ 0 := by
    by_contra h
    push Not at h
    have h1k : (1:ℤ) ≤ k := by omega
    have step : (q:ℤ) ≤ (q:ℤ)*k := by
      have := mul_le_mul_of_nonneg_left h1k (le_of_lt hqpos)
      simpa using this
    linarith [step, hk, hu, hlt]
  have hk_ge : -1 ≤ k := by
    by_contra h
    push Not at h
    have h2k : k ≤ -2 := by omega
    have step : (q:ℤ)*k ≤ (q:ℤ)*(-2) := mul_le_mul_of_nonneg_left h2k (le_of_lt hqpos)
    have hm0 : (0:ℤ) ≤ (m:ℤ) := by omega
    linarith [step, hk, hlow, hq, hm0]
  have hk01 : k = -1 ∨ k = 0 := by omega
  have hu2 : (c:ℤ)-(e:ℤ)-(m:ℤ) ≤ (m:ℤ)+1 := by omega
  have hlow2 : -(3*(m:ℤ)+1) ≤ (c:ℤ)-(e:ℤ)-(m:ℤ) := by omega
  have hl_le : l ≤ 0 := by
    by_contra h
    push Not at h
    have h1l : (1:ℤ) ≤ l := by omega
    have step : (q:ℤ) ≤ (q:ℤ)*l := by
      have := mul_le_mul_of_nonneg_left h1l (le_of_lt hqpos)
      simpa using this
    linarith [step, hl, hu2, hlt]
  have hl_ge : -1 ≤ l := by
    by_contra h
    push Not at h
    have h2l : l ≤ -2 := by omega
    have step : (q:ℤ)*l ≤ (q:ℤ)*(-2) := mul_le_mul_of_nonneg_left h2l (le_of_lt hqpos)
    have hm0 : (0:ℤ) ≤ (m:ℤ) := by omega
    linarith [step, hl, hlow2, hq, hm0]
  have hl01 : l = -1 ∨ l = 0 := by omega
  have ha_eq : (a:ℤ) = (b:ℤ) + (m:ℤ) + (q:ℤ)*k := by linarith [hk]
  have hc_eq : (c:ℤ) = (e:ℤ) + (m:ℤ) + (q:ℤ)*l := by linarith [hl]
  have hS : (a:ℤ)+(b:ℤ)+(c:ℤ)+(e:ℤ) ≤ 2*(m:ℤ)+1 := by omega
  rcases hk01 with hk0 | hk0 <;> rcases hl01 with hl0 | hl0
  · subst hk0; subst hl0; omega
  · subst hk0; subst hl0; omega
  · subst hk0; subst hl0; omega
  · subst hk0; subst hl0; omega

end Work.TMC14Core.ceyEvenAux
