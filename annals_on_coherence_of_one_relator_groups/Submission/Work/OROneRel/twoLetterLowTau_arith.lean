import Mathlib

namespace Work.OROneRel

theorem twoLetterLowTau_arith (p q s t : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) (hsp : s < p)
    (hst : q * s = p * t + 1) :
    t + 1 ≤ q ∧ (q : ℤ) * (s : ℤ) ≤ (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1 := by
  -- Work in ℤ, where the key identity is polynomial.
  have hstZ : (q : ℤ) * (s : ℤ) = (p : ℤ) * (t : ℤ) + 1 := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hst
    push_cast at h
    exact h
  have hp0 : (0 : ℤ) < (p : ℤ) := by omega
  have hq0 : (0 : ℤ) < (q : ℤ) := by omega
  -- q*s = p*t + 1 and t ≤ q and s ≤ p give  p*(q - t) = q*(p - s) + 1.
  have hkey : (p : ℤ) * ((q : ℤ) - (t : ℤ)) = (q : ℤ) * ((p : ℤ) - (s : ℤ)) + 1 := by
    nlinarith [hstZ]
  have ha : (1 : ℤ) ≤ (p : ℤ) - (s : ℤ) := by omega
  have hRpos : (0 : ℤ) < (q : ℤ) * ((p : ℤ) - (s : ℤ)) + 1 := by nlinarith [ha, hq0]
  have hprodpos : (0 : ℤ) < (p : ℤ) * ((q : ℤ) - (t : ℤ)) := by nlinarith [hkey, hRpos]
  have hqt : (0 : ℤ) < (q : ℤ) - (t : ℤ) := pos_of_mul_pos_right hprodpos (le_of_lt hp0)
  have hqt1 : (1 : ℤ) ≤ (q : ℤ) - (t : ℤ) := by omega
  constructor
  · omega
  · have hple : (p : ℤ) ≤ (p : ℤ) * ((q : ℤ) - (t : ℤ)) := by nlinarith [hqt1, hp0]
    have hqle : (q : ℤ) ≤ (p : ℤ) * ((q : ℤ) - (t : ℤ)) := by nlinarith [hkey, ha, hq0]
    have hmax : max (p : ℤ) (q : ℤ) ≤ (p : ℤ) * ((q : ℤ) - (t : ℤ)) := max_le hple hqle
    have hdist : (p : ℤ) * ((q : ℤ) - (t : ℤ)) = (p : ℤ) * (q : ℤ) - (p : ℤ) * (t : ℤ) := by ring
    nlinarith [hstZ, hmax, hdist]

end Work.OROneRel
