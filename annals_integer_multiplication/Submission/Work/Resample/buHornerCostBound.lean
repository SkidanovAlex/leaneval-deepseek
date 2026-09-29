import Mathlib
import Submission.Work.Resample.buHornerKit

namespace Work.Resample

/-- `buSZ p + 8` grows at most quadratically in `p` (with a generous constant), for `p ≥ 100`. -/
theorem buSZ_add_eight_le (p : ℕ) (hp : 100 ≤ p) : buSZ p + 8 ≤ 150 * (p + 1) ^ 2 := by
  have h1 : 0 ≤ p - 100 := by omega
  have h2 : 0 ≤ 70 * p + 1300 := by omega
  have h3 := mul_nonneg h1 h2
  simp only [buSZ]
  nlinarith [h3]

/-- The uniform one-step Horner budget is at most `22500 · KS · (p+1)^4`. -/
theorem buSB_le_pow (p KS : ℕ) (hp : 100 ≤ p) : buHSB p KS ≤ 22500 * KS * (p + 1) ^ 4 := by
  have hbuSZ := buSZ_add_eight_le p hp
  rw [buHSB]
  calc KS * (buSZ p + 8) ^ 2 ≤ KS * (150 * (p + 1) ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbuSZ 2)
    _ = 22500 * KS * (p + 1) ^ 4 := by ring

/-- `auNstep p + 1 ≤ 8 (p+1)` for `p ≥ 100`. -/
theorem auNstep_add_one_le (p : ℕ) (hp : 100 ≤ p) : auNstep p + 1 ≤ 8 * (p + 1) := by
  simp only [auNstep, auPrec]; omega

theorem buHornerCostBound (p KS Kpre Kfin Kloop c e n : ℕ) (hp : 100 ≤ p) (hKS : 1 ≤ KS)
    (hKpre : Kpre ≤ KS) (hKfin : Kfin ≤ KS) (hKloop : Kloop ≤ KS)
    (he1 : Kpre ≤ e) (he2 : Kfin ≤ e) (he3 : 5 ≤ e)
    (hc : c ≤ 18 * Work.Resample.buHSB p KS)
    (hn : n ≤ Kpre * (p + 1) ^ Kpre + ((Work.Resample.auNstep p + 1) * (c + Kloop) + Kloop)
      + Kfin * (p + 1) ^ Kfin) :
    n ≤ (10000000000000 * KS + 1000) * (p + 1) ^ e := by
  -- Basic monotonicity facts.
  have hA4 : 1 ≤ (p + 1) ^ 4 := Nat.one_le_pow 4 (p + 1) (by omega)
  have hAe : 1 ≤ (p + 1) ^ e := Nat.one_le_pow e (p + 1) (by omega)
  have hpe : (p + 1) ^ 5 ≤ (p + 1) ^ e := Nat.pow_le_pow_right (by omega) he3
  -- Bound on the per-step cost `c`.
  have hbuSB := buSB_le_pow p KS hp
  have hc' : c ≤ 405000 * KS * (p + 1) ^ 4 := by
    calc c ≤ 18 * buHSB p KS := hc
      _ ≤ 18 * (22500 * KS * (p + 1) ^ 4) := Nat.mul_le_mul_left _ hbuSB
      _ = 405000 * KS * (p + 1) ^ 4 := by ring
  have hAu := auNstep_add_one_le p hp
  -- The middle (bounded-cost) term.
  have hck : c + Kloop ≤ 405001 * KS * (p + 1) ^ 4 := by
    have h1 : Kloop ≤ KS * (p + 1) ^ 4 := by
      refine le_trans hKloop ?_
      calc KS = KS * 1 := by ring
        _ ≤ KS * (p + 1) ^ 4 := Nat.mul_le_mul_left KS hA4
    calc c + Kloop ≤ 405000 * KS * (p + 1) ^ 4 + KS * (p + 1) ^ 4 := Nat.add_le_add hc' h1
      _ = 405001 * KS * (p + 1) ^ 4 := by ring
  have hprod : (auNstep p + 1) * (c + Kloop) ≤ 3240008 * KS * (p + 1) ^ 5 := by
    refine le_trans (Nat.mul_le_mul hAu hck) ?_
    rw [show (8 * (p + 1)) * (405001 * KS * (p + 1) ^ 4) = 3240008 * KS * (p + 1) ^ 5 from by ring]
  have hprod' : (auNstep p + 1) * (c + Kloop) ≤ 3240008 * KS * (p + 1) ^ e :=
    le_trans hprod (Nat.mul_le_mul_left _ hpe)
  have hKloop' : Kloop ≤ KS * (p + 1) ^ e := by
    calc Kloop ≤ KS := hKloop
      _ = KS * 1 := by ring
      _ ≤ KS * (p + 1) ^ e := Nat.mul_le_mul_left KS hAe
  have hterm2 : (auNstep p + 1) * (c + Kloop) + Kloop ≤ 3240009 * KS * (p + 1) ^ e := by
    calc (auNstep p + 1) * (c + Kloop) + Kloop
        ≤ 3240008 * KS * (p + 1) ^ e + KS * (p + 1) ^ e := Nat.add_le_add hprod' hKloop'
      _ = 3240009 * KS * (p + 1) ^ e := by ring
  -- The two power terms.
  have hT1 : Kpre * (p + 1) ^ Kpre ≤ KS * (p + 1) ^ e :=
    Nat.mul_le_mul hKpre (Nat.pow_le_pow_right (by omega) he1)
  have hT3 : Kfin * (p + 1) ^ Kfin ≤ KS * (p + 1) ^ e :=
    Nat.mul_le_mul hKfin (Nat.pow_le_pow_right (by omega) he2)
  have hsum : Kpre * (p + 1) ^ Kpre + ((auNstep p + 1) * (c + Kloop) + Kloop)
      + Kfin * (p + 1) ^ Kfin
      ≤ KS * (p + 1) ^ e + 3240009 * KS * (p + 1) ^ e + KS * (p + 1) ^ e :=
    Nat.add_le_add (Nat.add_le_add hT1 hterm2) hT3
  -- Assemble.
  refine le_trans hn (le_trans hsum ?_)
  rw [show KS * (p + 1) ^ e + 3240009 * KS * (p + 1) ^ e + KS * (p + 1) ^ e
        = 3240011 * KS * (p + 1) ^ e from by ring]
  exact Nat.mul_le_mul_right _
    (calc 3240011 * KS ≤ 10000000000000 * KS := Nat.mul_le_mul_right KS (by norm_num)
      _ ≤ 10000000000000 * KS + 1000 := Nat.le_add_right _ _)

end Work.Resample
