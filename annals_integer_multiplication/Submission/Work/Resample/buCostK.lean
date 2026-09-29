import Mathlib
import Submission.Work.Resample.buQWwireDefs
import Submission.Work.Resample.buQWnloop
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- **Cost arithmetic of the `B̃` wire.**  `egCostShape Kw p α t Cm = Kw (t+1)(√p+1)(α+1)
(Cm (Kw p) + p+1) + Kw (t+1)(p+1)^2` absorbs the 20 window moves and the three stage words, given
only that `Kw` dominates the constants.

PROOF RECIPE.  Let `X := (t+1)*(√p+1)*(α+1)*(Cm (Kw*p) + p+1)` and `Y := (t+1)*(p+1)^2`.
* `Work.Resample.buQWnloop_prod` (fed `Work.Resample.buQWnloop_egN_le`) gives
  `(egN p α s t+1)*(egM p α+1)*(s+1) ≤ 16*(t+1)*(√p+1)*(α+1)`;
* unfold `Work.Resample.buSB`: `buSB p α t = 10^6*(t+1)*(p+4)*(√p+1)*(α+1)`, and `p+4 ≤ 2*(p+1)`
  (`hp`), `s+1 ≤ t+1` (`hst`), `√p+1 ≥ 1`, `α+1 ≥ 1`;
* `hKw` gives `Ksel ≤ Kw`, `Kscl ≤ Kw`, `Krnd ≤ Kw`, hence (`Nat.mul_le_mul_right p _` and
  `hmono : Monotone Cm`) also `Cm (Krnd*p) ≤ Cm (Kw*p)`, `Cm (Kscl*p) ≤ Cm (Kw*p)`;
* the five summands are bounded by `4*10^10*KS*X`, `Ksel*Y`, `16*Krnd*X`, `Kscl*Y`, `Kscl*X`
  respectively, and the extra `+1` by `X` (as `X, Y ≥ 1`);
* group: the coefficient of `X` is `≤ 4*10^10*KS + 16*Krnd + Kscl + 1 ≤ Kw` and that of `Y` is
  `Ksel + Kscl ≤ Kw`, both from `hKw`; so the total is `≤ Kw*X + Kw*Y`.  Mind that `egCostShape`
  writes `Kw*(t+1)*(√p+1)*(α+1)*(...)` left-associated, so rewrite with `ring`/`mul_assoc`. -/
theorem buCostK (Ksel Krnd Kscl KS Kw p α s t : ℕ) (Cm : ℕ → ℕ)
    (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) (hmono : Monotone Cm)
    (hKw : 4 * 10 ^ 10 * KS + 16 * Krnd + Ksel + 2 * Kscl + 2 ≤ Kw) :
    20 * (1000 * KS * Work.Resample.buSB p α t) + 1
      + Ksel * (t + 1) * (p + 1) * (p + 1)
      + Krnd * (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1)
          * (Cm (Krnd * p) + p + 1)
      + (Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1))
    ≤ Work.Resample.egCostShape Kw p α t Cm := by
  -- size of the window bound `buSB`
  have hN := buQWnloop_egN_le p α s t hs hst hα hp hθ
  have hF := buQWnloop_prod p α s t hs hst hα hp hαp hN
  have hKrnd : Krnd ≤ Kw := by omega
  have hKscl : Kscl ≤ Kw := by omega
  have hCmR : Cm (Krnd * p) ≤ Cm (Kw * p) := hmono (Nat.mul_le_mul_right p hKrnd)
  have hCmS : Cm (Kscl * p) ≤ Cm (Kw * p) := hmono (Nat.mul_le_mul_right p hKscl)
  have hs1 : s + 1 ≤ t + 1 := by omega
  have hb : 1 ≤ Nat.sqrt p + 1 := by omega
  have hc : 1 ≤ α + 1 := by omega
  have hbuSB : buSB p α t ≤
      2 * 10 ^ 6 * ((t + 1) * (p + 1) * (Nat.sqrt p + 1) * (α + 1)) := by
    rw [buSB]
    have h : p + 4 ≤ 2 * (p + 1) := by omega
    calc 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)
        ≤ 1000000 * (t + 1) * (2 * (p + 1)) * (Nat.sqrt p + 1) * (α + 1) := by gcongr
      _ = 2 * 10 ^ 6 * ((t + 1) * (p + 1) * (Nat.sqrt p + 1) * (α + 1)) := by ring
  -- the two monomials of the cost shape
  set W : ℕ := (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1) with hW
  set Y : ℕ := (t + 1) * (p + 1) ^ 2 with hY
  have hcost : egCostShape Kw p α t Cm = Kw * W + Kw * Y := by
    rw [egCostShape, hW, hY]; ring
  have h2 : 1 ≤ W := by
    rw [hW]
    have : 0 < (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1) := by
      positivity
    omega
  have h2' : 1 ≤ 1 * W := by rw [one_mul]; exact h2
  -- the 20 window moves
  have h1 : 20 * (1000 * KS * buSB p α t) ≤ 4 * 10 ^ 10 * KS * W := by
    rw [hW]
    have hE : p + 1 ≤ Cm (Kw * p) + p + 1 := by omega
    have hA : (t + 1) * (p + 1) * (Nat.sqrt p + 1) * (α + 1)
        ≤ (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1) := by
      calc (t + 1) * (p + 1) * (Nat.sqrt p + 1) * (α + 1)
          = (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (p + 1) := by ring
        _ ≤ (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1) :=
            Nat.mul_le_mul_left ((t + 1) * (Nat.sqrt p + 1) * (α + 1)) hE
    calc 20 * (1000 * KS * buSB p α t)
        ≤ 20 * (1000 * KS * (2 * 10 ^ 6 *
            ((t + 1) * (p + 1) * (Nat.sqrt p + 1) * (α + 1)))) :=
          Nat.mul_le_mul_left 20 (Nat.mul_le_mul_left (1000 * KS) hbuSB)
      _ ≤ 20 * (1000 * KS * (2 * 10 ^ 6 *
            ((t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1)))) :=
          Nat.mul_le_mul_left 20 (Nat.mul_le_mul_left (1000 * KS)
            (Nat.mul_le_mul_left (2 * 10 ^ 6) hA))
      _ = 4 * 10 ^ 10 * KS *
            ((t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1)) := by ring
  -- the selection stage
  have h3 : Ksel * (t + 1) * (p + 1) * (p + 1) ≤ Ksel * Y := by
    rw [hY]; exact le_of_eq (by ring)
  -- the rounding stage
  have h4 : Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1)
        * (Cm (Krnd * p) + p + 1) ≤ 16 * Krnd * W := by
    rw [hW]
    calc Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)
        = Krnd * ((egN p α s t + 1) * (egM p α + 1) * (s + 1)) *
            (Cm (Krnd * p) + p + 1) := by ring
      _ ≤ Krnd * (16 * (t + 1) * (Nat.sqrt p + 1) * (α + 1)) * (Cm (Kw * p) + p + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left Krnd hF) (by omega)
      _ = 16 * Krnd * ((t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1)) := by
          ring
  -- the scaling stage, low-level part
  have h5 : Kscl * (s + 1) * (p + 1) * (p + 1) ≤ Kscl * Y := by
    rw [hY]
    calc Kscl * (s + 1) * (p + 1) * (p + 1) = Kscl * ((s + 1) * (p + 1) ^ 2) := by ring
      _ ≤ Kscl * ((t + 1) * (p + 1) ^ 2) :=
          Nat.mul_le_mul_left Kscl (Nat.mul_le_mul_right ((p + 1) ^ 2) hs1)
  -- the scaling stage, `self`-product part
  have h6 : Kscl * (s + 1) * (Cm (Kscl * p) + p + 1) ≤ Kscl * W := by
    rw [hW]
    have h1' : s + 1 ≤ (t + 1) * (Nat.sqrt p + 1) * (α + 1) := by
      calc s + 1 ≤ t + 1 := hs1
        _ = (t + 1) * 1 := by ring
        _ ≤ (t + 1) * (Nat.sqrt p + 1) := Nat.mul_le_mul_left (t + 1) hb
        _ = (t + 1) * (Nat.sqrt p + 1) * 1 := by ring
        _ ≤ (t + 1) * (Nat.sqrt p + 1) * (α + 1) :=
            Nat.mul_le_mul_left ((t + 1) * (Nat.sqrt p + 1)) hc
    calc Kscl * (s + 1) * (Cm (Kscl * p) + p + 1)
        = Kscl * ((s + 1) * (Cm (Kscl * p) + p + 1)) := by ring
      _ ≤ Kscl * (((t + 1) * (Nat.sqrt p + 1) * (α + 1)) * (Cm (Kw * p) + p + 1)) :=
          Nat.mul_le_mul_left Kscl (Nat.mul_le_mul h1' (by omega))
      _ = Kscl * ((t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kw * p) + p + 1)) := by ring
  -- assemble the five summands
  have hkey : 20 * (1000 * KS * buSB p α t) + 1
      + Ksel * (t + 1) * (p + 1) * (p + 1)
      + Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)
      + (Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1))
      ≤ (((4 * 10 ^ 10 * KS * W + 1 * W) + Ksel * Y) + 16 * Krnd * W)
          + (Kscl * Y + Kscl * W) :=
    add_le_add (add_le_add (add_le_add (add_le_add h1 h2') h3) h4) (add_le_add h5 h6)
  have hgrp : (((4 * 10 ^ 10 * KS * W + 1 * W) + Ksel * Y) + 16 * Krnd * W)
        + (Kscl * Y + Kscl * W)
      = (4 * 10 ^ 10 * KS + 16 * Krnd + Kscl + 1) * W + (Ksel + Kscl) * Y := by ring
  calc 20 * (1000 * KS * buSB p α t) + 1
      + Ksel * (t + 1) * (p + 1) * (p + 1)
      + Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)
      + (Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1))
      ≤ (((4 * 10 ^ 10 * KS * W + 1 * W) + Ksel * Y) + 16 * Krnd * W)
          + (Kscl * Y + Kscl * W) := hkey
    _ = (4 * 10 ^ 10 * KS + 16 * Krnd + Kscl + 1) * W + (Ksel + Kscl) * Y := hgrp
    _ ≤ Kw * W + Kw * Y := Nat.add_le_add (Nat.mul_le_mul_right W (by omega))
          (Nat.mul_le_mul_right Y (by omega))
    _ = egCostShape Kw p α t Cm := hcost.symm


end Work.Resample
