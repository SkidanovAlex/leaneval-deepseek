import Mathlib
import Submission.Work.FIArea2.R6.WCcount

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `FIArea2/R6/WC_cube` — the per-modulus count under the cube range `c³ ≤ r(X²+Y²)`

`R6/WC_basic` bounds `WC` by `C·X·Y·r·τ(c)/c + C·X·Y·min(c, X²+Y²)/c`; `R6/WCcount` gives the
periodic bound `WC c r X Y ≤ 64·X·r·τ(c)^5·(2Y/c+1)` (and, by symmetry, the same with `X` and `Y`
interchanged).  Combining them:

* if `max(X,Y) ≥ c`: use the periodic bound on the larger coordinate, giving
  `WC ≤ 192·X·Y·r·τ(c)^5/c`;
* if `max(X,Y) < c`: then `r(X²+Y²) < 2rc²`, so the cube range `c³ ≤ r(X²+Y²)` forces `c ≤ 2r`,
  and `WC_basic` gives `WC ≤ C·X·Y·r·τ(c)/c + C·X·Y ≤ 3C·X·Y·r·τ(c)^5/c`.

Hence `c³ ≤ r(X²+Y²)` implies `WC c r X Y ≤ C·X·Y·r·τ(c)^5/c`.  This is the per-modulus estimate
used by `R6/ubox_bound3`; its `τ(c)^5`-loss is exactly what makes the "hard region"
`c > max(2r, X, Y)` of `WC_perMod` disappear (see `R6/WC_PERMOD_LEAD.md`, Part VII).
-/

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Symmetry of `WC` in `X` and `Y`**: swapping the two `h`-ranges and the two `w`-variables
sends `w₁h₁² - w₂h₂²` to its negative, leaving every condition and the weight `1/max` unchanged. -/
lemma WC_symm (c r X Y : ℕ) : Work.FIArea2.R6.WC c r X Y = Work.FIArea2.R6.WC c r Y X := by
  have key : ∀ a b u v : ℤ,
      (if Int.gcd u v = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0 ∧ (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2
        then (1 : ℝ) / ((max u.natAbs v.natAbs : ℕ) : ℝ) else 0)
      = (if Int.gcd v u = 1 ∧ v * b ^ 2 - u * a ^ 2 ≠ 0 ∧ (c : ℤ) ∣ v * b ^ 2 - u * a ^ 2
        then (1 : ℝ) / ((max v.natAbs u.natAbs : ℕ) : ℝ) else 0) := by
    intro a b u v
    have hg : (Int.gcd u v = 1) ↔ (Int.gcd v u = 1) := by rw [Int.gcd_comm]
    have hz : (u * a ^ 2 - v * b ^ 2 ≠ 0) ↔ (v * b ^ 2 - u * a ^ 2 ≠ 0) := by
      have h : v * b ^ 2 - u * a ^ 2 = -(u * a ^ 2 - v * b ^ 2) := by ring
      rw [h, neg_ne_zero]
    have hd : ((c : ℤ) ∣ u * a ^ 2 - v * b ^ 2) ↔ ((c : ℤ) ∣ v * b ^ 2 - u * a ^ 2) := by
      have : v * b ^ 2 - u * a ^ 2 = -(u * a ^ 2 - v * b ^ 2) := by ring
      rw [this, dvd_neg]
    have hm : ((max u.natAbs v.natAbs : ℕ) : ℝ) = ((max v.natAbs u.natAbs : ℕ) : ℝ) := by
      rw [max_comm]
    by_cases h : Int.gcd u v = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0 ∧ (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2
    · rw [if_pos h, if_pos ⟨hg.mp h.1, hz.mp h.2.1, hd.mp h.2.2⟩, hm]
    · rw [if_neg h]
      exact (if_neg (fun h' : Int.gcd v u = 1 ∧ v * b ^ 2 - u * a ^ 2 ≠ 0
          ∧ (c : ℤ) ∣ v * b ^ 2 - u * a ^ 2 =>
            h ⟨hg.mpr h'.1, hz.mpr h'.2.1, hd.mpr h'.2.2⟩)).symm
  unfold Work.FIArea2.R6.WC
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  exact key b a v u

/-- **The per-modulus weighted primitive-pair count under the cube range**, conditional on the
lossy local-density bound (`R6/LD_lossy`, whose statement is the hypothesis `hLD` here). -/
theorem WC_cube
    (hLD : ∀ (c X S : ℕ) [NeZero c],
      (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S,
          (((Finset.univ : Finset (ZMod c)).filter
              (fun z => (v2 : ZMod c) * z ^ 2
                = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
            / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
        ≤ 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5)
    (hWB : ∃ C : ℝ, 0 < C ∧ ∀ (c r X Y : ℕ), 1 ≤ c → 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.WC c r X Y
        ≤ C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
          + C * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2))
              / (c : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c r X Y : ℕ), 1 ≤ c → 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      c ^ 3 ≤ r * (X ^ 2 + Y ^ 2) →
      Work.FIArea2.R6.WC c r X Y
        ≤ C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) ^ 5 / (c : ℝ) := by
  obtain ⟨Cb, hCbpos, hWb⟩ := hWB
  refine ⟨3 * Cb + 384, by positivity, ?_⟩
  intro c r X Y hc hr hX hY hcub
  haveI : NeZero c := ⟨by omega⟩
  set C : ℝ := 3 * Cb + 384 with hCdef
  set T : ℝ := ((c.divisors.card : ℕ) : ℝ) ^ 5 with hT
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (show 0 < c by omega)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := by positivity
  have hτ1 : (1 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := by
    have h : 1 ≤ c.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast h
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hT]
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hτ1 5
  have hτT : ((c.divisors.card : ℕ) : ℝ) ≤ T := by
    rw [hT]
    simpa using pow_le_pow_right₀ hτ1 (by norm_num : 1 ≤ 5)
  have hCge192 : (192 : ℝ) ≤ C := by rw [hCdef]; nlinarith [hCbpos.le]
  have hCge3Cb : 3 * Cb ≤ C := by rw [hCdef]; nlinarith
  -- the two periodic cases both give `192 X Y r T / c`
  have hper : ∀ {A B : ℕ}, 1 ≤ A → 1 ≤ B → B ≥ c →
      Work.FIArea2.R6.WC c r A B ≤ C * (A : ℝ) * (B : ℝ) * (r : ℝ) * T / (c : ℝ) := by
    intro A B hA hB hBc
    have := WC_le_periodic c r A B (hLD c A r)
    have hBcR : (c : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBc
    have h1 : (1 : ℝ) ≤ (B : ℝ) / (c : ℝ) := by
      rw [le_div_iff₀ hcpos]; linarith
    have h2 : 2 * (B : ℝ) / (c : ℝ) + 1 ≤ 3 * ((B : ℝ) / (c : ℝ)) := by
      have h2' : 2 * (B : ℝ) / (c : ℝ) = 2 * ((B : ℝ) / (c : ℝ)) := by ring
      rw [h2']; linarith
    have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := by positivity
    have hTnn : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
    calc Work.FIArea2.R6.WC c r A B
        ≤ 64 * (A : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) ^ 5
            * (2 * (B : ℝ) / (c : ℝ) + 1) := this
      _ = 64 * (A : ℝ) * (r : ℝ) * T * (2 * (B : ℝ) / (c : ℝ) + 1) := by rw [hT]
      _ ≤ 64 * (A : ℝ) * (r : ℝ) * T * (3 * ((B : ℝ) / (c : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ C * (A : ℝ) * (B : ℝ) * (r : ℝ) * T / (c : ℝ) := by
          have hprod : (192 : ℝ) * ((A : ℝ) * (B : ℝ) * (r : ℝ) * T)
              ≤ C * ((A : ℝ) * (B : ℝ) * (r : ℝ) * T) :=
            mul_le_mul_of_nonneg_right hCge192 (by positivity)
          calc 64 * (A : ℝ) * (r : ℝ) * T * (3 * ((B : ℝ) / (c : ℝ)))
              = (192 * ((A : ℝ) * (B : ℝ) * (r : ℝ) * T)) * (c : ℝ)⁻¹ := by ring
            _ ≤ (C * ((A : ℝ) * (B : ℝ) * (r : ℝ) * T)) * (c : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right hprod (by positivity)
            _ = C * (A : ℝ) * (B : ℝ) * (r : ℝ) * T / (c : ℝ) := by ring
  by_cases hYc : c ≤ Y
  · -- `Y ≥ c`: periodic count on the second coordinate
    exact hper (by omega) (by omega) hYc
  · have hYclt : Y < c := lt_of_not_ge hYc
    by_cases hcX : c ≤ X
    · -- `X ≥ c`: periodic count on the first coordinate, using symmetry
      have h := hper (A := Y) (B := X) (by omega) (by omega) hcX
      calc Work.FIArea2.R6.WC c r X Y = Work.FIArea2.R6.WC c r Y X := WC_symm c r X Y
        _ ≤ C * (Y : ℝ) * (X : ℝ) * (r : ℝ) * T / (c : ℝ) := h
        _ = C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by ring
    · have hXclt : X < c := lt_of_not_ge hcX
      -- `X < c` and `Y < c`: the cube range forces `c ≤ 2r`, and `WC_basic` applies
      have hXY : X ^ 2 + Y ^ 2 ≤ 2 * c ^ 2 := by nlinarith [hXclt, hYclt]
      have hc3 : c ^ 3 ≤ 2 * r * c ^ 2 := by
        calc c ^ 3 ≤ r * (X ^ 2 + Y ^ 2) := hcub
          _ ≤ r * (2 * c ^ 2) := Nat.mul_le_mul_left r hXY
          _ = 2 * r * c ^ 2 := by ring
      have h2r : c ≤ 2 * r := by
        have h := hc3
        rw [show c ^ 3 = c * c ^ 2 by ring,
          show 2 * r * c ^ 2 = (2 * r) * c ^ 2 by ring] at h
        exact Nat.le_of_mul_le_mul_right h (by positivity)
      have h2rR : (c : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast h2r
      have h2rT : (1 : ℝ) ≤ 2 * (r : ℝ) * T / (c : ℝ) := by
        rw [le_div_iff₀ hcpos]
        nlinarith [h2rR, hT1, hr0]
      have hb := hWb c r X Y hc hr hX hY
      have ht1 : Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
          ≤ Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by
        have h' := mul_le_mul_of_nonneg_left hτT (by positivity : (0 : ℝ) ≤ Cb * (X : ℝ)
          * (Y : ℝ) * (r : ℝ))
        exact div_le_div_of_nonneg_right h' hcpos.le
      have ht2 : Cb * (X : ℝ) * (Y : ℝ)
            * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2)) / (c : ℝ)
          ≤ 2 * Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by
        have hmin : min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) ≤ (c : ℝ) := min_le_left _ _
        have h1 : Cb * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2)) / (c : ℝ)
            ≤ Cb * (X : ℝ) * (Y : ℝ) := by
          rw [div_le_iff₀ hcpos]
          calc Cb * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2))
              ≤ Cb * (X : ℝ) * (Y : ℝ) * (c : ℝ) :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ = Cb * (X : ℝ) * (Y : ℝ) * (c : ℝ) := rfl
        calc Cb * (X : ℝ) * (Y : ℝ)
              * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2)) / (c : ℝ)
            ≤ Cb * (X : ℝ) * (Y : ℝ) := h1
          _ ≤ Cb * (X : ℝ) * (Y : ℝ) * (2 * (r : ℝ) * T / (c : ℝ)) := by
              have := mul_le_mul_of_nonneg_left h2rT (by positivity : (0 : ℝ) ≤ Cb * (X : ℝ)
                * (Y : ℝ))
              rwa [mul_one] at this
          _ = 2 * Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by ring
      calc Work.FIArea2.R6.WC c r X Y
          ≤ Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
            + Cb * (X : ℝ) * (Y : ℝ)
                * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2)) / (c : ℝ) := hb
        _ ≤ Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ)
            + 2 * Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := add_le_add ht1 ht2
        _ = 3 * Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by ring
        _ ≤ C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by
            have hprod : (3 * Cb) * ((X : ℝ) * (Y : ℝ) * (r : ℝ) * T)
                ≤ C * ((X : ℝ) * (Y : ℝ) * (r : ℝ) * T) :=
              mul_le_mul_of_nonneg_right hCge3Cb (by positivity)
            calc 3 * Cb * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ)
                = ((3 * Cb) * ((X : ℝ) * (Y : ℝ) * (r : ℝ) * T)) * (c : ℝ)⁻¹ := by ring
              _ ≤ (C * ((X : ℝ) * (Y : ℝ) * (r : ℝ) * T)) * (c : ℝ)⁻¹ :=
                  mul_le_mul_of_nonneg_right hprod (by positivity)
              _ = C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * T / (c : ℝ) := by ring

end

end Work.FIArea2.R6
