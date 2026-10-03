import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_intpairs_eq_four_mul_natpairs_sub
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs_asymptotic

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- **Integer point count for `X² + Y⁴`.**

The number of integer pairs `(a, b)` with `a ^ 2 + b ^ 4 ≤ x` is asymptotic to
`4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * x ^ (3/4)` with error `O(Real.sqrt x)`.

This is the integer counterpart of `card_sq_add_pow_four_natpairs_asymptotic`.  The exact
relation `card_intpairs_eq_four_mul_natpairs_sub` expresses the integer count as four times
the natural count minus a correction `2 * √x + 2 * x ^ (1/4) + 3` coming from the sign
choices of the two coordinates, and this correction is itself `O(Real.sqrt x)`.  Combining
this exact relation with the asymptotic for the natural count gives the stated bound. -/
lemma card_sq_add_pow_four_intpairs_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) -
        4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| ≤ C * Real.sqrt x := by
  obtain ⟨C0, hC0pos, hC0⟩ := card_sq_add_pow_four_natpairs_asymptotic
  refine ⟨4 * C0 + 8, by linarith, ?_⟩
  intro x hx
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set nZ : ℕ := ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard) with hnZdef
  set nN : ℕ := ({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard) with hnNdef
  set b : ℕ := 4 * nN with hbdef
  set c : ℕ := 2 * Nat.sqrt x + 2 * Nat.sqrt (Nat.sqrt x) + 3 with hcdef
  -- exact relation between the integer and natural counts
  have hcount : nZ = b - c := by
    rw [hbdef, hcdef, hnZdef, hnNdef, card_intpairs_eq_four_mul_natpairs_sub]
    omega
  -- the correction `c` is bounded by the (truncated) difference
  have ha_le_b : nZ ≤ b := by rw [hcount]; exact Nat.sub_le _ _
  have hb_le : b ≤ nZ + c := by
    have : b - c ≤ nZ := by rw [← hcount]
    exact Nat.sub_le_iff_le_add.mp this
  have habs : |(nZ : ℝ) - (b : ℝ)| ≤ (c : ℝ) := by
    have hle1 : (nZ : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha_le_b
    have hle2 : (b : ℝ) - (c : ℝ) ≤ (nZ : ℝ) := by
      have h : (b : ℝ) ≤ (nZ : ℝ) + (c : ℝ) := by exact_mod_cast hb_le
      linarith
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- asymptotic for the natural count
  have hnat : |(nN : ℝ) - (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ C0 * Real.sqrt (x : ℝ) := by
    rw [hnNdef]; exact hC0 x hx
  have hb_bnd :
      |(b : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ 4 * C0 * Real.sqrt (x : ℝ) := by
    have hb_eq : (b : ℝ) = 4 * (nN : ℝ) := by rw [hbdef]; push_cast; ring
    have key : (b : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)
        = 4 * ((nN : ℝ) -
            (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)) := by
      rw [hb_eq]; ring
    rw [key, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc 4 * |(nN : ℝ) - (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
        ≤ 4 * (C0 * Real.sqrt (x : ℝ)) := mul_le_mul_of_nonneg_left hnat (by norm_num)
      _ = 4 * C0 * Real.sqrt (x : ℝ) := by ring
  -- bound on the correction `c`
  have hsx : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc (Nat.sqrt x : ℝ) ^ 2 = ((Nat.sqrt x ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (x : ℝ) := by exact_mod_cast Nat.sqrt_le' x
  have hsxs : (Nat.sqrt (Nat.sqrt x) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have h1 : (Nat.sqrt (Nat.sqrt x) : ℝ) ≤ Real.sqrt (Nat.sqrt x : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc (Nat.sqrt (Nat.sqrt x) : ℝ) ^ 2
            = ((Nat.sqrt (Nat.sqrt x) ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (Nat.sqrt x : ℝ) := by exact_mod_cast Nat.sqrt_le' (Nat.sqrt x)
    have h2 : Real.sqrt (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le_self x)
    linarith
  have hc_bnd : (c : ℝ) ≤ 8 * Real.sqrt (x : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.one_le_sqrt.mpr hxR
    rw [hcdef]; push_cast
    nlinarith [hsx, hsxs, h1]
  -- triangle inequality and assembly
  have htri :
      |(nZ : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ |(nZ : ℝ) - (b : ℝ)|
        + |(b : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| := by
    have hsplit : (nZ : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)
        = ((nZ : ℝ) - (b : ℝ))
          + ((b : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  calc |(nZ : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ |(nZ : ℝ) - (b : ℝ)|
        + |(b : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| := htri
    _ ≤ (c : ℝ) + 4 * C0 * Real.sqrt (x : ℝ) := add_le_add habs hb_bnd
    _ ≤ 8 * Real.sqrt (x : ℝ) + 4 * C0 * Real.sqrt (x : ℝ) := add_le_add hc_bnd le_rfl
    _ = (4 * C0 + 8) * Real.sqrt (x : ℝ) := by ring

end Commons.NumberTheory.FriedlanderIwaniec
