import Mathlib
import Submission.Work.Analysis.InverseTheory.calc_of_decay

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-!
# The weighted lattice sum `∑_u ε ⟨ε u⟩^{-12} |u| ≤ 2 ^ 61 / ε`

This is the lattice (integer) companion of the "absolute moment" estimate for the smoothing
weight of Proposition `lip` of Krause--Mirek--Tao (§5, the alternate inverse theorem for `f`):
the weight `w(m) = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε (m - m'))` has an `ℓ¹` *first moment*
`∑_m ‖w(m)‖ |m - m₀|` which is `O(1/ε)` uniformly in `0 < ε ≤ 1`; the first moment of the
lattice factor `⟨εm⟩^{-12}` is the sum bounded here.

The two ingredients are

* the pointwise absorption `⟨t⟩^{-12} |t| ≤ ⟨t⟩^{-11}` (the factor `|t|` is eaten by one power of
  the bracket), so that the *weighted* sum is dominated by the *unweighted* sum at exponent `11`;
* `riemann_shift` at `n = 10`, which bounds the two one-sided sums
  `∑_{k ≥ 0} ε ⟨ε k⟩^{-11} ≤ 2 ^ 60` (at `t = 0`) and `∑_{k ≥ 0} ε ⟨ε (k+1)⟩^{-11} ≤ 2 ^ 60`
  (at `t = ε`); splitting `ℤ` into its two half-lines (`tsum_of_nat_of_neg_add_one`) gives twice
  that, i.e. `2 ^ 61 / ε`.

The constants are absurdly generous, as everywhere in this chapter of the paper.
-/

/-- One power of the bracket absorbs the factor `|t|`: `⟨t⟩^{-12} |t| ≤ ⟨t⟩^{-11}`. -/
theorem jbDecay_twelve_mul_abs_le_eleven (t : ℝ) :
    jbDecay 12 t * |t| ≤ jbDecay 11 t := by
  have hdec : jbDecay 12 t = jbDecay 11 t * (jb t)⁻¹ := by
    rw [jbDecay, jbDecay, show (12 : ℕ) = 11 + 1 by norm_num, pow_succ]
  have hkey : (jb t)⁻¹ * |t| ≤ 1 := by
    rw [inv_mul_le_iff₀ (jb_pos t), mul_one]
    exact abs_le_jb t
  calc jbDecay 12 t * |t| = jbDecay 11 t * ((jb t)⁻¹ * |t|) := by rw [hdec]; ring
    _ ≤ jbDecay 11 t * 1 := mul_le_mul_of_nonneg_left hkey (jbDecay_nonneg 11 t)
    _ = jbDecay 11 t := mul_one _

/-- `k ↦ ⟨ε k⟩^{-11}` is summable on `ℕ` (comparison with `(k+1)^{-11}`). -/
theorem summable_jbDecay_eleven_nat {ε : ℝ} (hε0 : 0 < ε) :
    Summable (fun k : ℕ => jbDecay 11 (ε * (k : ℝ))) := by
  set C : ℝ := max 1 (ε⁻¹ ^ 11 * 2 ^ 11) with hC
  have hbase : Summable (fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 11) := by
    have h1 : Summable (fun k : ℕ => 1 / ((k : ℝ)) ^ 11) :=
      (Real.summable_one_div_nat_pow (p := 11)).mpr (by norm_num)
    have h2 : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)) ^ 11) :=
      (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ)) ^ 11) 1).mpr h1
    refine h2.congr (fun k => ?_)
    push_cast
    rw [one_div, inv_pow]
  refine Summable.of_nonneg_of_le (g := fun k : ℕ => jbDecay 11 (ε * (k : ℝ)))
    (f := fun k : ℕ => C * (((k : ℝ) + 1)⁻¹) ^ 11) (fun k => jbDecay_nonneg 11 _)
    (fun k => ?_) (hbase.mul_left C)
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hC2 : ε⁻¹ ^ 11 * 2 ^ 11 ≤ C := le_max_right _ _
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, mul_zero]
    have h0 : jbDecay 11 (0 : ℝ) = 1 := by simp [jbDecay, jb]
    rw [h0, show (((0 : ℝ) + 1)⁻¹) ^ 11 = 1 by norm_num, mul_one]
    exact hC1
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
    have hek : 0 < ε * (k : ℝ) := mul_pos hε0 hkpos
    have hstep1 : (jb (ε * (k : ℝ)))⁻¹ ≤ (ε * (k : ℝ))⁻¹ := by
      rw [inv_le_inv₀ (jb_pos _) hek]
      calc ε * (k : ℝ) = |ε * (k : ℝ)| := (abs_of_pos hek).symm
        _ ≤ jb (ε * (k : ℝ)) := abs_le_jb _
    have hstep2 : jbDecay 11 (ε * (k : ℝ)) ≤ (ε * (k : ℝ))⁻¹ ^ 11 := by
      rw [jbDecay]
      exact pow_le_pow_left₀ (jb_inv_nonneg _) hstep1 11
    have hstep3 : (ε * (k : ℝ))⁻¹ ^ 11 = ε⁻¹ ^ 11 * ((k : ℝ)⁻¹) ^ 11 := by
      rw [mul_inv, mul_pow]
    have h2 : (k : ℝ)⁻¹ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
      rw [inv_eq_one_div]
      rw [show (2 : ℝ) * ((k : ℝ) + 1)⁻¹ = 2 / ((k : ℝ) + 1) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hkpos (by positivity)]
      linarith
    have hstep4 : ((k : ℝ)⁻¹) ^ 11 ≤ 2 ^ 11 * (((k : ℝ) + 1)⁻¹) ^ 11 := by
      calc ((k : ℝ)⁻¹) ^ 11 ≤ (2 * ((k : ℝ) + 1)⁻¹) ^ 11 :=
            pow_le_pow_left₀ (by positivity) h2 11
        _ = 2 ^ 11 * (((k : ℝ) + 1)⁻¹) ^ 11 := by rw [mul_pow]
    calc jbDecay 11 (ε * (k : ℝ)) ≤ (ε * (k : ℝ))⁻¹ ^ 11 := hstep2
      _ = ε⁻¹ ^ 11 * ((k : ℝ)⁻¹) ^ 11 := hstep3
      _ ≤ ε⁻¹ ^ 11 * (2 ^ 11 * (((k : ℝ) + 1)⁻¹) ^ 11) :=
            mul_le_mul_of_nonneg_left hstep4 (by positivity)
      _ = (ε⁻¹ ^ 11 * 2 ^ 11) * (((k : ℝ) + 1)⁻¹) ^ 11 := by ring
      _ ≤ C * (((k : ℝ) + 1)⁻¹) ^ 11 :=
            mul_le_mul_of_nonneg_right hC2 (by positivity)

/-- The weighted lattice summand is dominated by the plain decay `⟨ε u⟩^{-11}`. -/
theorem eps_jbDecay_twelve_mul_abs_le_eleven {ε : ℝ} (hε0 : 0 < ε) (u : ℤ) :
    ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)| ≤ jbDecay 11 (ε * (u : ℝ)) := by
  have habs : |ε * (u : ℝ)| = ε * |(u : ℝ)| := by rw [abs_mul, abs_of_pos hε0]
  calc ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)|
      = jbDecay 12 (ε * (u : ℝ)) * (ε * |(u : ℝ)|) := by ring
    _ = jbDecay 12 (ε * (u : ℝ)) * |ε * (u : ℝ)| := by rw [habs]
    _ ≤ jbDecay 11 (ε * (u : ℝ)) := jbDecay_twelve_mul_abs_le_eleven _

/-- The `ℤ`-lattice sum of `⟨ε u⟩^{-11}` is `≤ 2 ^ 61 / ε`, uniformly for `0 < ε ≤ 1`.

The two half-lines are bounded by `riemann_shift` at `n = 10` (`t = 0` and `t = ε`); the negative
half-line is identified with the `k + 1` half-line by evenness of the bracket. -/
theorem tsum_jbDecay_eleven_int_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∑' u : ℤ, jbDecay 11 (ε * (u : ℝ)) ≤ (2 : ℝ) ^ 61 / ε := by
  have h1 : Summable (fun k : ℕ => jbDecay 11 (ε * (k : ℝ))) :=
    summable_jbDecay_eleven_nat hε0
  have hhalf1 : (∑' k : ℕ, jbDecay 11 (ε * (k : ℝ))) ≤ (2 : ℝ) ^ 60 / ε := by
    have hr := riemann_shift 10 (by norm_num) hε0 hε1 (le_refl (0 : ℝ))
    have hbridge : (∑' k : ℕ, ε * jbDecay 11 (ε * (k : ℝ)))
        = ∑' k : ℕ, ε * jbDecay (10 + 1) (0 + ε * (k : ℝ)) := by
      refine tsum_congr fun k => ?_
      rw [zero_add]
    have hB : (2 : ℝ) ^ 60 * jbDecay 10 (0 : ℝ) = (2 : ℝ) ^ 60 := by
      rw [show jbDecay 10 (0 : ℝ) = 1 by simp [jbDecay, jb], mul_one]
    have hmain : (∑' k : ℕ, ε * jbDecay 11 (ε * (k : ℝ))) ≤ (2 : ℝ) ^ 60 :=
      calc _ = ∑' k : ℕ, ε * jbDecay (10 + 1) (0 + ε * (k : ℝ)) := hbridge
        _ ≤ (2 : ℝ) ^ 60 * jbDecay 10 (0 : ℝ) := hr
        _ = (2 : ℝ) ^ 60 := hB
    have hmain2 : ε * (∑' k : ℕ, jbDecay 11 (ε * (k : ℝ))) ≤ (2 : ℝ) ^ 60 := by
      rw [← tsum_mul_left]
      exact hmain
    rw [le_div_iff₀ hε0]
    linarith
  have h2 : Summable (fun k : ℕ => jbDecay 11 (ε * (↑(-(k + 1) : ℤ) : ℝ))) := by
    have hs : Summable (fun k : ℕ => jbDecay 11 (ε * (((k + 1 : ℕ)) : ℝ))) :=
      (summable_nat_add_iff (f := fun m : ℕ => jbDecay 11 (ε * (m : ℝ))) 1).mpr
        (summable_jbDecay_eleven_nat hε0)
    refine hs.congr (fun k => ?_)
    have hcast : (ε : ℝ) * (↑(-(k + 1) : ℤ) : ℝ) = -(ε * (((k + 1 : ℕ)) : ℝ)) := by
      push_cast; ring
    rw [hcast, jbDecay_neg]
  have hhalf2 : (∑' k : ℕ, jbDecay 11 (ε * (↑(-(k + 1) : ℤ) : ℝ))) ≤ (2 : ℝ) ^ 60 / ε := by
    have hr := riemann_shift 10 (by norm_num) hε0 hε1 hε0.le
    have hbridge1 : (∑' k : ℕ, ε * jbDecay 11 (ε + ε * (k : ℝ)))
        = ∑' k : ℕ, ε * jbDecay 11 (ε * (↑(k + 1 : ℕ) : ℝ)) := by
      refine tsum_congr fun k => ?_
      rw [show ε * (↑(k + 1 : ℕ) : ℝ) = ε + ε * (k : ℝ) from by push_cast; ring]
    have hbridge2 : (∑' k : ℕ, jbDecay 11 (ε * (↑(-(k + 1) : ℤ) : ℝ)))
        = ∑' k : ℕ, jbDecay 11 (ε * (↑(k + 1 : ℕ) : ℝ)) := by
      refine tsum_congr fun k => ?_
      have hcast : (ε : ℝ) * (↑(-(k + 1) : ℤ) : ℝ) = -(ε * (↑(k + 1 : ℕ) : ℝ)) := by
        push_cast; ring
      rw [hcast, jbDecay_neg]
    have hB : (2 : ℝ) ^ 60 * jbDecay 10 ε ≤ (2 : ℝ) ^ 60 := by
      calc (2 : ℝ) ^ 60 * jbDecay 10 ε ≤ (2 : ℝ) ^ 60 * 1 :=
            mul_le_mul_of_nonneg_left (jbDecay_le_one 10 ε) (by positivity)
        _ = (2 : ℝ) ^ 60 := mul_one _
    have hmain : (∑' k : ℕ, ε * jbDecay 11 (ε * (↑(k + 1 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ 60 :=
      calc _ = ∑' k : ℕ, ε * jbDecay 11 (ε + ε * (k : ℝ)) := hbridge1.symm
        _ ≤ (2 : ℝ) ^ 60 * jbDecay 10 ε := hr
        _ ≤ (2 : ℝ) ^ 60 := hB
    have hmain2 : ε * (∑' k : ℕ, jbDecay 11 (ε * (↑(k + 1 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ 60 := by
      rw [← tsum_mul_left]
      exact hmain
    rw [hbridge2]
    rw [le_div_iff₀ hε0]
    linarith
  calc ∑' u : ℤ, jbDecay 11 (ε * (u : ℝ))
      = (∑' k : ℕ, jbDecay 11 (ε * (k : ℝ)))
        + (∑' k : ℕ, jbDecay 11 (ε * (↑(-(k + 1) : ℤ) : ℝ))) :=
        tsum_of_nat_of_neg_add_one (f := fun u : ℤ => jbDecay 11 (ε * (u : ℝ))) h1 h2
    _ ≤ (2 : ℝ) ^ 60 / ε + (2 : ℝ) ^ 60 / ε := add_le_add hhalf1 hhalf2
    _ = (2 : ℝ) ^ 61 / ε := by rw [← add_div]; norm_num

theorem lipWeightAbsMomentLattice {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∑' u : ℤ, ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((u : ℤ) : ℝ)) * |((u : ℤ) : ℝ)| ≤ (2 : ℝ) ^ 61 / ε := by
  have h1 : Summable (fun k : ℕ => jbDecay 11 (ε * (k : ℝ))) :=
    summable_jbDecay_eleven_nat hε0
  have h2 : Summable (fun k : ℕ => jbDecay 11 (ε * (↑(-(k + 1) : ℤ) : ℝ))) := by
    have hs : Summable (fun k : ℕ => jbDecay 11 (ε * (((k + 1 : ℕ)) : ℝ))) :=
      (summable_nat_add_iff (f := fun m : ℕ => jbDecay 11 (ε * (m : ℝ))) 1).mpr
        (summable_jbDecay_eleven_nat hε0)
    refine hs.congr (fun k => ?_)
    have hcast : (ε : ℝ) * (↑(-(k + 1) : ℤ) : ℝ) = -(ε * (((k + 1 : ℕ)) : ℝ)) := by
      push_cast; ring
    rw [hcast, jbDecay_neg]
  have hg : Summable (fun u : ℤ => jbDecay 11 (ε * (u : ℝ))) :=
    Summable.of_nat_of_neg_add_one (f := fun u : ℤ => jbDecay 11 (ε * (u : ℝ))) h1 h2
  have hpt : ∀ u : ℤ,
      ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)| ≤ jbDecay 11 (ε * (u : ℝ)) :=
    fun u => eps_jbDecay_twelve_mul_abs_le_eleven hε0 u
  refine (Summable.tsum_le_tsum hpt ?_ hg).trans (tsum_jbDecay_eleven_int_le hε0 hε1)
  exact Summable.of_nonneg_of_le (f := fun u : ℤ => jbDecay 11 (ε * (u : ℝ)))
    (fun u => mul_nonneg (mul_nonneg hε0.le (jbDecay_nonneg 12 _)) (abs_nonneg _)) hpt hg

end Work.KMTAreas.A4
