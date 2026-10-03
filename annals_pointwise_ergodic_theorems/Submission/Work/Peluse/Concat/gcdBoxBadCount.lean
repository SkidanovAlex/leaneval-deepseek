import Mathlib

namespace Work.Peluse.Concat

open scoped BigOperators

/-!
## Counting the box points with a large coordinate gcd

For `M ≥ 1`, `T ≥ 1` we bound the number of lattice points `z` in the box `[-M,M]²` whose
coordinate gcd exceeds `T` by `36 M²/T`.

The argument is elementary.  If `z = (a,b)` lies in the box and `d = gcd a b > T`, then `d` divides
both coordinates, so `d` occurs as the gcd of `z`, and (as `d ∣ a` and `d ∣ b` with `d ≥ 1`) the
point `z` is a pair of multiples of `d` in `[-M,M]`.  Since `d ≤ M` (a divisor of a nonzero
coordinate, or the absolute value of the other coordinate), the bad points are the disjoint union,
over `d ∈ [⌈T⌉, M]`, of the fibres `{z : gcd z = d}`.  Each fibre has at most `(2⌊M/d⌋+1)²`
elements (division by `d` injects it into the box `[-⌊M/d⌋, ⌊M/d⌋]²`), and the resulting sum is
bounded by `9M² ∑_{d ≥ ⌈T⌉} d⁻² ≤ 18M²/⌈T⌉ ≤ 36M²/T`.
-/

/-- For `z` in the box `[-M,M]²` the gcd of the two coordinates is at most `M`. -/
lemma gcd_le_of_mem_box {M : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    Int.gcd z.1 z.2 ≤ M := by
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hz
  have h1 : |z.1| ≤ (M : ℤ) := abs_le.mpr ⟨hz.1.1, hz.1.2⟩
  have h2 : |z.2| ≤ (M : ℤ) := abs_le.mpr ⟨hz.2.1, hz.2.2⟩
  have h1' : z.1.natAbs ≤ M := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]; exact h1
  have h2' : z.2.natAbs ≤ M := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]; exact h2
  rw [Int.gcd_eq_natAbs]
  by_cases h : z.1.natAbs = 0
  · rw [h, Nat.gcd_zero_left]; exact h2'
  · exact (Nat.gcd_le_left _ (Nat.pos_of_ne_zero h)).trans h1'

/-- The number of integers in `[-M,M]` divisible by `d` is at most `2*(M/d)+1` (`d ≥ 1`). -/
lemma card_Icc_filter_dvd_le (M d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun a => (d : ℤ) ∣ a)).card ≤ 2 * (M / d) + 1 := by
  set m := M / d with hm
  have hsub : (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun a => (d : ℤ) ∣ a)
      ⊆ (Finset.Icc (-(m : ℤ)) (m : ℤ)).image (fun k => (d : ℤ) * k) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, ha2⟩, k, hk⟩ := ha
    rw [Finset.mem_image]
    refine ⟨k, ?_, hk.symm⟩
    rw [Finset.mem_Icc]
    have habs : |a| ≤ (M : ℤ) := abs_le.mpr ⟨ha1, ha2⟩
    have h1 : a.natAbs ≤ M := by
      rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]; exact habs
    have h2 : a.natAbs = d * k.natAbs := by
      rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
    have h3 : d * k.natAbs ≤ M := by rw [← h2]; exact h1
    have h4 : k.natAbs ≤ m := by
      rw [hm, Nat.le_div_iff_mul_le (by omega : 0 < d)]
      rw [mul_comm]; exact h3
    have h5 : |k| ≤ (m : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast h4
    exact abs_le.mp h5
  calc ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun a => (d : ℤ) ∣ a)).card
      ≤ ((Finset.Icc (-(m : ℤ)) (m : ℤ)).image (fun k => (d : ℤ) * k)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-(m : ℤ)) (m : ℤ)).card := Finset.card_image_le
    _ = 2 * m + 1 := by
        rw [Int.card_Icc]
        have h : (m : ℤ) + 1 - (-(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h, Int.toNat_natCast]
    _ = 2 * (M / d) + 1 := by rw [hm]

/-- Every pair in the box `[-M,M]²` with coordinate gcd `d` consists of two multiples of `d`, so
the fibre has at most `(2*(M/d)+1)²` elements. -/
lemma boxFiberGcdCardLe {M d : ℕ} (hd : 1 ≤ d) :
    (((Finset.Icc (-(M : ℤ)) (M : ℤ)) ×ˢ (Finset.Icc (-(M : ℤ)) (M : ℤ))).filter
      (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)).card ≤ (2 * (M / d) + 1) ^ 2 := by
  set S : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun a => (d : ℤ) ∣ a) with hS
  have hsub : (((Finset.Icc (-(M : ℤ)) (M : ℤ)) ×ˢ (Finset.Icc (-(M : ℤ)) (M : ℤ))).filter
      (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)) ⊆ S ×ˢ S := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨⟨hz1, hz2⟩, hg⟩ := hz
    rw [Finset.mem_product, hS, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨hz1, ?_⟩, ⟨hz2, ?_⟩⟩
    · have h : ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣ z.1 := Int.gcd_dvd_left z.1 z.2
      rwa [hg] at h
    · have h : ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣ z.2 := Int.gcd_dvd_right z.1 z.2
      rwa [hg] at h
  calc _ ≤ (S ×ˢ S).card := Finset.card_le_card hsub
    _ = S.card * S.card := Finset.card_product S S
    _ ≤ (2 * (M / d) + 1) * (2 * (M / d) + 1) :=
        Nat.mul_le_mul (card_Icc_filter_dvd_le M d hd) (card_Icc_filter_dvd_le M d hd)
    _ = (2 * (M / d) + 1) ^ 2 := by ring

/-- The harmonic sum over the fibre sizes: `∑_{d=E}^{M} (2⌊M/d⌋+1)² ≤ 36 M²/T` when `T ≤ E`. -/
lemma gcdBoxSumBound {M E : ℕ} {T : ℝ} (hM : 1 ≤ M) (hE1 : 1 ≤ E) (hT0 : 0 < T)
    (hTE : T ≤ (E : ℝ)) :
    (∑ d ∈ Finset.Icc E M, ((2 * (M / d) + 1 : ℕ) : ℝ) ^ 2) ≤ 36 * (M : ℝ) ^ 2 / T := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hEpos : (0 : ℝ) < E := by exact_mod_cast hE1
  have hharm : (∑ d ∈ Finset.Icc E M, ((d : ℝ) ^ 2)⁻¹) ≤ 2 / (E : ℝ) := by
    have hsub : Finset.Icc E M ⊆ Finset.Ioo (E - 1) (M + 1) := by
      intro e he
      simp only [Finset.mem_Icc] at he
      simp only [Finset.mem_Ioo]
      omega
    calc (∑ d ∈ Finset.Icc E M, ((d : ℝ) ^ 2)⁻¹)
        ≤ ∑ i ∈ Finset.Ioo (E - 1) (M + 1), ((i : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ ≤ 2 / (((E - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (E - 1) (M + 1)
      _ = 2 / (E : ℝ) := by
          have hc : ((E - 1 : ℕ) : ℝ) + 1 = (E : ℝ) := by
            rw [Nat.cast_sub hE1, Nat.cast_one]; ring
          rw [hc]
  have hstep : ∀ d ∈ Finset.Icc E M,
      ((2 * (M / d) + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < d := by
      have h : 0 < d := lt_of_lt_of_le (by omega : 0 < E) hd.1
      exact_mod_cast h
    have hdiv : 1 ≤ (M : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdpos]
      have : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast hd.2
      linarith
    have hcast : (((M / d : ℕ) : ℝ)) ≤ (M : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hle : ((2 * (M / d) + 1 : ℕ) : ℝ) ≤ 3 * ((M : ℝ) / (d : ℝ)) := by
      have h1 : ((2 * (M / d) + 1 : ℕ) : ℝ) = 2 * (((M / d : ℕ)) : ℝ) + 1 := by
        push_cast; ring
      rw [h1]
      linarith
    have hnn : (0 : ℝ) ≤ ((2 * (M / d) + 1 : ℕ) : ℝ) := by positivity
    calc ((2 * (M / d) + 1 : ℕ) : ℝ) ^ 2 ≤ (3 * ((M : ℝ) / (d : ℝ))) ^ 2 :=
          pow_le_pow_left₀ hnn hle 2
      _ = 9 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := by ring
  have hsum : (∑ d ∈ Finset.Icc E M, 9 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2)
      = 9 * (M : ℝ) ^ 2 * (∑ d ∈ Finset.Icc E M, ((d : ℝ) ^ 2)⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  calc (∑ d ∈ Finset.Icc E M, ((2 * (M / d) + 1 : ℕ) : ℝ) ^ 2)
      ≤ ∑ d ∈ Finset.Icc E M, 9 * (M : ℝ) ^ 2 / (d : ℝ) ^ 2 := Finset.sum_le_sum hstep
    _ = 9 * (M : ℝ) ^ 2 * (∑ d ∈ Finset.Icc E M, ((d : ℝ) ^ 2)⁻¹) := hsum
    _ ≤ 9 * (M : ℝ) ^ 2 * (2 / (E : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hharm; positivity
    _ ≤ 9 * (M : ℝ) ^ 2 * (2 / T) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) hT0 hTE
    _ = 18 * (M : ℝ) ^ 2 / T := by field_simp; ring
    _ ≤ 36 * (M : ℝ) ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
        linarith [sq_nonneg (M : ℝ)]

theorem gcdBoxBadCount {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 1 ≤ T) :
    ((Finset.filter (fun z : ℤ × ℤ => T < ((Int.gcd z.1 z.2 : ℕ) : ℝ))
        (Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)
      ≤ 36 * (M : ℝ) ^ 2 / T := by
  classical
  have hTpos : (0 : ℝ) < T := by linarith
  have hceilpos : 0 < ⌈T⌉₊ := Nat.ceil_pos.mpr hTpos
  have hE1 : 1 ≤ ⌈T⌉₊ := by omega
  have hTE : T ≤ ((⌈T⌉₊ : ℕ) : ℝ) := Nat.le_ceil T
  set B : Finset (ℤ × ℤ) :=
    Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ) with hB
  set Bad : Finset (ℤ × ℤ) :=
    B.filter (fun z : ℤ × ℤ => T < ((Int.gcd z.1 z.2 : ℕ) : ℝ)) with hBad
  have hfib : Bad.card
      = ∑ d ∈ Finset.Icc ⌈T⌉₊ M,
          (Bad.filter (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)).card := by
    refine Finset.card_eq_sum_card_fiberwise
      (f := fun z : ℤ × ℤ => Int.gcd z.1 z.2) (t := Finset.Icc ⌈T⌉₊ M) ?_
    intro z hz
    rw [Finset.mem_coe, Finset.mem_Icc]
    rw [Finset.mem_coe] at hz
    rw [hBad, Finset.mem_filter] at hz
    obtain ⟨hzB, hzg⟩ := hz
    rw [hB] at hzB
    exact ⟨Nat.ceil_le.mpr (le_of_lt hzg), gcd_le_of_mem_box hzB⟩
  have hfiber : ∀ d ∈ Finset.Icc ⌈T⌉₊ M,
      (Bad.filter (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)).card ≤ (2 * (M / d) + 1) ^ 2 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := le_trans hE1 hd.1
    calc (Bad.filter (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)).card
        ≤ (B.filter (fun z : ℤ × ℤ => Int.gcd z.1 z.2 = d)).card := by
          refine Finset.card_le_card ?_
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          rw [hBad, Finset.mem_filter] at hz
          exact ⟨hz.1.1, hz.2⟩
      _ ≤ (2 * (M / d) + 1) ^ 2 := by
          rw [hB]
          exact boxFiberGcdCardLe hd1
  have hmain : (Bad.card : ℝ)
      ≤ ∑ d ∈ Finset.Icc ⌈T⌉₊ M, ((2 * (M / d) + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hfib, Nat.cast_sum]
    exact Finset.sum_le_sum (fun d hd => by exact_mod_cast hfiber d hd)
  exact le_trans hmain (gcdBoxSumBound hM hE1 hTpos hTE)

end Work.Peluse.Concat
