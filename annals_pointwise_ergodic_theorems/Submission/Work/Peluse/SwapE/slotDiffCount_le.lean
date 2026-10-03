import Mathlib
import Submission.Work.Peluse.SwapE.slotDensityAux

namespace Work.Peluse.SwapE

/-- The solutions of `a X - b Y = n` in a box, for `a` and `b` coprime, form a subset of an
arithmetic progression of step `(b, a)`: any two of them differ by `(b t, a t)`.  In particular
the parameter `t` is bounded by `2K / max |a| |b|`, which gives the counting bound. -/
theorem slotDiffCount_le (a b : ℤ) (K : ℕ) (n : ℤ)
    (hab : IsCoprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (slotDiffCount a b K n : ℝ) ≤ 4 * (K : ℝ) / max |(a : ℝ)| |(b : ℝ)| + 1 := by
  set M : ℝ := max |(a : ℝ)| |(b : ℝ)| with hMdef
  set c : ℝ := 2 * (K : ℝ) / M with hcdef
  have hMpos : 0 < M := by
    have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (Int.one_le_abs ha : (1 : ℤ) ≤ |a|)
    have h2 : (1 : ℝ) ≤ M := le_trans h1 (le_max_left _ _)
    linarith
  have hcnonneg : 0 ≤ c := by rw [hcdef]; positivity
  by_cases hne : (slotDiffSet a b K n).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    -- every solution differs from `p₀` by an integer multiple of the primitive direction
    have hparam : ∀ p ∈ slotDiffSet a b K n,
        ∃ t : ℤ, p.2 - p₀.2 = a * t ∧ p.1 - p₀.1 = b * t := by
      intro p hp
      have hp_eq : a * p.1 - b * p.2 = n := (mem_slotDiffSet.mp hp).2.2
      have hq_eq : a * p₀.1 - b * p₀.2 = n := (mem_slotDiffSet.mp hp₀).2.2
      have heq : a * (p.1 - p₀.1) = b * (p.2 - p₀.2) := by linarith
      have hdvd : a ∣ p.2 - p₀.2 := hab.dvd_of_dvd_mul_left ⟨p.1 - p₀.1, heq.symm⟩
      obtain ⟨t, ht⟩ := hdvd
      refine ⟨t, ht, ?_⟩
      rw [ht] at heq
      exact mul_left_cancel₀ ha (by rw [heq]; ring)
    -- the parameter of a solution
    let tm : ℤ × ℤ → ℤ := fun p => (p.2 - p₀.2) / a
    have htm_eq : ∀ p ∈ slotDiffSet a b K n, a * tm p = p.2 - p₀.2 := by
      intro p hp
      obtain ⟨t, ht, _⟩ := hparam p hp
      exact Int.mul_ediv_cancel' ⟨t, ht⟩
    have htm1 : ∀ p ∈ slotDiffSet a b K n, b * tm p = p.1 - p₀.1 := by
      intro p hp
      obtain ⟨t, ht2, ht1⟩ := hparam p hp
      have hteq : tm p = t := mul_left_cancel₀ ha (by rw [htm_eq p hp, ht2])
      rw [hteq, ht1]
    -- first-coordinate displacement is bounded by `2K`
    have hc1 : ∀ p ∈ slotDiffSet a b K n,
        |((p.1 - p₀.1 : ℤ) : ℝ)| ≤ 2 * (K : ℝ) := by
      intro p hp
      have hp1 : p.1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (mem_slotDiffSet.mp hp).1
      have hq1 : p₀.1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (mem_slotDiffSet.mp hp₀).1
      rw [Finset.mem_Icc] at hp1 hq1
      have b1 : |(p.1 : ℝ)| ≤ (K : ℝ) := by
        rw [abs_le]; exact ⟨by exact_mod_cast hp1.1, by exact_mod_cast hp1.2⟩
      have b2 : |(p₀.1 : ℝ)| ≤ (K : ℝ) := by
        rw [abs_le]; exact ⟨by exact_mod_cast hq1.1, by exact_mod_cast hq1.2⟩
      calc |((p.1 - p₀.1 : ℤ) : ℝ)| = |(p.1 : ℝ) - (p₀.1 : ℝ)| := by rw [Int.cast_sub]
        _ ≤ |(p.1 : ℝ)| + |(p₀.1 : ℝ)| := by simpa using abs_sub_le (p.1 : ℝ) 0 (p₀.1 : ℝ)
        _ ≤ (K : ℝ) + (K : ℝ) := add_le_add b1 b2
        _ = 2 * (K : ℝ) := by ring
    have hc2 : ∀ p ∈ slotDiffSet a b K n,
        |((p.2 - p₀.2 : ℤ) : ℝ)| ≤ 2 * (K : ℝ) := by
      intro p hp
      have hp2 : p.2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (mem_slotDiffSet.mp hp).2.1
      have hq2 : p₀.2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := (mem_slotDiffSet.mp hp₀).2.1
      rw [Finset.mem_Icc] at hp2 hq2
      have b1 : |(p.2 : ℝ)| ≤ (K : ℝ) := by
        rw [abs_le]; exact ⟨by exact_mod_cast hp2.1, by exact_mod_cast hp2.2⟩
      have b2 : |(p₀.2 : ℝ)| ≤ (K : ℝ) := by
        rw [abs_le]; exact ⟨by exact_mod_cast hq2.1, by exact_mod_cast hq2.2⟩
      calc |((p.2 - p₀.2 : ℤ) : ℝ)| = |(p.2 : ℝ) - (p₀.2 : ℝ)| := by rw [Int.cast_sub]
        _ ≤ |(p.2 : ℝ)| + |(p₀.2 : ℝ)| := by simpa using abs_sub_le (p.2 : ℝ) 0 (p₀.2 : ℝ)
        _ ≤ (K : ℝ) + (K : ℝ) := add_le_add b1 b2
        _ = 2 * (K : ℝ) := by ring
    -- the parameter is bounded by `c`
    have habs : ∀ p ∈ slotDiffSet a b K n, |((tm p : ℤ) : ℝ)| ≤ c := by
      intro p hp
      have hA : |((tm p : ℤ) : ℝ)| * |(a : ℝ)| ≤ 2 * (K : ℝ) := by
        rw [← abs_mul]
        have hcast : ((tm p : ℤ) : ℝ) * (a : ℝ) = ((p.2 - p₀.2 : ℤ) : ℝ) := by
          rw [← Int.cast_mul, show tm p * a = p.2 - p₀.2 by rw [mul_comm, htm_eq p hp]]
        rw [hcast]
        exact hc2 p hp
      have hB : |((tm p : ℤ) : ℝ)| * |(b : ℝ)| ≤ 2 * (K : ℝ) := by
        rw [← abs_mul]
        have hcast : ((tm p : ℤ) : ℝ) * (b : ℝ) = ((p.1 - p₀.1 : ℤ) : ℝ) := by
          rw [← Int.cast_mul, show tm p * b = p.1 - p₀.1 by rw [mul_comm, htm1 p hp]]
        rw [hcast]
        exact hc1 p hp
      have hMle : |((tm p : ℤ) : ℝ)| * M ≤ 2 * (K : ℝ) := by
        have hmax : |((tm p : ℤ) : ℝ)| * M
            = max (|((tm p : ℤ) : ℝ)| * |(a : ℝ)|) (|((tm p : ℤ) : ℝ)| * |(b : ℝ)|) := by
          rw [hMdef]
          exact mul_max_of_nonneg (|(a : ℝ)|) (|(b : ℝ)|) (abs_nonneg _)
        rw [hmax]
        exact max_le hA hB
      rw [hcdef, le_div_iff₀ hMpos]
      exact hMle
    -- the parameter map is injective on the solution set
    have hinj : Set.InjOn tm ↑(slotDiffSet a b K n) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe] at hp hq
      have h2eq : p.2 = q.2 := by
        have h1 := htm_eq p hp
        have h2 := htm_eq q hq
        rw [hpq] at h1
        linarith
      have h1eq : p.1 = q.1 := by
        have hp_eq : a * p.1 - b * p.2 = n := (mem_slotDiffSet.mp hp).2.2
        have hq_eq : a * q.1 - b * q.2 = n := (mem_slotDiffSet.mp hq).2.2
        have : a * p.1 = a * q.1 := by rw [h2eq] at hp_eq; linarith
        exact mul_left_cancel₀ ha this
      exact Prod.ext h1eq h2eq
    have hmaps : Set.MapsTo tm ↑(slotDiffSet a b K n)
        ↑(Finset.Icc (-(Int.floor c)) (Int.floor c)) := by
      intro p hp
      rw [Finset.mem_coe] at hp
      rw [Finset.mem_coe, Finset.mem_Icc]
      have hb' := habs p hp
      rw [abs_le] at hb'
      refine ⟨?_, Int.le_floor.mpr hb'.2⟩
      have h2 : ((-tm p : ℤ) : ℝ) ≤ c := by
        rw [Int.cast_neg]; linarith [hb'.1]
      have := Int.le_floor.mpr h2
      omega
    have hcard_le : (slotDiffSet a b K n).card
        ≤ (Finset.Icc (-(Int.floor c)) (Int.floor c)).card :=
      Finset.card_le_card_of_injOn tm hmaps hinj
    have hIcc : ((Finset.Icc (-(Int.floor c)) (Int.floor c)).card : ℝ) ≤ 2 * c + 1 := by
      rw [Int.card_Icc]
      have hfl : (0 : ℤ) ≤ Int.floor c := Int.floor_nonneg.mpr hcnonneg
      have heq : Int.floor c + 1 - -(Int.floor c) = 2 * Int.floor c + 1 := by ring
      rw [heq]
      have hnn : (0 : ℤ) ≤ 2 * Int.floor c + 1 := by linarith
      have hcast : (((2 * Int.floor c + 1 : ℤ)).toNat : ℝ) = ((2 * Int.floor c + 1 : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      rw [hcast]
      push_cast
      have := Int.floor_le c
      linarith
    have hmain : (slotDiffCount a b K n : ℝ) ≤ 2 * c + 1 := by
      rw [slotDiffCount]
      calc ((slotDiffSet a b K n).card : ℝ)
          ≤ ((Finset.Icc (-(Int.floor c)) (Int.floor c)).card : ℝ) := by
            exact_mod_cast hcard_le
        _ ≤ 2 * c + 1 := hIcc
    have hcm : 2 * c + 1 = 4 * (K : ℝ) / max |(a : ℝ)| |(b : ℝ)| + 1 := by
      rw [hcdef, hMdef]; ring
    linarith [hmain, hcm.le, hcm.ge]
  · have hempty : slotDiffSet a b K n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : slotDiffCount a b K n = 0 := by rw [slotDiffCount, hempty, Finset.card_empty]
    rw [hzero]
    push_cast
    have : (0 : ℝ) ≤ 4 * (K : ℝ) / max |(a : ℝ)| |(b : ℝ)| := by
      rw [div_nonneg_iff]
      exact Or.inl ⟨by positivity, le_trans (abs_nonneg _) (le_max_left _ _)⟩
    linarith

end Work.Peluse.SwapE
