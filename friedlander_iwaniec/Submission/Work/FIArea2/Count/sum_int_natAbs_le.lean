import Mathlib

namespace Work.FIArea2.Count

/-- The sum over nonzero `u ∈ [-R,R]` of a nonnegative function of `|u|` is at most twice the
sum over `a ∈ [1,R]`. -/
theorem sum_int_natAbs_le (R : ℕ) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) :
    (∑ u ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => u ≠ 0), h u.natAbs)
      ≤ 2 * ∑ a ∈ Finset.Icc 1 R, h a := by
  set S : Finset ℤ := (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => u ≠ 0) with hS
  -- Every nonzero `u ∈ [-R,R]` has `u.natAbs ∈ [1,R]`.
  have hmap : ∀ u ∈ S, u.natAbs ∈ Finset.Icc 1 R := by
    intro u hu
    rw [hS] at hu
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hge, hle⟩, hne⟩ := hu
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hpos : 0 < u.natAbs := by rwa [Int.natAbs_pos]
      omega
    · have habs : |u| ≤ (R : ℤ) := abs_le.mpr ⟨hge, hle⟩
      have h2 : (u.natAbs : ℤ) ≤ (R : ℤ) := by rw [Int.natCast_natAbs]; exact habs
      exact_mod_cast h2
  -- Decompose the sum into fibers of `u ↦ u.natAbs`.
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun u => h u.natAbs)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  -- Each fiber over `a` is contained in `{a, -a}`, hence has at most two elements.
  have hfiber_sub : (S.filter (fun u => u.natAbs = a)) ⊆ ({(a : ℤ), -((a : ℤ))} : Finset ℤ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, hnat⟩ := hu
    rw [Finset.mem_insert, Finset.mem_singleton]
    rw [Int.natAbs_eq_iff] at hnat
    exact hnat
  have hcard : (S.filter (fun u => u.natAbs = a)).card ≤ 2 :=
    le_trans (Finset.card_le_card hfiber_sub) Finset.card_le_two
  -- On the fiber the summand is constantly `h a`.
  have hsum : ∑ u ∈ S.filter (fun u => u.natAbs = a), h u.natAbs
      = (S.filter (fun u => u.natAbs = a)).card • h a := by
    have h1 : ∑ u ∈ S.filter (fun u => u.natAbs = a), h u.natAbs
        = ∑ u ∈ S.filter (fun u => u.natAbs = a), h a :=
      Finset.sum_congr rfl (fun u hu => by
        have := (Finset.mem_filter.mp hu).2
        rw [this])
    rw [h1, Finset.sum_const]
  rw [hsum, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hh a)
  exact_mod_cast hcard

end Work.FIArea2.Count
