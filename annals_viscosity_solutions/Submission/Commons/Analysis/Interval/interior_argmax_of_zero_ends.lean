import Mathlib.Analysis.Normed.Order.Lattice

open Set

namespace Commons.Analysis.Interval

theorem interior_argmax_of_zero_ends {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hpos : ∃ t ∈ Ioo a b, 0 < f t) :
    ∃ x₀ ∈ Ioo a b, (∀ y ∈ Icc a b, f y ≤ f x₀) ∧ f x₀ = sSup (f '' Ioo a b) := by
  -- `f` attains its maximum on the compact interval `[a,b]`.
  have hIcc_ne : (Icc a b : Set ℝ).Nonempty := ⟨a, ⟨le_rfl, hab.le⟩⟩
  have hcomp : IsCompact (Icc a b : Set ℝ) := isCompact_Icc
  obtain ⟨x₀, hx₀, hmax⟩ := hcomp.exists_isMaxOn hIcc_ne hf
  have hmax' : ∀ y ∈ Icc a b, f y ≤ f x₀ := isMaxOn_iff.mp hmax
  -- Since some interior value is positive, the maximum value is positive.
  obtain ⟨t, ht_ioo, hft⟩ := hpos
  have ht_icc : t ∈ Icc a b := Ioo_subset_Icc_self ht_ioo
  have hfx₀_pos : 0 < f x₀ := lt_of_lt_of_le hft (hmax' t ht_icc)
  -- ... hence the maximizer cannot be an endpoint, and lies in the interior.
  have hx₀_ne_a : x₀ ≠ a := by
    intro hEq
    have hlt : 0 < f a := by simpa [hEq] using hfx₀_pos
    linarith [hfa]
  have hx₀_ne_b : x₀ ≠ b := by
    intro hEq
    have hlt : 0 < f b := by simpa [hEq] using hfx₀_pos
    linarith [hfb]
  have hx₀_gt_a : a < x₀ := lt_of_le_of_ne' hx₀.1 hx₀_ne_a
  have hx₀_lt_b : x₀ < b := lt_of_le_of_ne hx₀.2 hx₀_ne_b
  have hx₀_ioo : x₀ ∈ Ioo a b := ⟨hx₀_gt_a, hx₀_lt_b⟩
  -- The image of the open interval is bounded above by `f x₀` ...
  have hmem : f x₀ ∈ f '' Ioo a b := mem_image_of_mem f hx₀_ioo
  have hbdd : BddAbove (f '' Ioo a b) := by
    refine ⟨f x₀, ?_⟩
    intro z hz
    rcases hz with ⟨y, hy_ioo, rfl⟩
    exact hmax' y (Ioo_subset_Icc_self hy_ioo)
  -- ... so the supremum of that image equals `f x₀`.
  have hsup_le : sSup (f '' Ioo a b) ≤ f x₀ := by
    exact csSup_le (by
      refine ⟨f x₀, ?_⟩
      exact mem_image_of_mem f hx₀_ioo) (by
      intro z hz
      rcases hz with ⟨y, hy_ioo, rfl⟩
      exact hmax' y (Ioo_subset_Icc_self hy_ioo))
  have hle_sup : f x₀ ≤ sSup (f '' Ioo a b) := le_csSup hbdd hmem
  refine ⟨x₀, hx₀_ioo, ⟨hmax', le_antisymm hle_sup hsup_le⟩⟩

end Commons.Analysis.Interval