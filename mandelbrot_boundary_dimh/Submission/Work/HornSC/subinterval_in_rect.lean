import Mathlib

namespace Work.HornSC

open Set

/-- Between a value below `X` at `0` and a value above `Y` at `1` (with `X < Y`), a continuous
real function attains `X` first and then `Y`, and stays inside the rectangle `[X,Y]` in between. -/
theorem subinterval_in_rect {f : ℝ → ℝ} (hf : Continuous f) {X Y : ℝ} (hXY : X < Y)
    (h0 : f 0 < X) (h1 : Y < f 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ f a = X ∧ f b = Y ∧
      ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc X Y := by
  have hX1 : X < f 1 := lt_trans hXY h1
  -- `a` is the last point of `[0,1]` where `f ≤ X`.
  obtain ⟨a, ha0, ha1, hfale, ha_max⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ f a ≤ X ∧
      ∀ t, 0 ≤ t → t ≤ 1 → f t ≤ X → t ≤ a := by
    have hcl : IsClosed (Set.Icc (0:ℝ) 1 ∩ {t : ℝ | f t ≤ X}) :=
      isClosed_Icc.inter (isClosed_le hf continuous_const)
    have hne : (Set.Icc (0:ℝ) 1 ∩ {t : ℝ | f t ≤ X}).Nonempty :=
      ⟨0, ⟨⟨le_rfl, zero_le_one⟩, h0.le⟩⟩
    have hbd : BddAbove (Set.Icc (0:ℝ) 1 ∩ {t : ℝ | f t ≤ X}) := ⟨1, fun t ht => ht.1.2⟩
    have hmem := IsClosed.csSup_mem hcl hne hbd
    exact ⟨sSup (Set.Icc (0:ℝ) 1 ∩ {t : ℝ | f t ≤ X}),
      le_csSup hbd ⟨⟨le_rfl, zero_le_one⟩, h0.le⟩, hmem.1.2, hmem.2,
      fun t ht0 ht1 hft => le_csSup hbd ⟨⟨ht0, ht1⟩, hft⟩⟩
  -- `b` is the first point of `[a,1]` where `f ≥ Y`.
  obtain ⟨b, hab, hb1, hYfb, hb_min⟩ : ∃ b : ℝ, a ≤ b ∧ b ≤ 1 ∧ Y ≤ f b ∧
      ∀ t, a ≤ t → t ≤ 1 → Y ≤ f t → b ≤ t := by
    have hcl : IsClosed (Set.Icc a 1 ∩ {t : ℝ | Y ≤ f t}) :=
      isClosed_Icc.inter (isClosed_le continuous_const hf)
    have hne : (Set.Icc a 1 ∩ {t : ℝ | Y ≤ f t}).Nonempty :=
      ⟨1, ⟨⟨ha1, le_rfl⟩, h1.le⟩⟩
    have hbd : BddBelow (Set.Icc a 1 ∩ {t : ℝ | Y ≤ f t}) := ⟨a, fun t ht => ht.1.1⟩
    have hmem := IsClosed.csInf_mem hcl hne hbd
    exact ⟨sInf (Set.Icc a 1 ∩ {t : ℝ | Y ≤ f t}), hmem.1.1, hmem.1.2, hmem.2,
      fun t ha ha1' hY => csInf_le hbd ⟨⟨ha, ha1'⟩, hY⟩⟩
  -- `a` is an actual crossing point: `f a = X`.
  have hfaX : f a = X := by
    refine le_antisymm hfale ?_
    by_contra hnot
    have hlt : f a < X := lt_of_not_ge hnot
    obtain ⟨s, hsIoo, hsX⟩ :=
      (intermediate_value_Ioo ha1 hf.continuousOn)
        (show X ∈ Set.Ioo (f a) (f 1) from ⟨hlt, hX1⟩)
    have hsle : s ≤ a := ha_max s (le_trans ha0 hsIoo.1.le) hsIoo.2.le (le_of_eq hsX)
    exact absurd hsle (not_le.mpr hsIoo.1)
  -- `b` is an actual crossing point: `f b = Y`.
  have hfbY : f b = Y := by
    refine le_antisymm ?_ hYfb
    by_contra hnot
    have hlt : Y < f b := lt_of_not_ge hnot
    obtain ⟨s, hsIoo, hsY⟩ :=
      (intermediate_value_Ioo hab hf.continuousOn)
        (show Y ∈ Set.Ioo (f a) (f b) from ⟨by rw [hfaX]; exact hXY, hlt⟩)
    have hsge : b ≤ s := hb_min s hsIoo.1.le (le_trans hsIoo.2.le hb1) (le_of_eq hsY.symm)
    exact absurd hsge (not_le.mpr hsIoo.2)
  refine ⟨a, b, ha0, hab, hb1, hfaX, hfbY, ?_⟩
  -- the rectangle condition
  intro t ht
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hle : f t ≤ X := (lt_of_not_ge hnot).le
    have hta : t ≤ a := ha_max t (le_trans ha0 ht.1) (le_trans ht.2 hb1) hle
    have hEq : t = a := le_antisymm hta ht.1
    rw [hEq, hfaX] at hnot
    exact hnot le_rfl
  · by_contra hnot
    have hle : Y ≤ f t := (lt_of_not_ge hnot).le
    have hbt : b ≤ t := hb_min t ht.1 (le_trans ht.2 hb1) hle
    have hEq : t = b := le_antisymm ht.2 hbt
    rw [hEq, hfbY] at hnot
    exact hnot le_rfl

end Work.HornSC
