import Mathlib.Analysis.Normed.Order.Lattice

open Set

namespace Commons.Topology.Order

/-- **Last crossing lemma.** If `f` is continuous on `[a, b]` with `f a < y` and `y < f b`,
then there is a *last* point `s ∈ [a, b]` at which `f` crosses the level `y`: `f s = y`
and `y ≤ f t` for every `t ∈ [s, b]`. -/
theorem exists_last_crossing {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {y : ℝ} (hlt : f a < y) (hgt : y < f b) :
    ∃ s ∈ Set.Icc a b, f s = y ∧ ∀ t ∈ Set.Icc s b, y ≤ f t := by
  -- The set of points of `[a, b]` where `f` has not yet crossed the level `y` (in the
  -- non-strict sense). `sSup A` is the last crossing.
  set A : Set ℝ := Set.Icc a b ∩ f ⁻¹' Set.Iic y with hA
  have hAne : A.Nonempty := ⟨a, left_mem_Icc.mpr hab, le_of_lt hlt⟩
  have hAbdd : BddAbove A := ⟨b, fun x hx => hx.1.2⟩
  have hAclosed : IsClosed A := by
    rw [hA]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsmem : sSup A ∈ A := hAclosed.csSup_mem hAne hAbdd
  have hsIcc : sSup A ∈ Set.Icc a b := hsmem.1
  have hsle : f (sSup A) ≤ y := hsmem.2
  -- `f (sSup A) ≥ y`: otherwise continuity gives a slightly larger point still in `A`.
  have hgte : y ≤ f (sSup A) := by
    by_contra hcon
    have hcon' : f (sSup A) < y := lt_of_not_ge hcon
    have hεpos : 0 < y - f (sSup A) := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
      (hf.continuousWithinAt hsIcc) (y - f (sSup A)) hεpos
    -- a point `t` strictly between `sSup A` and `b`, and within `δ` of `sSup A`.
    have hbgt : sSup A < b := by
      rcases lt_or_eq_of_le hsIcc.2 with h | h
      · exact h
      · exfalso; rw [h] at hsle; linarith
    set m : ℝ := min (δ / 2) ((b - sSup A) / 2) with hm
    have hmpos : 0 < m := lt_min (by linarith) (by linarith)
    have hmδ : m < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hmb : sSup A + m < b := by
      have : m ≤ (b - sSup A) / 2 := min_le_right _ _
      linarith
    have htIcc : sSup A + m ∈ Set.Icc a b :=
      ⟨by linarith [hsIcc.1, hmpos], hmb.le⟩
    have hdist : dist (sSup A + m) (sSup A) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hmpos]; exact hmδ
    have hd := hδ htIcc hdist
    have hft : f (sSup A + m) < y := by
      rw [Real.dist_eq] at hd
      have := (abs_lt.mp hd).2
      linarith
    have htA : sSup A + m ∈ A := ⟨htIcc, le_of_lt hft⟩
    have := le_csSup hAbdd htA
    linarith
  have heq : f (sSup A) = y := le_antisymm hsle hgte
  refine ⟨sSup A, hsIcc, heq, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, heq]
  · by_contra hcon
    have hcon' : f t < y := lt_of_not_ge hcon
    have htA : t ∈ A := ⟨⟨le_trans hsIcc.1 h.le, ht.2⟩, le_of_lt hcon'⟩
    have := le_csSup hAbdd htA
    linarith

end Commons.Topology.Order