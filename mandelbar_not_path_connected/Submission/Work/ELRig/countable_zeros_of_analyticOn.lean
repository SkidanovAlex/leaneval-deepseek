import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter

/-- A subset of `ℝ` in which every point is isolated is countable: pick for each point a
rational number close enough to it; this assignment is injective. -/
theorem countable_of_isolated {s : Set ℝ}
    (h : ∀ x ∈ s, ∃ ε > 0, ∀ y ∈ s, |y - x| < ε → y = x) : s.Countable := by
  classical
  let ε : ℝ → ℝ := fun x => if hx : x ∈ s then Classical.choose (h x hx) else 1
  have hεpos : ∀ x ∈ s, 0 < ε x := by
    intro x hx
    dsimp only [ε]
    rw [dite_eq_left hx]
    exact (Classical.choose_spec (h x hx)).1
  have hisol : ∀ x ∈ s, ∀ y ∈ s, |y - x| < ε x → y = x := by
    intro x hx
    dsimp only [ε]
    rw [dite_eq_left hx]
    exact (Classical.choose_spec (h x hx)).2
  have hq_exists : ∀ x : s, ∃ q : ℚ, |(q : ℝ) - x.1| < ε x.1 / 2 := by
    intro x
    have hpos : 0 < ε x.1 := hεpos x.1 x.2
    obtain ⟨q, hq1, hq2⟩ :=
      exists_rat_btwn (show x.1 - ε x.1 / 2 < x.1 + ε x.1 / 2 by linarith)
    exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩
  choose q hq using hq_exists
  have hq_inj : Function.Injective q := by
    intro x y hxy
    have hx := hq x
    have hy := hq y
    rw [hxy] at hx
    have hbound : |x.1 - y.1| < ε x.1 / 2 + ε y.1 / 2 := by
      calc |x.1 - y.1| ≤ |x.1 - (q y : ℝ)| + |(q y : ℝ) - y.1| := abs_sub_le _ _ _
        _ = |(q y : ℝ) - x.1| + |(q y : ℝ) - y.1| := by rw [abs_sub_comm]
        _ < ε x.1 / 2 + ε y.1 / 2 := add_lt_add hx hy
    rcases le_total (ε x.1) (ε y.1) with hle | hle
    · exact Subtype.ext (hisol y.1 y.2 x.1 x.2 (by linarith))
    · exact Subtype.ext (hisol x.1 x.2 y.1 y.2 (by rw [abs_sub_comm]; linarith)).symm
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat ℚ
  rw [Set.countable_iff_exists_injective]
  exact ⟨fun z => g (q z), fun z w hzw => hq_inj (hg hzw)⟩

theorem countable_zeros_of_analyticOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOn ℝ f (Set.Ioo a b)) (hne : ¬ ∀ x ∈ Set.Ioo a b, f x = 0) :
    ({x : ℝ | x ∈ Set.Ioo a b ∧ f x = 0}).Countable := by
  have hfNhd : AnalyticOnNhd ℝ f (Set.Ioo a b) :=
    fun x hx => hf.analyticAt (isOpen_Ioo.mem_nhds hx)
  apply countable_of_isolated
  intro x hx
  rw [Set.mem_ofPred_eq] at hx
  obtain ⟨hxa, hfx⟩ := hx
  have hAt : AnalyticAt ℝ f x := hfNhd x hxa
  rcases hAt.eventually_eq_zero_or_eventually_ne_zero with hzero | hne'
  · exact absurd (fun y hy =>
      hfNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo hxa hzero hy) hne
  · rw [eventually_nhdsWithin_iff] at hne'
    obtain ⟨t, ht, ht'⟩ := Filter.eventually_iff_exists_mem.mp hne'
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨ε, hε, fun y hy hyx => ?_⟩
    rw [Set.mem_ofPred_eq] at hy
    by_contra h
    exact (ht' y (hεsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hyx)) h) hy.2

end Work.ELRig
