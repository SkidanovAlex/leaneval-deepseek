import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

/-- Two distinct integers, regarded as complex numbers, are at distance at least `1`. -/
theorem one_le_dist_intCast {m n : ℤ} (h : m ≠ n) : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := by
  have hmn : m - n ≠ 0 := sub_ne_zero.mpr h
  rw [Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hmn

/-- The set of integers, viewed as a subset of the complex numbers, is discrete:
every integer has a neighbourhood (namely the ball of radius `1/2`) meeting the
integers only in itself. -/
theorem isDiscrete_range_intCast : IsDiscrete (Set.range (Int.cast : ℤ → ℂ)) := by
  refine IsDiscrete.of_nhdsWithin fun x hx => ?_
  obtain ⟨n, rfl⟩ := hx
  rw [Filter.le_pure_iff]
  show {(n : ℂ)} ∈ nhds (n : ℂ) ⊓ Filter.principal (Set.range (Int.cast : ℤ → ℂ))
  have hU : Metric.ball (n : ℂ) (1 / 2) ∈ nhds (n : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  have hS : Set.range (Int.cast : ℤ → ℂ) ∈ Filter.principal (Set.range (Int.cast : ℤ → ℂ)) :=
    Filter.mem_principal_self _
  have hmem : Metric.ball (n : ℂ) (1 / 2) ∩ Set.range (Int.cast : ℤ → ℂ)
      ∈ nhds (n : ℂ) ⊓ Filter.principal (Set.range (Int.cast : ℤ → ℂ)) :=
    Filter.mem_inf_iff.mpr ⟨_, hU, _, hS, rfl⟩
  refine Filter.mem_of_superset hmem ?_
  rintro w ⟨hwb, ⟨m, rfl⟩⟩
  simp only [Set.mem_singleton_iff]
  by_contra hne
  have hmn : m ≠ n := fun h => hne (by rw [h])
  have h1 : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := one_le_dist_intCast hmn
  simp only [Metric.mem_ball] at hwb
  linarith

/-- A continuous function on a preconnected set `s ⊆ ℂ` whose values on `s` are all
integers is constant on `s`. -/
theorem int_continuous_const {s : Set ℂ} (hs : IsPreconnected s) {k : ℂ → ℂ}
    (hc : ContinuousOn k s) (hint : ∀ z ∈ s, ∃ n : ℤ, k z = n) {x y : ℂ} (hx : x ∈ s)
    (hy : y ∈ s) : k x = k y := by
  refine IsPreconnected.constant_of_mapsTo hs isDiscrete_range_intCast hc ?_ hx hy
  intro z hz
  obtain ⟨n, hn⟩ := hint z hz
  exact ⟨n, hn.symm⟩

end Work.FlowerGlue
