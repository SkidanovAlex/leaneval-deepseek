import Mathlib

namespace NK.LocalReciprocityLubinTate.Unramified

open Set Filter Valuation ValuativeRel MonoidWithZeroHom
open scoped Topology

/-- **A compact subring of a field with a valuative topology lies in the unit ball of every
compatible valuation.**

Mathematical claim: if `v` induces (up to equivalence) the valuative topology of `F`, and `S ≤ F`
is a subring that is compact for that topology, then `v x ≤ 1` for all `x ∈ S`.

Proof sketch.  Suppose `x ∈ S` with `1 < v x` (the negation of `v x ≤ 1`).  Then `x ≠ 0`, the
powers `x ^ n` are pairwise distinct, and `n ↦ (v x) ^ n` is strictly increasing
(`pow_lt_pow_right₀`), so `v (x ^ m) = v (x ^ n)` forces `m = n`.

1. `D := Set.range (fun n : ℕ => x ^ n)` is closed in `F`: for `a : F`, if `a = 0` then
   `{z | v z < 1}` is a neighbourhood of `a` disjoint from `D` (as `1 ≤ (v x) ^ n`); if `a ≠ 0`,
   then `V := {z | v z = v a}` is a neighbourhood of `a` (Mathlib: `Valuation.locally_const`)
   meeting `D` in at most one point, so if `a ∉ D` one can shrink to a neighbourhood of `a`
   avoiding `D` (or argue with `isClosed_iff_clusterPt`: a cluster point `a` of `D` yields `m`
   with `v (x ^ m) = v a`; then the neighbourhood `{z | v (z - a) < min (v (x ^ m - a)) (v a)}`
   of `a` contains no point of `D` at all, contradiction).
2. So `D` is compact, being a closed subset of the compact set `S` (`IsCompact.of_isClosed_subset`).
3. For each `n`, pick an open neighbourhood `U n` of `x ^ n` with `U n ⊆ {z | v z = v (x ^ n)}`
   (`Valuation.locally_const` + `mem_nhds_iff`).  The `U n` cover `D`; by compactness
   (`IsCompact.elim_finite_subcover`) there is a finite `t : Finset ℕ` with
   `D ⊆ ⋃ n ∈ t, U n`.  Pick `N ∉ t` (e.g. `t.sup id + 1`); then `x ^ N ∈ U n` for some `n ∈ t`,
   so `v (x ^ N) = v (x ^ n)`, hence `N = n`, contradiction.  -/
theorem subring_subset_integer_of_isCompact {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsValuativeTopology F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) [v.Compatible]
    (S : Subring F) (hS : IsCompact (S : Set F)) :
    (S : Set F) ⊆ {x : F | v x ≤ 1} := by
  -- Argument by contradiction: suppose some `x ∈ S` has `1 < v x`.
  -- Then the powers `x ^ n` are pairwise distinct and `S`, being compact, forces the (infinite)
  -- tail-filter of the sequence `n ↦ x ^ n` to have a cluster point `a ∈ S`.  Both cases
  -- `a = 0` and `a ≠ 0` contradict the strict ultrametric growth of the powers.
  rintro x hxS
  by_contra hx
  simp only [Set.mem_ofPred_eq, not_le] at hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  let f : ℕ → F := fun n => x ^ n
  have hfS : ∀ n, f n ∈ (S : Set F) := fun n => S.pow_mem hxS n
  -- The filter of tails of the sequence lies inside `𝓟 (S : Set F)`.
  have hlS : Filter.atTop.map f ≤ 𝓟 (S : Set F) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    rw [show f ⁻¹' (S : Set F) = Set.univ from Set.eq_univ_iff_forall.mpr hfS]
    exact Filter.univ_mem
  have hne : (Filter.atTop.map f).NeBot := Filter.NeBot.map atTop_neBot f
  -- Compactness of `S` produces a cluster point of the tails, inside `S`.
  obtain ⟨a, haS, ha⟩ := @hS (Filter.atTop.map f) hne hlS
  rcases eq_or_ne a 0 with rfl | ha0
  · -- Case `a = 0`: the neighbourhood `{v < 1}` of `0` meets the tails only finitely often.
    have hmem : {y : F | v y < 1} ∈ 𝓝 (0 : F) := by
      rw [IsValuativeTopology.mem_nhds_zero_iff]
      refine ⟨1, ?_⟩
      intro y hy
      have h1 : y <ᵥ (1 : F) := (Valuation.vlt_one_iff (valuation F)).mpr (by simpa using hy)
      rwa [Valuation.vlt_one_iff v] at h1
    have hfreq : ∃ᶠ y in (Filter.atTop.map f), y ∈ {y : F | v y < 1} :=
      (clusterPt_iff_frequently.mp ha) _ hmem
    rw [Filter.frequently_map] at hfreq
    obtain ⟨n, hn⟩ := hfreq.exists
    have hge : (1 : Γ₀) ≤ v (x ^ n) := by
      rw [map_pow]; exact one_le_pow₀ (le_of_lt hx)
    exact not_lt_of_ge hge hn
  · -- Case `a ≠ 0`: `{v = v a}` is a neighbourhood of `a`, so the tails hit it infinitely often;
    -- but `n ↦ v (x ^ n)` is strictly increasing, so it hits the value `v a` at most once.
    have hva : (v a : Γ₀) ≠ 0 := (Valuation.ne_zero_iff v).mpr ha0
    have hmem : {y : F | v y = v a} ∈ 𝓝 a := Valuation.locally_const v hva
    have hfreq : ∃ᶠ y in (Filter.atTop.map f), y ∈ {y : F | v y = v a} :=
      (clusterPt_iff_frequently.mp ha) _ hmem
    rw [Filter.frequently_map] at hfreq
    obtain ⟨m, hm⟩ := hfreq.exists
    obtain ⟨n, hmn, hn⟩ := (Filter.frequently_atTop.mp hfreq) (m + 1)
    have heq : (v x) ^ m = (v x) ^ n := by rw [← map_pow, ← map_pow, hm, hn]
    have hmn' : m = n := by
      rcases lt_trichotomy m n with h | h | h
      · exact absurd heq (ne_of_lt (pow_lt_pow_right₀ hx h))
      · exact h
      · exact absurd heq (ne_of_gt (pow_lt_pow_right₀ hx h))
    omega

end NK.LocalReciprocityLubinTate.Unramified
