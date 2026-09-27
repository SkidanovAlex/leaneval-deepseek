import Mathlib

/-!
# Injectivity of a locally injective map on a neighbourhood of a compact set

This is the topological core of the last step of the collar flattening
(`CutPush/NOTES_STATE_S60.md` §2): the projection `ψ = π_{K'} ∘ A ∘ f` of the sheet is a *local*
diffeomorphism near the arc and is injective on the (compact) core, hence injective on an entire
*neighbourhood* of the core.  That is what makes the sheet a graph over `K'` and lets the collar be
chosen inside the flattening region.

The proof is the standard compactness argument: if `ψ` failed to be injective on every neighbourhood of
`K`, one would find `x n ≠ y n`, both within `1/(n+1)` of `K`, with `ψ (x n) = ψ (y n)`.  Projecting onto
`K` (which is compact) and passing to a subsequence, both sequences converge to the *same* point
`k ∈ K` (the limits are equal because `ψ` is continuous and injective on `K`), and local injectivity at
`k` then forces `x n = y n` for large `n`, a contradiction.
-/

namespace Work.Whitney.CutPush

open Filter Topology

/-- **Injectivity near a compact set.**  Let `ψ : X → Y` with `X` a pseudo-metric space and `Y`
Hausdorff be continuous, *locally injective* at every point of the compact set `K`, and injective on
`K`.  Then it is injective on a whole neighbourhood of `K`. -/
theorem exists_isOpen_injOn_of_compact_injOn {X Y : Type*} [PseudoMetricSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {K : Set X} (hK : IsCompact K) {ψ : X → Y} (hψ : Continuous ψ)
    (hKinj : Set.InjOn ψ K) (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, Set.InjOn ψ U) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ Set.InjOn ψ U := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | _
  · refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · rw [hKe]
    · intro x hx
      exact absurd hx (Set.notMem_empty x)
  by_contra hcon
  have hcon' : ∀ U : Set X, IsOpen U → K ⊆ U → ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ ψ x = ψ y := by
    intro U hU hKU
    by_contra h
    push_neg at h
    exact hcon ⟨U, hU, hKU, fun x hx y hy hxy => by
      by_contra hne
      exact h x hx y hy hne hxy⟩
  have hV : ∀ n : ℕ, ∃ x ∈ Metric.thickening (1 / ((n : ℝ) + 1)) K,
      ∃ y ∈ Metric.thickening (1 / ((n : ℝ) + 1)) K, x ≠ y ∧ ψ x = ψ y := by
    intro n
    refine hcon' _ Metric.isOpen_thickening ?_
    intro z hz
    rw [Metric.mem_thickening_iff]
    exact ⟨z, hz, by simpa using (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)⟩
  choose x hxmem y hymem hne heq using hV
  choose kx hkx hkxdist using fun n =>
    (Metric.mem_thickening_iff.mp (hxmem n) : ∃ z ∈ K, dist (x n) z < 1 / ((n : ℝ) + 1))
  choose ky hky hkydist using fun n =>
    (Metric.mem_thickening_iff.mp (hymem n) : ∃ z ∈ K, dist (y n) z < 1 / ((n : ℝ) + 1))
  obtain ⟨p, hp, φ, hφ, hφt⟩ :=
    (hK.prod hK).tendsto_subseq (x := fun n : ℕ => (kx n, ky n)) (fun n => ⟨hkx n, hky n⟩)
  have hp1 : p.1 ∈ K := hp.1
  have hp2 : p.2 ∈ K := hp.2
  have hkxt : Tendsto (fun n => kx (φ n)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hφt
  have hkyt : Tendsto (fun n => ky (φ n)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hφt
  have hzero : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hxdt : Tendsto (fun n : ℕ => dist (x (φ n)) (kx (φ n))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Eventually.of_forall (fun n => dist_nonneg))
      (Eventually.of_forall (fun n => le_of_lt (hkxdist (φ n))))
  have hydt : Tendsto (fun n : ℕ => dist (y (φ n)) (ky (φ n))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Eventually.of_forall (fun n => dist_nonneg))
      (Eventually.of_forall (fun n => le_of_lt (hkydist (φ n))))
  have hkxt2 : Tendsto (fun n : ℕ => dist (kx (φ n)) p.1) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hkxt
  have hkyt2 : Tendsto (fun n : ℕ => dist (ky (φ n)) p.2) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hkyt
  have hxt : Tendsto (fun n => x (φ n)) atTop (𝓝 p.1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun n => dist (x (φ n)) p.1) (g := fun _ => (0 : ℝ))
      (h := fun n => dist (x (φ n)) (kx (φ n)) + dist (kx (φ n)) p.1)
      tendsto_const_nhds ?_ (Eventually.of_forall (fun n => dist_nonneg))
      (Eventually.of_forall (fun n => dist_triangle _ _ _))
    simpa using hxdt.add hkxt2
  have hyt : Tendsto (fun n => y (φ n)) atTop (𝓝 p.2) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun n => dist (y (φ n)) p.2) (g := fun _ => (0 : ℝ))
      (h := fun n => dist (y (φ n)) (ky (φ n)) + dist (ky (φ n)) p.2)
      tendsto_const_nhds ?_ (Eventually.of_forall (fun n => dist_nonneg))
      (Eventually.of_forall (fun n => dist_triangle _ _ _))
    simpa using hydt.add hkyt2
  have hlim1 : Tendsto (fun n => ψ (x (φ n))) atTop (𝓝 (ψ p.1)) :=
    Filter.Tendsto.comp hψ.continuousAt hxt
  have hlim2 : Tendsto (fun n => ψ (x (φ n))) atTop (𝓝 (ψ p.2)) := by
    have heq' : (fun n => ψ (x (φ n))) = fun n => ψ (y (φ n)) := funext (fun n => heq (φ n))
    rw [heq']
    exact Filter.Tendsto.comp hψ.continuousAt hyt
  have hpp : ψ p.1 = ψ p.2 := tendsto_nhds_unique hlim1 hlim2
  have hpeq : p.1 = p.2 := hKinj hp1 hp2 hpp
  obtain ⟨U, hU, hUinj⟩ := hloc p.1 hp1
  have hxU : ∀ᶠ n in atTop, x (φ n) ∈ U := hxt.eventually hU
  have hyU : ∀ᶠ n in atTop, y (φ n) ∈ U := hyt.eventually (hpeq ▸ hU)
  obtain ⟨n, hn1, hn2⟩ := (hxU.and hyU).exists
  exact hne (φ n) (hUinj hn1 hn2 (heq (φ n)))

end Work.Whitney.CutPush
