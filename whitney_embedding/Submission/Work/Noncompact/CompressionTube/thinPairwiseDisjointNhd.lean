import Mathlib

/-!
# Thin pairwise disjoint open neighbourhoods of a locally finite family of closed sets

`Work.Noncompact.CompressionTube.exists_thin_pairwiseDisjoint_isOpen_nhds`: for a locally finite
family `L j` of pairwise disjoint closed subsets of a second countable `n`-manifold and a prescribed
positive "size" function `ρ`, there are pairwise disjoint open neighbourhoods `U j ⊇ L j` such that
`U j` is contained in the `ρ j`-neighbourhood of `L j` in the sense of the charts at the points of
`L j`:

    ∀ x ∈ U j, ∃ y ∈ L j, x ∈ (chartAt y).source ∧ (chartAt y) x ∈ ball ((chartAt y) y) (ρ j).

This is the **thin** strengthening of `exists_pairwiseDisjoint_isOpen_nhds`
(`exhaustionAux.lean`); the design note `CompressionTube/NOTES_SESSION_twoLanes.md` (Addendum BK)
identifies it as the missing input that makes the corridors of the routing construction *thin tubes
around the spine arcs* (the non-thin version gives no control on the size of the neighbourhood, so
the components of `U b ∩ int K (·+2) ∩ (K (·))ᶜ` are not known to be thin).

The proof is the same Urysohn + enumeration construction as in the non-thin case, with the
prescribed thin neighbourhood intersected in.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- The `ρ j`-chart-neighbourhood of `L j`: the union, over the points `y ∈ L j`, of the points
whose chart coordinate at `y` is within distance `ρ j` of the chart coordinate of `y`. -/
def thinNhd (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {ι : Type*} (L : ι → Set M) (ρ : ι → ℝ)
    (j : ι) : Set M :=
  ⋃ y : L j, ((chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).source ∩
    (chartAt (EuclideanSpace ℝ (Fin n)) (y : M)) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) (y : M)) (y : M)) (ρ j))

theorem mem_thinNhd {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {ι : Type*} {L : ι → Set M} {ρ : ι → ℝ}
    {j : ι} {x : M} :
    x ∈ thinNhd n L ρ j ↔ ∃ y ∈ L j, x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).source ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) y) x ∈
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) y) y) (ρ j) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨y, y.2, hy.1, hy.2⟩
  · rintro ⟨y, hy, h1, h2⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, h1, h2⟩

theorem isOpen_thinNhd (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {ι : Type*} (L : ι → Set M) (ρ : ι → ℝ)
    (j : ι) : IsOpen (thinNhd n L ρ j) := by
  refine isOpen_iUnion fun y : L j => ?_
  exact (chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).continuousOn.isOpen_inter_preimage
    (chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).open_source Metric.isOpen_ball

theorem subset_thinNhd (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {ι : Type*} {L : ι → Set M} {ρ : ι → ℝ}
    (hρ : ∀ j, 0 < ρ j) (j : ι) : L j ⊆ thinNhd n L ρ j := by
  intro y hy
  rw [mem_thinNhd]
  exact ⟨y, hy, mem_chart_source (EuclideanSpace ℝ (Fin n)) y, by
    rw [Metric.mem_ball, dist_self]; exact hρ j⟩

/-- **Thin pairwise disjoint open neighbourhoods.** -/
theorem exists_thin_pairwiseDisjoint_isOpen_nhds {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    {ι : Type*} [Countable ι] {L : ι → Set M}
    (hclosed : ∀ j, IsClosed (L j)) (hlocfin : LocallyFinite L)
    (hdisj : Pairwise (fun j j' => Disjoint (L j) (L j')))
    {ρ : ι → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ U : ι → Set M, (∀ j, IsOpen (U j)) ∧ (∀ j, L j ⊆ U j) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) ∧
      (∀ j, U j ⊆ thinNhd n L ρ j) := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : NormalSpace M := inferInstance
  have hSclosed : ∀ j, IsClosed (⋃ (j' : {x : ι // x ≠ j}), L j'.1) := by
    intro j
    have hlf : LocallyFinite (fun a : {x : ι // x ≠ j} => L a.1) :=
      hlocfin.comp_injOn (g := (Subtype.val : {x : ι // x ≠ j} → ι))
        (fun a _ b _ hab => Subtype.ext hab)
    exact hlf.isClosed_iUnion (fun a => hclosed a.1)
  have hSdisj : ∀ j, Disjoint (⋃ (j' : {x : ι // x ≠ j}), L j'.1) (L j) := by
    intro j
    rw [Set.disjoint_left]
    intro x hx hxL
    obtain ⟨j', hxj'⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdisj j'.2) hxj' hxL
  have hUry : ∀ j, ∃ f : C(M, ℝ),
      (∀ x, x ∈ (⋃ (j' : {x : ι // x ≠ j}), L j'.1) → f x = 0) ∧
      (∀ x ∈ L j, f x = 1) ∧ (∀ x, f x ∈ Set.Icc (0:ℝ) 1) := by
    intro j
    obtain ⟨f, hf0, hf1, hf01⟩ :=
      exists_continuous_zero_one_of_isClosed (hSclosed j) (hclosed j) (hSdisj j)
    exact ⟨f, fun x hx => hf0 hx, hf1, hf01⟩
  choose f hf0 hf1 hf01 using hUry
  -- the *thin* open sets around the `L j`
  have hO : ∀ j, ∃ (O : Set M), IsOpen O ∧ L j ⊆ O ∧ O ⊆ thinNhd n L ρ j ∧
      (∀ j' ≠ j, Disjoint (closure O) (L j')) := by
    intro j
    refine ⟨{x | (1/2 : ℝ) < f j x} ∩ thinNhd n L ρ j,
      (isOpen_lt continuous_const (f j).continuous).inter (isOpen_thinNhd n L ρ j), ?_,
      inter_subset_right, ?_⟩
    · intro x hx
      refine ⟨?_, subset_thinNhd n hρ j hx⟩
      show (1 : ℝ) / 2 < f j x
      rw [hf1 j x hx]
      norm_num
    · intro j' hj'
      rw [Set.disjoint_left]
      intro x hxcl hxL
      have hx' : (1/2 : ℝ) ≤ f j x :=
        closure_minimal (fun y hy => le_of_lt hy.1)
          (isClosed_Ici.preimage (f j).continuous) hxcl
      have h0 : f j x = 0 := hf0 j x (Set.mem_iUnion.mpr ⟨⟨j', hj'⟩, hxL⟩)
      rw [h0] at hx'
      norm_num at hx'
  choose O hOopen hOL hOthin hOcl using hO
  obtain ⟨e, he⟩ := exists_injective_nat ι
  refine ⟨fun j => O j \ (⋃ j' ∈ {j' | e j' < e j}, closure (O j')), ?_, ?_, ?_, ?_⟩
  · intro j
    refine (hOopen j).sdiff ?_
    refine (Set.finite_lt_nat (e j)).preimage (fun a _ b _ h => he h) |>.isClosed_biUnion ?_
    intro j' _
    exact isClosed_closure
  · intro j x hx
    refine ⟨hOL j hx, ?_⟩
    intro hcon
    obtain ⟨j', hj', hxcl⟩ := Set.mem_iUnion₂.mp hcon
    have hne : j ≠ j' := by rintro rfl; simp at hj'
    exact Set.disjoint_left.mp (hOcl j' j hne) hxcl hx
  · intro j j' hjj'
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases lt_trichotomy (e j) (e j') with h | h | h
    · exact hx'.2 (Set.mem_iUnion₂.mpr ⟨j, h, subset_closure hx.1⟩)
    · exact absurd (he h) hjj'
    · exact hx.2 (Set.mem_iUnion₂.mpr ⟨j', h, subset_closure hx'.1⟩)
  · intro j x hx
    exact hOthin j hx.1

end Work.Noncompact.CompressionTube
