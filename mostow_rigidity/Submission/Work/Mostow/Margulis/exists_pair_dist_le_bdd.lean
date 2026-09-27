import Mathlib

/-!
# Pigeonhole with an explicit bound

If `K` is a totally bounded set in a pseudometric space and `φ : ℕ → α` takes its values in `K`,
then two indices `i < j`, with `j` bounded by a number depending only on `K` and `ε`, satisfy
`dist (φ i) (φ j) ≤ ε`.

This is the quantitative form of `Work.Mostow.exists_pair_dist_le` (which forgets the bound on
the second index); it is the pigeonhole step of the compact-stabiliser argument.
-/

namespace Work.Mostow.Margulis

/-- Uniform form of the pigeonhole: the bound on the second index can be chosen *before* the
sequence, depending only on `K` and `ε`. -/
theorem exists_uniform_pair_dist_le_bdd {α : Type*} [PseudoMetricSpace α] {K : Set α}
    (hK : TotallyBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ φ : ℕ → α, (∀ n, φ n ∈ K) →
      ∃ i j : ℕ, i < j ∧ j ≤ N ∧ dist (φ i) (φ j) ≤ ε := by
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨t, htfin, hcov⟩ := (Metric.totallyBounded_iff.mp hK) (ε / 2) hδ
  let s : Finset α := htfin.toFinset
  have hmem : ∀ y : α, y ∈ s ↔ y ∈ t := fun y => Set.Finite.mem_toFinset htfin
  refine ⟨s.card, fun φ hφ => ?_⟩
  have hcov' : ∀ n : ℕ, ∃ y : α, y ∈ s ∧ dist (φ n) y < ε / 2 := by
    intro n
    have h := hcov (hφ n)
    simp only [Set.mem_iUnion] at h
    obtain ⟨y, hyt, hyb⟩ := h
    exact ⟨y, (hmem y).mpr hyt, Metric.mem_ball.mp hyb⟩
  let f : Fin (s.card + 1) → α := fun i => Classical.choose (hcov' (i : ℕ))
  have hfs : ∀ i : Fin (s.card + 1), f i ∈ s :=
    fun i => (Classical.choose_spec (hcov' (i : ℕ))).1
  have hfd : ∀ i : Fin (s.card + 1), dist (φ (i : ℕ)) (f i) < ε / 2 :=
    fun i => (Classical.choose_spec (hcov' (i : ℕ))).2
  have hfd' : ∀ i : Fin (s.card + 1), dist (f i) (φ (i : ℕ)) < ε / 2 :=
    fun i => by rw [dist_comm]; exact hfd i
  have hcard : s.card < (Finset.univ : Finset (Fin (s.card + 1))).card := by simp
  obtain ⟨x, -, y, -, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := (Finset.univ : Finset (Fin (s.card + 1))))
      (t := s) hcard (f := f) (fun i _ => hfs i)
  have hd : dist (φ (x : ℕ)) (φ (y : ℕ)) ≤ ε := by
    have h1 := hfd x
    have h2 := hfd' y
    calc dist (φ (x : ℕ)) (φ (y : ℕ))
        ≤ dist (φ (x : ℕ)) (f x) + dist (f x) (φ (y : ℕ)) := dist_triangle _ _ _
      _ = dist (φ (x : ℕ)) (f x) + dist (f y) (φ (y : ℕ)) := by rw [hfeq]
      _ ≤ ε / 2 + ε / 2 := add_le_add (le_of_lt h1) (le_of_lt h2)
      _ = ε := add_halves ε
  have hxle : (x : ℕ) ≤ s.card := by have := x.isLt; omega
  have hyle : (y : ℕ) ≤ s.card := by have := y.isLt; omega
  rcases lt_or_gt_of_ne (fun h : (x : ℕ) = (y : ℕ) => hxy (Fin.ext h)) with hlt | hgt
  · exact ⟨(x : ℕ), (y : ℕ), hlt, hyle, hd⟩
  · exact ⟨(y : ℕ), (x : ℕ), hgt, hxle, by rw [dist_comm]; exact hd⟩

/-- Pigeonhole with an explicit bound: from a finite `ε/2`-net of `K` of cardinality `M`, two of
the `M+1` terms `φ 0, …, φ M` fall in the same net ball. -/
theorem exists_pair_dist_le_bdd {α : Type*} [PseudoMetricSpace α] {K : Set α}
    (hK : TotallyBounded K) {ε : ℝ} (hε : 0 < ε) (φ : ℕ → α) (hφ : ∀ n, φ n ∈ K) :
    ∃ N : ℕ, ∃ i j : ℕ, i < j ∧ j ≤ N ∧ dist (φ i) (φ j) ≤ ε := by
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨t, htfin, hcov⟩ := (Metric.totallyBounded_iff.mp hK) (ε / 2) hδ
  let s : Finset α := htfin.toFinset
  have hmem : ∀ y : α, y ∈ s ↔ y ∈ t := fun y => Set.Finite.mem_toFinset htfin
  have hcov' : ∀ n : ℕ, ∃ y : α, y ∈ s ∧ dist (φ n) y < ε / 2 := by
    intro n
    have h := hcov (hφ n)
    simp only [Set.mem_iUnion] at h
    obtain ⟨y, hyt, hyb⟩ := h
    exact ⟨y, (hmem y).mpr hyt, Metric.mem_ball.mp hyb⟩
  let f : Fin (s.card + 1) → α := fun i => Classical.choose (hcov' (i : ℕ))
  have hfs : ∀ i : Fin (s.card + 1), f i ∈ s :=
    fun i => (Classical.choose_spec (hcov' (i : ℕ))).1
  have hfd : ∀ i : Fin (s.card + 1), dist (φ (i : ℕ)) (f i) < ε / 2 :=
    fun i => (Classical.choose_spec (hcov' (i : ℕ))).2
  have hcard : s.card < (Finset.univ : Finset (Fin (s.card + 1))).card := by simp
  obtain ⟨x, -, y, -, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := (Finset.univ : Finset (Fin (s.card + 1))))
      (t := s) hcard (f := f) (fun i _ => hfs i)
  have hfd' : ∀ i : Fin (s.card + 1), dist (f i) (φ (i : ℕ)) < ε / 2 :=
    fun i => by rw [dist_comm]; exact hfd i
  have hd : dist (φ (x : ℕ)) (φ (y : ℕ)) ≤ ε := by
    have h1 := hfd x
    have h2 := hfd' y
    calc dist (φ (x : ℕ)) (φ (y : ℕ))
        ≤ dist (φ (x : ℕ)) (f x) + dist (f x) (φ (y : ℕ)) := dist_triangle _ _ _
      _ = dist (φ (x : ℕ)) (f x) + dist (f y) (φ (y : ℕ)) := by rw [hfeq]
      _ ≤ ε / 2 + ε / 2 := add_le_add (le_of_lt h1) (le_of_lt h2)
      _ = ε := add_halves ε
  have hxle : (x : ℕ) ≤ s.card := by have := x.isLt; omega
  have hyle : (y : ℕ) ≤ s.card := by have := y.isLt; omega
  rcases lt_or_gt_of_ne (fun h : (x : ℕ) = (y : ℕ) => hxy (Fin.ext h)) with hlt | hgt
  · exact ⟨s.card, (x : ℕ), (y : ℕ), hlt, hyle, hd⟩
  · exact ⟨s.card, (y : ℕ), (x : ℕ), hgt, hxle, by rw [dist_comm]; exact hd⟩

end Work.Mostow.Margulis
