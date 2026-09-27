import Mathlib

set_option linter.unusedVariables false

namespace Work.Isotopy

theorem exists_box_separation {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M]
    (Φ : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hc : Continuous (Function.uncurry Φ)) (hinj : ∀ s, Function.Injective (Φ s))
    (s₀ : ℝ) (x₀ : M) (V : Set M) (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (O₀ : Set ℝ) (hO₀ : IsOpen O₀) (hs₀ : s₀ ∈ O₀)
    (W₀ : Set (EuclideanSpace ℝ (Fin N))) (hW₀ : IsOpen W₀) (hw₀ : Φ s₀ x₀ ∈ W₀) :
    ∃ (O : Set ℝ) (B : Set (EuclideanSpace ℝ (Fin N))),
      IsOpen O ∧ s₀ ∈ O ∧ O ⊆ O₀ ∧ IsOpen B ∧ Φ s₀ x₀ ∈ B ∧ B ⊆ W₀ ∧
      Bornology.IsBounded B ∧ (∀ s ∈ O, ∀ x : M, Φ s x ∈ B → x ∈ V) := by
  classical
  -- A radius around `Φ s₀ x₀` lying inside `W₀`.
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.isOpen_iff.mp hW₀ (Φ s₀ x₀) hw₀
  -- `K = M \ V` is compact.
  set K : Set M := Vᶜ with hKdef
  have hKcompact : IsCompact K := hV.isClosed_compl.isCompact
  -- The continuous function measuring the distance to `Φ s₀ x₀`.
  set f : M → ℝ := fun x => dist (Φ s₀ x) (Φ s₀ x₀) with hfdef
  have hs₀cont : Continuous (Φ s₀) := by
    have h : Continuous (Function.uncurry Φ ∘ fun x : M => (s₀, x)) :=
      hc.comp (continuous_const.prodMk continuous_id)
    simpa [Function.uncurry, Function.comp_def] using h
  have hfcont : Continuous f := by
    rw [hfdef]
    exact hs₀cont.dist continuous_const
  have hfpos : ∀ x ∈ K, (0 : ℝ) < f x := by
    intro x hx
    rw [hfdef, dist_pos]
    intro hxe
    have hxV : x ∉ V := by
      rwa [hKdef, Set.mem_compl_iff] at hx
    exact hxV (by rw [hinj s₀ hxe]; exact hx₀)
  -- A uniform positive lower bound for `f` on `K`.
  obtain ⟨δ, hδpos, hδle⟩ := hKcompact.exists_forall_le' hfcont.continuousOn hfpos
  -- The open set of parameter/point pairs whose distance exceeds `δ/2`.
  set n : Set (ℝ × M) := {p | δ / 2 < dist (Function.uncurry Φ p) (Φ s₀ x₀)} with hndef
  have hnopen : IsOpen n := by
    rw [hndef]
    exact isOpen_lt continuous_const (hc.dist continuous_const)
  have hgn : ({s₀} : Set ℝ) ×ˢ K ⊆ n := by
    rintro ⟨s, x⟩ hmem
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hmem
    obtain ⟨hs, hx⟩ := hmem
    subst s
    rw [hndef]
    simp only [Set.mem_ofPred_eq]
    have h1 : δ ≤ dist (Φ s₀ x) (Φ s₀ x₀) := hδle x hx
    have h2 : δ / 2 < δ := by linarith
    exact lt_of_lt_of_le h2 h1
  obtain ⟨u, v, huopen, hvopen, hsu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hKcompact hnopen hgn
  refine ⟨u ∩ O₀, Metric.ball (Φ s₀ x₀) (min r₁ (δ / 2)),
    huopen.inter hO₀, ⟨hsu (Set.mem_singleton s₀), hs₀⟩, Set.inter_subset_right,
    Metric.isOpen_ball, Metric.mem_ball_self (lt_min hr₁pos (by linarith)), ?_,
    Metric.isBounded_ball, ?_⟩
  · -- `B ⊆ W₀`
    intro y hy
    apply hr₁sub
    rw [Metric.mem_ball] at hy ⊢
    have hmin := min_le_left r₁ (δ / 2)
    linarith
  · -- the separation property
    intro s hs x hxB
    rw [Set.mem_inter_iff] at hs
    by_contra hxV
    have hxK : x ∈ K := by
      rw [hKdef, Set.mem_compl_iff]
      exact hxV
    have hmem : (s, x) ∈ u ×ˢ v := ⟨hs.1, hKv hxK⟩
    have hgt : δ / 2 < dist (Function.uncurry Φ (s, x)) (Φ s₀ x₀) := by
      have h := huv hmem
      simp only [hndef, Set.mem_ofPred_eq] at h
      exact h
    have hgt' : δ / 2 < dist (Φ s x) (Φ s₀ x₀) := hgt
    rw [Metric.mem_ball] at hxB
    have hlt : dist (Φ s x) (Φ s₀ x₀) < δ / 2 := by
      have hmin := min_le_right r₁ (δ / 2)
      linarith
    exact absurd hgt' (not_lt.mpr (le_of_lt hlt))

end Work.Isotopy
