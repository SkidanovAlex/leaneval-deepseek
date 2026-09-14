import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Topology.Metric

/-- A continuous collision-free curve on a compact interval is *uniformly* collision-free: there
is a positive lower bound for the distances between distinct bodies. -/
theorem exists_pos_le_dist_of_continuousOn_ne {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} {γ : ℝ → EuclideanSpace E (Fin N)} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hnc : ∀ t ∈ Set.Icc a b, ∀ i j, i ≠ j → γ t i ≠ γ t j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc a b, ∀ i j, i ≠ j → δ ≤ dist (γ t i) (γ t j) := by
  -- Write `hab` into a form that is used below (it is only needed to know the interval is
  -- nonempty, which enters through `a ∈ Icc a b`).
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  classical
  -- For every pair `p` of distinct indices, `t ↦ dist (γ t p.1) (γ t p.2)` is continuous on the
  -- compact interval and strictly positive there, hence attains a strictly positive minimum.
  have hpair : ∀ p : Fin N × Fin N, p.1 ≠ p.2 →
      ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc a b, m ≤ dist (γ t p.1) (γ t p.2) := by
    intro p hp
    have h1 : ContinuousOn (fun t => γ t p.1) (Set.Icc a b) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin N => E) p.1).comp_continuousOn hcont
    have h2 : ContinuousOn (fun t => γ t p.2) (Set.Icc a b) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin N => E) p.2).comp_continuousOn hcont
    have hci : ContinuousOn (fun t => dist (γ t p.1) (γ t p.2)) (Set.Icc a b) :=
      continuous_dist.comp_continuousOn (h1.prodMk h2)
    exact isCompact_Icc.exists_forall_le' hci (fun t ht => dist_pos.mpr (hnc t ht p.1 p.2 hp))
  -- Choose such a minimum for every pair (with an arbitrary value on the diagonal).
  set m : Fin N × Fin N → ℝ :=
    fun p => if h : p.1 ≠ p.2 then Classical.choose (hpair p h) else 1 with hm
  have hm_pos : ∀ p, 0 < m p := by
    intro p
    rw [hm]
    by_cases h : p.1 ≠ p.2
    · simp only [dif_pos h]; exact (Classical.choose_spec (hpair p h)).1
    · simp only [dif_neg h]; norm_num
  have hm_le : ∀ p, p.1 ≠ p.2 → ∀ t ∈ Set.Icc a b, m p ≤ dist (γ t p.1) (γ t p.2) := by
    intro p hp t ht
    rw [hm]
    simp only [dif_pos hp]
    exact (Classical.choose_spec (hpair p hp)).2 t ht
  -- The relevant (finite) set of ordered pairs of distinct indices.
  set P : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hP
  by_cases hne : P.Nonempty
  · -- If there is at least one pair of distinct indices, take the minimum of the `m p`.
    refine ⟨(P.image m).min' (hne.image m), ?_, ?_⟩
    · obtain ⟨p, -, hpm⟩ := Finset.mem_image.mp (Finset.isLeast_min' (P.image m) (hne.image m)).1
      rw [← hpm]
      exact hm_pos p
    · intro t ht i j hij
      have hmem : m (i, j) ∈ P.image m := by
        refine Finset.mem_image.mpr ⟨(i, j), ?_, rfl⟩
        rw [hP]; simp [hij]
      exact le_trans ((Finset.isLeast_min' (P.image m) (hne.image m)).2 hmem)
        (hm_le (i, j) hij t ht)
  · -- Otherwise there are no distinct indices at all and the claim is vacuous.
    exact ⟨1, one_pos, fun t _ i j hij =>
      absurd ⟨(i, j), by rw [hP]; simp [hij]⟩ hne⟩

end Commons.Topology.Metric