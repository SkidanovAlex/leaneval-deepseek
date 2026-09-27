import Mathlib

namespace Work.Drive

/-- **Uniform one-sided tubular neighbourhood of a compact set in a product `E × X`.**

If `S` is a compact subset of the open set `U` in `E × X` (`E` a normed group, `X` an arbitrary
topological space), then there is a uniform `δ > 0` such that replacing the `E`-coordinate `q` of a
point `(q, z) ∈ S` by any `q'` with `‖q' - q‖ ≤ δ` keeps the point inside `U` — with the same
`X`-coordinate `z`.

Proof: for each `p ∈ S`, openness of `U` in the product topology gives a basic neighbourhood
`ball p.1 r ×ˢ V` of `p` inside `U` (`V` open, containing `p.2`).  The sets
`ball p.1 (r/2) ×ˢ V` cover the compact `S`, and a finite subcover gives a uniform radius. -/
theorem exists_pos_norm_subset_of_isCompact_subset_isOpen {E : Type*} [NormedAddCommGroup E]
    {X : Type*} [TopologicalSpace X]
    {S U : Set (E × X)} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q q' : E) (z : X), (q, z) ∈ S → ‖q' - q‖ ≤ δ → (q', z) ∈ U := by
  classical
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    exact ⟨1, one_pos, by simp⟩
  -- Local data: a basic product neighbourhood of each point of `S` inside `U`,
  -- with the `E`-radius chosen twice as large as the one used for the cover.
  have hloc : ∀ p : S, ∃ ε : ℝ, ∃ V : Set X, 0 < ε ∧ IsOpen V ∧ (p : E × X).2 ∈ V ∧
      (Metric.ball (p : E × X).1 (2 * ε)) ×ˢ V ⊆ U := by
    intro p
    have hpU : ((p : E × X)) ∈ U := hSU p.2
    have hmem : U ∈ nhds ((p : E × X)) := hU.mem_nhds hpU
    obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.mp hmem
    obtain ⟨r, hr, hra⟩ := Metric.mem_nhds_iff.mp ha
    obtain ⟨V, hVb, hVo, hVz⟩ := mem_nhds_iff.mp hb
    exact ⟨r / 2, V, half_pos hr, hVo, hVz, by
      have h2 : 2 * (r / 2) = r := by ring
      rw [h2]
      exact (Set.prod_mono hra hVb).trans hab⟩
  choose ε V hε hVo hVz hVsub using hloc
  -- The half-radius boxes cover `S`.
  have hcover : S ⊆ ⋃ p : S, Metric.ball (p : E × X).1 (ε p) ×ˢ V p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (hε ⟨p, hp⟩), hVz ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun p : S => Metric.ball (p : E × X).1 (ε p) ×ˢ V p)
    (fun p => Metric.isOpen_ball.prod (hVo p)) hcover
  have htne : t.Nonempty := by
    obtain ⟨p0, hp0⟩ := hSne
    obtain ⟨i, hi, -⟩ := by simpa only [Set.mem_iUnion, exists_prop] using ht hp0
    exact ⟨i, hi⟩
  -- The uniform radius is the minimum of the finitely many cover radii.
  refine ⟨(t.image ε).min' (htne.image ε), ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, -, rfl⟩
    exact hε p
  · intro q q' z hq hq'
    obtain ⟨p, hpt, hqb, hzV⟩ := by
      simpa only [Set.mem_iUnion, exists_prop, Set.mem_prod] using ht hq
    have hδp : (t.image ε).min' (htne.image ε) ≤ ε p :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hpt, rfl⟩)
    have hq'd : dist q' q ≤ (t.image ε).min' (htne.image ε) := by rwa [dist_eq_norm]
    have hb : q' ∈ Metric.ball (p : E × X).1 (2 * ε p) := by
      rw [Metric.mem_ball] at hqb ⊢
      calc dist q' (p : E × X).1 ≤ dist q' q + dist q (p : E × X).1 := dist_triangle _ _ _
        _ < (t.image ε).min' (htne.image ε) + ε p := add_lt_add_of_le_of_lt hq'd hqb
        _ ≤ 2 * ε p := by linarith
    exact hVsub p ⟨hb, hzV⟩

end Work.Drive
