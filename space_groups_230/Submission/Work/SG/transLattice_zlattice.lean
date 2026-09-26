import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.NormalForm

/-!
# The translation lattice of a 3-dimensional crystallographic group is a `ℤ`-lattice

For a crystallographic group `G ≤ E₃` (discrete, and containing translations by three linearly
independent vectors — see `IsCrystallographicGroup`) the group of translations of `G` is a full
`ℤ`-lattice of `E 3`:

* it is discrete, because `IsDiscrete` at `0` bounds the number of lattice vectors of norm `≤ 1`;
* it spans `E 3` over `ℝ`, because the three independent translation vectors given by
  `IsCrystallographicGroup.cocompact` already lie in it.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- **Spanning.** The translation lattice of a crystallographic group spans `E 3` over `ℝ`:
the three linearly independent translation vectors supplied by `cocompact` are lattice
vectors, and three independent vectors of the 3-dimensional space `E 3` already span it. -/
theorem transLattice_span_top (G : CrystallographicGroup 3) :
    Submodule.span ℝ (Work.SG.transLattice G.1 : Set (E 3)) = ⊤ := by
  obtain ⟨v, hvlin, hv⟩ := G.2.cocompact
  have hmem : ∀ i, v i ∈ Work.SG.transLattice G.1 := fun i => by
    obtain ⟨g, hg, hgv⟩ := hv i
    exact Work.SG.mem_transLattice.mpr ⟨g, hg, hgv⟩
  have hrange : Set.range v ⊆ (Work.SG.transLattice G.1 : Set (E 3)) := by
    rintro _ ⟨i, rfl⟩; exact hmem i
  have htop : Submodule.span ℝ (Set.range v) = ⊤ :=
    hvlin.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  have hle := Submodule.span_mono (R := ℝ) hrange
  rw [htop] at hle
  exact top_le_iff.mp hle

/-- **Discreteness.** The translation lattice of a crystallographic group is discrete: the
proper-discontinuity hypothesis at `0` shows that there are only finitely many lattice vectors
of norm `≤ 1`, and a finite set is closed, so `0` is isolated in the lattice. -/
theorem transLattice_discreteTopology (G : CrystallographicGroup 3) :
    DiscreteTopology (Work.SG.transLattice G.1) := by
  -- only finitely many elements of `G` lie in the closed unit ball around `0`
  have hfin : {g : EuclideanIsom 3 | g ∈ G.1 ∧ dist (g 0) 0 ≤ 1}.Finite :=
    G.2.discrete 0 1 (by norm_num)
  -- hence only finitely many lattice vectors of norm `≤ 1`
  have hSfin : ({v : E 3 | v ∈ Work.SG.transLattice G.1 ∧ ‖v‖ ≤ 1}).Finite := by
    refine Set.Finite.subset (hfin.image (fun g => g 0)) ?_
    rintro v ⟨hvL, hv1⟩
    obtain ⟨g, hg, hgv⟩ := Work.SG.mem_transLattice.mp hvL
    refine ⟨g, ⟨hg, ?_⟩, ?_⟩
    · rw [show g 0 = v from by simpa using hgv 0]
      rw [dist_eq_norm, sub_zero]; exact hv1
    · simpa using hgv 0
  -- a finite set is closed, so its zero-free part has open complement containing `0`
  have hSfin' : ({v : E 3 | v ∈ Work.SG.transLattice G.1 ∧ ‖v‖ ≤ 1} \ {0}).Finite :=
    hSfin.sdiff
  have hopen : IsOpen ({v : E 3 | v ∈ Work.SG.transLattice G.1 ∧ ‖v‖ ≤ 1} \ {0})ᶜ :=
    hSfin'.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simp)
  -- a nonzero lattice vector always has norm at least `min ε 1`
  have hkey : ∀ v : E 3, v ∈ Work.SG.transLattice G.1 → ‖v‖ < min ε 1 → v = 0 := by
    intro v hvL hvlt
    have hvlt1 : ‖v‖ < 1 := lt_of_lt_of_le hvlt (min_le_right _ _)
    have hvltε : ‖v‖ < ε := lt_of_lt_of_le hvlt (min_le_left _ _)
    have hvS : v ∈ ({w : E 3 | w ∈ Work.SG.transLattice G.1 ∧ ‖w‖ ≤ 1}) :=
      ⟨hvL, le_of_lt hvlt1⟩
    have hvball : v ∈ Metric.ball (0 : E 3) ε := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hvltε
    have hnot := hball hvball
    by_contra hne
    exact hnot ⟨hvS, by simpa using hne⟩
  -- consequently `{0}` is open in the lattice, i.e. the lattice topology is discrete
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, Metric.mem_nhds_iff]
  refine ⟨min ε 1, lt_min hε one_pos, fun y hy => ?_⟩
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  refine hkey y y.2 ?_
  have := hy
  rw [Metric.mem_ball] at this
  simpa using this

theorem transLattice_zlattice (G : LeanEval.Geometry.SpaceGroupsProblem.CrystallographicGroup 3) :
    ∃ hD : DiscreteTopology (Work.SG.transLattice G.1),
      @IsZLattice ℝ _ _ _ _ (Work.SG.transLattice G.1) hD := by
  exact ⟨transLattice_discreteTopology G,
    @IsZLattice.mk ℝ _ _ _ _ (Work.SG.transLattice G.1) (transLattice_discreteTopology G)
      (transLattice_span_top G)⟩

end Work.SG
