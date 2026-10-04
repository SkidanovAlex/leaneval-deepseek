import Mathlib.Geometry.Manifold.IsManifold.Basic
import Submission.Commons.Topology.Interval.exists_grid_Icc_gap_lt
import Submission.Commons.Topology.Manifold.exists_lebesgue_chartAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Topology

/-!
## Grid refinement of the unit square into chart domains

Given a map `F : ℝ × ℝ → M` that is continuous on a rectangle `[a,b] × [c,d]`, we produce a
rectangular grid `s 0 = a ≤ ⋯ ≤ s n = b`, `t 0 = c ≤ ⋯ ≤ t m = d` such that the image under `F`
of every grid cell `[s i, s (i+1)] × [t j, t (j+1)]` lies inside the source of a single chart of
`M`.

The proof is the standard compactness argument: on the compact rectangle the preimages of the
chart sources form an open cover, whose Lebesgue number `δ` controls how fine the grid must be.
The one-dimensional grid is provided by `Commons.Topology.Interval.exists_grid_Icc_gap_lt`, and
the Lebesgue number statement by `Commons.Topology.Manifold.exists_lebesgue_chartAt`.
-/

theorem exists_grid_forall_mapsTo_chartAt_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {a b c d : ℝ} {F : ℝ × ℝ → M}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn F (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∃ (n m : ℕ) (s t : ℕ → ℝ),
      s 0 = a ∧ s n = b ∧ t 0 = c ∧ t m = d ∧
      (∀ i < n, s i < s (i + 1)) ∧ (∀ j < m, t j < t (j + 1)) ∧
      (∀ i < n, ∀ j < m, ∃ y : M,
        ∀ p ∈ Set.Icc (s i) (s (i + 1)) ×ˢ Set.Icc (t j) (t (j + 1)),
          F p ∈ (chartAt H y).source) := by
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcomp
  have hG : Continuous (fun p : ↥K => F p.val) := hF.domRestrict
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Topology.Manifold.exists_lebesgue_chartAt (H := H) (K := ↥K)
      (fun p : ↥K => F p.val) hG
  obtain ⟨n, s, hs0, hsn, hsmono, hsstrict, hsgap⟩ :=
    Commons.Topology.Interval.exists_grid_Icc_gap_lt hab (by linarith : (0:ℝ) < δ/2)
  obtain ⟨m, t, ht0, htm, htmono, htstrict, htgap⟩ :=
    Commons.Topology.Interval.exists_grid_Icc_gap_lt hcd (by linarith : (0:ℝ) < δ/2)
  refine ⟨n, m, s, t, hs0, hsn, ht0, htm, hsstrict, htstrict, ?_⟩
  intro i hi j hj
  have hsi : s i ∈ Set.Icc a b :=
    ⟨by rw [← hs0]; exact hsmono (Nat.zero_le i),
     by rw [← hsn]; exact hsmono (Nat.le_of_lt hi)⟩
  have htj : t j ∈ Set.Icc c d :=
    ⟨by rw [← ht0]; exact htmono (Nat.zero_le j),
     by rw [← htm]; exact htmono (Nat.le_of_lt hj)⟩
  let x0 : ↥K := ⟨(s i, t j), ⟨hsi, htj⟩⟩
  obtain ⟨y, hy⟩ := hδ x0
  refine ⟨y, ?_⟩
  intro p hp
  rw [Set.mem_prod] at hp
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_Icc] at hp1 hp2
  obtain ⟨hp1a, hp1b⟩ := hp1
  obtain ⟨hp2a, hp2b⟩ := hp2
  have hpK : p ∈ K := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact le_trans hsi.1 hp1a
    · refine le_trans hp1b ?_
      rw [← hsn]; exact hsmono (Nat.succ_le_of_lt hi)
    · exact le_trans htj.1 hp2a
    · refine le_trans hp2b ?_
      rw [← htm]; exact htmono (Nat.succ_le_of_lt hj)
  let z : ↥K := ⟨p, hpK⟩
  have hdist : dist z x0 < δ := by
    show dist (p : ℝ × ℝ) ((s i, t j) : ℝ × ℝ) < δ
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have h1 : |p.1 - s i| < δ/2 := by
      have hg := hsgap i hi
      rw [abs_of_nonneg (by linarith [hp1a])]
      linarith
    have h2 : |p.2 - t j| < δ/2 := by
      have hg := htgap j hj
      rw [abs_of_nonneg (by linarith [hp2a])]
      linarith
    exact lt_of_le_of_lt (max_le (le_of_lt h1) (le_of_lt h2)) (by linarith)
  exact hy z hdist

end Commons.Topology