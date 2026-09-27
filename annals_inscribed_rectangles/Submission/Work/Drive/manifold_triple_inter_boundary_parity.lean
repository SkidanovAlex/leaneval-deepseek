import Mathlib
import Submission.Work.Drive.TripleMeetDefs
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.TParity.Assembly
import Submission.Work.Drive.TParity.Transfer3

namespace Work.Drive

/-- **The mod-2 parity of the boundary triple intersections of three transverse `3`-chains in a
smooth `4`-manifold** — the manifold form of the vector-space theorem
`Work.Drive.even_ncard_blockMeet_sum` (`Submission/Work/Drive/intersection_triple.lean`), exactly as
`Work.Drive.transverse_inter_boundary_parity` is the manifold form of
`Work.Drive.even_ncard_loopMeet_add_solidMeet`.

* `Work.Drive.tripleBdryMeet M D k` is the set of triples `(x₀,x₁,x₂)` of points of the three unit
  cubes at which the three chains meet in a single point of `M`, with the `k`-th parameter on the
  boundary of its cube;
* `Work.Drive.TripleTransverse f₀ f₁ f₂` is the transversality of the triple (the surjectivity of
  `(v₀,v₁,v₂) ↦ (f₀v₀ − f₁v₁, f₀v₀ − f₂v₂)` onto the tangent space squared), stated for the three
  derivatives alone — this is chart-independent and is *stronger* than the three tangent images
  spanning the tangent space (the three tangent spaces must meet in the expected dimension);
* `Work.Drive.TripleCommonDir f₀ f₁ f₂ v` says that `v` is a common tangent direction of the three
  chains (the tangent vector of the triple intersection `1`-manifold);
* `hface` says that at every boundary triple intersection exactly one coordinate of exactly one
  parameter is on a face, everything else strictly interior, and the intersection `1`-manifold crosses
  that face transversally (there is a common direction with `v k i ≠ 0` in the boundary coordinate).

The conclusion is the analogue of `even_ncard_blockMeet_sum`: the three labelled boundary counts are
finite and their sum is even.  This is the parity identity `n_P + n_Q + n_R ≡ 0` of
`RADIAL_CHAIN_NOTES.md` §2, i.e. the boundary bookkeeping that Hugelmeyer's Lemma 4 (transitivity of
`≺`) is built from; it cannot be obtained from `transverse_inter_boundary_parity`, which is about *two*
chains and produces a `0`-dimensional count rather than the `1`-dimensional triple intersection.

Route: this is the manifold analogue of `intersection_triple.lean`.  `Submission/Work/Drive/ChartBridge.lean`
plus `Submission/Work/Drive/ManifoldParity/*` already carry out exactly this passage for the `2 + 3`
case (`transverse_inter_boundary_parity`): the charted difference map, its transversality from the
manifold derivatives, the local graph structure of the intersection set, the global tangential field
and the flow pairing of the boundary intersections.  The `3 + 3 + 3` case needs the same construction
with the nine-box `(ℝ³)³` in place of the five-box `ℝ² × ℝ³` and the difference map
`(x₀,x₁,x₂) ↦ (D₀x₀ − D₁x₁, D₀x₀ − D₂x₂)` in place of `(s,t) ↦ Ds − Nt`; see
`Submission/Work/Drive/MANIFOLD_PARITY_STATUS.md` for the existing template. -/
theorem manifold_triple_inter_boundary_parity (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      Work.Drive.TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)))
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          Work.Drive.TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0) :
    (∀ k : Fin 3, (Work.Drive.tripleBdryMeet M D k).Finite) ∧
      Even ((Work.Drive.tripleBdryMeet M D 0).ncard + (Work.Drive.tripleBdryMeet M D 1).ncard
        + (Work.Drive.tripleBdryMeet M D 2).ncard) := by
  classical
  -- the two hypotheses of the target statement, in the nine-box picture
  have htr : Work.Drive.TParity.transHyp D :=
    Work.Drive.TParity.transHyp_of_forall D htrans
  have hfc : Work.Drive.TParity.faceHyp D :=
    Work.Drive.TParity.faceHyp_of_forall D hface
  -- the mod-2 parity of the boundary triple intersections in the nine-box
  obtain ⟨hfin, heven⟩ := Work.Drive.TParity.bK3_even D hD htr hfc
  have hsub : ∀ k : Fin 3, Work.Drive.TParity.S3 D k ⊆ Work.Drive.TParity.bK3 D := by
    intro k x hx
    rw [Work.Drive.TParity.bK3_eq_union]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h
    · subst h; exact Or.inl (Or.inl hx)
    · subst h; exact Or.inl (Or.inr hx)
    · subst h; exact Or.inr hx
  refine ⟨fun k => ?_, ?_⟩
  · exact (Work.Drive.TParity.tripleBdryMeet_finite_iff D k).mpr (hfin.subset (hsub k))
  · rw [← Work.Drive.TParity.S3_ncard_eq D 0, ← Work.Drive.TParity.S3_ncard_eq D 1,
      ← Work.Drive.TParity.S3_ncard_eq D 2]
    exact heven

end Work.Drive
