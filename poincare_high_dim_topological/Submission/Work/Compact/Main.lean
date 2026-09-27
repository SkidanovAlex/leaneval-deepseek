import Submission.Work.Compact.Connected.connectedSpace_of_homotopyEquiv_sphere
import Submission.Work.Compact.Noncompact.isZero_homology_of_noncompact
import Submission.Work.Cohomology.sphereHomologyTop

/-!
# Compactness of a homotopy `n`-sphere (`n ≥ 1`)

**Main result of this area** (`Work.Compact.compactSpace_of_homotopyEquiv_sphere`): a Hausdorff
`n`-manifold which is homotopy equivalent to the standard `n`-sphere is compact.  This is step R0
of the Poincaré blueprint: it turns the homotopy-theoretic hypothesis of the challenge into a
compactness hypothesis, which the engulfing chapter needs.

The proof is the standard one via top homology:

* `Hₙ(M; ℤ) ≅ Hₙ(Sⁿ; ℤ) ≅ ℤ` because `M ≃ₕ Sⁿ` (`Work.Cohomology.homologyIso_of_homotopyEquiv`)
  and `Hₙ(Sⁿ; ℤ) ≅ ℤ` (`Work.Cohomology.sphereHomologyTop`);
* a connected *noncompact* `n`-manifold has `Hₙ(M; ℤ) = 0`
  (`Work.Compact.Noncompact.isZero_homology_of_noncompact`, Hatcher Prop. 3.29);
* so if `M` were noncompact its top homology would be both `ℤ` and `0`, a contradiction.

The homology is that of the ported fleet library `Submission/Work/Cohomology/` (namespace
`Work.Cohomology`), which uses `ℤ` coefficients and Mathlib's singular chain complex.

The statements here are at universe `0`, which is the universe of that library
(`Work.Cohomology.singularChains` takes `TopCat.{0}`); see `Work.Compact.univ` for the reduction
of the universe-polymorphic statement of the challenge to this one.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace Work.Compact

/-- `Hₙ(·; ℤ)` of a space homotopy equivalent to `Sⁿ` is `ℤ` (`n ≥ 1`). -/
theorem homology_top_iso_of_homotopyEquiv_sphere (n : ℕ) (hn : 1 ≤ n) {M : Type}
    [TopologicalSpace M]
    (e : ContinuousMap.HomotopyEquiv M
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv e n
  obtain ⟨e2⟩ := Work.Cohomology.sphereHomologyTop n hn
  exact ⟨e1 ≪≫ e2⟩

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is compact** (`n ≥ 1`). -/
theorem compactSpace_of_homotopyEquiv_sphere (n : ℕ) (hn : 1 ≤ n) {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : ContinuousMap.HomotopyEquiv M
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    CompactSpace M := by
  by_contra hM
  haveI : NoncompactSpace M := ⟨fun h => hM ⟨h⟩⟩
  haveI : ConnectedSpace M :=
    Work.Compact.Connected.connectedSpace_of_homotopyEquiv_sphere n hn e
  have hzero : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n) :=
    Work.Compact.Noncompact.isZero_homology_of_noncompact n hn
  obtain ⟨e1⟩ := homology_top_iso_of_homotopyEquiv_sphere n hn e
  have hZ : IsZero (ModuleCat.of ℤ ℤ) := hzero.of_iso e1.symm
  have hid : (𝟙 (ModuleCat.of ℤ ℤ)) = 0 := (IsZero.iff_id_eq_zero (ModuleCat.of ℤ ℤ)).mp hZ
  have h10 : (1 : ℤ) = 0 := by
    have h := congrArg
      (fun f : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ) => (show ℤ → ℤ from f) 1) hid
    simpa using h
  exact one_ne_zero h10

end Work.Compact
