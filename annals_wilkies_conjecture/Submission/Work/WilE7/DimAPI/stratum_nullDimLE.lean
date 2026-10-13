/-
  `Work.WilE7.DimAPI.stratum_nullDimLE` — node C2 of the E7 main design
  (`Submission/Work/WilE7/E7main_DESIGN.md`): an absolute `Good` stratum `S : Stratum 0 (n+m)` of
  dimension `N - S.j` (`N = n + m`) has `NullDimLE (π_n(S)) (N - S.j)`.

  Route (the design's "20–40 lines, C1 + rank–nullity", but self-contained rather than through the
  packaged Sard node C1):

  * `NullDimLE X μ` unfolds to: for every `e : Fin (μ+1) ↪ Fin n`, the image of `X` under the
    coordinate projection `x ↦ x ∘ e` is Lebesgue-null.  For `μ = N - S.j` there are exactly
    `μ + 1` of these coordinates, and `image_coordMap` identifies
    `(x ↦ x ∘ e) '' (π_n '' absSet S)` with `coordMap n m (μ+1) e '' S.X.set`: the coordinate
    projection of the stratum onto an arbitrary `(μ+1)`-subset of the base coordinates.
  * At every point `z` of the stratum, the derivative of the *coordinate map* `coordMap n m (μ+1) e`
    is the linear map `coordLin n m (μ+1) e`, whose restriction to the tangent space
    `ker (dh(z))` of the stratum has image of dimension `≤ finrank (ker (dh z)) = N - S.j = μ`
    (rank–nullity, with `dh(z)` surjective by `Good`).  Since `μ < μ + 1`, that restriction is
    **never** surjective: every stratum point is a critical point of `coordMap`,
    and Sard for the pair `(h, coordMap)` (`locus_null_of_good_analytic`, the glued form of the
    level-set Sard theorem `WilE9G.Sard.sardOnLevelSet`) makes the projection null.

  The only inputs are the analytic Sard machinery of `WilE9G` (`sardOnLevelSet`, glued over the
  stratum by a Lindelöf cover) and the elementary rank–nullity identity
  `finrank (ker (dh z)) = N - S.j`, both delegated and proved in
  `Submission/Work/WilE7/DimAPI/locus_null_of_good_analytic.lean` and
  `Submission/Work/WilE7/DimAPI/finrank_ker_fderiv_eqMap.lean`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.locus_null_of_good_analytic
import Submission.Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap

set_option autoImplicit false
noncomputable section
open Classical Filter Topology MeasureTheory
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem stratum_nullDimLE {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + m)) (hS : S.Good) :
    Work.WilE7.MainDesign.NullDimLE
      (WilkiesDesign.E.projFirst n m '' Work.WilE7.MainDesign.absSet S) (n + m - S.j) := by
  intro e
  -- Replace the projected stratum by the image of the coordinate map `coordMap n m (μ+1) e`.
  simp only [Work.WilE7.MainDesign.absSet]
  rw [image_coordMap n m (n + m - S.j + 1) e S.X.set]
  -- Sard: the critical points of the coordinate map along the stratum map into a null set.
  obtain ⟨N₁, hN₁, hconcl⟩ := locus_null_of_good_analytic S hS
    (coordMap n m (n + m - S.j + 1) e)
    (fun x => coordMap_analyticAt n m (n + m - S.j + 1) e x)
  refine MeasureTheory.measure_mono_null ?_ hN₁
  rintro y ⟨z, hz, rfl⟩
  refine hconcl z hz ?_
  -- Every point of the stratum is a critical point: the tangent space has dimension `μ < μ + 1`.
  intro hw
  refine not_surj_restrict_of_finrank_le
    (LinearMap.ker ((fderiv ℝ (fun z' : Fin (0 + (n + m)) → ℝ => fun a : Fin S.j =>
      eaEval S.X.c (S.h a) z') z).toLinearMap))
    LinearMap.id (coordLin n m (n + m - S.j + 1) e) ?_ ?_
  · rw [Submodule.map_id]
    rw [finrank_ker_fderiv_eqMap S hS hz]
  · intro w
    obtain ⟨v, hv1, hv2⟩ := hw w
    refine ⟨v, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      simpa using hv1
    · rw [LinearMap.comp_apply, LinearMap.id_apply,
        ← fderiv_coordMap_apply n m (n + m - S.j + 1) e z v]
      exact hv2

end Work.WilE7.DimAPI
