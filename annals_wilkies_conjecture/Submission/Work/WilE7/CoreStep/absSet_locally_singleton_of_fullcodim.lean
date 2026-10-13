import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.DimAPI.fnpFibre_absPt_surj
import Submission.Work.WilE7.DimAPI.absSet_local_levelSet
import Submission.Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv
import Submission.Work.WilE7.DimAPI.chart_of_good_mem

namespace Work.WilE7.CoreStep

open Filter Topology
open scoped Topology

/-- **A `Good` absolute stratum of full codimension is locally a single point.**

`S : Stratum 0 N` is an absolute stratum given by `S.j` equations in `ℝ^N` (`absSet S` is
`S.X.set` reindexed by `absPt : ℝ^{0+N} → ℝ^N`).  If `S` is `Good` and `S.j = N` — i.e. the
stratum has codimension `N`, hence dimension `N - S.j = 0` — then at every `z ∈ S.X.set` the set
`absSet S` is locally just `{absPt z}`.

The mathematics is the local structure theorem for a `Good` stratum
(`Work.WilE7.DimAPI.chart_of_good_mem`): at `z` the germ of `absSet S` is the image of an
analytic immersion `γ : ℝ^{N - S.j} → ℝ^N` with `γ 0 = absPt z`, and this chart *covers* the
germ (every nearby point of `absSet S` is a value of `γ`).  When `S.j = N` the source
`ℝ^{N - S.j} = ℝ^0` is a one-point space, so `γ` is constant with value `absPt z`; the covering
clause then says that every nearby point of `absSet S` is `absPt z`.

(An equivalent formulation — isolation at each point of `absSet S` — is
`Work.CoreStep.absSet_point_isolated`, proved from `Work.WilE7.Dim.fiber_isolated`; the proof
below is self-contained in this module's imports.) -/
theorem absSet_locally_singleton_of_fullcodim {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N)
    (hS : S.Good) (hj : S.j = N) :
    ∀ z ∈ S.X.set, ∀ᶠ w in nhds (Work.WilE7.MainDesign.absPt z),
      w ∈ Work.WilE7.MainDesign.absSet S → w = Work.WilE7.MainDesign.absPt z := by
  intro z hz
  -- The local analytic chart of the `Good` stratum `S` at `z`.
  obtain ⟨γ, Ω, _hΩopen, _h0Ω, hγ0, _hγan, _hγinjOn, _hγdinj, _himage, hcover⟩ :=
    Work.WilE7.DimAPI.chart_of_good_mem S hS z hz
  -- `S.j = N` makes the chart's source `ℝ^{N - S.j} = ℝ^0` a one-point space.
  have hsub : Subsingleton (Fin (N - S.j) → ℝ) := by
    rw [hj, Nat.sub_self]
    refine ⟨fun f g => ?_⟩
    funext i
    exact i.elim0
  -- The chart is therefore constant, equal to `absPt z`, and it covers the germ of `absSet S`.
  filter_upwards [hcover] with w hw hwS
  obtain ⟨s, _hs, hγs⟩ := hw hwS
  rw [← hγs, ← hγ0]
  exact congrArg γ (@Subsingleton.elim (Fin (N - S.j) → ℝ) hsub s 0)

end Work.WilE7.CoreStep
