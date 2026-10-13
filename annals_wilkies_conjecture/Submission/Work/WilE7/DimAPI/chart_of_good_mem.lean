import Mathlib
import Submission.Work.WilE7.DimAPI.openMap_of_equalDim
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.Chart.exists_continuousLinearEquiv_ker
import Submission.Work.WilE9G.Sard.levelSetChartAnalytic
import Submission.Work.WilE7.DimAPI.absSet_local_levelSet
import Submission.Work.WilE7.DimAPI.fnpFibre_absPt_surj
import Submission.Work.WilE7.Chart.injective_fderiv_of_eventually_leftInv

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.Nondrop

/-! ## The local chart of a `Good` absolute stratum

Every point of a `Good` absolute stratum `S : Stratum 0 N` has a neighbourhood (inside the
stratum) which is the image of an analytic, injective parametrisation by `ℝ^{N - S.j}` — i.e.
the germ of the stratum at the point is an analytic manifold germ of dimension `N - S.j`.

The route.  Write `absPt z` for `z : Fin (0 + N) → ℝ` reindexed to `Fin N → ℝ`, `absSet S`
for `S.X.set` in these coordinates, and `g := fnpFibre S (projFirst 0 N z)` for the fibre map
of `S` at the (unique) base point of `z`.

* `absSet_local_levelSet` (`Work.WilE7.DimAPI.absSet_local_levelSet`, delegated): on `absSet S`
  the map `g` vanishes, and near `absPt z` the converse holds; so the stratum germ is the level
  set of `g`.
* `fnpFibre_absPt_surj` (`Work.WilE7.DimAPI.fnpFibre_absPt_surj`, delegated): `g` is a
  submersion at `absPt z`, and `finrank ℝ (ker (dg)) = N - S.j` (`Stratum.Good` gives the full
  rank of the fibrewise Jacobian).
* `Work.WilE9G.Sard.levelSetChartAnalytic`: the analytic implicit-function chart
  `γ₀ : ker (dg) → ℝ^N` of the level set `{g = g (absPt z)}`, together with an open
  neighbourhood `V` of `0` on which it is analytic and injective (the latter from the
  projection clause `C (γ₀ t - absPt z) = t`), with `dγ₀ 0` injective
  (`Work.WilE7.Chart.injective_fderiv_of_eventually_leftInv`, delegated).
* `Work.WilE7.Chart.exists_continuousLinearEquiv_ker`: a linear homeomorphism
  `ℝ^{N - S.j} ≃ ker (dg)`; precomposing `γ₀` with it gives the parametrisation `γ` on an open
  `Ω ∋ 0`, chosen small enough that `γ` lands in `absSet S`.
* `Work.WilE7.DimAPI.levelSet_subset_image_of_inj`: since `γ '' Ω ⊆ absSet S` and `γ` has
  injective differential at `0` of the right dimension, `γ '' Ω` covers the germ of the level
  set — hence the germ of the stratum. -/

theorem chart_of_good_mem {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (hS : S.Good)
    (z : Fin (0 + N) → ℝ) (hz : z ∈ S.X.set) :
    ∃ (γ : (Fin (N - S.j) → ℝ) → (Fin N → ℝ)) (Ω : Set (Fin (N - S.j) → ℝ)),
      IsOpen Ω ∧ (0 : Fin (N - S.j) → ℝ) ∈ Ω ∧
      γ 0 = Work.WilE7.MainDesign.absPt z ∧
      AnalyticOnNhd ℝ γ Ω ∧
      Set.InjOn γ Ω ∧
      Function.Injective (fderiv ℝ γ 0) ∧
      γ '' Ω ⊆ Work.WilE7.MainDesign.absSet S ∧
      (∀ᶠ w in nhds (Work.WilE7.MainDesign.absPt z),
        w ∈ Work.WilE7.MainDesign.absSet S → w ∈ γ '' Ω) := by
  classical
  -- The stratum is locally the level set of the fibre map.
  obtain ⟨hlevel_mem, hlevel_nhd⟩ := absSet_local_levelSet S hS z hz
  obtain ⟨hsurj, hkerdim⟩ := fnpFibre_absPt_surj S hS z hz
  have hsurjtop : (fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
      (Work.WilE7.MainDesign.absPt z)).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hzero : fnpFibre S (WilkiesDesign.E.projFirst 0 N z)
      (Work.WilE7.MainDesign.absPt z) = 0 :=
    hlevel_mem _ ⟨z, hz, rfl⟩
  -- The implicit-function chart of the level set.
  obtain ⟨C, γ₀, V, U, hVopen, hUopen, h0V, hzU, hγ₀0, hγ₀anV, hγ₀VU, hγ₀lev, hγ₀C, hγ₀surj⟩ :=
    Work.WilE9G.Sard.levelSetChartAnalytic (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
      (Work.WilE7.MainDesign.absPt z) (fnpFibre_analytic S (WilkiesDesign.E.projFirst 0 N z))
      hsurj
  have hγ₀an : AnalyticAt ℝ γ₀ 0 := hγ₀anV 0 h0V
  -- Injectivity of the differential of the chart.
  have hγ₀dinj : Function.Injective (fderiv ℝ γ₀ 0) := by
    have hdiff : DifferentiableAt ℝ
        (fun t => γ₀ t - Work.WilE7.MainDesign.absPt z) 0 :=
      hγ₀an.differentiableAt.sub_const _
    have hleft : ∀ᶠ t in nhds (0 : ↥(fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
        (Work.WilE7.MainDesign.absPt z)).ker),
        C ((fun t => γ₀ t - Work.WilE7.MainDesign.absPt z) t) = t :=
      (Filter.mem_of_superset (hVopen.mem_nhds h0V) (fun t ht => hγ₀C t ht))
    have h := Work.WilE7.Chart.injective_fderiv_of_eventually_leftInv hdiff hleft
    rwa [fderiv_sub_const] at h
  have hγ₀injOn : Set.InjOn γ₀ V := by
    intro t ht t' ht' htt
    rw [← hγ₀C t ht, htt, hγ₀C t' ht']
  -- The linear reindexing of the kernel with `ℝ^{N - S.j}`.
  obtain ⟨e⟩ := Work.WilE7.Chart.exists_continuousLinearEquiv_ker
    (fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z)) (Work.WilE7.MainDesign.absPt z))
    hsurjtop
  -- The open neighbourhood of `0` where the chart values lie in the stratum.
  obtain ⟨B, hBmem, hBsub⟩ := Filter.eventually_iff_exists_mem.mp hlevel_nhd
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hBmem
  have hballsub : ∀ w ∈ Metric.ball (Work.WilE7.MainDesign.absPt z) δ,
      fnpFibre S (WilkiesDesign.E.projFirst 0 N z) w = 0 →
        w ∈ Work.WilE7.MainDesign.absSet S :=
    fun w hw => hBsub w (hδsub hw)
  have hGmem : γ₀ ⁻¹' Metric.ball (Work.WilE7.MainDesign.absPt z) δ ∈
      nhds (0 : ↥(fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
        (Work.WilE7.MainDesign.absPt z)).ker) :=
    hγ₀an.continuousAt.preimage_mem_nhds
      (by rw [hγ₀0]; exact Metric.ball_mem_nhds _ hδpos)
  obtain ⟨Ω₀, hΩ₀sub, hΩ₀open, h0Ω₀⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hVopen.mem_nhds h0V) hGmem)
  -- The parametrisation and its domain.
  let γ : (Fin (N - S.j) → ℝ) → (Fin N → ℝ) := fun s => γ₀ (e s)
  let Ω : Set (Fin (N - S.j) → ℝ) := e ⁻¹' Ω₀
  have hΩopen : IsOpen Ω := hΩ₀open.preimage e.continuous
  have h0Ω : (0 : Fin (N - S.j) → ℝ) ∈ Ω := by
    show e 0 ∈ Ω₀
    rw [map_zero]; exact h0Ω₀
  have hγan : AnalyticOnNhd ℝ γ Ω :=
    fun s hs => (hγ₀anV (e s) (hΩ₀sub hs).1).comp (e.analyticAt s)
  have hγinjOn : Set.InjOn γ Ω := by
    intro s hs s' hs' hss
    exact e.injective (hγ₀injOn (hΩ₀sub hs).1 (hΩ₀sub hs').1 hss)
  have hγdinj : Function.Injective (fderiv ℝ γ 0) := by
    have hcomp : fderiv ℝ γ 0
        = (fderiv ℝ γ₀ 0).comp (e : (Fin (N - S.j) → ℝ) →L[ℝ]
            ↥(fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
              (Work.WilE7.MainDesign.absPt z)).ker) := by
      have h1 : HasFDerivAt (fun s : Fin (N - S.j) → ℝ => e s)
          (e : (Fin (N - S.j) → ℝ) →L[ℝ]
            ↥(fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
              (Work.WilE7.MainDesign.absPt z)).ker) 0 :=
        (e : (Fin (N - S.j) → ℝ) →L[ℝ]
          ↥(fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
            (Work.WilE7.MainDesign.absPt z)).ker).hasFDerivAt
      have hf : HasFDerivAt γ₀ (fderiv ℝ γ₀ 0) (e 0) := by
        simpa only [map_zero] using hγ₀an.hasStrictFDerivAt.hasFDerivAt
      exact (hf.comp (0 : Fin (N - S.j) → ℝ) h1).fderiv
    rw [hcomp]
    exact hγ₀dinj.comp (fun v w h => e.injective h)
  have himage : γ '' Ω ⊆ Work.WilE7.MainDesign.absSet S := by
    rintro w ⟨s, hs, rfl⟩
    exact hballsub (γ₀ (e s)) (hΩ₀sub hs).2
      (by rw [hγ₀lev (e s) (hΩ₀sub hs).1, hzero])
  have hΩmem : Ω ∈ nhds (0 : Fin (N - S.j) → ℝ) := hΩopen.mem_nhds h0Ω
  have hγan0 : AnalyticAt ℝ γ 0 := hγan 0 h0Ω
  have hγ0 : γ 0 = Work.WilE7.MainDesign.absPt z := by
    show γ₀ (e 0) = Work.WilE7.MainDesign.absPt z
    rw [map_zero, hγ₀0]
  have hdim : Module.finrank ℝ (fderiv ℝ (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
      (Work.WilE7.MainDesign.absPt z)).ker = Module.finrank ℝ (Fin (N - S.j) → ℝ) := by
    rw [hkerdim, Module.finrank_fin_fun]
  have hlevel : ∀ᶠ s in nhds (0 : Fin (N - S.j) → ℝ),
      fnpFibre S (WilkiesDesign.E.projFirst 0 N z) (γ s)
        = fnpFibre S (WilkiesDesign.E.projFirst 0 N z) (Work.WilE7.MainDesign.absPt z) :=
    Filter.mem_of_superset hΩmem
      (fun s hs => by
        simp only [Set.mem_ofPred_eq]
        rw [hlevel_mem (γ s) (himage ⟨s, hs, rfl⟩), hzero])
  -- The germ-covering statement, from the level-set covering lemma.
  have hcover : ∀ᶠ w in nhds (Work.WilE7.MainDesign.absPt z),
      w ∈ Work.WilE7.MainDesign.absSet S → w ∈ γ '' Ω := by
    obtain ⟨O, hO, hOprop⟩ :=
      levelSet_subset_image_of_inj (fnpFibre S (WilkiesDesign.E.projFirst 0 N z))
        (Work.WilE7.MainDesign.absPt z)
        (fnpFibre_analytic S (WilkiesDesign.E.projFirst 0 N z)) hsurjtop hγ0 hγan0 hγdinj
        hdim hlevel Ω hΩmem
    refine Filter.mem_of_superset hO (fun w hw hwS => ?_)
    obtain ⟨s, hsΩ, hγs⟩ := hOprop w hw (by rw [hlevel_mem w hwS, hzero])
    exact ⟨s, hsΩ, hγs⟩
  exact ⟨γ, Ω, hΩopen, h0Ω, hγ0, hγan, hγinjOn, hγdinj, himage, hcover⟩

end Work.WilE7.DimAPI
