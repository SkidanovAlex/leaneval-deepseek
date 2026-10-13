import Mathlib
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv

namespace Work.CoreStep

open scoped Topology

theorem exists_levelSet_chart {N : ℕ} (W : WilkiesDesign.E.Stratum 0 N) (hW : W.Good)
    (z : Fin (0 + N) → ℝ) (hz : z ∈ W.X.set)
    (V0 : Set (Fin (0 + N) → ℝ)) (hV0 : V0 ∈ nhds z) :
    ∃ (γ : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker → (Fin (0 + N) → ℝ))
      (V : Set (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker)
      (U : Set (Fin (0 + N) → ℝ))
      (χ : (Fin (0 + N) → ℝ) → (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker),
      IsOpen V ∧ (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker) ∈ V ∧ γ 0 = z ∧
      AnalyticAt ℝ γ 0 ∧
      (fderiv ℝ γ 0).range = (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker ∧
      Set.InjOn γ V ∧ (∀ v ∈ V, γ v ∈ W.X.set ∧ γ v ∈ V0) ∧
      IsOpen U ∧ z ∈ U ∧ AnalyticAt ℝ χ z ∧
      (∀ y ∈ U, Work.WilE7.DimAPI.eqMap W y = 0 → χ y ∈ V ∧ γ (χ y) = y) := by
  -- the equations vanish at `z`
  have hg0 : Work.WilE7.DimAPI.eqMap W z = 0 :=
    Work.WilE7.DimAPI.eqMap_eq_zero_of_good W hW hz
  -- the differential of the equation map at `z` is surjective
  have hsurj : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).range = ⊤ :=
    Work.WilE7.DimAPI.range_fderiv_good_eq_top W hW hz
  -- the analytic implicit-function chart of the level set of `eqMap W` at `z`
  obtain ⟨γ, V, U, χ, hVopen, hUopen, h0V, hzU, hγ0, hγan, -, hγlvl, -, hInj, hrange, hχan,
    hχinv⟩ :=
    Work.WilE7.Nondrop.analyticLevelSetChartRange (Work.WilE7.DimAPI.eqMap W) z
      (Work.WilE7.DimAPI.analyticAt_eqMap W) hsurj
  -- `Good` gives an open neighbourhood of `z` on which the level set of `eqMap W` lies in `W.X.set`
  have hloc : ∀ᶠ y in nhds z, Work.WilE7.DimAPI.eqMap W y = 0 → y ∈ W.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hW hz] with y hy hy0
    exact hy (Subsingleton.elim _ _) fun a => congrFun hy0 a
  obtain ⟨T, hTsub, hTopen, hzT⟩ := mem_nhds_iff.mp hloc
  have hTin : T ∈ nhds z := hTopen.mem_nhds hzT
  -- `γ` is continuous at `0`, so the tube on which `γ` stays inside `V0 ∩ T` is a neighbourhood
  have hγpre : γ ⁻¹' (V0 ∩ T) ∈ nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W) z).ker) := by
    refine hγan.continuousAt.preimage_mem_nhds ?_
    rw [hγ0]
    exact Filter.inter_mem hV0 hTin
  -- `χ z = 0`, by injectivity of `γ` on `V`
  have hχz0 : χ z = 0 := by
    have hχz := hχinv z hzU (by rw [hg0])
    exact hInj hχz.1 h0V (by rw [hχz.2, hγ0])
  -- an open neighbourhood `V'` of `0` in the kernel with `V' ⊆ V` and `γ` mapping it into `V0 ∩ T`
  obtain ⟨V', hV'sub, hV'open, h0V'⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hVopen.mem_nhds h0V) hγpre)
  -- an open neighbourhood `U'` of `z` on which the chart `χ` lands in `V'`
  have hχpre : χ ⁻¹' V' ∈ nhds z := by
    refine hχan.continuousAt.preimage_mem_nhds ?_
    rw [hχz0]
    exact hV'open.mem_nhds h0V'
  obtain ⟨U', hU'sub, hU'open, hzU'⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hUopen.mem_nhds hzU) hχpre)
  exact ⟨γ, V', U', χ, hV'open, h0V', hγ0, hγan, hrange,
    hInj.mono fun v hv => (hV'sub hv).1,
    fun v hv => ⟨hTsub (hV'sub hv).2.2 (by rw [hγlvl v (hV'sub hv).1, hg0]),
      (hV'sub hv).2.1⟩,
    hU'open, hzU', hχan, fun y hy hy0 =>
      ⟨(hU'sub hy).2, (hχinv y (hU'sub hy).1 (by rw [hy0, hg0])).2⟩⟩

end Work.CoreStep
