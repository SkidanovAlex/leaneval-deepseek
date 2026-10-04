import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.metric_equiv_of_ric_bound
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.scalar_max_principle
import Submission.Work.Diff.EXT.shibounds_of_interfaces
import Submission.Work.Diff.EXT.chartBounds_of_shibounds
import Submission.Work.Diff.EXT.metric_equiv_of_curvBound
import Submission.Work.Diff.EXT.curvNormK_jointSmooth
import Submission.Work.Diff.EXT.evolK_of_flow
import Submission.Work.Diff.EXT.glue_seam_T_self
import Submission.Work.Diff.EXT.chartMat_uniform_ell
import Submission.Work.Diff.EXT.chartMat_jets_bounded
import Submission.Work.Diff.EXT.ext_of_bounded_jets
import Submission.Work.Diff.EXT.chartMat_ext_symm_posDef_at_centre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local smooth extension of a Ricci flow across a time where the curvature is bounded

Target: `Work.Diff.EXT.local_ext_of_bounded_curv` (the `H`-input of `glue_extensions`, i.e. the
analytic core of the continuation theorem: bounded curvature implies that the flow is smooth up to
the maximal time and extends a little beyond it).

## The proof as assembled here

`local_ext_of_bounded_curv_of_inputs` (below, proved) reduces the target to four inputs, each stated
and proved in a sibling module of this directory:

* `ShiBounds` (`|∇^k Rm|^2 ≤ C_k` on `[σ,T)` for every `k`), assembled in
  `shibounds_of_interfaces` from `NormSmoothK` (`curvNormK_jointSmooth`), `EvolK`
  (`evolK_of_flow`), `LCSmooth` (T-area) and `ScalarMaxPrinciple` (GE-area);
* the metric equivalence `e^{-2nCt} g(0) ≤ g(t) ≤ e^{2nCt} g(0)` (`metric_equiv_of_curvBound`);
* the passage from covariant to coordinate bounds, `ChartBounds G (T/2) T` plus a uniform lower
  bound (`chartBounds_of_shibounds`);
* the endgame, chart bounds imply the smooth extension (`local_ext_of_chart_bounds`).

`EvolK` (Hamilton's evolution inequality for `|∇^k Rm|^2`) is itself reduced in `evolK_of_flow` to
the componentwise evolution `evolCompK_all`, the Kato identity `laplAt_curvNormK_eq`, the frame
family of the GE area and the frame independence `curvNormK_frame_indep` (proved).

The remaining open inputs are therefore exactly: `EvolCompK` for all `k`, `laplAt_curvNormK_eq`,
`NormSmoothK` for all `k`, `chartBounds_of_shibounds` and `local_ext_of_chart_bounds`.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]


/-! ## The endgame: chart bounds imply the smooth extension -/

/-- **The endgame.**  From the a priori chart bounds `ChartBounds G (T/2) T` and the uniform metric
lower bound `hnd`, the family `G` extends to a jointly smooth family on a two-sided neighbourhood of
`T`.

Per chart centre `x₀`: `chartMat_uniform_ell` supplies a bounded chart neighbourhood `U` on which the
chart matrices have uniform spatial `C^k` bounds and uniform ellipticity; `chartMat_jets_bounded`
upgrades these to uniform bounds on *all* iterated Fréchet derivatives of `(t,y) ↦ chartMat G x₀ t y`
on the slab `(Ico (T/2) T) ×ˢ U`, together with joint smoothness there; `ext_of_bounded_jets`
(Whitney/Borel) then extends the chart matrix smoothly across `t = T`; finally
`chartMat_ext_symm_posDef_at_centre` symmetrises that extension and shrinks the neighbourhood so that
it is symmetric and positive definite on the whole two-sided slab and still contains the chart
centre.  The local data are glued by `glue_seam_T_self`. -/
theorem local_ext_of_chart_bounds_of_chart_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : IsRicciFlow G T)
    (hb : ChartBounds (I := I) (M := M) G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u) :
    ∃ δ > 0, ∃ H₁ : ℝ → SMet I M,
      JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧ ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t := by
  refine glue_seam_T_self G T hT hflow.1 (fun x₀ => ?_)
  obtain ⟨U₁, hU₁o, hU₁m, hU₁b, hjet₁, hell₁⟩ := chartMat_uniform_ell G T hT hflow hb hnd x₀
  obtain ⟨U₂, hU₂o, hU₂m, _hU₂b, hcont₂, hjet₂⟩ := chartMat_jets_bounded G T hT hflow hb hnd x₀
  let U : Set E := U₁ ∩ U₂
  have hUo : IsOpen U := hU₁o.inter hU₂o
  have hUm : (extChartAt I x₀) x₀ ∈ U := ⟨hU₁m, hU₂m⟩
  have hUb : Bornology.IsBounded U := hU₁b.subset Set.inter_subset_left
  have hcont : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      ((Set.Ico (T / 2) T) ×ˢ U) :=
    hcont₂.mono (Set.prod_mono Subset.rfl Set.inter_subset_right)
  have hjet : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico (T / 2) T) ×ˢ U,
      ‖iteratedFDeriv ℝ k (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) p‖ ≤ C := by
    intro k
    obtain ⟨C, hC0, hC⟩ := hjet₂ k
    exact ⟨C, hC0, fun p hp => hC p ⟨hp.1, hp.2.2⟩⟩
  have hell : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j := by
    obtain ⟨ε, hε, h⟩ := hell₁
    exact ⟨ε, hε, fun t ht y hy v => h t ht y hy.1 v⟩
  obtain ⟨U', hU'o, hU'm, hU'sub, δ, hδ, V, hVs, hVeq⟩ :=
    ext_of_bounded_jets (σ := T / 2) (by linarith) hUo hcont hjet hUm
  have hU'b : Bornology.IsBounded U' := hUb.subset hU'sub
  set δ₁ : ℝ := min δ (T / 2) with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; exact lt_min hδ (by linarith)
  have hδ₁le : δ₁ ≤ δ := by rw [hδ₁def]; exact min_le_left _ _
  have hδ₁T : δ₁ ≤ T / 2 := by rw [hδ₁def]; exact min_le_right _ _
  have hVs₁ : ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (T - δ₁) (T + δ₁)) ×ˢ U') :=
    hVs.mono (Set.prod_mono
      (fun x hx => ⟨by linarith [hx.1, hδ₁le], by linarith [hx.2, hδ₁le]⟩) Subset.rfl)
  have hVeq₁ : ∀ t ∈ Set.Ico (T - δ₁) T, ∀ y ∈ U',
      V (t, y) = Work.Diff.EXT.chartMat G x₀ t y :=
    fun t ht y hy => hVeq t ⟨by linarith [ht.1, hδ₁le], ht.2⟩ y hy
  have hell₁' : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T - δ₁) T, ∀ y ∈ U',
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j := by
    obtain ⟨ε, hε, h⟩ := hell
    exact ⟨ε, hε, fun t ht y hy v => h t ⟨by linarith [ht.1, hδ₁T], ht.2⟩ y (hU'sub hy) v⟩
  obtain ⟨δ', hδ'pos, _hδ'le, U'', hU''o, _hU''sub, hU''m, W, hWs, hWeq, hWspd⟩ :=
    chartMat_ext_symm_posDef_at_centre G x₀ T δ₁ hδ₁pos V U' hU'o hU'b
      ((extChartAt I x₀) x₀) hU'm hVs₁ hVeq₁ hell₁'
  exact ⟨δ', hδ'pos, U'', hU''o, hU''m, W, hWs, hWeq, hWspd⟩

/-! ## The target and its assembly -/

/-- **Assembly of the target from its four inputs.**  The `ShiBounds` input is itself assembled in
`shibounds_of_interfaces`; the other three are `metric_equiv_of_curvBound`,
`chartBounds_of_shibounds` and `local_ext_of_chart_bounds`.  (The case `C < 0` is vacuous unless
`finrank ℝ E = 0`, where the metric data are vacuous; the shape below covers `0 ≤ C`.) -/
theorem local_ext_of_bounded_curv_of_inputs
    (hShi : ShiBounds (I := I) (M := M))
    (hmet : ∀ (G : ℝ → SMet I M) (T C : ℝ), 0 < T → IsRicciFlow G T →
      (∀ t ∈ Set.Ico 0 T, CurvBound (G t) C) → 0 ≤ C →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
        (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
        (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hconv : ∀ (G : ℝ → SMet I M) (T C : ℝ), 0 < T → IsRicciFlow G T →
      (∀ t ∈ Set.Ico 0 T, CurvBound (G t) C) → 0 ≤ C →
      (∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
        (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
        (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) →
      ChartBounds (I := I) (M := M) G (T / 2) T ∧
        ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
          a * (G 0).inner x u u ≤ (G t).inner x u u)
    (hext : ∀ (G : ℝ → SMet I M) (T : ℝ), 0 < T → IsRicciFlow G T →
      ChartBounds (I := I) (M := M) G (T / 2) T →
      (∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
          a * (G 0).inner x u u ≤ (G t).inner x u u) →
      ∃ δ > 0, ∃ H₁ : ℝ → SMet I M,
        JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧ ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t)
    (G : ℝ → SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlow G T) (hbound : ∀ t ∈ Set.Ico 0 T, CurvBound (G t) C) :
    ∃ δ > 0, ∃ H₁ : ℝ → SMet I M,
      JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧ ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t :=
  hext G T hT hflow
    (hconv G T C hT hflow hbound hC (hmet G T C hT hflow hbound hC)).1
    (hconv G T C hT hflow hbound hC (hmet G T C hT hflow hbound hC)).2

theorem local_ext_of_bounded_curv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C) :
    ∃ δ > 0, ∃ H₁ : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧
        ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t := by
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  have hShi : ShiBounds (I := I) (M := M) :=
    shibounds_of_interfaces (I := I) (M := M) hLC
      (Work.Diff.GE.scalar_max_principle (I := I) (M := M) hLC)
      (curvNormK_jointSmooth (I := I) (M := M) hLC) (evolK_of_flow (I := I) (M := M))
  have hbound' : ∀ t ∈ Set.Ico 0 T, CurvBound (G t) (max C 0) :=
    fun t ht x e he i j k l => le_trans (hbound t ht x e he i j k l) (le_max_left C 0)
  refine local_ext_of_bounded_curv_of_inputs ?_ ?_ ?_ ?_ G T (max C 0) hT (le_max_right C 0)
    hflow hbound'
  · exact hShi
  · intro G' T' C' hT' hflow' hbound'' hC'
    exact metric_equiv_of_curvBound G' T' C' hT' hC' hflow' hbound''
  · intro G' T' C' hT' hflow' hbound'' hC' hme
    exact chartBounds_of_shibounds (I := I) (M := M) hLC G' T' C' hT' hC' hflow' hbound'' hme hShi
  · intro G' T' hT' hflow' hb' hnd'
    exact local_ext_of_chart_bounds_of_chart_data G' T' hT' hflow' hb' hnd'

end Work.Diff.EXT
