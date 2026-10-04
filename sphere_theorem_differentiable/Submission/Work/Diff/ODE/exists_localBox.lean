import Mathlib
import Submission.Work.Diff.ODE.Basic
import Submission.Work.Diff.ODE.ChartField
import Submission.Work.Diff.ODE.chartField_contDiffOn
import Submission.Work.Diff.ODE.LocalFlow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of a local flow box for a jointly smooth time-dependent vector field

`Work.Diff.ODE.exists_localBox`: every point `(a₀, x₀)` of `ℝ × M` (with `M` a `C^∞`-manifold
without boundary, and `X : ℝ → Π x, TangentSpace I x` a jointly smooth time-dependent vector
field) lies in the domain `U` of a local flow box for `X` (`Work.Diff.ODE.LocalBox`).

The proof runs the standard "extended phase space" trick.  In the chart at `x₀` the field `X`
becomes the coordinate field `F = chartField X x₀ : ℝ × E → E`, which is smooth on
`univ × (extChartAt I x₀).target` (`chartField_contDiffOn`).  The *autonomous* field
`G (a, v) = (1, F (a, v))` on `ℝ × E` has, by `Commons.Analysis.ODE.uniform_flow_joint` (smooth
dependence on the initial condition, locally uniform in time), a flow `α` on a neighbourhood of
`K = [a₀ - 1, a₀ + 1] × closedBall (chart x₀) r`, whose second component solves the time-dependent
equation of `F` while its first component is `a + τ` (`fst_flow_eq_add`).  Transporting back through
the chart gives the local flow box: the box `U` is the set of parameters whose chart image lies in
the *open* box `K' = (a₀ - 1, a₀ + 1) × ball (chart x₀) r ⊆ K` (`isOpen_chartBox`), the flow is
`FL τ a y = chart⁻¹ ((α (a, chart y) τ).2)`, its equation is `hasMFDerivAt_chartCurve`, and its
smoothness is `contMDiffAt_chartFlow`.
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Set

theorem exists_localBox
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (a₀ : ℝ) (x₀ : M) :
    ∃ B : Work.Diff.ODE.LocalBox X, (a₀, x₀) ∈ B.U := by
  classical
  -- ## The chart data
  have hx₀src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hv₀tgt : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hx₀src)
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ (extChartAt I x₀).target := by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x₀) _ hv₀tgt
    refine ⟨ε / 2, by linarith, fun z hz => hsub ?_⟩
    rw [Metric.mem_ball, dist_comm]
    have h := Metric.mem_closedBall.mp hz
    rw [dist_comm] at h
    linarith
  -- ## The coordinate field and its extended (autonomous) version
  set F : ℝ × E → E := chartField X x₀ with hFdef
  set G : ℝ × E → ℝ × E := fun p => ((1 : ℝ), F p) with hGdef
  set W : Set (ℝ × E) := Set.prod Set.univ (extChartAt I x₀).target with hWdef
  set K : Set (ℝ × E) := Set.prod (Set.Icc (a₀ - 1) (a₀ + 1))
    (Metric.closedBall ((extChartAt I x₀) x₀) r) with hKdef
  set K' : Set (ℝ × E) := Set.prod (Set.Ioo (a₀ - 1) (a₀ + 1))
    (Metric.ball ((extChartAt I x₀) x₀) r) with hK'def
  have hWopen : IsOpen W := by
    rw [hWdef]; exact isOpen_univ.prod (isOpen_extChartAt_target x₀)
  have hF : ContDiffOn ℝ ∞ F W := by
    rw [hFdef, hWdef]
    exact chartField_contDiffOn (I := I) hX x₀
  have hG : ContDiffOn ℝ ∞ G W := by
    rw [hGdef]
    exact contDiffOn_const.prodMk hF
  have hKcpt : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKW : K ⊆ W := by
    rw [hKdef, hWdef]
    intro p hp
    exact ⟨trivial, hrsub hp.2⟩
  have hK'K : K' ⊆ K := by
    rw [hK'def, hKdef]
    exact Set.prod_mono Ioo_subset_Icc_self Metric.ball_subset_closedBall
  have hK'open : IsOpen K' := by
    rw [hK'def]
    exact isOpen_Ioo.prod Metric.isOpen_ball
  have hK'W : K' ⊆ W := hK'K.trans hKW
  -- ## The uniform local flow of the extended field
  obtain ⟨ρ, hρ, O, hOopen, hKO, hOW, α, hα0, hαode, hαmem, hαsmooth, _hαuniq⟩ :=
    Commons.Analysis.ODE.uniform_flow_joint hWopen hG hKcpt hKW
  have hOW' : O ⊆ Set.prod Set.univ (extChartAt I x₀).target := by
    rw [← hWdef]; exact hOW
  have hKO' : K' ⊆ O := hK'K.trans hKO
  -- ## The box and the local flow
  refine ⟨⟨ρ / 4, by linarith,
      {p : ℝ × M | p.2 ∈ (chartAt H x₀).source ∧ (p.1, (extChartAt I x₀) p.2) ∈ K'},
      isOpen_chartBox (I := I) (x₀ := x₀) hK'open (by rw [hK'def]; exact hK'W),
      fun τ a y => (extChartAt I x₀).symm ((α (a, (extChartAt I x₀) y) τ).2),
      ?_, ?_, ?_⟩, ?_⟩
  · -- the flow starts at the point
    intro a y hay
    obtain ⟨hysrc, hayK'⟩ := hay
    have hysrc' : y ∈ (extChartAt I x₀).source := by
      simpa only [extChartAt_source] using hysrc
    have h0' : α (a, (extChartAt I x₀) y) 0 = (a, (extChartAt I x₀) y) :=
      hα0 _ (hKO' hayK')
    rw [h0']
    exact (extChartAt I x₀).left_inv hysrc'
  · -- the flow solves the ODE
    intro a y hay τ hτ
    obtain ⟨hysrc, hayK'⟩ := hay
    have hysrc' : y ∈ (extChartAt I x₀).source := by
      simpa only [extChartAt_source] using hysrc
    have hpO : (a, (extChartAt I x₀) y) ∈ O := hKO' hayK'
    have hτρ : |τ| ≤ ρ := by
      have h2 : 2 * (ρ / 4) = ρ / 2 := by ring
      rw [h2] at hτ
      linarith
    have hode_p := hαode (a, (extChartAt I x₀) y) hpO τ hτρ
    have hfst_eq : (α (a, (extChartAt I x₀) y) τ).1 = a + τ :=
      fst_flow_eq_add (F := F) (O := O) (ρ := ρ) hα0 hαode hpO hτρ
    have hpair : α (a, (extChartAt I x₀) y) τ =
        (a + τ, (α (a, (extChartAt I x₀) y) τ).2) := by
      rw [← hfst_eq]
    have hw : HasDerivAt (fun σ : ℝ => (α (a, (extChartAt I x₀) y) σ).2)
        (F (a + τ, (α (a, (extChartAt I x₀) y) τ).2)) τ := by
      have h := hasDerivAt_snd_prod hode_p
      rw [hGdef] at h
      rw [hpair] at h
      exact h
    have hmem_tgt : (α (a, (extChartAt I x₀) y) τ).2 ∈ (extChartAt I x₀).target :=
      (hαmem _ hpO τ hτρ).2
    refine hasMFDerivAt_chartCurve (I := I) (X := X) (x₀ := x₀) (a := a) (τ := τ)
      (w := fun σ : ℝ => (α (a, (extChartAt I x₀) y) σ).2) (v := F (a + τ,
        (α (a, (extChartAt I x₀) y) τ).2)) hw hmem_tgt ?_ ?_
    · -- the coordinate curve stays in the chart target near `τ`
      have hτlt : |τ| < ρ := by linarith
      filter_upwards [Metric.ball_mem_nhds τ (by linarith : 0 < ρ - |τ|)] with σ hσ
      rw [Metric.mem_ball, Real.dist_eq] at hσ
      have hbound : |σ| < ρ := by
        have h1 : |σ| ≤ |σ - τ| + |τ| := by
          have h2 : σ = (σ - τ) + τ := by ring
          calc |σ| = |(σ - τ) + τ| := congrArg (fun z : ℝ => |z|) h2
            _ ≤ |σ - τ| + |τ| := abs_add_le (σ - τ) τ
        linarith
      exact (hαmem _ hpO σ (le_of_lt hbound)).2
    · -- the coordinate vector is the reading of `X (a + τ)`
      simp only [hFdef, chartField]
  · -- smooth dependence on the initial parameter and the time
    intro a y hay τ hτ
    obtain ⟨hysrc, hayK'⟩ := hay
    have hysrc' : y ∈ (extChartAt I x₀).source := by
      simpa only [extChartAt_source] using hysrc
    have hpK : (a, (extChartAt I x₀) y) ∈ K := hK'K hayK'
    have hpO : (a, (extChartAt I x₀) y) ∈ O := hKO' hayK'
    have hτρ : |τ| < ρ := by
      have h2 : 2 * (ρ / 4) = ρ / 2 := by ring
      rw [h2] at hτ
      linarith
    have hsmooth_at := hαsmooth (a, (extChartAt I x₀) y) hpK τ hτρ
    have htgt : (α (a, (extChartAt I x₀) y) τ).2 ∈ (extChartAt I x₀).target :=
      (hαmem _ hpO τ (le_of_lt hτρ)).2
    exact contMDiffAt_chartFlow (I := I) (x₀ := x₀) hysrc' hsmooth_at htgt
  · -- the point `(a₀, x₀)` lies in the box
    refine ⟨hx₀src, ?_⟩
    rw [hK'def]
    exact ⟨by constructor <;> linarith, Metric.mem_ball_self hrpos⟩

end Work.Diff.ODE
