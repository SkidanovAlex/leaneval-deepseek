import Mathlib
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.chartBall_transport
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen
import Submission.Lib.Unif2.Work.SimplyConnected.PushOff

/-!
# Surjectivity of `π₁(X ∖ {z₀}) → π₁(X)` for a Riemann surface

For a connected complex one-manifold `X` (a Riemann surface), a point `z₀ : X` and a base point
`u₀ : X ∖ {z₀}`, the map of fundamental groups induced by the inclusion `X ∖ {z₀} ↪ X`

`π₁(X ∖ {z₀}, u₀) → π₁(X, u₀)`

is surjective: *a loop in `X` can be pushed off the point `z₀`*.

## The argument

Let `D` be a small simply connected chart ball around `z₀`, chosen so small that it misses the base
point `u₀` (possible because `u₀ ≠ z₀` and `X` is Hausdorff).  Then `U := X ∖ {z₀}` and `D` are
open sets covering `X`, `U` is path connected (the punctured surface is connected, and it is open
in a locally path connected space), `U ∩ D = D ∖ {z₀}` is path connected (a punctured chart ball)
and `D` is simply connected (a chart ball is homeomorphic to a ball in `ℂ`, hence contractible).

`Work.SimplyConnected.exists_path_homotopic_mem_of_open_cover` (the surjectivity half of van
Kampen for the cover `{U, D}`, proved in `PushOff.lean`) then shows that every loop at `u₀` in `X`
is homotopic, relative to the base point, to a loop whose image lies in `U`.  Reading that loop as
a loop of the punctured surface gives a preimage of the class of the original loop.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.SimplyConnected

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A point of a punctured ball of `ℂ`. -/
theorem mem_ball_diff_singleton {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    c + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball c ρ \ {c} := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hz : c + ((ρ / 2 : ℝ) : ℂ) - c = ((ρ / 2 : ℝ) : ℂ) := by ring
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ρ / 2)]
    linarith
  · intro h
    have h2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
      have := congrArg (fun z : ℂ => z - c) h
      simpa using this
    have h3 : ρ / 2 = 0 := by simpa using h2
    linarith

/-- **A punctured ball of `ℂ` is path connected.** -/
theorem isPathConnected_ball_diff_singleton {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    IsPathConnected (Metric.ball c ρ \ {c}) :=
  (Metric.isOpen_ball.sdiff isClosed_singleton).isConnected_iff_isPathConnected.mp
    ⟨⟨c + ((ρ / 2 : ℝ) : ℂ), mem_ball_diff_singleton hρ⟩,
      Work.Modulus.isPreconnected_ball_diff_center hρ⟩

/-- **The punctured surface `X ∖ {z₀}` is path connected.** -/
theorem isPathConnected_punctured (z₀ : X) : IsPathConnected ({z₀}ᶜ : Set X) := by
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have hconn : IsConnected ({z₀}ᶜ : Set X) :=
    isConnected_iff_connectedSpace.mpr (Work.Modulus.puncturedConnected z₀)
  exact (isOpen_compl_singleton.isConnected_iff_isPathConnected).mp hconn

/-- **A chart ball around `z₀` missing `u`, which is simply connected and whose punctured version is
path connected.** -/
theorem exists_chartBall_punctured {z₀ u : X} (hu : u ≠ z₀) :
    ∃ D : Set X, IsOpen D ∧ z₀ ∈ D ∧ u ∉ D ∧ IsSimplyConnected D ∧
      IsPathConnected (D \ {z₀}) := by
  classical
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with he
  set c : ℂ := e z₀ with hc
  have hzsrc : z₀ ∈ e.source := mem_chart_source ℂ z₀
  have hct : c ∈ e.target := hc ▸ mem_chart_target ℂ z₀
  obtain ⟨ρ₁, hρ₁, hball₁⟩ : ∃ ρ₁ > 0, Metric.ball c ρ₁ ⊆ e.target := by
    obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.isOpen_iff.mp e.open_target c hct
    exact ⟨ρ₁, hρ₁, hb⟩
  let ρ : ℝ := if _ : u ∈ e.source then min (ρ₁ / 2) (dist (e u) c / 2) else ρ₁ / 2
  have huc : u ∈ e.source → e u ≠ c := by
    intro hsrc h
    exact hu (e.injOn hsrc hzsrc (by rw [← hc]; exact h))
  have hρpos : 0 < ρ := by
    dsimp only [ρ]
    split_ifs with hsrc
    · refine lt_min (by linarith) ?_
      have := dist_pos.mpr (huc hsrc)
      linarith
    · linarith
  have hρlt : ρ < ρ₁ := by
    dsimp only [ρ]
    split_ifs with hsrc
    · have := min_le_left (ρ₁ / 2) (dist (e u) c / 2)
      linarith
    · linarith
  have hsub : Metric.closedBall c ρ ⊆ e.target :=
    (Metric.closedBall_subset_ball hρlt).trans hball₁
  have hnotmem : u ∉ Submission.chartBall e c ρ := by
    intro hmem
    rw [Submission.mem_chartBall] at hmem
    dsimp only [ρ] at hmem
    split_ifs at hmem with hsrc
    · have h1 : dist (e u) c < dist (e u) c / 2 :=
        lt_of_lt_of_le hmem.2 (min_le_right _ _)
      have h2 : 0 < dist (e u) c := dist_pos.mpr (huc hsrc)
      linarith
    · exact hsrc hmem.1
  have himg : e.symm '' Metric.ball c ρ = Submission.chartBall e c ρ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z ∈ e.target := hsub (Metric.ball_subset_closedBall hz)
      rw [Submission.mem_chartBall]
      exact ⟨e.map_target hzt, by rw [e.right_inv hzt]; exact hz⟩
    · intro hy
      rw [Submission.mem_chartBall] at hy
      exact ⟨e y, hy.2, e.left_inv hy.1⟩
  have hsc : IsSimplyConnected (Submission.chartBall e c ρ) := by
    rw [← himg]
    exact (Work.SimplyConnected.ABS.chartBall_transport e hρpos hsub).2.2.2.2.2.2
  have hz₀mem : z₀ ∈ Submission.chartBall e c ρ := by
    rw [Submission.mem_chartBall]
    exact ⟨hzsrc, by rw [hc]; exact Metric.mem_ball_self hρpos⟩
  have hpc : IsPathConnected (Submission.chartBall e c ρ \ {z₀}) := by
    haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
    have hpt : c + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball c ρ \ {c} := mem_ball_diff_singleton hρpos
    have hne : (Submission.chartBall e c ρ \ {z₀}).Nonempty := by
      refine ⟨e.symm (c + ((ρ / 2 : ℝ) : ℂ)), ?_⟩
      refine ⟨?_, ?_⟩
      · rw [← himg]
        exact ⟨_, hpt.1, rfl⟩
      · intro h
        have hzt : c + ((ρ / 2 : ℝ) : ℂ) = c := by
          rw [← e.right_inv (hsub (Metric.ball_subset_closedBall hpt.1)), h, hc]
        exact hpt.2 (Set.mem_singleton_iff.mpr hzt)
    have hpre : IsPreconnected (Submission.chartBall e c ρ \ {z₀}) :=
      Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen
        (Submission.chartBall_isOpen e c ρ) hsc.isPathConnected.isConnected.isPreconnected hz₀mem
    exact ((Submission.chartBall_isOpen e c ρ).sdiff isClosed_singleton).isConnected_iff_isPathConnected.mp
      ⟨hne, hpre⟩
  exact ⟨Submission.chartBall e c ρ, Submission.chartBall_isOpen e c ρ, hz₀mem,
    hnotmem, hsc, hpc⟩

/-- **The inclusion of the punctured surface induces a surjection on `π₁`.** -/
theorem fundamentalGroup_map_surjective_of_punctured {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X}
    (u₀ : Work.Modulus.puncturedOpens z₀) :
    Function.Surjective (FundamentalGroup.map
      (ContinuousMap.mk (Subtype.val : ↥(Work.Modulus.puncturedOpens z₀) → X)
        continuous_subtype_val) u₀) := by
  intro g
  obtain ⟨γ, rfl⟩ : ∃ γ : Path (u₀ : X) (u₀ : X), Path.Homotopic.Quotient.mk γ = g :=
    Quotient.exists_rep g
  obtain ⟨D, hDo, hz₀D, huD, hDsc, hDpc⟩ :=
    exists_chartBall_punctured (X := X) (z₀ := z₀) (u := (u₀ : X)) u₀.2
  have hcover : ({z₀}ᶜ : Set X) ∪ D = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = z₀
    · exact Or.inr (hx ▸ hz₀D)
    · exact Or.inl hx
  have hUDpc : IsPathConnected (({z₀}ᶜ : Set X) ∩ D) := by
    rw [Set.inter_comm]
    exact hDpc
  obtain ⟨γ', hγ'mem, hhom⟩ :=
    exists_path_homotopic_mem_of_open_cover (U := ({z₀}ᶜ : Set X)) (D := D)
      isOpen_compl_singleton hDo hcover (isPathConnected_punctured z₀) hUDpc hDsc
      (p₀ := (u₀ : X)) u₀.2 huD γ
  let γ'' : Path u₀ u₀ :=
    { toContinuousMap :=
        ⟨fun t => ⟨γ' t, hγ'mem t⟩,
          Continuous.subtype_mk γ'.continuous fun t => hγ'mem t⟩
      source' := by apply Subtype.ext; exact γ'.source
      target' := by apply Subtype.ext; exact γ'.target }
  refine ⟨Path.Homotopic.Quotient.mk γ'', ?_⟩
  rw [FundamentalGroup.map_apply]
  have hmk : Path.Homotopic.Quotient.mk (γ''.map continuous_subtype_val) =
      Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk γ'')
        (ContinuousMap.mk (Subtype.val : ↥(Work.Modulus.puncturedOpens z₀) → X)
          continuous_subtype_val) :=
    Path.Homotopic.Quotient.mk_map γ''
      (ContinuousMap.mk (Subtype.val : ↥(Work.Modulus.puncturedOpens z₀) → X)
        continuous_subtype_val)
  rw [← hmk]
  have hcoe : γ''.map continuous_subtype_val = γ' := by
    apply Path.ext
    funext t
    rw [Path.map_coe]
    rfl
  rw [hcoe]
  exact Path.Homotopic.Quotient.eq.mpr hhom.symm

end Work.SimplyConnected
