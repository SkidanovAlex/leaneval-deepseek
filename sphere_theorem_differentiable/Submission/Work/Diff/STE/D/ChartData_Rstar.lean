import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.continuousAt_mat_Rstar
import Submission.Work.Diff.STE.contDiffOn_chartComp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.tsupport_zeta_subset
import Submission.Work.Diff.STE.D.Rstar_value_contMDiffAt_source

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: the chart data of the reconstruction `Rstar i u`

The reconstruction `D.Rstar i u` of a family of component functions `u` is a section of the bundle
of bilinear forms on `M`,

`p ↦ ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹ · Σ_ab u a b (coord i p) · eᵢa♭ ⊗ eᵢb♭`

(`Work.Diff.STE.B3Data.Rstar`).  This file proves that it satisfies `Work.Diff.STE.D.ChartData`,
i.e. that its chart matrix in the chart at any point `x₀'` is `C^∞` on the chart target.  This is
the smoothness input which turns a positive definite element of the Galerkin space into a global
smooth metric (`Work.Diff.STE.D.smetOf`).

The proof splits the *value* function `p ↦ Rstar i u p (X p) (Y p)` (for smooth sections `X`, `Y`)
at a point `p₀ : M` in two cases:

* `p₀ ∉ tsupport (ζ i)`: the section vanishes identically on the open complement of
  `tsupport (ζ i)`, so the value function is locally `0`;
* `p₀ ∈ tsupport (ζ i)`: then `p₀` lies in the chart source of `x₀ i`
  (`Work.Diff.STE.D.tsupport_zeta_subset`) and its flat coordinate there has norm `< 2 σ i`
  (`coord_norm_le_sigma_of_mem_tsupport`), so `Rstar` is *there* the explicit smooth product of
  `Work.Diff.STE.B3.Rstar_apply` — this is
  `Work.Diff.STE.D.Rstar_value_contMDiffAt_source`.

Composing with the (smooth) chart inverse and assembling the `Fin n → Fin n → ℝ`-valued function
from its components gives `ChartData`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

noncomputable section

/-- **The flat coordinate of a point of the topological support of `ζ i` is bounded by `σ i`.**
`Work.Diff.STE.D.tsupport_zeta_subset` puts `tsupport (ζ i)` inside the chart source of `x₀ i`;
there `coord i` is continuous, and it is `< σ i` on the (dense in its closure) ordinary support of
`ζ i`, so it is `≤ σ i` on the topological support. -/
lemma coord_norm_le_sigma_of_mem_tsupport
    [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ tsupport (D.ζ i)) :
    ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p‖ ≤ D.σ i := by
  by_contra h
  have hlt0 : D.σ i < ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p‖ := not_le.mp h
  have hsrc : p ∈ (extChartAt I (D.x₀ i)).source :=
    Work.Diff.STE.D.tsupport_zeta_subset D i hp
  have hcont : ContinuousAt (fun q : M => Work.Diff.STE.coord (I := I) (D.x₀ i) q) p :=
    Work.Diff.STE.B3.continuousAt_coord_of_mem_source hsrc
  have hmem : {q : M | D.σ i < ‖Work.Diff.STE.coord (I := I) (D.x₀ i) q‖} ∈ 𝓝 p :=
    hcont.norm.preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt0)
  rw [tsupport] at hp
  rw [mem_closure_iff_nhds] at hp
  obtain ⟨q, hq, hqsupp⟩ := hp _ hmem
  have hq2 : D.σ i < ‖Work.Diff.STE.coord (I := I) (D.x₀ i) q‖ := hq
  have hq' : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) q‖ < D.σ i := (D.hζsupp i q hqsupp).2
  linarith

/-- **The value function `p ↦ Rstar i u p (X p) (Y p)` is smooth at every point of `M`**, for
smooth sections `X`, `Y`.  Off the (closed) topological support of `ζ i` the section vanishes, so
the value is locally `0`; on it, the formula of `Rstar_apply` is a smooth product. -/
lemma Rstar_value_contMDiffAt
    [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (a b : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (u a b))
    (p₀ : M) {X Y : Π q : M, TangentSpace I q}
    (hX : Work.Diff.EXT.SmoothFieldAt I M X p₀)
    (hY : Work.Diff.EXT.SmoothFieldAt I M Y p₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => D.Rstar i u q (X q) (Y q)) p₀ := by
  by_cases hp : p₀ ∈ tsupport (D.ζ i)
  · have hsrc : p₀ ∈ (extChartAt I (D.x₀ i)).source :=
      Work.Diff.STE.D.tsupport_zeta_subset D i hp
    have hlt : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p₀‖ < 2 * D.σ i := by
      have h1 := coord_norm_le_sigma_of_mem_tsupport (I := I) D i hp
      have h2 := D.hσ i
      linarith
    exact Work.Diff.STE.D.Rstar_value_contMDiffAt_source D i u hu hsrc hlt hX hY
  · have hmem : (tsupport (D.ζ i))ᶜ ∈ 𝓝 p₀ :=
      (isClosed_tsupport (D.ζ i)).isOpen_compl.mem_nhds hp
    have h0 : (fun q : M => D.Rstar i u q (X q) (Y q)) =ᶠ[𝓝 p₀] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with q hq
      have hz : D.ζ i q = 0 := image_eq_zero_of_notMem_tsupport hq
      rw [Work.Diff.STE.B3.Rstar_eq_zero_of_zeta_eq_zero D u hz]
      simp
    exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0

end

theorem ChartData_Rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (a b : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (u a b)) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (D.Rstar i u) := by
  intro x₀'
  rw [contDiffOn_pi]
  intro a
  rw [contDiffOn_pi]
  intro b
  have hΦ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun p : M => D.Rstar i u p
        (Submission.Geodesic.frameVector (I := I) x₀' p (Work.Diff.EXT.bB (E := E) a))
        (Submission.Geodesic.frameVector (I := I) x₀' p (Work.Diff.EXT.bB (E := E) b)))
      (chartAt H x₀').source := by
    intro p hp
    exact (Rstar_value_contMDiffAt D i u hu p
      (Work.Diff.EXT.contMDiffAt_frameVector x₀' (Work.Diff.EXT.bB (E := E) a) hp)
      (Work.Diff.EXT.contMDiffAt_frameVector x₀' (Work.Diff.EXT.bB (E := E) b) hp)).contMDiffWithinAt
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      ((fun p : M => D.Rstar i u p
        (Submission.Geodesic.frameVector (I := I) x₀' p (Work.Diff.EXT.bB (E := E) a))
        (Submission.Geodesic.frameVector (I := I) x₀' p (Work.Diff.EXT.bB (E := E) b)))
        ∘ (extChartAt I x₀').symm) (extChartAt I x₀').target :=
    hΦ.comp (contMDiffOn_extChartAt_symm (I := I) x₀' (n := ∞)) (fun y hy => by
      rw [← extChartAt_source (I := I) x₀']
      exact (extChartAt I x₀').map_target hy)
  simpa only [Function.comp_def] using hcomp.contDiffOn

end Work.Diff.STE.D
