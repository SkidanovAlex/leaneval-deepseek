import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ricJetDefs
import Submission.Work.Diff.EXT.ricAt_invGram_chart
import Submission.Work.Diff.EXT.gRmC_eq_jRm
import Submission.Work.Diff.EXT.ricPhi_contDiffOn
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart Ricci matrix is a smooth function of the `2`-jet of the chart matrix

The main lemma of this file, `Work.Diff.EXT.chartRic_mat_smooth_of_jet`, produces a single smooth
function `Φ` of the spatial `2`-jet `Work.Diff.EXT.jet2` of the chart matrix of a metric which
reproduces the chart Ricci matrix `chartRicMat g x₀ y` for *every* smooth metric `g`, chart centre
`x₀` and chart point `y`.  Here `jet2` records the value, the first Fréchet derivative and the
second Fréchet derivative of `u = fun p : ℝ × E => chartMatFun g x₀ p.2` at `(0, y)`, i.e. a triple
`(A, L, B)` of the metric matrix in the coordinate frame of the chart at `x₀` together with its two
successive Fréchet derivatives; these are exactly the metric coefficients, their first and their
second coordinate derivatives.

The candidate `Φ = Work.Diff.EXT.ricPhi` is the classical coordinate (Christoffel) expression for
the Ricci tensor, read off from `(A, L, B)`:

`ricPhi (y, (A, L, B)) i j = ∑ k, ∑ l, γ^{kl} R_{kilj}`,

with `γ^{kl} = (A⁻¹) k l`, the Koszul pairings `Γ_{abc} = ½(∂_a g_{bc} + ∂_b g_{ac} - ∂_c g_{ab})`
and the curvature components
`R_{abcd} = ∂_a Γ_{dbc} - ∂_b Γ_{dac} - γ^{rs}Γ_{dbr}Γ_{acs} + γ^{rs}Γ_{dar}Γ_{bcs}`.

The proof has three parts, each established in a separate module of this area:

* `Work.Diff.EXT.ricAt_invGram_chart`: the Ricci trace read in the coordinate frame,
  `Ric(σ_i,σ_j) = ∑_{k,l} γ^{kl} ⟪R(σ_k,σ_i)σ_j, σ_l⟫`, with `γ` the Gram matrix of the frame;
* `Work.Diff.EXT.gRmC_eq_jRm`: the curvature components `⟪R(σ_a,σ_b)σ_d, σ_c⟫` of the coordinate
  frame are the explicit expression in `(A, L, B)` above;
* `Work.Diff.EXT.ricPhi_contDiffOn`: the resulting function `ricPhi` of the jet is `C^∞` on the
  open set where the metric matrix is invertible.

The smoothness of the Levi-Civita connection, used to make `rmVec` tensorial (and hence in both of
the first two references), is the contract `Submission.Diff.LCSmooth`, proved in
`Submission.Work.Diff.T.lc_smooth`; the hypotheses `[I.Boundaryless]` and `[T2Space M]` are exactly
those of that contract.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- **The Ricci trace in the coordinate frame** (restated from
`Work.Diff.EXT.ricAt_invGram_chart` in the notation of this file): the trace of
`w ↦ R(w,σ_i)σ_j` read in the coordinate frame is `∑_{k,l} γ^{kl}⟪R(σ_k,σ_i)σ_j, σ_l⟫`, with `γ`
the Gram matrix of the frame. -/
lemma ricAt_eq_sum_gramInv
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source)
    (i j : Fin (Module.finrank ℝ E)) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) p (fvec (I := I) x₀ p i)
        (fvec (I := I) x₀ p j)
      = ∑ k, ∑ l, (Matrix.of (gmat (I := I) g x₀ p))⁻¹ k l *
          gRmC (I := I) g x₀ p k i l j := by
  have hmat : Matrix.of (gmat (I := I) g x₀ p) = cgramM (I := I) g x₀ p := rfl
  have hvec : ∀ k : Fin (Module.finrank ℝ E),
      fvec (I := I) x₀ p k = cvec (I := I) x₀ p (bB (E := E) k) := fun k => rfl
  have h := ricAt_invGram_chart (I := I) g x₀ hp i j
  simp only [hmat, hvec]
  rw [h]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => rfl

/-- The Gram matrix of the coordinate frame at `(extChartAt I x₀).symm y` is the chart matrix of
`g` in the chart at `x₀` at the point `y`. -/
lemma gmat_symm {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    gmat (I := I) g x₀ ((extChartAt I x₀).symm y) = chartMatFun g x₀ y := rfl

theorem chartRic_mat_smooth_of_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] :
    ∃ Φ : E × ((Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
        (E →L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ×
        (E →L[ℝ] E →L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ))) →
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ {z | (Matrix.of z.2.1).det ≠ 0} ∧
      ∀ (x₀ : M) (g : Submission.Diff.SMet I M) (y : E), y ∈ (extChartAt I x₀).target →
        Work.Diff.EXT.chartRicMat g x₀ y =
          Φ (y, Work.Diff.EXT.jet2 (fun p : ℝ × E => Work.Diff.EXT.chartMatFun g x₀ p.2) (0, y)) := by
  classical
  have hcov_all : ∀ g : Submission.Diff.SMet I M,
      CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    fun g => (Work.Diff.T.lc_smooth (I := I) (M := M) g).1.some
  refine ⟨ricPhi (E := E), ricPhi_contDiffOn (E := E), ?_⟩
  intro x₀ g y hy
  ext i j
  -- the chart point and its membership in the chart source
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    rw [← extChartAt_source (I := I) (x := x₀)]
    exact (extChartAt I x₀).map_target hy
  have hpy : (extChartAt I x₀) ((extChartAt I x₀).symm y) = y := (extChartAt I x₀).right_inv hy
  have hcov := hcov_all g
  -- the left-hand side, as a Ricci trace in the coordinate frame
  rw [show chartRicMat g x₀ y i j
      = Submission.Diff.ricAt (Submission.Diff.lcOf g) ((extChartAt I x₀).symm y)
          (fvec (I := I) x₀ ((extChartAt I x₀).symm y) i)
          (fvec (I := I) x₀ ((extChartAt I x₀).symm y) j) from rfl]
  rw [ricAt_eq_sum_gramInv (I := I) g x₀ (p := (extChartAt I x₀).symm y) hp i j]
  -- the right-hand side, unfolded into the jet expression
  rw [show (ricPhi (E := E)
        (y, jet2 (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y))) i j
      = ∑ k, ∑ l, jInv (chartMatFun g x₀ y) k l *
          jRm (chartMatFun g x₀ y) (fderiv ℝ (chartMatFun g x₀) y)
            (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) k i l j from rfl]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have h2 := gRmC_eq_jRm (I := I) g hcov x₀ hp k i l j
  rw [hpy] at h2
  rw [gmat_symm, h2, jInv]

end Work.Diff.EXT
