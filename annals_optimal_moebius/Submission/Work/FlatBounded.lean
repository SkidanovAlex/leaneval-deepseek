import Submission.Work.NoVerticalKernel
import Submission.Work.FlatComponents

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat components are bounded (FlatBounded)

G1 item 3 (no unbounded frontier arcs / bounded components): every flat
component `C = flatComponent f p` of the embedded band is a BOUNDED set
in the strip.  Proof: on `C` the shape operator vanishes, so `f` is
AFFINE with linear part `L = fderiv f x₀` (`affine_on_flat`,
`fderiv_const_on_flat`), `L` is a linear isometry
(`fderiv_norm_eq_interior`), and the whole image of the unit strip is
bounded (`f_strip_bounded`, from the compact `bandChunk` + the deck
periodicity of `f`).  Hence `‖z − x₀‖ = ‖f z − f x₀‖` is bounded on `C`.

Consequences (feeding (S4) of T1-i):
* `frontier_flatComponent_bounded` — the frontier of `C` is also within
  a bounded distance of `x₀` (frontier ⊆ closure ⊆ the same closed
  ball), so no frontier component `K(e)` is an unbounded ray/line:
  every frontier arc is a bounded straight segment, and — with (S3),
  `frontierComponent_closed_in_strip` — its closure endpoints cannot lie
  in `stripInterior`, so each bounded arc's ends are on the seam lines
  `x0 ∈ {0,1}`.

Build: `lake build Submission.Work.FlatBounded` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **Every flat component is bounded**: with `x₀` a point of the flat
component `C = flatComponent f p`, all points of `C` lie within a fixed
distance `R` of `x₀`.  (Rigidity: `f` is affine on `C` with isometric
linear part, and the whole image of the strip is bounded.) -/
theorem flatComponent_bounded {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p x₀ : ℝ²} (hx₀C : x₀ ∈ flatComponent f p) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ flatComponent f p, ‖z - x₀‖ ≤ R := by
  rcases f_strip_bounded hf ha with ⟨Rb, hRb⟩
  refine ⟨Rb + ‖f x₀‖, ?_, ?_⟩
  · have hx₀U : x₀ ∈ unitStrip :=
      stripInterior_subset_unitStrip (flatComponent_subset_stripInterior f p hx₀C)
    have hRb0 : 0 ≤ Rb := le_trans (norm_nonneg (f x₀)) (hRb x₀ hx₀U)
    have hn : 0 ≤ ‖f x₀‖ := norm_nonneg (f x₀)
    nlinarith
  · intro z hzC
    have hzS : z ∈ stripInterior := flatComponent_subset_stripInterior f p hzC
    have hx₀S : x₀ ∈ stripInterior := flatComponent_subset_stripInterior f p hx₀C
    have haff : f z = f x₀ + (fderiv ℝ f x₀) (z - x₀) :=
      affine_on_flat hf (s := flatComponent f p) (isOpen_flatComponent f p)
        (isPreconnected_flatComponent f p) (flatComponent_subset_stripInterior f p)
        (fun x hx => flatComponent_flat (p := p) hx) hx₀C z hzC
    have hsub : f z - f x₀ = (fderiv ℝ f x₀) (z - x₀) := by
      rw [haff]
      abel
    have hzU : z ∈ unitStrip := stripInterior_subset_unitStrip hzS
    calc
      ‖z - x₀‖ = ‖(fderiv ℝ f x₀) (z - x₀)‖ :=
        (fderiv_norm_eq_interior hf x₀ hx₀S (z - x₀)).symm
      _ = ‖f z - f x₀‖ := by rw [hsub]
      _ ≤ ‖f z‖ + ‖f x₀‖ := norm_sub_le (f z) (f x₀)
      _ ≤ Rb + ‖f x₀‖ := add_le_add (hRb z hzU) le_rfl

/-- **The closure of a flat component is bounded**: the closure of
`C = flatComponent f p` lies in the closed ball `B̄(x₀, R)` (the bound
from `flatComponent_bounded`; a closed ball is closed). -/
theorem flatComponent_closure_bounded {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p x₀ : ℝ²} (hx₀C : x₀ ∈ flatComponent f p) :
    ∃ R : ℝ, 0 ≤ R ∧ closure (flatComponent f p) ⊆ Metric.closedBall x₀ R := by
  rcases flatComponent_bounded hf ha hx₀C with ⟨R, hR0, hR⟩
  refine ⟨R, hR0, ?_⟩
  have hsub : flatComponent f p ⊆ Metric.closedBall x₀ R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hR z hz
  exact Metric.isClosed_closedBall.closure_subset_iff.mpr hsub

/-- **The frontier of a flat component is bounded**: every frontier point
of `C = flatComponent f p` (hence in particular every point of a
frontier component `K(e)`) is within distance `R` of `x₀`.  Combined
with `frontierComponent_is_open_segment` (K(e) is an open straight
segment with (possibly infinite) endpoints) this rules out unbounded
frontier arcs: a bounded straight segment has finite endpoints. -/
theorem frontier_flatComponent_bounded {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p x₀ : ℝ²} (hx₀C : x₀ ∈ flatComponent f p) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ frontier (flatComponent f p), ‖z - x₀‖ ≤ R := by
  rcases flatComponent_closure_bounded hf ha hx₀C with ⟨R, hR0, hcl⟩
  refine ⟨R, hR0, ?_⟩
  intro z hzF
  have hzcl : z ∈ closure (flatComponent f p) := by
    rw [frontier] at hzF
    exact hzF.1
  have hzball := hcl hzcl
  rw [Metric.mem_closedBall, dist_eq_norm] at hzball
  exact hzball

end Submission.PaperBand
