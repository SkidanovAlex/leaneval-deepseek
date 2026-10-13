import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reconstructed velocity field is divergence free

`Work.Cyl.div_psiField` proves `div (psiField ψ) x = 0` at every point `x` off the axis at which
the stream function `ψ` is `C²`.  The hypotheses available for the design's meridian stream
function `merPsi` are weaker: we only know `ψ` is `C²` at the points `(r,z)` with `r > 0` and
`z ≠ 0` (and that the resulting field is globally `C¹`).

The set of points where that hypothesis fails — the axis `r = 0` together with the plane
`x₃ = 0` (the set `Work.FTS.BSIdent.Uaxᶜ`) — is a finite union of hyperplanes, hence has empty
interior: it is *dense* in `ℝ³` that the hypothesis holds (`dense_Uax` below).  Since
`ContDiff ℝ 1 u` makes `x ↦ div u x` continuous, the divergence — which vanishes on `Uax` —
vanishes on the closure of `Uax`, i.e. everywhere.  This is the content of
`div_psiField_merPsi`.
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Cyl

/-! ## Continuity of the trace of a continuous linear endomorphism of `ℝ³` -/

/-- The trace, as a function of a continuous linear endomorphism of `ℝ³`, is continuous: it is a
linear map on the finite dimensional space `ℝ³ →L[ℝ] ℝ³`. -/
private theorem continuous_trace_clm :
    Continuous (fun L : Work.Cyl.R3 →L[ℝ] Work.Cyl.R3 => LinearMap.trace ℝ Work.Cyl.R3 L) := by
  let T : (Work.Cyl.R3 →L[ℝ] Work.Cyl.R3) →ₗ[ℝ] ℝ :=
    { toFun := fun L => LinearMap.trace ℝ Work.Cyl.R3 L
      map_add' := by intro L M; simp
      map_smul' := by intro c L; simp }
  exact LinearMap.continuous_of_finiteDimensional T

/-! ## Density of the coordinate hyperplane complements -/

/-- For each coordinate direction of `ℝ³`, the set of points with non-vanishing coordinate is
dense: from any point one reaches it by a displacement `(r/2) • e i` which does not undo the
coordinate unless the point is already exactly `-(r/2) • e i` on it — and in that case the point
itself already has a non-vanishing `i`-th coordinate. -/
private theorem dense_coord_ne_zero (i : Fin 3) : Dense {x : Work.Cyl.R3 | x i ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  rcases eq_or_ne (x i) 0 with hx | hx
  · refine ⟨x + (r / 2) • FiniteTimeSingularity.e i, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + (r / 2) • FiniteTimeSingularity.e i - x
          = (r / 2) • FiniteTimeSingularity.e i := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2),
        show ‖FiniteTimeSingularity.e i‖ = 1 from by simp [FiniteTimeSingularity.e]]
      linarith
    · show (x + (r / 2) • FiniteTimeSingularity.e i) i ≠ 0
      have h2 : (x + (r / 2) • FiniteTimeSingularity.e i) i = r / 2 := by
        simp [FiniteTimeSingularity.e, hx]
      rw [h2]; linarith
  · exact ⟨x, by simpa using hr, hx⟩

/-- The domain of the identification `Uax = {x₃ ≠ 0, x₀² + x₁² ≠ 0}` (the complement of the axis
and of the plane `x₃ = 0`) is dense in `ℝ³`: it contains the intersection of the two open dense
sets `{x₃ ≠ 0}` and `{x₀ ≠ 0}`. -/
private theorem dense_Uax : Dense (Work.FTS.BSIdent.Uax : Set Work.Cyl.R3) := by
  have h1 : Dense ({x : Work.Cyl.R3 | x 2 ≠ 0} : Set Work.Cyl.R3) := dense_coord_ne_zero 2
  have h2 : Dense ({x : Work.Cyl.R3 | x 0 ≠ 0} : Set Work.Cyl.R3) := dense_coord_ne_zero 0
  have h2' : Dense ({x : Work.Cyl.R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} : Set Work.Cyl.R3) :=
    Dense.mono (fun x hx => by
      intro hc
      have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      exact hx (sq_eq_zero_iff.mp h0)) h2
  have hopen : IsOpen ({x : Work.Cyl.R3 | x 2 ≠ 0} : Set Work.Cyl.R3) :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have hint := Dense.inter_of_isOpen_left h1 h2' hopen
  convert hint using 1
  ext x; simp [Work.FTS.BSIdent.Uax]

/-! ## The theorem -/

theorem div_psiField_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ)
    (hC1 : ContDiff ℝ 1 (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)))
    (hsm : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z)) :
    FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) = 0 := by
  -- the divergence is continuous, being the trace of the (continuous) derivative of a `C¹` field
  have hcont : Continuous (fun x => FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x) := by
    show Continuous (fun x => (fderiv ℝ
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x).trace ℝ
        Work.Cyl.R3)
    exact continuous_trace_clm.comp (hC1.continuous_fderiv (by simp))
  -- it vanishes wherever the meridional slice of the stream function is `C²`
  have hvan : Set.EqOn (fun x => FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x)
      (fun _ => (0 : ℝ)) (Work.FTS.BSIdent.Uax) := by
    intro x hx
    exact Work.Cyl.div_psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t) x
      (hsm (Work.Cyl.radial x) (Work.Cyl.axial x)
        (Work.FTS.BSIdent.radial_pos_of_mem_Uax hx)
        (Work.FTS.BSIdent.axial_ne_zero_of_mem_Uax hx))
      (Work.FTS.BSIdent.radial_pos_of_mem_Uax hx)
  -- `Uax` is dense, so a continuous function vanishing on it vanishes everywhere
  funext x
  have hcl := Set.EqOn.closure hvan hcont continuous_const
  rw [dense_Uax.closure_eq] at hcl
  exact hcl (Set.mem_univ x)

end Work.FTS.BSIdent.Cyl
