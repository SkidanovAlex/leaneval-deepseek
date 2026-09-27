import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.collapseT5
import Submission.Work.Drive.contMDiff_loopFam
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.meetBoxForallEventual
import Submission.Work.Drive.loopBoxData_eventually
import Submission.Work.Drive.diamClause_design_eventually

/-!
# The loop families of the design are jointly smooth in `(t, θ, u)`

The design's loop families — `diamFam (blockChart k t) θ` and `arcFam (blockChart k t) θ` — depend on
three variables: the design parameter `t : ℝ¹²` (through the perturbed rotated chart of the block `k`),
the *angle* `θ` (the first square coordinate of the family) and the loop parameter `u : 𝔼²` (the second
square coordinate, which is also the interpolation/rotation parameter).

This module records the joint `C^∞`-smoothness of both families, in the exact shape consumed by the
openness engine `Work.Drive.eventually_forall_meetBox_of_eventually` (`Prop`-valued clause depending on
`(t, θ)`) together with the general persistence lemma `Work.Drive.loopBoxData_eventually`.  It is the
`diamFam`/`arcFam` analogue of `Work.Drive.contMDiff_diamFam_design` (the `diamLoop` family, in
`diamClause_design_eventually.lean`), and it is proved the same way: the argument of the chart is a
smooth `ℂ`-valued map of `(t, θ, u)` (`Work.Drive.contDiff_colCirclePt_comp`), and `chartPert` is
`C^∞` jointly (`Work.Drive.contMDiff_chartPert`).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- `Work.Drive.colCirclePt` composed with a smooth real function is smooth (a local copy, so that
this module does not depend on the private copy in `contMDiff_loopFam.lean`). -/
lemma contDiff_colCirclePt_comp_loopFam {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ Ctop f) :
    ContDiff ℝ Ctop (fun x : X => colCirclePt (f x)) := by
  have hlin : ContDiff ℝ Ctop (fun x : X => (Real.pi : ℂ) * ((f x : ℝ) : ℂ) * Complex.I) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hf)).mul contDiff_const
  simpa only [colCirclePt, Function.comp_def] using Complex.contDiff_exp.comp hlin

/-- **The core loop family of the design's block `k` is jointly `C^∞` in `(t, θ)`.** -/
lemma contMDiff_coreLoop_design {Q : ℂ → CappingSpace}
    (k : Fin 3) (u : Fin 3 → UnitAddCircle) (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun r : EuclideanSpace ℝ (Fin 12) × ℝ =>
        coreLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j r.1) k) r.2) := by
  have hz : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓘(ℝ, ℂ)) Ctop
      (fun r : EuclideanSpace ℝ (Fin 12) × ℝ => colCirclePt r.2) :=
    contMDiff_iff_contDiff.mpr (contDiff_colCirclePt_comp_loopFam (by fun_prop))
  have hG1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun r : EuclideanSpace ℝ (Fin 12) × ℝ => blk k r.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hG2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun r : EuclideanSpace ℝ (Fin 12) × ℝ =>
        rotCapping (u k) (Q (colCirclePt r.2))) :=
    (contMDiff_rotCappingAngle (u k)).comp (hQ.comp hz)
  have hmain := contMDiff_chartPert.comp (hG1.prodMk hG2)
  refine hmain.congr fun r => ?_
  simp only [Function.comp_apply, blockChart, coreLoop, colCirclePt]


/-- **The diameter-to-half-circle family of the design's block `k` is jointly `C^∞` in
`(t, θ, u)`.** -/
lemma contMDiff_diamFam_loopFam_design {Q : ℂ → CappingSpace}
    (k : Fin 3) (u : Fin 3 → UnitAddCircle) (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        diamFam (blockChart (fun s p => chartPert s p) Q u (fun j => blk j q.1.1) k) q.1.2 q.2) := by
  have hz : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, ℂ)) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        (((1 - q.2 0) * (1 - 2 * q.2 1) : ℝ) : ℂ) * colCirclePt q.1.2
          + ((q.2 0 : ℝ) : ℂ) * colCirclePt (q.1.2 + q.2 1)) := by
    rw [contMDiff_iff_contDiff]
    have hp0 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.2 0) := by fun_prop
    have hp1 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.2 1) := by fun_prop
    have hth : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.1.2) := by fun_prop
    have hA : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          (((1 - q.2 0) * (1 - 2 * q.2 1) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.sub hp0).mul (contDiff_const.sub (contDiff_const.mul hp1)))
    have hB : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          colCirclePt q.1.2) :=
      contDiff_colCirclePt_comp_loopFam hth
    have hC : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          ((q.2 0 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hp0
    have hD : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
          colCirclePt (q.1.2 + q.2 1)) :=
      contDiff_colCirclePt_comp_loopFam (hth.add hp1)
    exact (hA.mul hB).add (hC.mul hD)
  have hG1 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => blk k q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hG2 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        rotCapping (u k) (Q ((((1 - q.2 0) * (1 - 2 * q.2 1) : ℝ) : ℂ) * colCirclePt q.1.2
          + ((q.2 0 : ℝ) : ℂ) * colCirclePt (q.1.2 + q.2 1)))) :=
    (contMDiff_rotCappingAngle (u k)).comp (hQ.comp hz)
  have hmain := contMDiff_chartPert.comp (hG1.prodMk hG2)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_apply, blockChart, diamFam, diamInterp]

/-- **The rotation family of the design's block `k` is jointly `C^∞` in `(t, θ, u)`.** -/
lemma contMDiff_arcFam_loopFam_design {Q : ℂ → CappingSpace}
    (k : Fin 3) (u : Fin 3 → UnitAddCircle) (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        arcFam (blockChart (fun s p => chartPert s p) Q u (fun j => blk j q.1.1) k) q.1.2 q.2) := by
  have hz : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, ℂ)) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        colCirclePt ((1 - q.2 0) * q.1.2 + q.2 1)) := by
    rw [contMDiff_iff_contDiff]
    have hp0 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.2 0) := by fun_prop
    have hp1 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.2 1) := by fun_prop
    have hth : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => q.1.2) := by fun_prop
    exact contDiff_colCirclePt_comp_loopFam (((contDiff_const.sub hp0).mul hth).add hp1)
  have hG1 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => blk k q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hG2 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        rotCapping (u k) (Q (colCirclePt ((1 - q.2 0) * q.1.2 + q.2 1)))) :=
    (contMDiff_rotCappingAngle (u k)).comp (hQ.comp hz)
  have hmain := contMDiff_chartPert.comp (hG1.prodMk hG2)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_apply, blockChart, arcFam, arcRot]


/-! ## The design's blocks and chains, indexed by the design parameter -/

/-- The chart of block `k` of the design's triple at the design parameter `t`. -/
def designChartT (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : ℂ → CappingSpace :=
  blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k

/-- The plane presentation of block `j` of the design's triple at the design parameter `t`. -/
def designPlaneT (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (j : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j

/-- The `3`-chain of block `j` of the design's triple at the design parameter `t`. -/
def designSweepT (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (j : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  clampedSweep (cblk j) (fun r => 1 - r) (designPlaneT Q u j t)

/-- **The chain of a fixed block of the design is jointly `C^∞` in `(t, θ, x)`** (the unused angle
`θ` is carried along, because the meet-box clauses are indexed by the pair `(t, θ)`). -/
lemma contMDiff_designSweepT_fam {Q : ℂ → CappingSpace}
    (j : Fin 3) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) =>
        designSweepT Q u cblk j q.1.1 q.2) := by
  have hshift : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) => (q.1.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  simpa only [designSweepT, designPlaneT, Function.comp_def] using
    (Work.Drive.contMDiff_designChainFam_blk j u cblk hQ).comp hshift

/-! ## The base-point form of `Work.Drive.loopBoxData_eventually` -/

/-- **`Work.Drive.LoopBoxData` is a neighbourhood property of the family parameter, at an arbitrary
base point** (the statement `Work.Drive.loopBoxData_eventually` is at the base parameter `0`; this is
the form the design needs, where the base parameter is the pair `(t₀, θ)`). -/
theorem loopBoxData_eventually_at {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (p₀ : P) (A A' : P → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hA : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2))
    (hA' : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 2) => A' q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (h0 : LoopBoxData (A p₀) (D p₀)) (h0' : LoopBoxData (A' p₀) (D p₀)) :
    ∀ᶠ p in 𝓝 p₀, LoopBoxData (A p) (D p) ∧ LoopBoxData (A' p) (D p) := by
  have hshift2 : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) Ctop (fun q : P × EuclideanSpace ℝ (Fin 2) =>
      (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hshift3 : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop (fun q : P × EuclideanSpace ℝ (Fin 3) =>
      (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have htr := loopBoxData_eventually (A := fun u : P => A (p₀ + u))
    (D := fun u : P => D (p₀ + u)) (hA.comp hshift2) (hD.comp hshift3) (by simpa using h0)
  have htr' := loopBoxData_eventually (A := fun u : P => A' (p₀ + u))
    (D := fun u : P => D (p₀ + u)) (hA'.comp hshift2) (hD.comp hshift3) (by simpa using h0')
  have hmain : ∀ᶠ u in 𝓝 (0 : P), LoopBoxData (A (p₀ + u)) (D (p₀ + u))
      ∧ LoopBoxData (A' (p₀ + u)) (D (p₀ + u)) := htr.and htr'
  have htend : Tendsto (fun p : P => p - p₀) (𝓝 p₀) (𝓝 (0 : P)) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  refine (htend.eventually hmain).mono fun p hp => ?_
  have hpp : p₀ + (p - p₀) = p := by abel
  simpa only [hpp] using hp


/-- The plain `(t, x)`-smoothness of the design's chain of a fixed block (the `\theta`-component of
`Work.Drive.contMDiff_designSweepT_fam` is dropped). -/
lemma contMDiff_designSweepT {Q : ℂ → CappingSpace}
    (j : Fin 3) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun r : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        designSweepT Q u cblk j r.1 r.2) := by
  simpa only [designSweepT, designPlaneT, Function.comp_def] using
    Work.Drive.contMDiff_designChainFam_blk j u cblk hQ

/-- **The meet-box clause engine with smoothness hypotheses**: the continuity hypothesis of
`Work.Drive.eventually_forall_meetBox_of_eventually` is derived from the joint `C^∞`-smoothness of the
two families.  Stated with the families as *variables*, so that the (expensive) unification of a
concrete pair map against the `Continuous` goal never has to unfold a concrete family. -/
theorem eventually_forall_meetBox_of_eventually_smooth {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (p₀ : P) {L : P → ℝ → CappingSpace} {D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (R : P → ℝ → Prop)
    (hprop : ∀ ξ ∈ meetBox (L p₀) (D p₀), ∀ᶠ z in 𝓝 ((p₀, ξ.1) : P × ℝ), R z.1 z.2) :
    ∀ᶠ p in 𝓝 p₀, ∀ q ∈ meetBox (L p) (D p), R p q.1 := by
  have hprojL : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) := by
    fun_prop
  have hprojD : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) := by
    fun_prop
  refine eventually_forall_meetBox_of_eventually p₀ ?_ R hprop
  exact (hL.continuous.comp hprojL).prodMk (hD.continuous.comp hprojD)

end

end Work.Drive
