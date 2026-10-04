import Submission.ParallelBridge
import Submission.SyngeFieldR

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.GlobalExp
open Submission.ParallelGlobal
open Submission.OrientSign

/-!
# The Synge package: unit, normal, periodic, smooth, parallel field along a closed geodesic

This module assembles the two halves of Synge's input for the even-dimensional Klingenberg estimate:

* `Submission.SyngeFieldR.exists_periodic_parallelFieldR` gives a smooth, parallel, *periodic*
  field along a chart-covered geodesic loop of a simply connected even-dimensional manifold;
* `velocity_eq_parallelField` and `inner_parallelField_eq` identify the velocity field with a
  `parallelField` and provide the **bilinear** Gram constancy of the parallel field, which turns the
  base-point normality of the Synge datum into normality at every point, and `norm_parallelField`
  which turns the norm of the datum into constancy of the norm.

The conclusion `exists_synge_field` is the exact input of
`Submission.SyngeShorten.exists_shorter_closed_curve`.
-/

/-- Polarisation of the squared norm in a real inner product space. -/
private lemma inner_eq_half_sub {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x y : F) : inner ℝ x y = (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
  have h := norm_add_sq_real x y
  linarith

namespace Submission.HolDet

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {γ : ℝ → M} {a b : ℝ}

/-- **The velocity field is a `parallelField`** (with the chart-velocity datum): a geodesic is
parallel along itself. -/
theorem velocity_eq_parallelField (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) {t : ℝ} (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    curveVelocity (I := I) γ t
      = parallelField (cov := cov) htor C hN
          (deriv (coordCurve (I := I) C 0) (C.c 0)) t := by
  have hcc0 : coordCurve (I := I) C 0 = fun s => (extChartAt I (C.x 0)) (γ s) := rfl
  have hkN : kOf (cov := cov) C hN t < C.N := kOf_lt (cov := cov) C hN t
  have hmem : t ∈ Icc (C.c (kOf (cov := cov) C hN t)) (C.c (kOf (cov := cov) C hN t + 1)) :=
    ⟨c_kOf_le (cov := cov) C hN ht, kOf_spec' (cov := cov) C hN ht.2⟩
  show curveVelocity (I := I) γ t
      = pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
          (datumAt (cov := cov) htor C (deriv (coordCurve (I := I) C 0) (C.c 0))
            (kOf (cov := cov) C hN t)) t
  rw [hcc0]
  rw [datumAt_deriv (cov := cov) C htor (kOf (cov := cov) C hN t) hkN]
  show curveVelocity (I := I) γ t
      = frameVector (I := I) (C.x (kOf (cov := cov) C hN t)) (γ t)
          (pieceSol (cov := cov) htor C (kOf (cov := cov) C hN t)
            (deriv (fun s => (extChartAt I (C.x (kOf (cov := cov) C hN t))) (γ s))
              (C.c (kOf (cov := cov) C hN t))) t)
  rw [pieceSol_deriv (cov := cov) C htor hkN hmem]
  exact (frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hkN
    (piece_subset_room (cov := cov) C hkN hmem)).symm

/-- **The bilinear Gram constancy of the global parallel field**: all pairings of parallel fields are
constant, equal to the pairing of the data at the base time.  (Polarisation of
`norm_parallelField_sq` together with the linearity `parallelField_add`.) -/
theorem inner_parallelField_eq (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v w : E) {t : ℝ}
    (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    inner ℝ (parallelField (cov := cov) htor C hN v t)
        (parallelField (cov := cov) htor C hN w t)
      = inner ℝ (frameVector (I := I) (C.x 0) (γ (C.c 0)) v)
          (frameVector (I := I) (C.x 0) (γ (C.c 0)) w) := by
  have hm : t ∈ Icc (C.c 0) (C.c C.N) := ht
  have hvw : ∀ p : E, ‖parallelField (cov := cov) htor C hN p t‖ ^ 2
      = ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) p‖ ^ 2 :=
    fun p => norm_parallelField_sq (cov := cov) hmet C htor hN p hm
  have hadd : parallelField (cov := cov) htor C hN (v + w) t
      = parallelField (cov := cov) htor C hN v t + parallelField (cov := cov) htor C hN w t :=
    parallelField_add (cov := cov) C htor hN v w hm
  have hfadd : frameVector (I := I) (C.x 0) (γ (C.c 0)) (v + w)
      = frameVector (I := I) (C.x 0) (γ (C.c 0)) v
        + frameVector (I := I) (C.x 0) (γ (C.c 0)) w :=
    frameVector_add (I := I) (C.x 0) (γ (C.c 0)) v w
  rw [inner_eq_half_sub, inner_eq_half_sub, ← hadd, ← hfadd, hvw (v + w), hvw v, hvw w]


/-- **THE SYNGE PACKAGE.**  For a chart-covered `C^∞` geodesic loop of a *simply connected* (?)
even-dimensional manifold with `loopSign = 1` there is a `GeodesicCover` of the loop, with the
prescribed partition and charts, and a datum `v ≠ 0` such that the room-based parallel field
`X := parallelFieldR htor C hN v` is

* smooth along `γ`, parallel (`∇X = 0`), periodic (`X (C.c C.N) = X (C.c 0)`),
* of norm `1` at every point of the loop,
* **normal** to the velocity at every point of the loop.

(The simple connectivity enters through `hloopSign`; the even-dimensionality through `hEven`.) -/
theorem exists_synge_field (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeov : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {P : Partition 0 1} {z : ℕ → M} (hP : IsChartLoop (H := H) P γ z)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ (C : GeodesicCover (I := I) cov γ (P.t 0) (P.t P.N)) (hN : 0 < C.N) (v : E),
      C.N = P.N ∧ C.c = P.t ∧ C.x = z ∧ v ≠ 0 ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        SmoothAlongAt (I := I) γ
          (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t) ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        covAlong cov (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v) t = 0) ∧
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c C.N)
        = Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v (C.c 0) ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        ‖Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v t‖ = 1) ∧
      (∀ t ∈ Icc (C.c 0) (C.c C.N),
        inner ℝ (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v t)
          (curveVelocity (I := I) γ t) = 0) := by
  classical
  obtain ⟨C, hN, v, hCN, hCc, hCx, hv0, hnormP, hper⟩ :=
    exists_periodic_parallelField (cov := cov) (P := P) (z := z) (γ := γ) hP hγsm.continuous
      isOpen_univ (Set.subset_univ _) hγsm.contMDiffOn (fun t _ => hgeov t) (fun t _ => hnev t)
      hloop hvelper hloopSign hEven hmet htor
  -- the coordinate curves of the two languages agree
  have hcoord : coordCurve (I := I) C 0 = coordC (I := I) (z := z) (γ := γ) 0 := by
    show (fun t : ℝ => (extChartAt I (C.x 0)) (γ t)) = coordC (I := I) (z := z) (γ := γ) 0
    rw [hCx]
    rfl
  -- the base-point normality, in the cover's own coordinates
  have hnormC : Submission.ChartConnection.chartGram (I := I) (C.x 0) (γ (C.c 0))
      (deriv (coordCurve (I := I) C 0) (C.c 0)) v = 0 := by
    rw [hcoord, hCc, hCx]
    exact hnormP
  have hle : C.c 0 ≤ C.c C.N := c_mono_le (cov := cov) C (Nat.zero_le C.N) le_rfl
  have hbase : γ (C.c 0) ∈ (chartAt H (C.x 0)).source :=
    C.src 0 hN (C.c 0) (piece_subset_room (cov := cov) C hN ⟨le_rfl, (C.mono 0 hN).le⟩)
  -- the norm of the datum, and its normalisation
  have hcpos : 0 < ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v‖ := by
    refine norm_pos_iff.mpr ?_
    intro h0
    exact hv0 ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := C.x 0)
      (p := γ (C.c 0)) hbase v).mp h0)
  set c : ℝ := ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v‖ with hcdef
  set v' : E := c⁻¹ • v with hv'def
  have hv'0 : v' ≠ 0 := by
    rw [hv'def]
    exact smul_ne_zero (inv_ne_zero (ne_of_gt hcpos)) hv0
  have hunit' : ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v'‖ = 1 := by
    rw [hv'def, frameVector_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
      show ‖frameVector (I := I) (C.x 0) (γ (C.c 0)) v‖ = c from hcdef.symm]
    exact inv_mul_cancel₀ (ne_of_gt hcpos)
  have hnorm0 : inner ℝ (frameVector (I := I) (C.x 0) (γ (C.c 0)) v)
      (curveVelocity (I := I) γ (C.c 0)) = 0 := by
    have hw : frameVector (I := I) (C.x 0) (γ (C.c 0))
        (deriv (coordCurve (I := I) C 0) (C.c 0)) = curveVelocity (I := I) γ (C.c 0) :=
      frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hN
        (piece_subset_room (cov := cov) C hN ⟨le_rfl, (C.mono 0 hN).le⟩)
    have hsym : Submission.ChartConnection.chartGram (I := I) (C.x 0) (γ (C.c 0)) v
        (deriv (coordCurve (I := I) C 0) (C.c 0))
        = Submission.ChartConnection.chartGram (I := I) (C.x 0) (γ (C.c 0))
          (deriv (coordCurve (I := I) C 0) (C.c 0)) v := by
      rw [Submission.ChartConnection.chartGram_apply,
        Submission.ChartConnection.chartGram_apply, real_inner_comm]
    rw [← hw, ← Submission.ChartConnection.chartGram_apply, hsym]
    exact hnormC
  -- the scaled datum is still fixed by the transport
  have hper' : parallelField (cov := cov) htor C hN v' (C.c C.N)
      = parallelField (cov := cov) htor C hN v' (C.c 0) := by
    rw [hv'def,
      parallelField_smul (cov := cov) C htor hN c⁻¹ v (t := C.c C.N) ⟨hle, le_rfl⟩,
      parallelField_smul (cov := cov) C htor hN c⁻¹ v (t := C.c 0) ⟨le_rfl, hle⟩, hper]
  -- the field data
  have hspec := Submission.ParallelRoom.parallelFieldR_spec (cov := cov) hmet htor C hN v'
    (fun k hk t ht => (hγsm.contMDiffOn).mono (Set.subset_univ _))
    (fun k hk t ht => hnev t)
  have hbridge : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v' t
        = parallelField (cov := cov) htor C hN v' t :=
    fun t ht => Submission.ParallelRoom.parallelFieldR_eq_parallelField (cov := cov) htor C hN v' ht
  have hspec1 : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      SmoothAlongAt (I := I) γ
        (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v') t := by
    rw [C.c_zero, C.c_last]
    exact hspec.1
  have hspec2 : ∀ t ∈ Icc (C.c 0) (C.c C.N),
      covAlong cov (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v') t = 0 := by
    rw [C.c_zero, C.c_last]
    exact hspec.2
  refine ⟨C, hN, v', hCN, hCc, hCx, hv'0, hspec1, hspec2, ?_, ?_, ?_⟩
  · rw [hbridge (C.c C.N) ⟨hle, le_rfl⟩, hbridge (C.c 0) ⟨le_rfl, hle⟩]
    exact hper'
  · intro t ht
    rw [hbridge t ht, norm_parallelField (cov := cov) hmet C htor hN v' ht]
    exact hunit'
  · intro t ht
    rw [hbridge t ht, velocity_eq_parallelField (cov := cov) htor C hN ht,
      inner_parallelField_eq (cov := cov) hmet htor C hN v'
        (deriv (coordCurve (I := I) C 0) (C.c 0)) ht, hv'def, frameVector_smul]
    rw [real_inner_smul_left]
    have hw : frameVector (I := I) (C.x 0) (γ (C.c 0))
        (deriv (coordCurve (I := I) C 0) (C.c 0)) = curveVelocity (I := I) γ (C.c 0) :=
      frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hN
        (piece_subset_room (cov := cov) C hN ⟨le_rfl, (C.mono 0 hN).le⟩)
    rw [hw, hnorm0, mul_zero]

end

end Submission.HolDet
