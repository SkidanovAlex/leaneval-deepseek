import Submission.HolCover
import Submission.UniformInj

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.OrientSign
open Submission.ChartConnection
open Submission.BonnetMyers
open Submission.Jacobi

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
variable {γ : ℝ → M}

/-- **THE SYNGE INPUT IN THE `ParallelGlobal` LANGUAGE.**  For a chart-covered unit-speed geodesic
loop with `loopSign = 1` (which simple connectivity supplies) in *even* dimension, there is a
`GeodesicCover` of the loop whose partition, charts and monotonicity are the given ones, together
with a non-zero vector `v` such that the global parallel field `parallelField C htor hN v` has the
**same value at the two ends of the loop** — a *periodic* parallel field.

The proof combines `exists_fixed_normal_coord_of_isChartLoop` (Synge's linear algebra: the composite
holonomy fixes a normal vector) with the identification
`parallelField_endpoint_eq_holAuxC` of the endpoint value of the global parallel field with the
composite holonomy. -/
theorem exists_periodic_parallelField {P : Partition 0 1} {z : ℕ → M}
    (hP : IsChartLoop (H := H) P γ z) (hγc : Continuous γ) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : Icc (P.t 0) (P.t P.N) ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeov : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0)
    (hloop : γ (P.t P.N) = γ (P.t 0))
    (hvelper : deriv (coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0))
    (hloopSign : loopSignOf (I := I) P γ z = 1)
    (hEven : Even (Module.finrank ℝ E))
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) :
    ∃ (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ (P.t 0) (P.t P.N))
      (hN : 0 < C.N) (v : E),
      C.N = P.N ∧ C.c = P.t ∧ C.x = z ∧ v ≠ 0 ∧
      Submission.ChartConnection.chartGram (I := I) (z 0) (γ (P.t 0))
        (deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0)) v = 0 ∧
      Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v (C.c C.N)
        = Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v (C.c 0) := by
  classical
  -- the chart velocity at the base point of the loop is non-zero
  have hbase : γ (P.t 0) ∈ (trivializationAt E (TangentSpace I) (z 0)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hP.1 0 P.pos_N (P.t 0) ⟨le_rfl, (P.mono 0 P.pos_N).le⟩
  have hvelne : deriv (coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) ≠ 0 := by
    intro h0
    have hmem : P.t 0 ∈ V := hVsub ⟨le_rfl, P.mono_le (Nat.zero_le P.N) le_rfl⟩
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ (P.t 0) :=
      (hγ.contMDiffAt (hV.mem_nhds hmem)).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hder := Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity
      (I := I) (z 0) hmd (hP.1 0 P.pos_N (P.t 0) ⟨le_rfl, (P.mono 0 P.pos_N).le⟩)
    have h0' : deriv (fun s => (extChartAt I (z 0)) (γ s)) (P.t 0) = 0 := h0
    rw [hder] at h0'
    have h2 : (Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) (z 0))
        (γ (P.t 0)) hbase) (curveVelocity (I := I) γ (P.t 0)) = 0 := by
      rw [Trivialization.linearEquivAt_apply]
      rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
        (trivializationAt E (TangentSpace I) (z 0)) hbase
        (curveVelocity (I := I) γ (P.t 0))] at h0'
      exact h0'
    exact hnev (P.t 0) hmem ((LinearEquiv.map_eq_zero_iff _).mp h2)
  obtain ⟨v, hv0, hnorm, hvfix⟩ := exists_fixed_normal_coord_of_isChartLoop (cov := cov)
    hP hmet htor hγc hV hVsub hγ hgeov hnev hloop hvelper hloopSign hvelne hEven
  obtain ⟨A, B, hAB, hroomV, hroomsrc⟩ := exists_room_of_isChartLoop hP hγc hV hVsub
  let C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ (P.t 0) (P.t P.N) :=
    { N := P.N, c := P.t, x := z, A := A, B := B, c_zero := rfl, c_last := rfl, mono := P.mono,
      room := hAB, src := fun k hk t ht => hroomsrc k hk t ht,
      ode := fun k hk t ht => hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z k) hV
        (hroomV k hk ht) hγ (hroomsrc k hk t ht) hgeov hnev }
  have hsrc' : ∀ k, k < C.N → γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source :=
    fun k hk => hP.2.1 k hk
  refine ⟨C, ?_, v, rfl, rfl, rfl, hv0, ?_, ?_⟩
  · exact P.pos_N
  · exact hnorm
  · have hkey := parallelField_endpoint_eq_holAuxC (cov := cov) C P.pos_N htor v hsrc'
    rw [hkey]
    have hv : holAuxC (cov := cov) htor C.N C.c C.x C.mono
        (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
        C.N v = v :=
      (congrArg (fun L : E →L[ℝ] E => L v)
        (holAuxC_self (cov := cov) (P := P) (z := z) (γ := γ) htor
          (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
          (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
          (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
          P.N)).trans (hvfix _ _ _)
    rw [hv, Submission.ParallelGlobal.parallelField_datum (cov := cov) htor C P.pos_N v]
    change frameVector (I := I) (z P.N) (γ (P.t P.N)) v = frameVector (I := I) (z 0) (γ (P.t 0)) v
    rw [hP.2.2, hloop]

end

#print axioms Submission.HolDet.exists_periodic_parallelField

end Submission.HolDet
