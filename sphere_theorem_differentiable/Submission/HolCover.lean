import Submission.SyngeInput

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The composite holonomy with explicit chart data, and its identification with `ParallelGlobal`

Roadmap §122.6.  `holAux` (`Submission.HolDet`) is the composite holonomy of a `Partition`-based
chart cover; `ParallelGlobal.datumAt` is the same object for a `GeodesicCover`, built from
`pieceSol` (`ParallelRoom.exists_parallelChart`) instead of `FundSol.fundSol`.  This module defines
`holAuxC`, **the same recursion with the partition, the charts and the geodesic run over bare
arguments** `N, c, x`, so that

* `holAuxC_self` gives back `holAux` at `(P.N, P.t, z)` (so all of `HolDet`/`HolSynge` applies), and
* `datumAt_eq_holAuxC` identifies the two recursions for **any** `GeodesicCover` (the step uses
  `SyngeInput.nextDatum_eq_chartTransition` and `SyngeInput.pieceSol_eq_fundSolOn`).

The remaining step to the Synge input in the `ParallelGlobal` language is
`transport C htor hN v = frameVector (z 0) (γ (P.t 0)) (holAux htor hu hw htgt P.N v)` (Roadmap
§122.6), which then transfers the fixed normal vector of `holAux` to `transport`.
-/

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
variable {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}

/-- The composite holonomy with the partition, the charts and the geodesic run over the **bare chart
data** `N, c, x` (Roadmap §122.6): this is `holAux` with the cover data explicit, so that it can be
instantiated both at `(P.N, P.t, z)` (giving back `holAux`) and at a `GeodesicCover`'s fields. -/
noncomputable def holAuxC (htor : cov.torsion = 0) (N : ℕ) (c : ℕ → ℝ) (x : ℕ → M)
    (mono : ∀ k < N, c k < c (k + 1))
    (hu : ∀ k < N, ContinuousOn (fun t : ℝ => (extChartAt I (x k)) (γ t)) (Icc (c k) (c (k + 1))))
    (hw : ∀ k < N, ContinuousOn (deriv (fun t : ℝ => (extChartAt I (x k)) (γ t)))
      (Icc (c k) (c (k + 1))))
    (htgt : ∀ k < N, ∀ t ∈ Icc (c k) (c (k + 1)),
      (extChartAt I (x k)) (γ t) ∈ (extChartAt I (x k)).target) : ℕ → E →L[ℝ] E
  | 0 => 1
  | (k+1) => (if h : k < N then
        (chartTransition (I := I) (x k) (x (k+1)) (γ (c (k+1)))
          * FundSol.fundSol (cov := cov) (x₀ := x k) htor (mono k h) (hu k h) (hw k h)
              (htgt k h) (c (k+1)))
          * holAuxC htor N c x mono hu hw htgt k
      else holAuxC htor N c x mono hu hw htgt k)

theorem holAuxC_zero (htor : cov.torsion = 0) (N : ℕ) (c : ℕ → ℝ) (x : ℕ → M)
    (mono : ∀ k < N, c k < c (k + 1))
    (hu : ∀ k < N, ContinuousOn (fun t : ℝ => (extChartAt I (x k)) (γ t)) (Icc (c k) (c (k + 1))))
    (hw : ∀ k < N, ContinuousOn (deriv (fun t : ℝ => (extChartAt I (x k)) (γ t)))
      (Icc (c k) (c (k + 1))))
    (htgt : ∀ k < N, ∀ t ∈ Icc (c k) (c (k + 1)),
      (extChartAt I (x k)) (γ t) ∈ (extChartAt I (x k)).target) :
    holAuxC (cov := cov) htor N c x mono hu hw htgt 0 = 1 := rfl

theorem holAuxC_self (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (fun t : ℝ => (extChartAt I (z k)) (γ t)) (Icc (P.t k) (P.t (k + 1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (fun t : ℝ => (extChartAt I (z k)) (γ t)))
      (Icc (P.t k) (P.t (k + 1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k + 1)),
      (extChartAt I (z k)) (γ t) ∈ (extChartAt I (z k)).target) :
    ∀ n, holAuxC (cov := cov) htor P.N P.t z P.mono hu hw htgt n
      = holAux (cov := cov) htor hu hw htgt n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [holAuxC, holAux]
    by_cases h : k < P.N
    · rw [dif_pos h, dif_pos h, ih]
      rfl
    · rw [dif_neg h, dif_neg h, ih]

/-- **The `ParallelGlobal` datum recursion is the composite holonomy**: `datumAt` transports `v` from
`c 0` to `c k` through the chart transitions, and `holAuxC` (with the cover's own chart data) does the
same with the fundamental solution `FundSol.fundSol`.  The step uses
`nextDatum_eq_chartTransition` and `pieceSol_eq_fundSolOn` (both in `Submission.SyngeInput`). -/
theorem datumAt_eq_holAuxC {a b : ℝ} (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ a b)
    (htor : cov.torsion = 0) (v : E)
    (hsrc' : ∀ k, k < C.N → γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source) :
    ∀ k, k ≤ C.N → Submission.ParallelGlobal.datumAt (cov := cov) htor C v k
      = holAuxC (cov := cov) htor C.N C.c C.x C.mono
          (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
          (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
          (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
          k v := by
  intro k
  refine Nat.le_induction ?_ ?_ k (Nat.zero_le k)
  · intro _
    have h0 : Submission.ParallelGlobal.datumAt (cov := cov) htor C v 0 = v := rfl
    rw [h0, holAuxC_zero]
    show (1 : E →L[ℝ] E) v = v
    exact one_apply_eq_self v
  · intro m _ ih hm
    have hm' : m < C.N := by omega
    set W : E := holAuxC (cov := cov) htor C.N C.c C.x C.mono
        (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
        m v with hW
    have hunf : holAuxC (cov := cov) htor C.N C.c C.x C.mono
        (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
        (m + 1) v
        = chartTransition (I := I) (C.x m) (C.x (m + 1)) (γ (C.c (m + 1)))
            (FundSol.fundSol (cov := cov) (x₀ := C.x m) htor (C.mono m hm')
              (Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hm')
              (Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hm')
              (Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hm')
              (C.c (m + 1)) W) := by
      simp only [holAuxC, dif_pos hm', mul_apply_eq_comp]
      rfl
    have hdat : Submission.ParallelGlobal.datumAt (cov := cov) htor C v (m + 1)
        = Submission.ParallelGlobal.nextDatum (cov := cov) htor C m
            (Submission.ParallelGlobal.datumAt (cov := cov) htor C v m) := rfl
    rw [hdat, ih (by omega), hunf,
      nextDatum_eq_chartTransition (cov := cov) C (k := m) hm' htor W (hsrc' m hm')]
    exact congrArg (chartTransition (I := I) (C.x m) (C.x (m + 1)) (γ (C.c (m + 1))))
      (pieceSol_eq_fundSolOn (cov := cov) C (k := m) hm' htor W
        ⟨(C.mono m hm').le, le_rfl⟩)

/-- One-step unfolding of `holAuxC`. -/
theorem holAuxC_succ {N : ℕ} {c : ℕ → ℝ} {x : ℕ → M}
    (mono : ∀ k < N, c k < c (k + 1))
    (hu : ∀ k < N, ContinuousOn (fun t : ℝ => (extChartAt I (x k)) (γ t)) (Icc (c k) (c (k + 1))))
    (hw : ∀ k < N, ContinuousOn (deriv (fun t : ℝ => (extChartAt I (x k)) (γ t)))
      (Icc (c k) (c (k + 1))))
    (htgt : ∀ k < N, ∀ t ∈ Icc (c k) (c (k + 1)),
      (extChartAt I (x k)) (γ t) ∈ (extChartAt I (x k)).target)
    (htor : cov.torsion = 0) {k : ℕ} (hk : k < N) (v : E) :
    holAuxC (cov := cov) htor N c x mono hu hw htgt (k + 1) v
      = chartTransition (I := I) (x k) (x (k + 1)) (γ (c (k + 1)))
          (FundSol.fundSol (cov := cov) (x₀ := x k) htor (mono k hk) (hu k hk) (hw k hk)
            (htgt k hk) (c (k + 1))
            (holAuxC (cov := cov) htor N c x mono hu hw htgt k v)) := by
  simp only [holAuxC, dif_pos hk, mul_apply_eq_comp]

/-- **The endpoint value of the global parallel field is the composite holonomy**, in the form in which
the recursion `holAuxC` unfolds: the index `C.N - 1 + 1` is the successor shape. -/
theorem parallelField_endpoint_eq_holAuxC_succ {a b : ℝ}
    (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ a b) (hN : 0 < C.N)
    (htor : cov.torsion = 0) (v : E)
    (hsrc' : ∀ k, k < C.N → γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source) :
    Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v (C.c (C.N - 1 + 1))
      = frameVector (I := I) (C.x (C.N - 1 + 1)) (γ (C.c (C.N - 1 + 1)))
          (holAuxC (cov := cov) htor C.N C.c C.x C.mono
            (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
            (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
            (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
            (C.N - 1 + 1) v) := by
  have hkN : C.N - 1 < C.N := Nat.sub_lt hN Nat.one_pos
  have hlt : C.c (C.N - 1) < C.c (C.N - 1 + 1) := C.mono (C.N - 1) hkN
  -- (A) the global field at the endpoint is the last piece field
  have hA : Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v (C.c (C.N - 1 + 1))
      = frameVector (I := I) (C.x (C.N - 1)) (γ (C.c (C.N - 1 + 1)))
          (Submission.ParallelGlobal.pieceSol (cov := cov) htor C (C.N - 1)
            (Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1)) (C.c (C.N - 1 + 1))) := by
    rw [Submission.ParallelGlobal.parallelField_piece (cov := cov) htor C hN v (k := C.N - 1) hkN hlt
      le_rfl]
    rfl
  -- (B) pieceSol = fundSol on the last piece
  have hB : frameVector (I := I) (C.x (C.N - 1)) (γ (C.c (C.N - 1 + 1)))
        (Submission.ParallelGlobal.pieceSol (cov := cov) htor C (C.N - 1)
          (Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1)) (C.c (C.N - 1 + 1)))
      = frameVector (I := I) (C.x (C.N - 1)) (γ (C.c (C.N - 1 + 1)))
          (FundSol.fundSol (cov := cov) (x₀ := C.x (C.N - 1)) htor (C.mono (C.N - 1) hkN)
            ((fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
              (C.N - 1) hkN)
            ((fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
              (C.N - 1) hkN)
            ((fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
              (C.N - 1) hkN)
            (C.c (C.N - 1 + 1))
            (Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1))) := by
    have hps := pieceSol_eq_fundSolOn (cov := cov) C (k := C.N - 1) hkN htor
      (Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1)) ⟨hlt.le, le_rfl⟩
    beta_reduce at hps
    rw [hps]
  -- (C) the fundamental solution at the endpoint has the holonomy as its value
  have hC : frameVector (I := I) (C.x (C.N - 1)) (γ (C.c (C.N - 1 + 1)))
        (FundSol.fundSol (cov := cov) (x₀ := C.x (C.N - 1)) htor (C.mono (C.N - 1) hkN)
          ((fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
            (C.N - 1) hkN)
          ((fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
            (C.N - 1) hkN)
          ((fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
            (C.N - 1) hkN)
          (C.c (C.N - 1 + 1)) (Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1)))
      = frameVector (I := I) (C.x (C.N - 1 + 1)) (γ (C.c (C.N - 1 + 1)))
          (holAuxC (cov := cov) htor C.N C.c C.x C.mono
            (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
            (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
            (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
            (C.N - 1 + 1) v) := by
    have hx : γ (C.c (C.N - 1 + 1)) ∈
        (chartAt H (C.x (C.N - 1))).source ∩ (chartAt H (C.x (C.N - 1 + 1))).source :=
      ⟨C.src (C.N - 1) hkN (C.c (C.N - 1 + 1))
          ⟨lt_trans (C.room (C.N - 1) hkN).1 hlt, (C.room (C.N - 1) hkN).2⟩,
        hsrc' (C.N - 1) hkN⟩
    have hd : Submission.ParallelGlobal.datumAt (cov := cov) htor C v (C.N - 1)
        = holAuxC (cov := cov) htor C.N C.c C.x C.mono
            (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
            (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
            (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
            (C.N - 1) v :=
      datumAt_eq_holAuxC (cov := cov) C htor v hsrc' (C.N - 1) (by omega)
    have hha : holAuxC (cov := cov) htor C.N C.c C.x C.mono
          (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
          (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
          (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
          (C.N - 1 + 1) v
        = chartTransition (I := I) (C.x (C.N - 1)) (C.x (C.N - 1 + 1)) (γ (C.c (C.N - 1 + 1)))
            (FundSol.fundSol (cov := cov) (x₀ := C.x (C.N - 1)) htor (C.mono (C.N - 1) hkN)
              ((fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
                (C.N - 1) hkN)
              ((fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
                (C.N - 1) hkN)
              ((fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
                (C.N - 1) hkN)
              (C.c (C.N - 1 + 1))
              (holAuxC (cov := cov) htor C.N C.c C.x C.mono
                (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
                (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
                (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
                (C.N - 1) v)) :=
      holAuxC_succ (mono := C.mono)
        (hu := fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
        (hw := fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
        (htgt := fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
        (htor := htor) (k := C.N - 1) hkN v
    rw [hha, hd, chartTransition_frameVector (I := I) hx]
  rw [hA, hB, hC]

/-- **The endpoint value of the global parallel field is the composite holonomy** in the chart of the
first piece: `parallelField C htor hN v` at `C.c C.N` is the frame vector of the composite
`holAuxC` applied to `v`.  This is the identification of Roadmap §122.7(1). -/
theorem parallelField_endpoint_eq_holAuxC {a b : ℝ}
    (C : Submission.ParallelGlobal.GeodesicCover (I := I) cov γ a b) (hN : 0 < C.N)
    (htor : cov.torsion = 0) (v : E)
    (hsrc' : ∀ k, k < C.N → γ (C.c (k + 1)) ∈ (chartAt H (C.x (k + 1))).source) :
    Submission.ParallelGlobal.parallelField (cov := cov) htor C hN v (C.c C.N)
      = frameVector (I := I) (C.x C.N) (γ (C.c C.N))
          (holAuxC (cov := cov) htor C.N C.c C.x C.mono
            (fun k hk => Submission.ParallelGlobal.continuousOn_chartCoord_piece (cov := cov) C hk)
            (fun k hk => Submission.ParallelGlobal.continuousOn_deriv_chartCoord_piece (cov := cov) C hk)
            (fun k hk t ht => Submission.ParallelGlobal.chartCoord_mem_target_piece (cov := cov) C hk t ht)
            C.N v) := by
  have hN1 : C.N - 1 + 1 = C.N := Nat.sub_add_cancel hN
  have h := parallelField_endpoint_eq_holAuxC_succ (cov := cov) C hN htor v hsrc'
  rw [hN1] at h
  exact h

end
end Submission.HolDet
