import Mathlib
import Submission.Work.EvenBound.Imports

namespace Work.EvenBound.SyngeField

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.ParallelGlobal
open Submission.OrientSign
open Submission.ParallelRoom

/-- **Synge's parallel normal field for a `1`-periodic closed geodesic.**  On a compact,
**simply connected**, **even-dimensional** manifold, every `1`-periodic geodesic `γ` with
non-vanishing velocity carries a **smooth, parallel, `1`-periodic unit normal field**:
`Z 1 = Z 0`, `‖Z t‖ = 1` and `Z t ⊥ γ'(t)` for `t ∈ [0,1]`, and `SmoothAlongAt`/`covAlong Z = 0`
on the window `[-1, 2]`.

*Proof route.*  Apply `Submission.OrientSign.exists_chartLoop_of_simplyConnected` to the closed path
`t ↦ γ (Set.projIcc 0 1 zero_le_one t)` to obtain a partition `P` of `[0,1]` and charts `z` with
`IsChartLoop P γ z` and `loopSignOf P γ z = 1`; derive `hloop : γ (P.t P.N) = γ (P.t 0)` and the
chart-velocity periodicity `hvelper` from `hper` (exactly as in
`Submission.SyngeWindow.exists_shorter_closed_curve_of_synge`), and apply
`Submission.HolDet.exists_synge_field` to get a parallel periodic unit normal field
`X = parallelFieldR` along `γ` on `[0,1]`, with `X 1 = X 0`, `‖X t‖ = 1` and `X t ⊥ γ'(t)` for
`t ∈ [0,1]`, and `SmoothAlongAt`/`covAlong X = 0` there.  Finally use
`Submission.SyngeWindow.pext_spec` (the periodic extension `pext` of a field along a `1`-periodic
curve) to extend `X` to the window `[-1, 2]`, keeping smoothness and parallelism (norm/normality and
periodicity `Z 1 = Z 0` are only asserted on `[0,1]`). -/
theorem exists_synge_field_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [SimplyConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov γ t)
    (hnev : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hEven : Even (Module.finrank ℝ E)) :
    ∃ (Z : (t : ℝ) → TangentSpace I (γ t)), Z 1 = Z 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Z t‖ = 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        inner ℝ (Z t) (Submission.Geodesic.curveVelocity (I := I) γ t) = 0) ∧
      (∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1), Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z s) ∧
      (∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1), Submission.JacobiGlobal.covAlong cov Z s = 0) := by
  classical
  -- The loop `γ` cut down to the window `[0,1]`, as a `Path (γ 0) (γ 0)`.
  let γpath : Path (γ 0) (γ 0) :=
    Path.mk ⟨fun t : Set.Icc (0 : ℝ) 1 => γ (t : ℝ),
      hγsm.continuous.comp continuous_subtype_val⟩ rfl (by simpa using hper 0)
  obtain ⟨P, z, hP0, hsign0⟩ :=
    Submission.OrientSign.exists_chartLoop_of_simplyConnected (I := I) γpath
  -- On `[0,1]` the re-projection is the identity, so `γpath ∘ projIcc = γ`.
  have hγ' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      γpath (Set.projIcc 0 1 zero_le_one τ) = γ τ := by
    intro τ hτ
    show γ (↑(Set.projIcc 0 1 zero_le_one τ) : ℝ) = γ τ
    rw [congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hτ)]
  -- The partition points of `P` lie in `[0,1]`.
  have h01 : ∀ k ≤ P.N, P.t k ∈ Set.Icc (0 : ℝ) 1 := fun k hk =>
    ⟨by linarith [P.mono_le (Nat.zero_le k) hk, P.t_zero],
     by linarith [P.mono_le hk le_rfl, P.t_last]⟩
  -- Transfer the chart-loop data from the re-projected path to `γ` itself.
  have hP : IsChartLoop (H := H) P γ z := by
    refine ⟨?_, ?_, hP0.2.2⟩
    · intro k hk x hx
      have hxk : x ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (h01 k hk.le).1 hx.1, le_trans hx.2 (h01 (k+1) hk).2⟩
      rw [← hγ' x hxk]
      exact hP0.1 k hk x hx
    · intro k hk
      have hxk : P.t (k+1) ∈ Set.Icc (0 : ℝ) 1 := h01 (k+1) (by omega)
      rw [← hγ' _ hxk]
      exact hP0.2.1 k hk
  -- The loop sign agrees, and is `1` by simple connectivity.
  have hloopSign : loopSignOf (I := I) P γ z = 1 := by
    have hsigneq : loopSignOf (I := I) P γ z
        = loopSignOf (I := I) P (fun τ : ℝ => γpath (Set.projIcc 0 1 zero_le_one τ)) z := by
      simp only [loopSignOf]
      refine Finset.prod_congr rfl ?_
      intro k hk
      have hk' : k < P.N := Finset.mem_range.mp hk
      rw [← hγ' _ (h01 (k+1) (by omega))]
    rw [hsigneq, hsign0]
  -- The endpoint periodicity and the chart-velocity periodicity, from `hper`.
  have hloop : γ (P.t P.N) = γ (P.t 0) := by
    rw [P.t_last, P.t_zero]
    simpa using hper 0
  have hvelper : deriv (Submission.HolDet.coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (Submission.HolDet.coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) := by
    have h1 : Submission.HolDet.coordC (I := I) (z := z) (γ := γ) P.N
        = Submission.HolDet.coordC (I := I) (z := z) (γ := γ) 0 := by
      funext t
      show (extChartAt I (z P.N)) (γ t) = (extChartAt I (z 0)) (γ t)
      rw [hP.2.2]
    rw [h1, P.t_last, P.t_zero]
    show deriv (fun s : ℝ => (extChartAt I (z 0)) (γ s)) 1
      = deriv (fun s : ℝ => (extChartAt I (z 0)) (γ s)) 0
    simpa using Submission.SyngeWindow.deriv_chartCoord_periodic (I := I) hper (z 0) 0
  -- Synge's fixed vector of the normal holonomy, on the cover of the loop.
  obtain ⟨C, hN, v, hCN, hCc, hCx, hv0, hXs, hXpar, hXper, hX1, hXnorm⟩ :=
    Submission.HolDet.exists_synge_field (cov := cov) hmet htor hγsm hgeo hnev hP hloop hvelper
      hloopSign hEven
  -- The cover, with the endpoints `0` and `1`.
  have hC0 : C.c 0 = 0 := by rw [hCc, P.t_zero]
  have hCN1 : C.c C.N = 1 := by rw [hCc, hCN, P.t_last]
  let Cs : GeodesicCover cov γ 0 1 :=
    { N := C.N, c := C.c, x := C.x, A := C.A, B := C.B, c_zero := hC0, c_last := hCN1,
      mono := C.mono, room := C.room, src := C.src, ode := C.ode }
  have hperX : parallelFieldR (cov := cov) htor Cs hN v 1
      = parallelFieldR (cov := cov) htor Cs hN v 0 := by
    have h1 : parallelFieldR (cov := cov) htor Cs hN v 1
        = parallelFieldR (cov := cov) htor Cs hN v (C.c C.N) :=
      (Submission.SyngeWindow.fieldArg_eq (V := parallelFieldR (cov := cov) htor Cs hN v)
        hCN1).symm
    have h2 : parallelFieldR (cov := cov) htor Cs hN v (C.c 0)
        = parallelFieldR (cov := cov) htor Cs hN v 0 :=
      Submission.SyngeWindow.fieldArg_eq (V := parallelFieldR (cov := cov) htor Cs hN v) hC0
    exact h1.trans (hXper.trans h2)
  -- The two facts on `[0,1]`, in the language of `Cs`.
  have hX1' : ∀ t ∈ Icc (0 : ℝ) 1, ‖parallelFieldR (cov := cov) htor Cs hN v t‖ = 1 := by
    rw [hC0, hCN1] at hX1
    intro t ht
    exact hX1 t ht
  have hXnorm' : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (parallelFieldR (cov := cov) htor Cs hN v t) (curveVelocity (I := I) γ t) = 0 := by
    rw [hC0, hCN1] at hXnorm
    intro t ht
    exact hXnorm t ht
  -- The periodic extension to the window.
  have hspec := Submission.SyngeWindow.pext_spec (cov := cov) (γ := γ) hmet htor hper hγsm hnev
    Cs hN v hperX
  have hZper : Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
        (parallelFieldR (cov := cov) htor Cs hN v) 1
      = Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
        (parallelFieldR (cov := cov) htor Cs hN v) 0 := by
    rw [Submission.SyngeWindow.pext_of_mem (I := I)
        (X := parallelFieldR (cov := cov) htor Cs hN v) zero_le_one le_rfl,
      Submission.SyngeWindow.pext_of_mem (I := I)
        (X := parallelFieldR (cov := cov) htor Cs hN v) le_rfl zero_le_one]
    exact hperX
  have hZ1 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
        (parallelFieldR (cov := cov) htor Cs hN v) t‖ = 1 := by
    intro t ht
    rw [Submission.SyngeWindow.pext_of_mem (I := I)
      (X := parallelFieldR (cov := cov) htor Cs hN v) ht.1 ht.2]
    exact hX1' t ht
  have hZnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
        (parallelFieldR (cov := cov) htor Cs hN v) t) (curveVelocity (I := I) γ t) = 0 := by
    intro t ht
    rw [Submission.SyngeWindow.pext_of_mem (I := I)
      (X := parallelFieldR (cov := cov) htor Cs hN v) ht.1 ht.2]
    exact hXnorm' t ht
  have hZsm : ∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1),
      SmoothAlongAt (I := I) γ
        (Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
          (parallelFieldR (cov := cov) htor Cs hN v)) s :=
    fun s hs => hspec.1 s (by
      rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hZpar : ∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1),
      covAlong (γ := γ) cov
        (Submission.SyngeWindow.pext (M := M) (γ := γ) (I := I)
          (parallelFieldR (cov := cov) htor Cs hN v)) s = 0 :=
    fun s hs => hspec.2 s (by
      rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  exact ⟨_, hZper, hZ1, hZnorm, hZsm, hZpar⟩

end Work.EvenBound.SyngeField
