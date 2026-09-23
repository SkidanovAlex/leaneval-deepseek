import Submission.ParallelRoom
import Submission.HolCover

/-!
# The room-based and the piece-based global parallel field agree

`Submission.ParallelRoom.parallelFieldR` (built from the *room* solutions `pieceSolR`, hence smooth
and parallel along `γ`, `parallelFieldR_spec`) and `Submission.ParallelGlobal.parallelField` (built
from the *piece* solutions `pieceSol`, hence directly comparable with the composite holonomy
`Submission.HolDet.holAuxC`) are two constructions of the same object.  This module proves that they
agree on the interval of the cover:

* `pieceSolR_eq_pieceSol` — on the closed piece;
* `nextDatumR_eq_nextDatum`, `datumAtR_eq_datumAt` — the datum recursions agree;
* **`parallelFieldR_eq_parallelField`** — the two global fields agree.

Consequence: everything proved for `parallelField` (the identification with `holAuxC`, hence the
existence of a *fixed* datum for a closed geodesic, `Submission.HolDet.exists_periodic_parallelField`)
transfers to `parallelFieldR`, and everything proved for `parallelFieldR` (smoothness and parallelism
along `γ`, `parallelFieldR_spec`) transfers back.  This is the bridge that the Synge argument
(Roadmap §§113–114, §122) needs.
-/

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

namespace Submission.ParallelRoom

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

/-- **The room solution and the piece solution agree on the closed piece** (uniqueness for the
parallel equation). -/
theorem pieceSolR_eq_pieceSol (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    EqOn (pieceSolR (cov := cov) htor C k v) (pieceSol (cov := cov) htor C k v)
      (Icc (C.c k) (C.c (k + 1))) :=
  pieceSol_unique (cov := cov) htor C hk v
    (pieceSolR_datum (cov := cov) htor C hk v)
    (pieceSolR_ode_piece (cov := cov) htor C hk v)

/-- The piece fields agree on the closed piece. -/
theorem pieceFieldR_eq_pieceField (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) {t : ℝ} (ht : t ∈ Icc (C.c k) (C.c (k + 1))) :
    pieceFieldR (cov := cov) htor C k v t = pieceField (cov := cov) htor C k v t := by
  rw [pieceFieldR_apply, pieceField]
  exact congrArg (fun w => frameVector (I := I) (C.x k) (γ t) w)
    (pieceSolR_eq_pieceSol (cov := cov) htor C hk v ht)

/-- The junction conversions of the two constructions agree. -/
theorem nextDatumR_eq_nextDatum (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) {k : ℕ}
    (hk : k < C.N) (v : E) :
    nextDatumR (cov := cov) htor C k v = nextDatum (cov := cov) htor C k v := by
  rw [nextDatumR, nextDatum]
  exact congrArg (fun W : TangentSpace I (γ (C.c (k + 1))) =>
      Submission.JacobiCoords.chartCoords (I := I) (C.x (k + 1)) γ
        (fun _ : ℝ => W) (C.c (k + 1)))
    (pieceFieldR_eq_pieceField (cov := cov) htor C hk v ⟨(C.mono k hk).le, le_rfl⟩)

/-- The datum recursions agree. -/
theorem datumAtR_eq_datumAt (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b) (v₀ : E) :
    ∀ k, k ≤ C.N → datumAtR (cov := cov) htor C v₀ k = datumAt (cov := cov) htor C v₀ k := by
  intro k
  induction k with
  | zero => intro _; rw [datumAtR_zero, datumAt_zero]
  | succ k ih =>
      intro hk
      have hklt : k < C.N := Nat.lt_of_succ_le hk
      rw [show datumAtR (cov := cov) htor C v₀ (k + 1)
          = nextDatumR (cov := cov) htor C k (datumAtR (cov := cov) htor C v₀ k) from rfl,
        show datumAt (cov := cov) htor C v₀ (k + 1)
          = nextDatum (cov := cov) htor C k (datumAt (cov := cov) htor C v₀ k) from rfl]
      rw [ih hklt.le]
      exact nextDatumR_eq_nextDatum (cov := cov) htor C hklt _

/-- **THE BRIDGE**: the room-based and the piece-based global parallel fields agree on the interval
of the cover. -/
theorem parallelFieldR_eq_parallelField (htor : cov.torsion = 0) (C : GeodesicCover cov γ a b)
    (hN : 0 < C.N) (v₀ : E) {t : ℝ} (ht : t ∈ Icc (C.c 0) (C.c C.N)) :
    parallelFieldR (cov := cov) htor C hN v₀ t = parallelField (cov := cov) htor C hN v₀ t := by
  have hkN : kOf (cov := cov) C hN t < C.N := kOf_lt (cov := cov) C hN t
  have hmem : t ∈ Icc (C.c (kOf (cov := cov) C hN t)) (C.c (kOf (cov := cov) C hN t + 1)) :=
    ⟨c_kOf_le (cov := cov) C hN ht, kOf_spec' (cov := cov) C hN ht.2⟩
  show pieceFieldR (cov := cov) htor C (kOf (cov := cov) C hN t)
      (datumAtR (cov := cov) htor C v₀ (kOf (cov := cov) C hN t)) t
    = pieceField (cov := cov) htor C (kOf (cov := cov) C hN t)
      (datumAt (cov := cov) htor C v₀ (kOf (cov := cov) C hN t)) t
  rw [datumAtR_eq_datumAt (cov := cov) htor C v₀ _
    (le_trans (kOf_le (cov := cov) C hN t) (Nat.sub_le _ _))]
  exact pieceFieldR_eq_pieceField (cov := cov) htor C hkN _ hmem

end

end Submission.ParallelRoom
