import Submission.Diff.Interfaces
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.DeTurckField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lead contracts for the last layer of short-time existence (Galerkin limit), in H10's vocabulary.
`IsGalSol` = the Galerkin ODE solution on `[0,τ]` (the form of `Work.Diff.STE.D.galSol2_exists`).
`GalUniform` = Galerkin solutions exist on ONE interval `[0,τ₀]` for all small `ε ∈ (0,ε₀]`, with `ε`-uniform `BNorm k` bounds for every
`k` and a uniform positivity margin. Definitions and `Prop`s only.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Submission.Diff.STEGal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

/-- The Galerkin state at coefficient vector `c`: `g₀ + Σ c_z · jSym z`. -/
noncomputable def galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : Work.Diff.STE.Bil (I := I) (M := M) :=
  Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)

/-- `c` solves the Galerkin ODE `u' = J (P (J u))` on `[0,τ]` from `u(0) = g₀`, with `J u` positive throughout. -/
def IsGalSol (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε τ : ℝ)
    (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) : Prop :=
  c 0 = 0 ∧
  (∀ t ∈ Icc 0 τ, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε (c t))) x v v) ∧
  ∀ t ∈ Icc 0 τ,
    ∀ (hsym : Work.Diff.STE.D.IsSymm (I := I) (D.J ρ ε (galState D ε (c t))))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε (galState D ε (c t))))
      (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (D.J ρ ε (galState D ε (c t))) x v v),
      ∀ (x : M) (u v : TangentSpace I x),
        HasDerivWithinAt (fun s => galState D ε (c s) x u v)
          ((D.J ρ ε (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ ε (galState D ε (c t)))
            hsym hpos hsm)) x u v)
          (Icc 0 τ) t

/-- Uniform Galerkin existence on one interval, for all SMALL `ε ∈ (0, ε₀]`, with `ε`-uniform bounds at every level and a
positivity margin. (Small `ε` only: positivity of `J ρ ε g₀` is available only for small `ε`; 2026-10-02 fix.) -/
def GalUniform (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ B : ℕ → ℝ,
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∃ c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
      IsGalSol hLC D ρ ε τ₀ c ∧
      ∀ t ∈ Icc 0 τ₀,
        (∀ k : ℕ, D.BNorm k (galState D ε (c t)) ≤ B k) ∧
        ∀ (x : M) (v : TangentSpace I x),
          lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v

end Submission.Diff.STEGal
