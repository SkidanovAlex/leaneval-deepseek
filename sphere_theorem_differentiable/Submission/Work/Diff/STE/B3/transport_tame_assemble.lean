/-
# The transport identity for the constructed coefficient matrix

This file discharges the **identity clause** of `Work.Diff.STE.B3.transport_deTurck_tame` for the
concrete coefficients of the assembly:

* the coefficient matrix is `A := tmA φ lam' (tmGfi D h j)`, where `tmGfi D h j` is the *honest*
  inverse of the coordinate-frame chart matrix `Gf` of `h` in the chart `j`, and `φ` is a cutoff
  that is identically `1` on the closed `2σ j`-ball and whose support lies in the ball of radius
  `R` with `R ≤ 1/2` (so that the periodisation in `tmA` has at most one non-vanishing translate);
* the residual is `Ψ := φ · tmPsi` (and `φ = 1` on the ball, so on the ball `Ψ` is `tmPsi` composed
  with `(z, Mf z, ∂Mf z)`).

The proof is `transport_identity` (the algebraic reduction, proved in
`B3/transport_tame_identity.lean`) with its three hypotheses supplied by
`tmSecJet` (`B3/transport_tame_sec.lean`), `tmGamma_props` (the clamped inverse `tmGKi` is the
honest inverse of the chart matrix on the `2σ j`-ball) and `tmNom_tame` (the matching of the
nominal objects), together with the identification `tmA φ lam' γ = γ` on the ball
(`B3/transport_tame_ball.lean`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_identity
import Submission.Work.Diff.STE.B3.transport_tame_sec
import Submission.Work.Diff.STE.B3.transport_tame_ball
import Submission.Work.Diff.STE.B3.tmGamma_props
import Submission.Work.Diff.STE.B3.tmNom_tame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The *honest* inverse of the coordinate-frame chart matrix of `h` in the chart `j`: the local
coefficient family of the transport identity, uniformly bounded in `h` (this is the object whose
uniform window/ellipticity data is produced by `tmGamma_uniform`). -/
def tmGfi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)) : ℝ :=
  ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q

/-- **The identity clause of the tame transport**, for the constructed coefficients. -/
theorem tm_identity_clause
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) (af bf : Fin (Module.finrank ℝ E))
    (φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → φ z = 1)
    (R : ℝ) (hR : R ≤ 1 / 2)
    (hsupp : Function.support φ ⊆ Metric.ball 0 R)
    (hRbig : 2 * D.σ j ≤ R)
    (lam' : ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hGam : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      ∀ c d : Fin (Module.finrank ℝ E),
      tmGKi (I := I) (M := M) D j a b ha hab z (fun p q => D.mat j h p q z) c d
        = tmGfi (I := I) (M := M) D h j z c d) :
    ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      ∀ a' b' : Fin (Module.finrank ℝ E),
      D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a' b' z
        = (∑ p, ∑ q, tmA φ lam' (tmGfi (I := I) (M := M) D h j) z p q
              * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a' b')) z)
          + φ z * tmPsi (I := I) (M := M) D j a b ha hab z (fun c d => D.mat j h c d z)
              (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b' := by
  intro z hz a' b'
  -- the transport identity, with the three hypotheses discharged
  have hid := transport_identity (I := I) (M := M) D hLC h hsym hpos hsmooth j a' b' a b ha hab
    (fun z' hz' c d => tmSecJet (I := I) (M := M) D h hsmooth j a' b' hz' c d)
    (fun z' hz' c d => hGam z' hz' c d)
    (fun z' hz' => tmNom_tame (I := I) (M := M) D h hsmooth j hz' a' b') z hz
  rw [hid]
  -- on the ball `tmA φ lam' (tmGfi …) = tmGfi … = tmGKi … (Mf z)`, and `φ = 1`
  have hγ : ∀ p q : Fin (Module.finrank ℝ E),
      tmA φ lam' (tmGfi (I := I) (M := M) D h j) z p q
        = tmGKi (I := I) (M := M) D j a b ha hab z (fun p q => D.mat j h p q z) p q := by
    intro p q
    rw [tmA_eq_of_one (n := Module.finrank ℝ E) φ (tmGfi (I := I) (M := M) D h j)
      hR hRbig hsupp (fun w hw => hφ1 w hw) hz p q]
    exact (hGam z hz p q).symm
  rw [hφ1 z hz, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [hγ p q]

end Work.Diff.STE.B3
