import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.garding_vec_uniform
import Submission.Work.Diff.STE.commutator_estimate
import Submission.Work.Diff.STE.ENormSq_pairing_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The interface of the DeTurck transport used by the Gårding assembly

The target `Work.Diff.STE.Lead.Gal.gardingAssembly` is the dissipation estimate for the DeTurck
operator `P = deTurckSec`, read in the Layer B3 components

`D.Rper i (P h) a b  =  Σ_{pq} A_{pq} · ∂_p∂_q (Rper i h a b) + Θ_{ab}`

with an elliptic periodic coefficient `A` and a lower-order term `Θ` whose `Hᵏ` norm is bounded.

The *geometry* (the DeTurck operator is a scalar second-order operator plus lower order in the
orthonormal-frame component picture, with the principal coefficient the inverse of the chart
metric) is the content of this interface; it is proved by a separate development
(`Work.Diff.STE.Lead.Gal.gardTransport_holds`) which only uses the chart bridge
`Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp` and the decomposition
`Work.Diff.STE.DeTurck.pPhi_decomp`.  The assembly in `gardingAssembly.lean` is then purely
analytic.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The static jet bound of the localised component.**  The `g₀`-orthonormal-frame chart matrix
`D.mat i h c d` has all its flat derivatives of order `≤ k+1` bounded by the jet constant `K`
(hypothesis `hjet` of the target); consequently so does the localised component
`D.Rper i h a b` (the weight `ψ i · √dens i` is a *fixed* smooth function).  This is a pure
Leibniz/Faà-di-Bruno statement about the Layer B3 data. -/
def GardJet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (K : ℝ) : Prop :=
  ∃ CJ : ℝ, 0 ≤ CJ ∧
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
      (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖Work.Diff.STE.pdVec m β (D.Rper j h a b) z‖ ≤ CJ * (1 + K) ^ (k + 1)

/-- **The transport data of the DeTurck operator in the Layer B3 components.**  For the fixed
constants `lam'`, `C` and a section `h` satisfying the standing hypotheses (positive definite,
bounded between `lam g₀` and `K g₀`, with bounded jets `hjet`), each chart `j` carries

* an elliptic (`lam'`), symmetric, `1`-periodic, smooth coefficient family `A` whose iterated
  derivatives of order `≤ k` are bounded by `C`;
* a smooth `1`-periodic lower-order term `Th`, whose `Hᵏ` norm is bounded by `C`;

such that the localised component of `P h` is the scalar second-order operator `Σ A_{pq}∂_p∂_q`
applied to the localised component of `h`, plus `Th`; and such that the `H^{k-1}` and `L²`
energies of `P h` are bounded by `C (1 + H^{k+1}(h))`. -/
def GardData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (lam' C : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) : Prop :=
  ∀ j : ι₀,
    ∃ (A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (Th : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
      (∀ c d z, A c d z = A d c z) ∧
      (∀ z (ξ : Fin (Module.finrank ℝ E) → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d z * ξ c * ξ d) ∧
      (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) ∧
      (∀ c d, Work.Diff.STE.Periodic1 (A c d)) ∧
      (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((A c d y : ℝ) : ℂ)) z‖ ≤ C) ∧
      (∀ a b, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Th a b)) ∧
      (∀ a b, Work.Diff.STE.Periodic1 (Th a b)) ∧
      (∀ a b, Work.Diff.STE.ENormSq k (Th a b) ≤ C) ∧
      (∀ a b z,
        D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
          = (∑ c, ∑ d,
              ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
            + Th a b z) ∧
      (∀ a b, Work.Diff.STE.ENormSq (k - 1)
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ C * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b))) ∧
      (∀ a b, Work.Diff.STE.ENormSq 0
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ C * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)))

end

end Work.Diff.STE.Lead.Gal
