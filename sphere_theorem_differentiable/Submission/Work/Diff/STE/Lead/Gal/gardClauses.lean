import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.Lead.Gal.GardDef

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The three work packages of `GardData`, as named propositions

`GardData` (in `GardDef.lean`, the interface consumed by `gardingAssembly`) is assembled from three
independent inputs, which this file names once and for all so that the lemmas proving them and the
bridge consuming them can be stated against a short name:

* `GardA` — the **coefficient package**: for `0 < lam ≤ h ≤ K`, a globally smooth, `1`-periodic,
  symmetric, `lam'`-elliptic coefficient family `A : Idx → Idx → (Idx → ℝ) → ℝ` agreeing with the
  inverse `(Gf)⁻¹` of the coordinate chart matrix of `h` on the closed `2σ_j`-ball, with all its
  `pdVec`-jets of order `≤ k` bounded by `CA`; `lam'` and `CA` are *uniform* in `h` and `j`.
* `GardP` — the **residual package**: a globally smooth residual `Ψ` supported in the *open*
  `σ_j`-ball, with `pdVec`-jets of order `≤ k` bounded by `CR` and agreeing with the explicit
  lower-order expression `residualLow` on the closed `2σ_j`-ball; `CR` uniform in `h` and `j`.
* `GardL` — the **energy package**: the `H^{k-1}` and `L²` energies of the localised DeTurck
  operator are bounded by `CL (1 + H^{k+1}(h))`, with `CL` uniform in `h` and `j`.

`GardData_of_data` (in `gardRjBridge.lean`) turns (`GardA`, `GardP`, `GardL`) into
`GardData`; the three components are proved separately (`gardAuniform`, `residualDataPsi`,
`gardingLowEnergy`).
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

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **The coefficient package of the transport.**  Uniform in the section `h` and the chart `j`. -/
def GardA (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (lam K : ℝ) : Prop :=
  ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
      (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
      (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Idx)
        (z : Idx → ℝ) (c d : Idx),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
      (j : ι₀),
      ∃ A : Idx → Idx → (Idx → ℝ) → ℝ,
        (∀ c d z, A c d z = A d c z) ∧
        (∀ z (ξ : Idx → ℝ), lam' * ∑ i, (ξ i) ^ 2
          ≤ ∑ c, ∑ d, A c d z * ξ c * ξ d) ∧
        (∀ c d, ContDiff ℝ (⊤ : ENat) (A c d)) ∧
        (∀ c d, Work.Diff.STE.Periodic1 (A c d)) ∧
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (z : Idx → ℝ) (c d : Idx),
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
            ((A c d y : ℝ) : ℂ)) z‖ ≤ C) ∧
        (∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j → ∀ c d : Idx,
          A c d z = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) c d)

/-- **The residual package of the transport.**  Uniform in the section `h` and the chart `j`. -/
def GardP (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (lam K : ℝ) : Prop :=
  ∃ CR : ℝ, 0 ≤ CR ∧
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
      (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
      (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Idx)
        (z : Idx → ℝ) (c d : Idx),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
      (j : ι₀),
      ∃ Ψ : Idx → Idx → (Idx → ℝ) → ℂ,
        (∀ a b, ContDiff ℝ (⊤ : ENat) (Ψ a b)) ∧
        (∀ a b, Function.support (Ψ a b) ⊆ Metric.ball (0 : Idx → ℝ) (D.σ j)) ∧
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (z : Idx → ℝ) (a b : Idx),
          ‖Work.Diff.STE.pdVec m β (Ψ a b) z‖ ≤ CR) ∧
        (∀ (a b : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ j →
          Ψ a b z
            = ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ))

/-- **The low-order energy package of the transport.**  Uniform in the section `h` and the chart
`j`. -/
def GardL (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (lam K : ℝ) : Prop :=
  ∃ CL : ℝ, 0 ≤ CL ∧
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
      (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
      (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
      (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Idx)
        (z : Idx → ℝ) (c d : Idx),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
      (j : ι₀) (a b : Idx),
      Work.Diff.STE.ENormSq (k - 1)
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        + Work.Diff.STE.ENormSq 0
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ CL * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b))

/-- The coefficient package in the *argument order* used by
`Work.Diff.STE.B3.transport_exists_A_uniform` (`A z p q` instead of `A p q z`, and `ContDiff` of the
uncurried family).  This is definitionally the conclusion of `transport_exists_A_uniform`. -/
def GardAraw (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (lam K : ℝ) : Prop :=
  ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (j : ι₀)
      (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
      (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
      (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Idx)
        (z : Idx → ℝ) (c d : Idx),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
      ∃ (A : (Idx → ℝ) → Idx → Idx → ℝ),
        (∀ z p q, A z p q = A z q p) ∧
        (∀ z (ξ : Idx → ℝ),
          lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) ∧
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx)
          (z : Idx → ℝ) (p q : Idx),
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
            ((A y p q : ℝ) : ℂ)) z‖ ≤ C) ∧
        ContDiff ℝ (⊤ : ENat) A ∧
        Work.Diff.STE.Periodic1 A ∧
        (∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j → ∀ p q,
          A z p q = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)

/-- The raw coefficient package implies `GardA` (transposing the two arguments). -/
theorem GardA_of_raw {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀} {k : ℕ} {lam K : ℝ}
    (h : GardAraw (I := I) (M := M) D k lam K) : GardA (I := I) (M := M) D k lam K := by
  obtain ⟨lam', C, hlam', hC, hb⟩ := h
  refine ⟨lam', C, hlam', hC, ?_⟩
  intro h hsym hsmooth hell hub hjet j
  obtain ⟨A, hsym', hell', hjet', hsm', hper', hid'⟩ := hb h hsym hsmooth j hell hub hjet
  refine ⟨fun c d z => A z c d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d z; exact hsym' z c d
  · intro z ξ; exact hell' z ξ
  · intro c d; exact contDiff_pi.mp (contDiff_pi.mp hsm' c) d
  · intro c d i z
    exact congrFun (congrFun (hper' i z) c) d
  · intro m hm β z c d; exact hjet' m hm β z c d
  · intro z hz c d; exact hid' z hz c d

end

end Work.Diff.STE.Lead.Gal
