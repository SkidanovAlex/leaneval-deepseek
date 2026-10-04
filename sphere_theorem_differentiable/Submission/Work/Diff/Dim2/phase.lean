import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.Dim2.PhaseDefs
import Submission.Work.Diff.Dim2.PhaseAux
import Submission.Work.Diff.Dim2.PhaseMain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

theorem phase
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {D a γ e : ℝ} (ha : 0 < a) (hγ : 0 < γ) (he : 0 < e)
    (htri : ∀ x : M, D ≤ Work.Diff.C.rdist (I := I) (M := M) p x +
      Work.Diff.C.rdist (I := I) (M := M) q x)
    (hsep1 : 3 * a / 4 + (3 * γ / 2 + e) < D) (hsep2 : a + (3 * γ / 2 + e) < D)
    {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {τ : M → ℝ}
    (hτsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ
      {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x})
    (hτV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1)
    (hτann : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 →
      a + τ x = Work.Diff.C.rdist (I := I) (M := M) p x)
    (hτpos : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → 0 < a + τ x)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : ∀ t : ℝ, t ≤ 0 → β t = 0) (hβ1 : ∀ t : ℝ, 1 ≤ t → β t = 1)
    (hβr : ∀ t : ℝ, 0 ≤ β t ∧ β t ≤ 1)
    (hband : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      0 < β (τ x) → β (τ x) < 1 →
      a < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        3 * γ / 2 + e < Work.Diff.C.rdist (I := I) (M := M) q x)
    {Ξ ϑ Θ ψp ψq : ℝ → ℝ}
    (hΞ : ContDiff ℝ ∞ Ξ) (hϑ : ContDiff ℝ ∞ ϑ) (hΘ : ContDiff ℝ ∞ Θ)
    (hψp : ContDiff ℝ ∞ ψp) (hψq : ContDiff ℝ ∞ ψq)
    (hΞarc : ∀ r : ℝ, 0 ≤ r → r ≤ 3 * a / 4 → Ξ r = Real.arcsin (r / (2 * a)))
    (hΞ' : ∀ r : ℝ, 0 < deriv Ξ r) (hΞπ : ∀ r : ℝ, Ξ r < Real.pi)
    (hϑarc : ∀ r : ℝ, 0 ≤ r → r ≤ 3 * γ / 2 → ϑ r = Real.arcsin (r / (2 * γ)))
    (hϑb : ∀ r : ℝ, 0 ≤ r → 0 ≤ ϑ r ∧ ϑ r ≤ Real.pi / 2)
    (hϑ' : ∀ r : ℝ, 0 ≤ r → r ≤ 3 * γ / 2 + e → 0 < deriv ϑ r)
    (hΘ' : ∀ t : ℝ, 0 < deriv Θ t)
    (hΞΘ : ∀ t : ℝ, Ξ (a + t) ≤ Θ t)
    (hΘϑ : ∀ t : ℝ, Θ t ≤ Real.pi - ϑ (3 * γ / 2 + e))
    (hψp1 : ∀ r : ℝ, r ≤ 3 * a / 4 → ψp r = 1)
    (hψp0 : ∀ r : ℝ, a ≤ r → ψp r = 0)
    (hψpr : ∀ r : ℝ, 0 ≤ ψp r ∧ ψp r ≤ 1)
    (hψq1 : ∀ r : ℝ, r ≤ 3 * γ / 2 → ψq r = 1)
    (hψq0 : ∀ r : ℝ, 3 * γ / 2 + e ≤ r → ψq r = 0)
    (hψqr : ∀ r : ℝ, 0 ≤ ψq r ∧ ψq r ≤ 1)
    (hfsm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x < a →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) x)
    (hgsm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 + e →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x)
    (hfV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ a →
      mfderiv I 𝓘(ℝ,ℝ) (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) x (V x) = 1)
    (hgV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 + e →
      mfderiv I 𝓘(ℝ,ℝ) (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x (V x) = -1) :
    ∃ ξ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ,ℝ) ∞ ξ
        {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
          γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x} ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
        ξ x = Ξ (Work.Diff.C.rdist (I := I) (M := M) p x)) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 →
        ξ x = Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x)) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        mfderiv I 𝓘(ℝ,ℝ) ξ x (V x) ≠ 0) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        0 < β (τ x) → β (τ x) < 1 →
        mfderiv I 𝓘(ℝ,ℝ) ξ x = deriv Θ (τ x) • mfderiv I 𝓘(ℝ,ℝ) τ x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        0 < ξ x ∧ ξ x < Real.pi) := by
  exact phase_aux (p := p) (q := q) (D := D) (a := a) (γ := γ) (e := e)
    (V := V) (τ := τ) (β := β) (Ξ := Ξ) (ϑ := ϑ) (Θ := Θ) (ψp := ψp) (ψq := ψq)
    hmet htor ha hγ he htri hsep1 hsep2 hVsm hτsm hτV hτann hτpos hβ hβ0 hβ1 hβr hband
    hΞ hϑ hΘ hψp hψq hΞarc hΞ' hΞπ hϑarc hϑb hϑ' hΘ' hΞΘ hΘϑ
    hψp1 hψp0 hψpr hψq1 hψq0 hψqr hfsm hgsm hfV hgV

end Work.Diff.Dim2
