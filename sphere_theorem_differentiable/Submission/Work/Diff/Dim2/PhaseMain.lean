import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.Dim2.PhaseDefs
import Submission.Work.Diff.Dim2.PhaseAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

/-! ## Auxiliary facts about the smooth cutoff `smoothCut` -/

private theorem scut_props {s t : ℝ} (hst : s < t) :
    ContDiff ℝ ∞ (smoothCut s t) ∧
    (∀ r : ℝ, r ≤ s → smoothCut s t r = 1) ∧
    (∀ r : ℝ, t ≤ r → smoothCut s t r = 0) ∧
    (∀ r : ℝ, 0 ≤ smoothCut s t r ∧ smoothCut s t r ≤ 1) ∧
    Antitone (smoothCut s t) ∧
    (∀ r : ℝ, deriv (smoothCut s t) r ≤ 0) ∧
    (∀ r : ℝ, t < r → deriv (smoothCut s t) r = 0) := by
  have hpos : 0 < t - s := by linarith
  have hcont : ContDiff ℝ ∞ (fun r : ℝ => (r - s) / (t - s)) :=
    (contDiff_id.sub contDiff_const).div_const _
  have hone : ∀ r : ℝ, r ≤ s → smoothCut s t r = 1 := by
    intro r hr
    unfold smoothCut
    have h : (r - s) / (t - s) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
    rw [Real.smoothTransition.zero_of_nonpos h, sub_zero]
  have hzero : ∀ r : ℝ, t ≤ r → smoothCut s t r = 0 := by
    intro r hr
    unfold smoothCut
    have h : 1 ≤ (r - s) / (t - s) := by
      rw [le_div_iff₀ hpos]; linarith
    rw [Real.smoothTransition.one_of_one_le h, sub_self]
  have hmono : Monotone (fun r : ℝ => (r - s) / (t - s)) := by
    intro r₁ r₂ hr
    change (r₁ - s) / (t - s) ≤ (r₂ - s) / (t - s)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hpos))
  have hcomp : Monotone (fun r : ℝ => Real.smoothTransition ((r - s) / (t - s))) :=
    Real.smoothTransition.monotone.comp hmono
  have hanti : Antitone (smoothCut s t) := by
    intro r₁ r₂ hr
    unfold smoothCut
    exact sub_le_sub_left (hcomp hr) 1
  refine ⟨?_, hone, hzero, ?_, hanti, fun r => Antitone.deriv_nonpos hanti, ?_⟩
  · unfold smoothCut
    exact contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp hcont)
  · intro r
    unfold smoothCut
    have h1 := Real.smoothTransition.le_one ((r - s) / (t - s))
    have h2 := Real.smoothTransition.nonneg ((r - s) / (t - s))
    constructor <;> linarith
  · intro r hr
    have hopen : {y : ℝ | t < y} ∈ 𝓝 r := (isOpen_lt continuous_const continuous_id).mem_nhds hr
    have hev : smoothCut s t =ᶠ[𝓝 r] (fun _ => 0) := by
      filter_upwards [hopen] with y hy
      exact hzero y (le_of_lt hy)
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact deriv_const r 0

/-! ## Smoothness of the phase shape -/

private theorem shape_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {A B Ξ ϑ Θ : ℝ → ℝ} {τ F G : M → ℝ} {x : M}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hΞ : ContDiff ℝ ∞ Ξ)
    (hϑ : ContDiff ℝ ∞ ϑ) (hΘ : ContDiff ℝ ∞ Θ)
    (hF : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F x) (hG : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ G x)
    (hτ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (phaseShape A B Ξ ϑ Θ τ F G) x := by
  have hAF : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => A (F y)) x :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ)).mpr hA).contMDiffAt.comp x hF
  have hΞF : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => Ξ (F y)) x :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ)).mpr hΞ).contMDiffAt.comp x hF
  have hBG : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => B (G y)) x :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ)).mpr hB).contMDiffAt.comp x hG
  have hϑG : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => ϑ (G y)) x :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ)).mpr hϑ).contMDiffAt.comp x hG
  have hΘτ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => Θ (τ y)) x :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ)).mpr hΘ).contMDiffAt.comp x hτ
  have hS1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => A (F y) * Ξ (F y)) x := hAF.mul hΞF
  have hP : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => 1 - A (F y) - B (G y)) x :=
    ((contMDiffAt_const (c := (1 : ℝ))).sub hAF).sub hBG
  have hS2 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => (1 - A (F y) - B (G y)) * Θ (τ y)) x :=
    hP.mul hΘτ
  have hR : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => Real.pi - ϑ (G y)) x :=
    (contMDiffAt_const (c := Real.pi)).sub hϑG
  have hS3 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => B (G y) * (Real.pi - ϑ (G y))) x :=
    hBG.mul hR
  have h123 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun y => (A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y))
        + B (G y) * (Real.pi - ϑ (G y))) x := hS1.add hS2 |>.add hS3
  exact h123

/-! ## The derivative of the phase shape in a direction -/

private theorem shape_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {A B Ξ ϑ Θ : ℝ → ℝ} {τ F G : M → ℝ} {x : M} {v : TangentSpace I x}
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B (G x))
    (hΞ : DifferentiableAt ℝ Ξ (F x)) (hϑ : DifferentiableAt ℝ ϑ (G x))
    (hΘ : DifferentiableAt ℝ Θ (τ x))
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) (hG : MDifferentiableAt I 𝓘(ℝ,ℝ) G x)
    (hτ : MDifferentiableAt I 𝓘(ℝ,ℝ) τ x)
    (hdF : mvfderiv I F x v = 1) (hdG : mvfderiv I G x v = -1) (hdτ : mvfderiv I τ x v = 1) :
    mvfderiv I (phaseShape A B Ξ ϑ Θ τ F G) x v
      = deriv A (F x) * (Ξ (F x) - Θ (τ x)) + A (F x) * deriv Ξ (F x)
        + (1 - A (F x) - B (G x)) * deriv Θ (τ x)
        - deriv B (G x) * (Real.pi - ϑ (G x) - Θ (τ x)) + B (G x) * deriv ϑ (G x) := by
  have hAF : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => A (F y)) x := hA.comp_mdifferentiableAt hF
  have hΞF : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => Ξ (F y)) x := hΞ.comp_mdifferentiableAt hF
  have hBG : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => B (G y)) x := hB.comp_mdifferentiableAt hG
  have hϑG : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => ϑ (G y)) x := hϑ.comp_mdifferentiableAt hG
  have hΘτ : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => Θ (τ y)) x := hΘ.comp_mdifferentiableAt hτ
  have h1 : mvfderiv I (fun y => A (F y) * Ξ (F y)) x v
      = A (F x) * (deriv Ξ (F x) * mvfderiv I F x v)
        + Ξ (F x) * (deriv A (F x) * mvfderiv I F x v) := by
    rw [mvfderiv_mul_apply hAF hΞF, mvfderiv_comp_scalar hΞ hF, mvfderiv_comp_scalar hA hF]
  have hPmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => 1 - A (F y) - B (G y)) x :=
    ((mdifferentiableAt_const (c := (1 : ℝ))).sub hAF).sub hBG
  have hPval : mvfderiv I (fun y => 1 - A (F y) - B (G y)) x v
      = -(deriv A (F x) * mvfderiv I F x v) - deriv B (G x) * mvfderiv I G x v := by
    have h1 : mvfderiv I (fun y => 1 - A (F y)) x v
        = -(deriv A (F x) * mvfderiv I F x v) := by
      rw [mvfderiv_const_sub_apply hAF, mvfderiv_comp_scalar hA hF]
    have hsub1 : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => 1 - A (F y)) x := by
      have hfun : (fun y : M => 1 - A (F y))
          = (fun _ : M => (1 : ℝ)) - (fun y : M => A (F y)) := rfl
      rw [hfun]
      exact (mdifferentiableAt_const (c := (1 : ℝ))).sub hAF
    rw [mvfderiv_sub_apply hsub1 hBG, h1, mvfderiv_comp_scalar hB hG]
  have h2 : mvfderiv I (fun y => (1 - A (F y) - B (G y)) * Θ (τ y)) x v
      = (1 - A (F x) - B (G x)) * (deriv Θ (τ x) * mvfderiv I τ x v)
        + Θ (τ x) * (-(deriv A (F x) * mvfderiv I F x v)
          - deriv B (G x) * mvfderiv I G x v) := by
    rw [mvfderiv_mul_apply hPmd hΘτ, hPval, mvfderiv_comp_scalar hΘ hτ]
  have hRmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => Real.pi - ϑ (G y)) x :=
    (mdifferentiableAt_const (c := Real.pi)).sub hϑG
  have hRval : mvfderiv I (fun y => Real.pi - ϑ (G y)) x v
      = -(deriv ϑ (G x) * mvfderiv I G x v) := by
    rw [mvfderiv_const_sub_apply hϑG, mvfderiv_comp_scalar hϑ hG]
  have h3 : mvfderiv I (fun y => B (G y) * (Real.pi - ϑ (G y))) x v
      = B (G x) * (-(deriv ϑ (G x) * mvfderiv I G x v))
        + (Real.pi - ϑ (G x)) * (deriv B (G x) * mvfderiv I G x v) := by
    rw [mvfderiv_mul_apply hBG hRmd, hRval, mvfderiv_comp_scalar hB hG]
  have h1md : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => A (F y) * Ξ (F y)) x := hAF.mul hΞF
  have h2md : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun y => (1 - A (F y) - B (G y)) * Θ (τ y)) x := hPmd.mul hΘτ
  have h3md : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun y => B (G y) * (Real.pi - ϑ (G y))) x := hBG.mul hRmd
  have h12md : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun y => A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y)) x :=
    h1md.add h2md
  have h12 : mvfderiv I (fun y => A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y)) x v
      = mvfderiv I (fun y => A (F y) * Ξ (F y)) x v
        + mvfderiv I (fun y => (1 - A (F y) - B (G y)) * Θ (τ y)) x v :=
    mvfderiv_add_apply h1md h2md
  have hfull : mvfderiv I (phaseShape A B Ξ ϑ Θ τ F G) x v
      = mvfderiv I (fun y => A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y)) x v
        + mvfderiv I (fun y => B (G y) * (Real.pi - ϑ (G y))) x v := by
    rw [show phaseShape A B Ξ ϑ Θ τ F G
        = fun y => (fun y => A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y)) y
            + (fun y => B (G y) * (Real.pi - ϑ (G y))) y from rfl]
    exact mvfderiv_add_apply h12md h3md
  rw [hfull, h12, h1, h2, h3, hdF, hdG, hdτ]
  ring

theorem phase_aux
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
  -- ## 0. The cutoffs and their properties
  set A : ℝ → ℝ := smoothCut (3 * a / 4) a with hAdef
  set B : ℝ → ℝ := smoothCut (3 * γ / 2) (3 * γ / 2 + e / 2) with hBdef
  obtain ⟨hAcut, hA1x, hA0x, hArng, hAanti, hAder, hAder0⟩ :=
    scut_props (s := 3 * a / 4) (t := a) (by linarith)
  obtain ⟨hBcut, hB1x, hB0x, hBrng, hBanti, hBder, hBder0⟩ :=
    scut_props (s := 3 * γ / 2) (t := 3 * γ / 2 + e / 2) (by linarith)
  have hAcA : ContDiff ℝ ∞ A := by rw [hAdef]; exact hAcut
  have hBcB : ContDiff ℝ ∞ B := by rw [hBdef]; exact hBcut
  have hA1 : ∀ r : ℝ, r ≤ 3 * a / 4 → A r = 1 := fun r hr => by rw [hAdef]; exact hA1x r hr
  have hA0 : ∀ r : ℝ, a ≤ r → A r = 0 := fun r hr => by rw [hAdef]; exact hA0x r hr
  have hAr : ∀ r : ℝ, 0 ≤ A r ∧ A r ≤ 1 := fun r => by rw [hAdef]; exact hArng r
  have hAd : ∀ r : ℝ, deriv A r ≤ 0 := fun r => by rw [hAdef]; exact hAder r
  have hAd0 : ∀ r : ℝ, a < r → deriv A r = 0 := fun r hr => by rw [hAdef]; exact hAder0 r hr
  have hB1 : ∀ r : ℝ, r ≤ 3 * γ / 2 → B r = 1 := fun r hr => by rw [hBdef]; exact hB1x r hr
  have hB0 : ∀ r : ℝ, 3 * γ / 2 + e / 2 ≤ r → B r = 0 := fun r hr => by
    rw [hBdef]; exact hB0x r hr
  have hBr : ∀ r : ℝ, 0 ≤ B r ∧ B r ≤ 1 := fun r => by rw [hBdef]; exact hBrng r
  have hBd : ∀ r : ℝ, deriv B r ≤ 0 := fun r => by rw [hBdef]; exact hBder r
  have hBd0 : ∀ r : ℝ, 3 * γ / 2 + e / 2 < r → deriv B r = 0 := fun r hr => by
    rw [hBdef]; exact hBder0 r hr
  -- ## 1. The distance functions, the phase and the region
  set f : M → ℝ := fun x => Work.Diff.C.rdist (I := I) (M := M) p x with hfdef
  set g : M → ℝ := fun x => Work.Diff.C.rdist (I := I) (M := M) q x with hgdef
  set R : Set M := {x : M | a / 4 < f x ∧ γ / 4 < g x} with hRdef
  set D1 : M → ℝ := fun x => deriv A (f x) * (Ξ (f x) - Θ (τ x)) + A (f x) * deriv Ξ (f x)
    + (1 - A (f x) - B (g x)) * deriv Θ (τ x)
    - deriv B (g x) * (Real.pi - ϑ (g x) - Θ (τ x)) + B (g x) * deriv ϑ (g x) with hD1def
  set ξ : M → ℝ := phaseShape A B Ξ ϑ Θ τ f g with hξdef
  have hfcont : Continuous f := by
    rw [hfdef]; exact Work.Diff.C.rdist_continuous (I := I) (M := M) p
  have hgcont : Continuous g := by
    rw [hgdef]; exact Work.Diff.C.rdist_continuous (I := I) (M := M) q
  have hRopen : IsOpen R := by
    rw [hRdef]
    exact IsOpen.inter (isOpen_lt continuous_const hfcont) (isOpen_lt continuous_const hgcont)
  have htri' : ∀ x : M, D ≤ f x + g x := fun x => by simpa only [hfdef, hgdef] using htri x
  have hτsm' : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ R := by
    rw [hRdef]; simpa only [hfdef, hgdef] using hτsm
  have hτV' : ∀ x : M, a / 4 < f x → γ / 4 < g x →
      mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1 := fun x h1 h2 =>
    hτV x (by simpa only [hfdef] using h1) (by simpa only [hgdef] using h2)
  have hτann' : ∀ x : M, a / 4 < f x → γ / 4 < g x → f x ≤ 3 * a / 2 →
      a + τ x = f x := fun x h1 h2 h3 => by
    simpa only [hfdef] using hτann x (by simpa only [hfdef] using h1)
      (by simpa only [hgdef] using h2) (by simpa only [hfdef] using h3)
  have hgsm' : ∀ x : M, a / 4 < f x → γ / 4 < g x → g x < 3 * γ / 2 + e →
      CMDiffAt ∞ g x := fun x h1 h2 h3 => by
    simpa only [hgdef] using hgsm x (by simpa only [hfdef] using h1)
      (by simpa only [hgdef] using h2) (by simpa only [hgdef] using h3)
  have hgV' : ∀ x : M, a / 4 < f x → γ / 4 < g x → g x ≤ 3 * γ / 2 + e →
      mfderiv I 𝓘(ℝ,ℝ) g x (V x) = -1 := fun x h1 h2 h3 => by
    simpa only [hgdef] using hgV x (by simpa only [hfdef] using h1)
      (by simpa only [hgdef] using h2) (by simpa only [hgdef] using h3)
  have hτat : ∀ x ∈ R, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x := fun x hx =>
    hτsm'.contMDiffAt (hRopen.mem_nhds hx)
  have hτmdAt : ∀ x ∈ R, MDifferentiableAt I 𝓘(ℝ,ℝ) τ x := fun x hx =>
    (hτat x hx).mdifferentiableAt (by simp)
  have hf_eq : ∀ x ∈ R, f x < 3 * a / 2 → f =ᶠ[𝓝 x] (fun y => a + τ y) := by
    intro x hxR hflt
    have hU : R ∩ {y : M | f y < 3 * a / 2} ∈ 𝓝 x :=
      Filter.inter_mem (hRopen.mem_nhds hxR) ((isOpen_lt hfcont continuous_const).mem_nhds hflt)
    filter_upwards [hU] with y hy
    exact (hτann' y hy.1.1 hy.1.2 (le_of_lt hy.2)).symm
  have hf_sm : ∀ x ∈ R, f x < 3 * a / 2 → CMDiffAt ∞ f x := by
    intro x hxR hflt
    have hs : CMDiffAt ∞ (fun y : M => a + τ y) x :=
      (contMDiffAt_const (c := a)).add (hτat x hxR)
    exact hs.congr_of_eventuallyEq (hf_eq x hxR hflt)
  have hdf : ∀ x ∈ R, f x < 3 * a / 2 → mvfderiv I f x (V x) = 1 := by
    intro x hxR hflt
    rw [mvfderiv_congr_of_eventuallyEq (hf_eq x hxR hflt),
      mvfderiv_const_add_apply (hτmdAt x hxR)]
    exact hτV' x hxR.1 hxR.2
  have hfun_add : ∀ x ∈ R, MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => a + τ y) x := fun x hx =>
    ((contMDiffAt_const (c := a)).add (hτat x hx)).mdifferentiableAt (by simp)
  have hfun_sub : ∀ x ∈ R, MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => a - τ y) x := fun x hx =>
    ((contMDiffAt_const (c := a)).sub (hτat x hx)).mdifferentiableAt (by simp)
  have hdf_add : ∀ x ∈ R, mvfderiv I (fun y : M => a + τ y) x (V x) = 1 := fun x hx => by
    rw [mvfderiv_const_add_apply (hτmdAt x hx)]
    exact hτV' x hx.1 hx.2
  have hdf_sub : ∀ x ∈ R, mvfderiv I (fun y : M => a - τ y) x (V x) = -1 := fun x hx => by
    rw [mvfderiv_const_sub_apply (hτmdAt x hx), show mvfderiv I τ x (V x) = (1 : ℝ) from
      hτV' x hx.1 hx.2]
  have hΞd : ∀ r : ℝ, DifferentiableAt ℝ Ξ r := fun r => (hΞ.differentiable (by simp)).differentiableAt
  have hϑd : ∀ r : ℝ, DifferentiableAt ℝ ϑ r := fun r => (hϑ.differentiable (by simp)).differentiableAt
  have hΘd : ∀ r : ℝ, DifferentiableAt ℝ Θ r := fun r => (hΘ.differentiable (by simp)).differentiableAt
  have hAdiff : ∀ r : ℝ, DifferentiableAt ℝ A r :=
    fun r => (hAcA.differentiable (by simp)).differentiableAt
  have hBdiff : ∀ r : ℝ, DifferentiableAt ℝ B r :=
    fun r => (hBcB.differentiable (by simp)).differentiableAt
  have hϑmono : MonotoneOn ϑ (Icc 0 (3 * γ / 2 + e)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) (3 * γ / 2 + e)) hϑ.continuous.continuousOn
      (fun r hr => hϑ' r (interior_subset hr).1 (interior_subset hr).2)).monotoneOn
  -- elementary consequences used repeatedly below
  have hA0_of : ∀ x : M, 3 * a / 2 ≤ f x → A (f x) = 0 := by
    intro x hx; exact hA0 (f x) (by linarith)
  have hAd0_of : ∀ x : M, 3 * a / 2 ≤ f x → deriv A (f x) = 0 := by
    intro x hx; exact hAd0 (f x) (by linarith)
  have hB0_of : ∀ x : M, 3 * γ / 2 + e ≤ g x → B (g x) = 0 := by
    intro x hx; exact hB0 (g x) (by linarith)
  have hBd0_of : ∀ x : M, 3 * γ / 2 + e ≤ g x → deriv B (g x) = 0 := by
    intro x hx; exact hBd0 (g x) (by linarith)
  have hg_mid : ∀ x : M, 3 * γ / 2 + e ≤ g x → 3 * γ / 2 + e / 2 < g x := by
    intro x hx; linarith
  have hf_gt : ∀ x : M, 3 * a / 2 ≤ f x → a < f x := by
    intro x hx; linarith
  -- ## 2. Positivity of the derivative formula
  have hD1pos : ∀ x ∈ R, 0 < D1 x := by
    intro x hxR
    obtain ⟨hx1, hx2⟩ := hxR
    have hb : A (f x) + B (g x) ≤ 1 := by
      by_contra hc
      have hc' : 1 < A (f x) + B (g x) := not_le.mp hc
      have h1 : 0 < A (f x) := by have hbb := (hBr (g x)).2; linarith
      have h2 : 0 < B (g x) := by have haa := (hAr (f x)).2; linarith
      have hfa : f x < a := by
        by_contra hc2
        have := hA0 (f x) (not_lt.mp hc2)
        linarith
      have hga : 3 * γ / 2 + e ≤ g x := by have := htri' x; linarith
      have := hB0 (g x) (by linarith)
      linarith
    have ht1 : 0 ≤ deriv A (f x) * (Ξ (f x) - Θ (τ x)) := by
      by_cases hfa : f x < 3 * a / 2
      · have he : a + τ x = f x := hτann' x hx1 hx2 (le_of_lt hfa)
        have hΞΘx : Ξ (f x) ≤ Θ (τ x) := by rw [← he]; exact hΞΘ (τ x)
        exact mul_nonneg_of_nonpos_of_nonpos (hAd (f x)) (by linarith)
      · have hz : deriv A (f x) = 0 := hAd0 (f x) (by linarith [not_lt.mp hfa])
        rw [hz, zero_mul]
    have ht2a : 0 ≤ A (f x) * deriv Ξ (f x) :=
      mul_nonneg (hAr (f x)).1 (le_of_lt (hΞ' (f x)))
    have ht2b : 0 ≤ (1 - A (f x) - B (g x)) * deriv Θ (τ x) :=
      mul_nonneg (by linarith) (le_of_lt (hΘ' (τ x)))
    have ht2c : 0 ≤ B (g x) * deriv ϑ (g x) := by
      by_cases hBz : B (g x) = 0
      · rw [hBz]; simp
      · have hBpos : 0 < B (g x) := lt_of_le_of_ne (hBr (g x)).1 (Ne.symm hBz)
        have hglt : g x < 3 * γ / 2 + e / 2 := by
          by_contra hc
          exact hBz (hB0 (g x) (not_lt.mp hc))
        exact mul_nonneg (hBr (g x)).1 (le_of_lt (hϑ' (g x) (by linarith [hx2]) (by linarith)))
    have ht3 : 0 ≤ -deriv B (g x) * (Real.pi - ϑ (g x) - Θ (τ x)) := by
      by_cases hge : 3 * γ / 2 + e ≤ g x
      · have hz : deriv B (g x) = 0 := hBd0 (g x) (by linarith)
        rw [hz]; simp
      · have hglt : g x < 3 * γ / 2 + e := not_le.mp hge
        have hmm : ϑ (g x) ≤ ϑ (3 * γ / 2 + e) :=
          hϑmono ⟨by linarith [hx2], le_of_lt hglt⟩ ⟨by linarith [hγ], le_rfl⟩ (le_of_lt hglt)
        have h2 : 0 ≤ Real.pi - ϑ (g x) - Θ (τ x) := by
          have h4 := hΘϑ (τ x); linarith
        exact mul_nonneg (neg_nonneg.mpr (hBd (g x))) h2
    have hkey : 0 < A (f x) * deriv Ξ (f x) + (1 - A (f x) - B (g x)) * deriv Θ (τ x)
        + B (g x) * deriv ϑ (g x) := by
      rcases lt_or_eq_of_le hb with hlt | heq
      · have h1 : 0 < 1 - A (f x) - B (g x) := by linarith
        have h3 : 0 < (1 - A (f x) - B (g x)) * deriv Θ (τ x) :=
          mul_pos h1 (hΘ' (τ x))
        linarith [ht2a, ht2c]
      · rcases lt_or_ge (A (f x)) 1 with hAlt | hAge
        · have hBpos : 0 < B (g x) := by linarith
          have hglt : g x < 3 * γ / 2 + e / 2 := by
            by_contra hc
            exact absurd (hB0 (g x) (not_lt.mp hc)) (ne_of_gt hBpos)
          have h3 : 0 < B (g x) * deriv ϑ (g x) :=
            mul_pos hBpos (hϑ' (g x) (by linarith [hx2]) (by linarith))
          have ht2b0 : (1 - A (f x) - B (g x)) * deriv Θ (τ x) = 0 := by
            rw [show 1 - A (f x) - B (g x) = 0 from by linarith, zero_mul]
          linarith [ht2a, ht2b0]
        · have hA1eq : A (f x) = 1 := le_antisymm (hAr (f x)).2 hAge
          have h3 : 0 < A (f x) * deriv Ξ (f x) := by
            rw [hA1eq, one_mul]; exact hΞ' (f x)
          have ht2b0 : (1 - A (f x) - B (g x)) * deriv Θ (τ x) = 0 := by
            rw [show 1 - A (f x) - B (g x) = 0 from by linarith, zero_mul]
          linarith [ht2c, ht2b0]
    rw [hD1def]
    linarith [ht1, ht2a, ht2b, ht2c, ht3, hkey]
  -- ## 3. Smoothness of `ξ` on `R`
  have hξsmAt : ∀ x ∈ R, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ ξ x := by
    intro x hxR
    have hx1 : a / 4 < f x := hxR.1
    have hx2 : γ / 4 < g x := hxR.2
    by_cases hflt : f x < 3 * a / 2
    · by_cases hglt : g x < 3 * γ / 2 + e
      · have h1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (phaseShape A B Ξ ϑ Θ τ f g) x :=
          shape_contMDiffAt hAcA hBcB hΞ hϑ hΘ (hf_sm x hxR hflt) (hgsm' x hx1 hx2 hglt)
            (hτat x hxR)
        simpa only [hξdef] using h1
      · have hU : R ∩ {y : M | 3 * γ / 2 + e / 2 < g y} ∈ 𝓝 x :=
          Filter.inter_mem (hRopen.mem_nhds hxR)
            ((isOpen_lt continuous_const hgcont).mem_nhds (hg_mid x (not_lt.mp hglt)))
        have heq : ξ =ᶠ[𝓝 x]
            phaseShape A (fun _ => (0 : ℝ)) Ξ ϑ Θ τ f (fun _ => (0 : ℝ)) := by
          filter_upwards [hU] with y hy
          obtain ⟨hyR, hyg⟩ := hy
          rw [hξdef]
          unfold phaseShape
          rw [hB0 (g y) (le_of_lt hyg)]
          simp only [zero_mul, mul_zero, sub_zero]
        have h2 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
            (phaseShape A (fun _ => (0 : ℝ)) Ξ ϑ Θ τ f (fun _ => (0 : ℝ))) x :=
          shape_contMDiffAt hAcA contDiff_const hΞ hϑ hΘ (hf_sm x hxR hflt) contMDiffAt_const
            (hτat x hxR)
        exact h2.congr_of_eventuallyEq heq
    · have hfge : 3 * a / 2 ≤ f x := not_lt.mp hflt
      by_cases hglt : g x < 3 * γ / 2 + e
      · have hU : R ∩ {y : M | a < f y} ∈ 𝓝 x :=
          Filter.inter_mem (hRopen.mem_nhds hxR)
            ((isOpen_lt continuous_const hfcont).mem_nhds (hf_gt x (not_lt.mp hflt)))
        have heq : ξ =ᶠ[𝓝 x]
            phaseShape (fun _ => (0 : ℝ)) B Ξ ϑ Θ τ (fun _ => (0 : ℝ)) g := by
          filter_upwards [hU] with y hy
          obtain ⟨hyR, hyf⟩ := hy
          rw [hξdef]
          unfold phaseShape
          rw [hA0 (f y) (le_of_lt hyf)]
          simp only [zero_mul, mul_zero, sub_zero, zero_sub]
          try ring
        have h2 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
            (phaseShape (fun _ => (0 : ℝ)) B Ξ ϑ Θ τ (fun _ => (0 : ℝ)) g) x :=
          shape_contMDiffAt contDiff_const hBcB hΞ hϑ hΘ contMDiffAt_const
            (hgsm' x hx1 hx2 hglt) (hτat x hxR)
        exact h2.congr_of_eventuallyEq heq
      · have hU : R ∩ {y : M | a < f y} ∩ {y : M | 3 * γ / 2 + e / 2 < g y} ∈ 𝓝 x :=
          Filter.inter_mem (Filter.inter_mem (hRopen.mem_nhds hxR)
            ((isOpen_lt continuous_const hfcont).mem_nhds (hf_gt x (not_lt.mp hflt))))
            ((isOpen_lt continuous_const hgcont).mem_nhds (hg_mid x (not_lt.mp hglt)))
        have heq : ξ =ᶠ[𝓝 x]
            phaseShape (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) Ξ ϑ Θ τ
              (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
          filter_upwards [hU] with y hy
          obtain ⟨⟨hyR, hyf⟩, hyg⟩ := hy
          rw [hξdef]
          unfold phaseShape
          rw [hA0 (f y) (le_of_lt hyf), hB0 (g y) (le_of_lt hyg)]
          simp only [zero_mul, mul_zero, sub_zero, zero_sub]
          try ring
        have h2 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
            (phaseShape (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) Ξ ϑ Θ τ
              (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))) x :=
          shape_contMDiffAt contDiff_const contDiff_const hΞ hϑ hΘ contMDiffAt_const
            contMDiffAt_const (hτat x hxR)
        exact h2.congr_of_eventuallyEq heq
  have hξsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ ξ R := fun x hx => (hξsmAt x hx).contMDiffWithinAt
  refine ⟨ξ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1
    rw [hRdef] at hξsm
    simpa only [hfdef, hgdef] using hξsm
  · -- conjunct 2: the `p`-side value
    intro x h1 h2 h3
    have hx1 : a / 4 < f x := by simpa only [hfdef] using h1
    have hx2 : γ / 4 < g x := by simpa only [hgdef] using h2
    have hx3 : f x ≤ 3 * a / 4 := by simpa only [hfdef] using h3
    have hBz : B (g x) = 0 := by
      apply hB0
      have := htri' x
      linarith
    have hval : ξ x = Ξ (f x) := by
      rw [hξdef]
      unfold phaseShape
      rw [hA1 (f x) hx3, hBz]
      ring
    rw [hval]
  · -- conjunct 3: the `q`-side value
    intro x h1 h2 h3
    have hx1 : a / 4 < f x := by simpa only [hfdef] using h1
    have hx2 : γ / 4 < g x := by simpa only [hgdef] using h2
    have hx3 : g x ≤ 3 * γ / 2 := by simpa only [hgdef] using h3
    have hAz : A (f x) = 0 := by
      apply hA0
      have := htri' x
      linarith
    have hval : ξ x = Real.pi - ϑ (g x) := by
      rw [hξdef]
      unfold phaseShape
      rw [hAz, hB1 (g x) hx3]
      ring
    rw [hval]
  · -- conjunct 4: the derivative in the direction of the field is nonzero
    intro x h1 h2
    have hx1 : a / 4 < f x := by simpa only [hfdef] using h1
    have hx2 : γ / 4 < g x := by simpa only [hgdef] using h2
    have hxR : x ∈ R := ⟨hx1, hx2⟩
    have hne : mvfderiv I ξ x (V x) = D1 x := by
      by_cases hflt : f x < 3 * a / 2
      · have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) f x :=
          (hf_sm x hxR hflt).mdifferentiableAt (by simp)
        have hdfx : mvfderiv I f x (V x) = 1 := hdf x hxR hflt
        by_cases hglt : g x < 3 * γ / 2 + e
        · have hGmd : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
            (hgsm' x hx1 hx2 hglt).mdifferentiableAt (by simp)
          have hdgx : mvfderiv I g x (V x) = -1 := hgV' x hx1 hx2 (le_of_lt hglt)
          rw [hD1def, hξdef]
          exact shape_mvfderiv (hAdiff (f x)) (hBdiff (g x)) (hΞd (f x)) (hϑd (g x))
            (hΘd (τ x)) hFmd hGmd (hτmdAt x hxR) hdfx hdgx (hτV' x hx1 hx2)
        · have hU : R ∩ {y : M | 3 * γ / 2 + e / 2 < g y} ∈ 𝓝 x :=
            Filter.inter_mem (hRopen.mem_nhds hxR)
              ((isOpen_lt continuous_const hgcont).mem_nhds (hg_mid x (not_lt.mp hglt)))
          have heq : ξ =ᶠ[𝓝 x]
              phaseShape A (fun _ => (0 : ℝ)) Ξ ϑ Θ τ f (fun y => a - τ y) := by
            filter_upwards [hU] with y hy
            obtain ⟨hyR, hyg⟩ := hy
            rw [hξdef]
            unfold phaseShape
            rw [hB0 (g y) (le_of_lt hyg)]
            simp only [zero_mul, mul_zero, sub_zero]
          rw [mvfderiv_congr_of_eventuallyEq heq,
            shape_mvfderiv (A := A) (B := fun _ => (0 : ℝ)) (Ξ := Ξ) (ϑ := ϑ) (Θ := Θ)
              (τ := τ) (F := f) (G := fun y => a - τ y) (v := V x)
              (hAdiff (f x)) (differentiableAt_const (0 : ℝ)) (hΞd (f x)) (hϑd (a - τ x))
              (hΘd (τ x)) hFmd (hfun_sub x hxR) (hτmdAt x hxR) hdfx (hdf_sub x hxR)
              (hτV' x hx1 hx2)]
          simp only [hD1def]
          rw [hB0_of x (not_lt.mp hglt), hBd0_of x (not_lt.mp hglt)]
          simp only [deriv_const, zero_mul, mul_zero, sub_zero]
          try ring
      · have hfge : 3 * a / 2 ≤ f x := not_lt.mp hflt
        by_cases hglt : g x < 3 * γ / 2 + e
        · have hGmd : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
            (hgsm' x hx1 hx2 hglt).mdifferentiableAt (by simp)
          have hdgx : mvfderiv I g x (V x) = -1 := hgV' x hx1 hx2 (le_of_lt hglt)
          have hU : R ∩ {y : M | a < f y} ∈ 𝓝 x :=
            Filter.inter_mem (hRopen.mem_nhds hxR)
              ((isOpen_lt continuous_const hfcont).mem_nhds (hf_gt x (not_lt.mp hflt)))
          have heq : ξ =ᶠ[𝓝 x]
              phaseShape (fun _ => (0 : ℝ)) B Ξ ϑ Θ τ (fun y => a + τ y) g := by
            filter_upwards [hU] with y hy
            obtain ⟨hyR, hyf⟩ := hy
            rw [hξdef]
            unfold phaseShape
            rw [hA0 (f y) (le_of_lt hyf)]
            simp only [zero_mul, mul_zero, sub_zero, zero_sub]
            try ring
          rw [mvfderiv_congr_of_eventuallyEq heq,
            shape_mvfderiv (A := fun _ => (0 : ℝ)) (B := B) (Ξ := Ξ) (ϑ := ϑ) (Θ := Θ)
              (τ := τ) (F := fun y => a + τ y) (G := g) (v := V x)
              (differentiableAt_const (0 : ℝ)) (hBdiff (g x)) (hΞd (a + τ x)) (hϑd (g x))
              (hΘd (τ x)) (hfun_add x hxR) hGmd (hτmdAt x hxR) (hdf_add x hxR) hdgx
              (hτV' x hx1 hx2)]
          simp only [hD1def]
          rw [hA0_of x hfge, hAd0_of x hfge]
          simp only [deriv_const, zero_mul, mul_zero, sub_zero, zero_sub]
          try ring
        · have hU : R ∩ {y : M | a < f y} ∩ {y : M | 3 * γ / 2 + e / 2 < g y} ∈ 𝓝 x :=
            Filter.inter_mem (Filter.inter_mem (hRopen.mem_nhds hxR)
              ((isOpen_lt continuous_const hfcont).mem_nhds (hf_gt x (not_lt.mp hflt))))
              ((isOpen_lt continuous_const hgcont).mem_nhds (hg_mid x (not_lt.mp hglt)))
          have heq : ξ =ᶠ[𝓝 x]
              phaseShape (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) Ξ ϑ Θ τ
                (fun y => a + τ y) (fun y => a - τ y) := by
            filter_upwards [hU] with y hy
            obtain ⟨⟨hyR, hyf⟩, hyg⟩ := hy
            rw [hξdef]
            unfold phaseShape
            rw [hA0 (f y) (le_of_lt hyf), hB0 (g y) (le_of_lt hyg)]
            simp only [zero_mul, mul_zero, sub_zero, zero_sub]
            try ring
          rw [mvfderiv_congr_of_eventuallyEq heq,
            shape_mvfderiv (A := fun _ => (0 : ℝ)) (B := fun _ => (0 : ℝ)) (Ξ := Ξ) (ϑ := ϑ)
              (Θ := Θ) (τ := τ) (F := fun y => a + τ y) (G := fun y => a - τ y) (v := V x)
              (differentiableAt_const (0 : ℝ)) (differentiableAt_const (0 : ℝ)) (hΞd (a + τ x))
              (hϑd (a - τ x)) (hΘd (τ x)) (hfun_add x hxR) (hfun_sub x hxR) (hτmdAt x hxR)
              (hdf_add x hxR) (hdf_sub x hxR) (hτV' x hx1 hx2)]
          simp only [hD1def]
          rw [hA0_of x hfge, hAd0_of x hfge, hB0_of x (not_lt.mp hglt),
            hBd0_of x (not_lt.mp hglt)]
          simp only [deriv_const, zero_mul, mul_zero, sub_zero, zero_sub]
          try ring
    intro hzero
    have h0 : mvfderiv I ξ x (V x) = 0 := hzero
    have hD1x : 0 < D1 x := hD1pos x hxR
    have hz : D1 x = 0 := hne.symm.trans h0
    linarith
  · -- conjunct 5: the band identity
    intro x h1 h2 hβ1 hβ2
    have hx1 : a / 4 < f x := by simpa only [hfdef] using h1
    have hx2 : γ / 4 < g x := by simpa only [hgdef] using h2
    have hxR : x ∈ R := ⟨hx1, hx2⟩
    obtain ⟨hfa, hga⟩ := hband x (by simpa only [hfdef] using h1) (by simpa only [hgdef] using h2)
      hβ1 hβ2
    have hfa' : a < f x := by simpa only [hfdef] using hfa
    have hga' : 3 * γ / 2 + e < g x := by simpa only [hgdef] using hga
    have hU : R ∩ {y : M | a < f y} ∩ {y : M | 3 * γ / 2 + e / 2 < g y} ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem (hRopen.mem_nhds hxR)
        ((isOpen_lt continuous_const hfcont).mem_nhds hfa'))
        ((isOpen_lt continuous_const hgcont).mem_nhds (hg_mid x (le_of_lt hga')))
    have heq : ξ =ᶠ[𝓝 x] (fun y : M => Θ (τ y)) := by
      filter_upwards [hU] with y hy
      obtain ⟨⟨hyR, hyf⟩, hyg⟩ := hy
      rw [hξdef]
      unfold phaseShape
      rw [hA0 (f y) (le_of_lt hyf), hB0 (g y) (le_of_lt hyg)]
      simp only [zero_mul, mul_zero, sub_zero, zero_sub]
      try ring
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => Θ (τ y)) x :=
      (hΘd (τ x)).comp_mdifferentiableAt (hτmdAt x hxR)
    have hder : mfderiv I 𝓘(ℝ,ℝ) ξ x = mfderiv I 𝓘(ℝ,ℝ) (fun y : M => Θ (τ y)) x :=
      (hmd.hasMFDerivAt.congr_of_eventuallyEq_abuse heq).mfderiv
    have hval : mfderiv I 𝓘(ℝ,ℝ) (fun y : M => Θ (τ y)) x
        = deriv Θ (τ x) • mfderiv I 𝓘(ℝ,ℝ) τ x := by
      have h2' : mvfderiv I (fun y : M => Θ (τ y)) x = deriv Θ (τ x) • mvfderiv I τ x := by
        ext v
        rw [mvfderiv_comp_scalar (hΘd (τ x)) (hτmdAt x hxR)]
        simp only [smul_apply, smul_eq_mul]
      exact h2'
    rw [hder, hval]

  · -- conjunct 6: the range of `ξ`
    intro x h1 h2
    have hx1 : a / 4 < f x := by simpa only [hfdef] using h1
    have hx2 : γ / 4 < g x := by simpa only [hgdef] using h2
    have hfx : (0 : ℝ) < f x := by linarith
    have hΞ0 : Ξ 0 = 0 := by
      rw [hΞarc 0 le_rfl (by linarith), zero_div, Real.arcsin_zero]
    have hΞmono : StrictMono Ξ := strictMono_of_deriv_pos hΞ'
    have hΞpos : ∀ r : ℝ, 0 < r → 0 < Ξ r := fun r hr => by
      have h := hΞmono hr
      rwa [hΞ0] at h
    have hϑ0 : ϑ 0 = 0 := by
      rw [hϑarc 0 le_rfl (by linarith), zero_div, Real.arcsin_zero]
    have hϑmono : StrictMonoOn ϑ (Set.Icc 0 (3 * γ / 2 + e)) :=
      strictMonoOn_of_deriv_pos (convex_Icc 0 (3 * γ / 2 + e))
        (ContDiff.continuous hϑ).continuousOn (fun z hz => by
          rw [interior_Icc] at hz
          exact hϑ' z (le_of_lt hz.1) (le_of_lt hz.2))
    have hϑpos : ∀ r : ℝ, 0 < r → r ≤ 3 * γ / 2 + e → 0 < ϑ r := by
      intro r hr0 hr
      have h := hϑmono (by constructor <;> linarith) (by constructor <;> linarith) hr0
      rwa [hϑ0] at h
    have hX : 0 < Ξ (f x) ∧ Ξ (f x) < Real.pi := ⟨hΞpos _ hfx, hΞπ _⟩
    have hY : 0 < Θ (τ x) ∧ Θ (τ x) < Real.pi := by
      have ha' : 0 < a + τ x := hτpos x hx1 hx2
      have h1 : Ξ (a + τ x) ≤ Θ (τ x) := hΞΘ (τ x)
      have h2 : 0 < Ξ (a + τ x) := hΞpos _ ha'
      have h3 : Θ (τ x) ≤ Real.pi - ϑ (3 * γ / 2 + e) := hΘϑ (τ x)
      have h4 : 0 < ϑ (3 * γ / 2 + e) := hϑpos _ (by linarith) le_rfl
      exact ⟨lt_of_lt_of_le h2 h1, by linarith⟩
    have key : ∀ (l m u v : ℝ), 0 ≤ l → 0 ≤ m → l + m = 1 → 0 < u → u < Real.pi →
        0 < v → v < Real.pi → 0 < l * u + m * v ∧ l * u + m * v < Real.pi := by
      intro l m u v hl hm hlm hu huπ hv hvπ
      have h1 : l * min u v + m * min u v ≤ l * u + m * v := by
        have ha := mul_le_mul_of_nonneg_left (min_le_left u v) hl
        have hb := mul_le_mul_of_nonneg_left (min_le_right u v) hm
        linarith
      have h2 : l * u + m * v ≤ l * max u v + m * max u v := by
        have ha := mul_le_mul_of_nonneg_left (le_max_left u v) hl
        have hb := mul_le_mul_of_nonneg_left (le_max_right u v) hm
        linarith
      have h3 : 0 < min u v := lt_min hu hv
      have h4 : max u v < Real.pi := max_lt huπ hvπ
      constructor <;> nlinarith [h1, h2, h3, h4]
    have hval : ξ x = A (f x) * Ξ (f x) + (1 - A (f x) - B (g x)) * Θ (τ x)
        + B (g x) * (Real.pi - ϑ (g x)) := by
      rw [hξdef]; unfold phaseShape; rfl
    rcases eq_or_lt_of_le (hBr (g x)).1 with hBz | hBp
    · -- `B (g x) = 0`: a convex combination of `Ξ (f x)` and `Θ (τ x)`
      have hthis : ξ x = A (f x) * Ξ (f x) + (1 - A (f x)) * Θ (τ x) := by
        rw [hval, hBz.symm]; ring
      rw [hthis]
      exact key (A (f x)) (1 - A (f x)) (Ξ (f x)) (Θ (τ x)) (hAr (f x)).1
        (by linarith [(hAr (f x)).2]) (by ring) hX.1 hX.2 hY.1 hY.2
    · -- `B (g x) > 0`: then `f x ≥ a`, so `A (f x) = 0`
      have hglt : g x < 3 * γ / 2 + e / 2 := by
        by_contra hcon
        push_neg at hcon
        rw [hB0 (g x) hcon] at hBp
        linarith
      have hfge : a ≤ f x := by
        by_contra hcon
        push_neg at hcon
        have htx := htri' x
        linarith
      have hAz : A (f x) = 0 := hA0 (f x) hfge
      have hZ : 0 < Real.pi - ϑ (g x) ∧ Real.pi - ϑ (g x) < Real.pi := by
        have hg0 : 0 ≤ g x := by linarith
        have hle : ϑ (g x) ≤ Real.pi / 2 := (hϑb (g x) hg0).2
        have hlt : g x ≤ 3 * γ / 2 + e := by linarith
        have hpos : 0 < ϑ (g x) := hϑpos (g x) (by linarith) hlt
        constructor <;> linarith
      have hthis : ξ x = (1 - B (g x)) * Θ (τ x)
          + B (g x) * (Real.pi - ϑ (g x)) := by
        rw [hval, hAz]; ring
      rw [hthis]
      exact key (1 - B (g x)) (B (g x)) (Θ (τ x)) (Real.pi - ϑ (g x))
        (by linarith [(hBr (g x)).2]) (hBr (g x)).1 (by ring) hY.1 hY.2 hZ.1 hZ.2

end Work.Diff.Dim2
