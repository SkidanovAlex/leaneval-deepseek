import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.STE.C2.flowData
import Submission.Work.Diff.STE.C2.FlowFamily
import Submission.Work.Diff.STE.C2.MasterPull
import Submission.Work.Diff.STE.C2.formFamJoint_pullMetBilin
import Submission.Work.Diff.STE.C2.ricAt_pullSMet
import Submission.Work.Diff.STE.C2.Kit
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: a sub-step of short_time_existence (H10 owns the rest). The contracts in Submission/Diff/*.lean are frozen.
GOAL (Layer C2, the DeTurck pull-back): a Ricci–DeTurck solution Ĝ (∂ₜĝ = −2Ric(ĝ) + L_W ĝ, with (L_W g)(u,v) = g(∇_uW, v) + g(u, ∇_vW),
∇ = lcOf ĝ(t)) on [0,τ] becomes a Ricci flow after pulling back by the flow of −W.
ROUTE:
1. hFlow (SmoothFlowIcc, PROVED as Work.Diff.ODE.flow_smooth_icc) applied to X := −W on [0,τ] gives Φ s t x, jointly smooth on
   [0,τ]² × M, with the flow identities. φ_t := Φ 0 t is a diffeomorphism of M (inverse Φ t 0).
2. G(t) := φ_t* Ĝ(t): (G t).inner x u v = (Ĝ t).inner (φ_t x) (dφ_t u) (dφ_t v). Build it as an SMet (ContMDiffRiemannianMetric):
   symmetric, positive (dφ_t invertible), smooth in x. JointSmooth G (Ico 0 τ) from joint smoothness of Φ and Ĝ.
3. NATURALITY (the geometric core; prove once as separate lemmas):
   (a) lcOf (φ* g) = φ* (lcOf g), i.e. the pulled-back connection is torsion-free and φ*g-compatible, then uniqueness
       (Mathlib IsLeviCivitaConnection.uniqueness);
   (b) hence rmVec and ricAt are natural: ricAt (lcOf (φ*g)) x u v = ricAt (lcOf g) (φ x) (dφ u) (dφ v).
4. Time derivative: d/dt (φ_t* ĝ_t) = φ_t*(∂ₜĝ_t) + φ_t*(L_{V_t} ĝ_t) with V_t = (∂ₜφ_t)∘φ_t⁻¹ = −W(t).
   This is the product rule plus the derivative of dφ_t, which is the variational equation ∂ₜ dφ_t = d(−W) ∘ dφ_t.
   So ∂ₜG = φ*(−2Ric(ĝ) + L_W ĝ − L_W ĝ) = −2 φ*Ric(ĝ) = −2 Ric(G) by 3(b).
5. G 0 = Ĝ 0 since φ_0 = id.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- Two smooth metrics with the same inner product are equal. -/
private lemma sMet_ext {g g' : SMet I M} (h : g.inner = g'.inner) : g = g' := by
  cases g with
  | mk inner symm pos hb cm =>
    cases g' with
    | mk inner' symm' pos' hb' cm' =>
      simp only [Submission.Diff.SMet] at h
      cases h
      congr 1

/-- The pull-back of `g` along `φ` is `g'` as soon as their inner products agree. -/
private lemma pullSMet_eq_of_inner {φ : Diffeomorph I I M M (⊤ : ℕ∞)} {g g' : SMet I M}
    (h : (pullSMet φ g).inner = g'.inner) : pullSMet φ g = g' := by
  refine sMet_ext ?_
  simpa only [pullSMet] using h

theorem ricci_of_deTurck
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hFlow : SmoothFlowIcc I M)
    (Ĝ : ℝ → SMet I M) (W : ℝ → Π x : M, TangentSpace I x) (τ : ℝ) (hτ : 0 < τ)
    (hĜ : JointSmooth Ĝ (Icc 0 τ))
    (hW : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (Icc 0 τ ×ˢ univ))
    (heq : ∀ t ∈ Ico 0 τ, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s ↦ (Ĝ s).inner x u v)
        (-2 * ricAt (lcOf (Ĝ t)) x u v
          + (Ĝ t).inner x (lcOf (Ĝ t) (W t) x u) v + (Ĝ t).inner x u (lcOf (Ĝ t) (W t) x v))
        (Ico 0 τ) t) :
    ∃ G : ℝ → SMet I M, IsRicciFlow G τ ∧ G 0 = Ĝ 0 := by
  classical
  have hτ0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  -- ## 1. the flow of `-W` on `[0,τ]`
  obtain ⟨Φ, hΦsm, hdiag, hcomp, hvelΦ, hslice0, hslice1, hinv0, hinv1⟩ :=
    flowData (I := I) (M := M) hFlow hτ W hW
  -- ## 2. the generating field, the metric family and its claimed derivative
  set Y : ℝ → Π x : M, TangentSpace I x := fun t x ↦ -(W t x) with hY_def
  set φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞) := flowFam Φ τ hslice0 hslice1 hinv1 hinv0 with hφ_def
  set dA : ℝ → (x : M) → TangentSpace I x → TangentSpace I x → ℝ :=
    fun t x u v ↦ -2 * ricAt (lcOf (Ĝ t)) x u v
      + (Ĝ t).inner x (lcOf (Ĝ t) (W t) x u) v + (Ĝ t).inner x u (lcOf (Ĝ t) (W t) x v)
    with hdA_def
  have hA : JointSmooth Ĝ (Ico 0 τ) :=
    hĜ.mono (Set.prod_mono Ico_subset_Icc_self (Subset.refl univ))
  have hAderiv : ∀ t ∈ Ico 0 τ, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s ↦ (Ĝ s).inner x u v) (dA t x u v) (Ico 0 τ) t := by
    intro t ht x u v
    exact heq t ht x u v
  -- ## 3. the diffeomorphism family is jointly smooth and has velocity `Y`
  have hφ_apply : ∀ {t : ℝ}, t ∈ Ico 0 τ → ∀ x : M, φ t x = Φ 0 t x := by
    intro t ht x
    rw [hφ_def]
    exact flowFam_apply Φ τ hslice0 hslice1 hinv1 hinv0 ⟨ht.1, ht.2.le⟩ x
  have hφsm : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (Ico 0 τ ×ˢ univ) := by
    rw [hφ_def]
    exact flowFam_jointSmooth Φ τ hτ hslice0 hslice1 hinv1 hinv0 hΦsm
  have hYsm : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) (Ico 0 τ ×ˢ univ) := by
    rw [hY_def]
    exact jointField_neg W (hW.mono (Set.prod_mono Ico_subset_Icc_self (Subset.refl univ)))
  have hvelφ : ∀ t ∈ Ico 0 τ, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) (Ico 0 τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x))) := by
    intro t ht x
    have h := flowFam_vel Φ W τ hτ hslice0 hslice1 hinv1 hinv0 hvelΦ ⟨ht.1, ht.2.le⟩ x
    have hfun : (fun s : ℝ ↦ φ s x) = fun s : ℝ ↦ flowFam Φ τ hslice0 hslice1 hinv1 hinv0 s x := by
      rw [hφ_def]
    have hval : (-(W t (Φ 0 t x))) = Y t (φ t x) := by
      rw [hY_def, hφ_apply ht x]
    rw [hfun, hval] at h
    exact h
  -- ## 4. the first variation of the pull-back
  have hmaster := hasDerivWithinAt_pullMetBilin_flow (I := I) (M := M)
    hLC φ Y Ĝ hτ dA hφsm hYsm hA hvelφ hAderiv
  -- ## 5. the candidate Ricci flow
  refine ⟨fun s ↦ if s ∈ Ico 0 τ then pullSMet (φ s) (Ĝ s) else Ĝ 0, ⟨?_, ?_⟩, ?_⟩
  · -- joint smoothness on `Ico 0 τ`
    have h := formFamJoint_pullMetBilin (I := I) (M := M) φ Ĝ (Ico 0 τ) hφsm hA
    rw [Work.Diff.EXT.jointSmooth_iff_formFamJoint]
    refine h.congr (fun p hp => ?_)
    refine TotalSpace.ext rfl ?_
    simp only [Work.Diff.EXT.formFamSection]
    rw [if_pos hp.1]
    exact HEq.rfl
  · -- the derivative
    intro t ht x u v
    -- the `G`-function agrees with the pulled-back pairing on `Ico 0 τ`
    have hev : (fun s : ℝ ↦ (((fun s ↦ if s ∈ Ico 0 τ then pullSMet (φ s) (Ĝ s) else Ĝ 0) s).inner x u v))
        =ᶠ[𝓝[Ico 0 τ] t] (fun s : ℝ ↦ pullMetBilin (φ s) (Ĝ s) x u v) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [if_pos hs]
      rfl
    have hxt : (((fun s ↦ if s ∈ Ico 0 τ then pullSMet (φ s) (Ĝ s) else Ĝ 0) t).inner x u v)
        = pullMetBilin (φ t) (Ĝ t) x u v := by
      simp only [if_pos ht]
      rfl
    have h := (hmaster t ht x u v).congr_of_eventuallyEq hev hxt
    refine h.congr_deriv ?_
    -- the value: replace `Y t` by `-W t` in the two `lcOf`-terms
    have hsmW : ∀ y : M, MDiffAt (T% (W t)) y := by
      intro y
      have hmem : (t, y) ∈ Icc 0 τ ×ˢ univ := ⟨⟨ht.1, ht.2.le⟩, mem_univ y⟩
      have hWc : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
          (fun p : ℝ × M ↦ (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (Icc 0 τ ×ˢ univ) (t, y) :=
        hW (t, y) hmem
      have hslice : ContMDiffAt I I.tangent (⊤ : ℕ∞)
          (fun z : M ↦ (⟨z, W t z⟩ : TangentBundle I M)) y :=
        (hWc.comp y ((contMDiffAt_const (c := t)).prodMk contMDiffAt_id)
          (fun z _ => ⟨hmem.1, mem_univ z⟩)).contMDiffAt (by simp)
      exact hslice.mdifferentiableAt (by simp)
    have hcovY : (lcOf (Ĝ t)) (Y t) (φ t x) = - ((lcOf (Ĝ t)) (W t) (φ t x)) := by
      have h1 : Y t = (-1 : ℝ) • (W t) := by
        rw [hY_def]
        funext z
        simp [neg_one_smul]
      rw [h1, ((lcOf (Ĝ t)).isCovariantDerivativeOn).smul_const (-1) (hsmW (φ t x))]
      simp
    have hterm : (Ĝ t).inner (φ t x) ((lcOf (Ĝ t)) (Y t) (φ t x) (mfderiv I I (φ t) x u))
          (mfderiv I I (φ t) x v)
        = - ((Ĝ t).inner (φ t x) ((lcOf (Ĝ t)) (W t) (φ t x) (mfderiv I I (φ t) x u))
              (mfderiv I I (φ t) x v))
        := by
      simp only [hcovY, neg_apply, map_neg]
    have hterm2 : (Ĝ t).inner (φ t x) (mfderiv I I (φ t) x u)
          ((lcOf (Ĝ t)) (Y t) (φ t x) (mfderiv I I (φ t) x v))
        = - ((Ĝ t).inner (φ t x) (mfderiv I I (φ t) x u)
              ((lcOf (Ĝ t)) (W t) (φ t x) (mfderiv I I (φ t) x v)))
        := by
      simp only [hcovY, neg_apply, map_neg]
    simp only [hdA_def]
    rw [hterm, hterm2]
    rw [← ricAt_pullSMet (I := I) (M := M) (φ t) (Ĝ t) x u v]
    ring_nf
    rw [if_pos ht]
  · -- `G 0 = Ĝ 0`
    have h0 : (0 : ℝ) ∈ Ico 0 τ := ⟨le_rfl, hτ⟩
    have hcoe : ((φ 0 : Diffeomorph I I M M (⊤ : ℕ∞)) : M → M) = id := by
      rw [hφ_def]
      funext x
      rw [flowFam_apply Φ τ hslice0 hslice1 hinv1 hinv0 ⟨le_rfl, hτ.le⟩ x]
      exact hdiag 0 ⟨le_rfl, hτ.le⟩ x
    show (if (0 : ℝ) ∈ Ico 0 τ then pullSMet (φ 0) (Ĝ 0) else Ĝ 0) = Ĝ 0
    rw [if_pos h0]
    exact pullSMet_eq_of_inner (I := I) (M := M) (φ := φ 0) (g := Ĝ 0) (g' := Ĝ 0) (by
      funext x
      ext u v
      rw [pullSMet_inner, pullMetBilin_apply, hcoe, mfderiv_id]
      rfl)

end Work.Diff.STE.C2
