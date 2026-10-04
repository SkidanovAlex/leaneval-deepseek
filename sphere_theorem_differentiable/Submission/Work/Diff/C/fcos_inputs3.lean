import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.rgrad_fcos
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.C.cosSqrt_props
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.rhess_comp_aux
import Submission.Work.Diff.C.dist_lt_pi
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.sqDist_hess_C
import Submission.Work.Diff.C.fcos_hess_pt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [SimplyConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## Elementary distance facts -/

lemma edist_lt_top_h (hdim : 2 ≤ Module.finrank ℝ E)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch4 : Pinched cov 1 4)
    (p x : M) : Manifold.riemannianEDist I p x ≠ ⊤ :=
  ne_top_of_lt (Submission.GlobalBM.riemannianEDist_lt_pi (cov := cov) hmet htor hpinch4 hdim p x)

lemma rdist_nonneg_h (p x : M) : 0 ≤ rdist (I := I) p x := by
  rw [rdist]; exact ENNReal.toReal_nonneg

lemma rdist_pos_of_ne_h (hdim : 2 ≤ Module.finrank ℝ E)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch4 : Pinched cov 1 4)
    {p x : M} (h : p ≠ x) : 0 < rdist (I := I) p x := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  haveI : RegularSpace M := inferInstance
  rw [rdist]
  exact ENNReal.toReal_pos (ne_of_gt (Submission.EDist.riemannianEDist_pos (I := I) h))
    (edist_lt_top_h hdim hmet htor hpinch4 p x)

lemma rdist_lt_arccos_h {c : ℝ} (hc : 0 < c) {q x : M}
    (hpi : rdist (I := I) q x < Real.pi)
    (hx : -1 + c < Real.cos (rdist (I := I) q x)) :
    rdist (I := I) q x < Real.arccos (-1 + c) := by
  have hd0 : 0 ≤ rdist (I := I) q x := rdist_nonneg_h q x
  by_cases hc2 : c < 2
  · have hlt1 : -1 + c < 1 := by linarith
    have hcosA : Real.cos (Real.arccos (-1 + c)) = -1 + c :=
      Real.cos_arccos (by linarith) hlt1.le
    have hA0 : 0 ≤ Real.arccos (-1 + c) := Real.arccos_nonneg _
    have hApi : Real.arccos (-1 + c) ≤ Real.pi := Real.arccos_le_pi _
    exact (Real.strictAntiOn_cos.lt_iff_gt (Set.mem_Icc.mpr ⟨hA0, hApi⟩)
      (Set.mem_Icc.mpr ⟨hd0, hpi.le⟩)).mp (by rw [hcosA]; exact hx)
  · push_neg at hc2
    exfalso
    have h1 : Real.cos (rdist (I := I) q x) ≤ 1 := Real.cos_le_one _
    linarith

lemma rdist_lt_pi_div_h {c η : ℝ} (hc : 0 < c)
    (harc : Real.arccos (-1 + c) < Real.pi / Real.sqrt (1 + η)) {q x : M}
    (hpi : rdist (I := I) q x < Real.pi)
    (hx : -1 + c < Real.cos (rdist (I := I) q x)) :
    rdist (I := I) q x < Real.pi / Real.sqrt (1 + η) :=
  lt_trans (rdist_lt_arccos_h hc hpi hx) harc

lemma rdist_lt_pi_div_weak {c η : ℝ} (hc : 0 < c)
    (harc : Real.arccos (-1 + c) < Real.pi / Real.sqrt (1 + η)) {q x : M}
    (hpi : rdist (I := I) q x < Real.pi)
    (hx : -1 + c ≤ Real.cos (rdist (I := I) q x)) :
    rdist (I := I) q x < Real.pi / Real.sqrt (1 + η) := by
  have hd0 : 0 ≤ rdist (I := I) q x := rdist_nonneg_h q x
  by_cases hc2 : c ≤ 2
  · have hcosA : Real.cos (Real.arccos (-1 + c)) = -1 + c :=
      Real.cos_arccos (by linarith) (by linarith)
    have hA0 : 0 ≤ Real.arccos (-1 + c) := Real.arccos_nonneg _
    have hApi : Real.arccos (-1 + c) ≤ Real.pi := Real.arccos_le_pi _
    have hle : rdist (I := I) q x ≤ Real.arccos (-1 + c) :=
      (Real.strictAntiOn_cos.le_iff_ge (Set.mem_Icc.mpr ⟨hA0, hApi⟩)
        (Set.mem_Icc.mpr ⟨hd0, hpi.le⟩)).mp (by rw [hcosA]; exact hx)
    exact lt_of_le_of_lt hle harc
  · push_neg at hc2
    exfalso
    have h1 : Real.cos (rdist (I := I) q x) ≤ 1 := Real.cos_le_one _
    linarith

/-! ## The centre of `fcos` -/

theorem fcos_centre_h (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (q : M) :
    CMDiffAt ∞ (fcos (I := I) (M := M) q) q ∧
      fcos (I := I) (M := M) q q = 1 ∧
      rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) q = 0 ∧
      (∀ V W : TangentSpace I q,
        rhess cov (fcos (I := I) (M := M) q) q V W = - Inner.inner ℝ V W) := by
  obtain ⟨hFsm, hFgrad, hFhess⟩ := sqDist_hess_C (I := I) (M := M) (cov := cov) hmet htor q
  obtain ⟨hcos_sm, hcos_0, hcos_deriv, hcos_sq⟩ := cosSqrt_props
  have hglob : fcos (I := I) (M := M) q
      = fun y : M => cosSqrt ((rdist (I := I) (M := M) q y) ^ 2) := by
    funext y
    show Real.cos (rdist (I := I) (M := M) q y) = cosSqrt ((rdist (I := I) (M := M) q y) ^ 2)
    exact (hcos_sq _).symm
  have hFq : (rdist (I := I) (M := M) q q) ^ 2 = 0 := by
    have h0 : rdist (I := I) (M := M) q q = 0 := by
      rw [rdist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    rw [h0]; ring
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (rdist (I := I) (M := M) q y) ^ 2) q := hFsm.mdifferentiableAt (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hglob]
    exact (contMDiffAt_iff_contDiffAt.mpr hcos_sm.contDiffAt).comp q hFsm
  · show Real.cos (rdist (I := I) (M := M) q q) = 1
    have h0 : rdist (I := I) (M := M) q q = 0 := by
      rw [rdist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    rw [h0, Real.cos_zero]
  · rw [hglob]
    have hcd : HasDerivAt cosSqrt (deriv cosSqrt ((rdist (I := I) (M := M) q q) ^ 2))
        ((rdist (I := I) (M := M) q q) ^ 2) :=
      (hcos_sm.contDiffAt.differentiableAt (by simp)).hasDerivAt
    rw [rgrad_comp_hasDerivAt hFmd hcd, hFgrad, smul_zero]
  · intro V W
    rw [hglob, rhess_comp cosSqrt (fun y : M => (rdist (I := I) (M := M) q y) ^ 2) q V W
      hcos_sm.contDiffAt hFsm]
    have hdFV : mvfderiv I (fun y : M => (rdist (I := I) (M := M) q y) ^ 2) q V = 0 := by
      rw [← inner_rgrad_mvfderiv]
      rw [hFgrad]; simp
    have hdFW : mvfderiv I (fun y : M => (rdist (I := I) (M := M) q y) ^ 2) q W = 0 := by
      rw [← inner_rgrad_mvfderiv]
      rw [hFgrad]; simp
    have hderiv : deriv cosSqrt ((rdist (I := I) (M := M) q q) ^ 2) = -(1 / 2) := by
      rw [hFq]; exact hcos_deriv.deriv
    rw [hdFV, hdFW, hFhess V W, hderiv]
    ring

end Helpers

section Main

theorem fcos_inputs3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [SimplyConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η c ε₁ : ℝ} (hη : 0 < η) (hη3 : η < 3) (hc : 0 < c) (hε₁ : 0 ≤ ε₁)
    (hInj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet
      (Real.pi / Real.sqrt (1 + η)))
    (hEik : EikonalInput (I := I) (M := M) cov η)
    (hUpper : HessUpperInput (I := I) (M := M) cov)
    (hLower : HessLowerInput (I := I) (M := M) cov η)
    (hpinch : Pinched cov 1 (1 + η)) (hpinch4 : Pinched cov 1 4)
    (harc : Real.arccos (-1 + c) < Real.pi / Real.sqrt (1 + η))
    (hkey : ∀ d : ℝ, 0 < d → d ≤ Real.arccos (-1 + c) →
      max (Real.cos d - Real.sin d * Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η) * d)) 0
        ≤ ε₁) :
    (∀ q : M, SmoothOnRegion (I := I) (M := M) c (fcos (I := I) (M := M) q)) ∧
    (∀ (q x : M), -1 + c ≤ fcos (I := I) (M := M) q x →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) x) ∧
    (∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q)) ∧
    (∀ q : M, Continuous (fcos (I := I) (M := M) q)) ∧
    (∀ (q x : M), -1 + c < fcos (I := I) (M := M) q x →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        = 1 - (fcos (I := I) (M := M) q x) ^ 2) := by
  classical
  haveI : RegularSpace M := inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q x hx
    obtain ⟨hsm_c, hval_c, hgrad_c, hhess_c⟩ :=
      fcos_centre_h (I := I) (M := M) (cov := cov) hmet htor q
    by_cases hxq : x = q
    · subst hxq; exact hsm_c
    · have hpi : rdist (I := I) (M := M) q x < Real.pi :=
        dist_lt_pi (I := I) (M := M) hdim cov hmet htor hpinch4 q x
      have hrpos : 0 < rdist (I := I) (M := M) q x :=
        rdist_pos_of_ne_h hdim hmet htor hpinch4 (Ne.symm hxq)
      have hrρ : rdist (I := I) (M := M) q x < Real.pi / Real.sqrt (1 + η) :=
        rdist_lt_pi_div_h hc harc hpi hx
      obtain ⟨hrsm, -⟩ := hEik q x hrpos hrρ
      exact (contMDiffAt_iff_contDiffAt.mpr Real.contDiff_cos.contDiffAt).comp x hrsm
  · intro q x hx
    obtain ⟨hsm_c, hval_c, hgrad_c, hhess_c⟩ :=
      fcos_centre_h (I := I) (M := M) (cov := cov) hmet htor q
    by_cases hxq : x = q
    · subst hxq; exact hsm_c
    · have hpi : rdist (I := I) (M := M) q x < Real.pi :=
        dist_lt_pi (I := I) (M := M) hdim cov hmet htor hpinch4 q x
      have hrpos : 0 < rdist (I := I) (M := M) q x :=
        rdist_pos_of_ne_h hdim hmet htor hpinch4 (Ne.symm hxq)
      have hrρ : rdist (I := I) (M := M) q x < Real.pi / Real.sqrt (1 + η) :=
        rdist_lt_pi_div_weak hc harc hpi hx
      obtain ⟨hrsm, -⟩ := hEik q x hrpos hrρ
      exact (contMDiffAt_iff_contDiffAt.mpr Real.contDiff_cos.contDiffAt).comp x hrsm
  · intro q x V W hx
    obtain ⟨hsm_c, hval_c, hgrad_c, hhess_c⟩ :=
      fcos_centre_h (I := I) (M := M) (cov := cov) hmet htor q
    by_cases hxq : x = q
    · subst hxq
      rw [hhess_c V W, hval_c,
        show -(Inner.inner ℝ V W) + 1 * Inner.inner ℝ V W = 0 by ring, abs_zero]
      exact mul_nonneg (mul_nonneg hε₁ (norm_nonneg V)) (norm_nonneg W)
    · have hpi : rdist (I := I) (M := M) q x < Real.pi :=
        dist_lt_pi (I := I) (M := M) hdim cov hmet htor hpinch4 q x
      have hrpos : 0 < rdist (I := I) (M := M) q x :=
        rdist_pos_of_ne_h hdim hmet htor hpinch4 (Ne.symm hxq)
      have hrarc : rdist (I := I) (M := M) q x < Real.arccos (-1 + c) :=
        rdist_lt_arccos_h hc hpi hx
      have hrρ : rdist (I := I) (M := M) q x < Real.pi / Real.sqrt (1 + η) :=
        lt_trans hrarc harc
      have hsqrtpos : 0 < Real.sqrt (1 + η) := Real.sqrt_pos.mpr (by linarith)
      have hsqrtd : Real.sqrt (1 + η) * rdist (I := I) (M := M) q x < Real.pi := by
        have h := (lt_div_iff₀ hsqrtpos).mp hrρ
        rw [mul_comm] at h; exact h
      obtain ⟨hrsm, hunit⟩ := hEik q x hrpos hrρ
      exact fcos_hess_pt hmet htor (by linarith) hc hε₁ hrpos hrarc hsqrtd hrsm hunit
        hUpper hLower (hkey (rdist (I := I) (M := M) q x) hrpos hrarc.le) V W
  · intro q
    change Continuous (fun y : M => Real.cos (rdist (I := I) (M := M) q y))
    exact Real.continuous_cos.comp (rdist_continuous (I := I) (M := M) q)
  · intro q x hx
    obtain ⟨hsm_c, hval_c, hgrad_c, hhess_c⟩ :=
      fcos_centre_h (I := I) (M := M) (cov := cov) hmet htor q
    by_cases hxq : x = q
    · subst hxq
      rw [hgrad_c]
      simp [hval_c]
    · have hpi : rdist (I := I) (M := M) q x < Real.pi :=
        dist_lt_pi (I := I) (M := M) hdim cov hmet htor hpinch4 q x
      have hrpos : 0 < rdist (I := I) (M := M) q x :=
        rdist_pos_of_ne_h hdim hmet htor hpinch4 (Ne.symm hxq)
      have hrarc : rdist (I := I) (M := M) q x < Real.arccos (-1 + c) :=
        rdist_lt_arccos_h hc hpi hx
      have hrρ : rdist (I := I) (M := M) q x < Real.pi / Real.sqrt (1 + η) :=
        lt_trans hrarc harc
      obtain ⟨hrsm, hunit⟩ := hEik q x hrpos hrρ
      have hgr := rgrad_fcos (I := I) (M := M) hrsm
      rw [hgr, real_inner_smul_left, real_inner_smul_right, hunit, mul_one]
      show -Real.sin (rdist (I := I) (M := M) q x) * -Real.sin (rdist (I := I) (M := M) q x)
        = 1 - Real.cos (rdist (I := I) (M := M) q x) ^ 2
      nlinarith [Real.sin_sq_add_cos_sq (rdist (I := I) (M := M) q x)]

end Main

end Work.Diff.C
