import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.flow_shift
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rdist_continuous

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A continuous linear map into a product, followed by the zero map in the second factor. -/
private lemma prod_zero_apply {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] F) (e : E) :
    (A.prod (0 : E →L[ℝ] G)) e = (A e, 0) := by
  rw [ContinuousLinearMap.prod_apply, zero_apply]

set_option linter.unusedVariables false in
theorem label_u_rank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {a γ v ρ : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hρ0 : 0 < ρ)
    (haρ : a < ρ) (hρv : ρ ≤ v)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hsmP : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y)
    {Φp : M → TangentSpace I p}
    (hsmΦp : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I p)) ∞ Φp y)
    (hnormP : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖)
    (hinvP : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Submission.GlobalExp.GExp (cov := cov) hmet p (Φp y) = y)
    (hroundP : ∀ w : TangentSpace I p, ‖w‖ < ρ →
      Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w) = w)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    {τ : M → ℝ}
    (hτsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ
      {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x})
    (hτV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1)
    (hτa : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ x)) x) = a)
    {u : M → TangentSpace I p}
    (hu : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ u x)
    (huf : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      u x = a⁻¹ • Φp (Φ 0 (-(τ x)) x)) :
    ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ, TangentSpace I p) u x ≠ 0 := by
  intro x hx1 hx2 hcon
  -- ## The region is a neighbourhood of `x`.
  have hS : {y : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p y ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q y} ∈ 𝓝 x := by
    have h1 : {y : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p y} ∈ 𝓝 x :=
      ((Work.Diff.C.rdist_continuous (I := I) (M := M) p).isOpen_preimage _
        isOpen_Ioi).mem_nhds hx1
    have h2 : {y : M | γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q y} ∈ 𝓝 x :=
      ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _
        isOpen_Ioi).mem_nhds hx2
    exact Filter.inter_mem h1 h2
  -- ## A nonzero tangent vector killed by `dτ` (`dτ x` is nonzero and `dim ≥ 2`).
  obtain ⟨w, hwker, hwne⟩ : ∃ w : TangentSpace I x,
      mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 ∧ w ≠ 0 := by
    have hker : LinearMap.ker ((mfderiv I 𝓘(ℝ,ℝ) τ x).toLinearMap) ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank ℝ
          ↥(LinearMap.ker ((mfderiv I 𝓘(ℝ,ℝ) τ x).toLinearMap)) = 0 :=
        Submodule.finrank_eq_zero.mpr hbot
      have hsum := LinearMap.finrank_range_add_finrank_ker
        ((mfderiv I 𝓘(ℝ,ℝ) τ x).toLinearMap)
      have hle : Module.finrank ℝ
          ↥(LinearMap.range ((mfderiv I 𝓘(ℝ,ℝ) τ x).toLinearMap)) ≤ 1 :=
        le_trans (Submodule.finrank_le _) (le_of_eq (Module.finrank_self ℝ))
      have hd : 2 ≤ Module.finrank ℝ (TangentSpace I x) := hdim
      omega
    obtain ⟨w, hwmem, hwne⟩ := (Submodule.ne_bot_iff _).mp hker
    exact ⟨w, hwmem, hwne⟩
  -- ## Smoothness of the pair map `Γ = (τ, u)` and of the return map `Λ` at `Γ x`.
  have hτmd : MDifferentiableAt I 𝓘(ℝ,ℝ) τ x :=
    (hτsm.contMDiffAt hS).mdifferentiableAt (by simp)
  have humd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I p) u x :=
    (hu x hx1 hx2).mdifferentiableAt (by simp)
  have hΓmd : MDifferentiableAt I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
      (fun z : M => (τ z, u z)) x :=
    ((hτsm.contMDiffAt hS).prodMk (hu x hx1 hx2)).mdifferentiableAt (by simp)
  have hΛmd : MDifferentiableAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I
      (fun z : ℝ × TangentSpace I p =>
        Φ 0 z.1 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2)))
      (τ x, u x) := by
    have hsmw : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
        𝓘(ℝ, TangentSpace I p) ∞ (fun z : ℝ × TangentSpace I p => a • z.2)
        (τ x, u x) :=
      ((ContinuousLinearMap.contMDiff
        ((a : ℝ) • ContinuousLinearMap.id ℝ (TangentSpace I p))).contMDiffAt).comp
        (τ x, u x) contMDiffAt_snd
    have hGsmE : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun y : E => Submission.GlobalExp.GExp (cov := cov) hmet p
          (show TangentSpace I p from y)) (show E from (a • u x)) :=
      Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p (a • u x)
    have hcastc : ContMDiffAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, E) ∞
        (fun y : TangentSpace I p => (show E from tangentSpaceCastModel I p y))
        (a • u x) :=
      (ContinuousLinearMap.contMDiff
        ((tangentSpaceCastModel I p) : TangentSpace I p →L[ℝ] E)).contMDiffAt
    have hGsm : ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞
        (fun y : TangentSpace I p =>
          Submission.GlobalExp.GExp (cov := cov) hmet p y) (a • u x) :=
      (hGsmE.comp (a • u x) hcastc).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => rfl))
    have hG : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I ∞
        (fun z : ℝ × TangentSpace I p =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2)) (τ x, u x) :=
      hGsm.comp (τ x, u x) hsmw
    have hpair : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
        ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun z : ℝ × TangentSpace I p => (((0 : ℝ), z.1),
          Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2))) (τ x, u x) :=
      ((contMDiffAt_const (c := (0 : ℝ))).prodMk contMDiffAt_fst).prodMk hG
    have hcomp : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I ∞
        ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∘
          (fun z : ℝ × TangentSpace I p => (((0 : ℝ), z.1),
            Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2))))
        (τ x, u x) :=
      hΦsm.contMDiffAt.comp (τ x, u x) hpair
    exact hcomp.mdifferentiableAt (by simp)
  -- ## `Λ ∘ Γ = id` on a neighbourhood of `x`.
  have hev : (fun z : M => Φ 0 (τ z)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z))) =ᶠ[𝓝 x] id := by
    filter_upwards [hS] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    have huz := huf z hz1 hz2
    have hrd := hτa z hz1 hz2
    have hrdv : Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ z)) z) < v := by
      rw [hrd]
      exact lt_of_lt_of_le haρ hρv
    have hmul : a • u z = Φp (Φ 0 (-(τ z)) z) := by
      rw [huz, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    show Φ 0 (τ z) (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z)) = z
    rw [hmul, hinvP _ hrdv]
    rw [Work.Diff.Dim2.flow_shift (I := I) (Φ := Φ) (V := V) hVsm hΦsm hΦself hΦderiv
      (-(τ z)) (τ z) z]
    rw [neg_add_cancel, hΦself 0 z]
  -- ## Chain rule: `mfderiv Λ (Γ x) ∘ mfderiv Γ x` is the canonical identification.
  have hmfΓ : mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) (fun z : M => (τ z, u z)) x
      = (mfderiv I 𝓘(ℝ,ℝ) τ x).prod (mfderiv I 𝓘(ℝ, TangentSpace I p) u x) :=
    mfderiv_prodMk hτmd humd
  have hcastmf : mfderiv I I (fun z : M => Φ 0 (τ z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z))) x
      = ↑(tangentSpaceCast I x ((fun z : M => Φ 0 (τ z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z))) x)) := by
    have h := hev.mfderiv_eq (I := I) (I' := I)
    rw [mfderiv_id, ContinuousLinearMap.comp_id] at h
    exact h
  have hmfc : mfderiv I I (fun z : M => Φ 0 (τ z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z))) x
      = (mfderiv (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I
          (fun z : ℝ × TangentSpace I p =>
            Φ 0 z.1 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2)))
          (τ x, u x)).comp
        (mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) (fun z : M => (τ z, u z)) x) :=
    mfderiv_comp x hΛmd hΓmd
  have hcomp : (mfderiv (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I
        (fun z : ℝ × TangentSpace I p =>
          Φ 0 z.1 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2)))
        (τ x, u x)).comp
      (mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) (fun z : M => (τ z, u z)) x)
      = ↑(tangentSpaceCast I x ((fun z : M => Φ 0 (τ z)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u z))) x)) := by
    rw [← hmfc]
    exact hcastmf
  have hact : ∀ y : TangentSpace I x,
      (mfderiv (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p)) I
        (fun z : ℝ × TangentSpace I p =>
          Φ 0 z.1 (Submission.GlobalExp.GExp (cov := cov) hmet p (a • z.2))) (τ x, u x))
      ((mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
        (fun z : M => (τ z, u z)) x) y) = y := by
    intro y
    have h := congrArg (fun L => L y) hcomp
    rw [ContinuousLinearMap.comp_apply] at h
    exact h
  -- ## Evaluate at the kernel vector `w`.
  have hΓw : (mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
      (fun z : M => (τ z, u z)) x) w = 0 := by
    have h2 : (mfderiv I (𝓘(ℝ,ℝ).prod 𝓘(ℝ, TangentSpace I p))
        (fun z : M => (τ z, u z)) x) w
        = (((mfderiv I 𝓘(ℝ,ℝ) τ x) w : ℝ), (0 : TangentSpace I p)) := by
      rw [hmfΓ, hcon]
      exact prod_zero_apply (mfderiv I 𝓘(ℝ,ℝ) τ x) w
    rw [h2, hwker]
    rfl
  have hw0 : w = 0 := by
    have h := hact w
    rw [hΓw] at h
    simpa using h.symm
  exact hwne hw0

end Work.Diff.Dim2
