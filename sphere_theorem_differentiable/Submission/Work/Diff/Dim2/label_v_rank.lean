import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rdist_continuous
import Submission.HopfRinow2
import Submission.GExpSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option maxHeartbeats 1000000

/-- **The global exponential map is `C^∞` in the tangent-space flavour.**  `Submission.GExpSmooth`
states the smoothness of the model-space version `u ↦ GExp q u` (`u : E`); the tangent space
`TangentSpace I q` is a non-reducible type synonym of `E` carrying the fibre norm, and the
identification is the continuous linear equivalence `tangentSpaceCastModel I q`. -/
lemma contMDiffAt_GExp_tangent_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (q : M) (w : TangentSpace I q) :
    ContMDiffAt (modelWithCornersSelf ℝ (TangentSpace I q)) I ∞
      (fun u : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q u) w := by
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) I ∞
      (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from u))
      (show E from w) :=
    Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q w
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ (TangentSpace I q)) (modelWithCornersSelf ℝ E) ∞
      (fun u : TangentSpace I q => (show E from u)) w :=
    (ContinuousLinearMap.contMDiff
      (tangentSpaceCastModel I q : TangentSpace I q →L[ℝ] E)).contMDiffAt
  exact h1.comp w h2

/-- **Hopf--Rinow plus the roundness of `Φq`: `GExp q` is a right inverse of `Φq` on the ball.**
If `Φq` inverts `GExp q` on the ball of radius `v` (in the fibre norm), then `Φq` is a two-sided
inverse of `GExp q` on the ball `{rdist q · < v}`: the missing direction is supplied by Hopf--Rinow,
which produces a *minimising* vector `w` with `GExp q w = y` and `‖w‖ = rdist q y < v`. -/
lemma GExp_comp_phiq_eq_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {v : ℝ} {Φq : M → TangentSpace I q}
    (hroundQ : ∀ w : TangentSpace I q, ‖w‖ < v →
      Φq (Submission.GlobalExp.GExp (cov := cov) hmet q w) = w) :
    ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      Submission.GlobalExp.GExp (cov := cov) hmet q (Φq y) = y := by
  intro y hy
  obtain ⟨w, hwG, hwd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q y
  have hw : ‖w‖ = Work.Diff.C.rdist (I := I) (M := M) q y := by
    rw [Work.Diff.C.rdist, hwd, ENNReal.toReal_ofReal (norm_nonneg w)]
  have hwv : ‖w‖ < v := by rw [hw]; exact hy
  have hΦ : Φq y = w := by rw [← hwG, hroundQ w hwv]
  rw [hΦ]
  exact hwG

theorem label_v_rank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {a γ c v : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hc : 0 < c)
    (hcv : c < v) (hc2 : γ / 4 < c)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {Φq : M → TangentSpace I q}
    (hsmΦq : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y)
    (hnormQ : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖)
    (hroundQ : ∀ w : TangentSpace I q, ‖w‖ < v →
      Φq (Submission.GlobalExp.GExp (cov := cov) hmet q w) = w)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {y : M → M}
    (hysm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I I ∞ y x)
    (hyg : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q (y x) = c)
    (hyV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I I y x (V x) = 0)
    (hyd : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I I y x ≠ 0)
    {vE : M → TangentSpace I q}
    (hvsm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞ vE x)
    (hvform : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      vE x = - c⁻¹ • Φq (y x)) :
    ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ, TangentSpace I q) vE x ≠ 0 := by
  intro x hpx hqx
  -- ## Step 0: `GExp q` is a right inverse of `Φq` on the ball `{rdist q · < v}`.
  have hright : ∀ y' : M, Work.Diff.C.rdist (I := I) (M := M) q y' < v →
      Submission.GlobalExp.GExp (cov := cov) hmet q (Φq y') = y' :=
    GExp_comp_phiq_eq_self (I := I) (cov := cov) hmet htor hroundQ
  -- ## Step 1: `y x` lies in that ball.
  have hzv : Work.Diff.C.rdist (I := I) (M := M) q (y x) < v := by
    rw [hyg x hpx hqx]; exact hcv
  -- ## Step 2: smoothness of the two factors.
  -- `GExp q` is smooth (in the tangent-space flavour) at `Φq (y x)`.
  have hGsm : ContMDiffAt (modelWithCornersSelf ℝ (TangentSpace I q)) I ∞
      (fun w : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q w)
      (Φq (y x)) :=
    contMDiffAt_GExp_tangent_space (I := I) (cov := cov) hmet q (Φq (y x))
  have hGmd : MDifferentiableAt (modelWithCornersSelf ℝ (TangentSpace I q)) I
      (fun w : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q w)
      (Φq (y x)) :=
    hGsm.mdifferentiableAt (by simp)
  have hysmd : MDifferentiableAt I I y x :=
    (hysm x hpx hqx).mdifferentiableAt (by simp)
  have hΦymd : MDifferentiableAt I (modelWithCornersSelf ℝ (TangentSpace I q))
      (fun z' : M => Φq (y z')) x :=
    ((hsmΦq (y x) hzv).comp x (hysm x hpx hqx)).mdifferentiableAt (by simp)
  -- ## Step 3: the composite `GExp q ∘ Φq ∘ y` agrees with `y` near `x`, hence has the same
  -- derivative.
  have hev : (fun z' : M => Submission.GlobalExp.GExp (cov := cov) hmet q (Φq (y z')))
      =ᶠ[𝓝 x] y := by
    have h1 : ∀ᶠ z' in 𝓝 x, Work.Diff.C.rdist (I := I) (M := M) q (y z') < v :=
      ((hysm x hpx hqx).continuousAt).eventually
        (((Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _
          isOpen_Iio).mem_nhds hzv)
    filter_upwards [h1] with z' hz'
    exact hright (y z') hz'
  have hchainB : mfderiv I I
      (fun z' : M => Submission.GlobalExp.GExp (cov := cov) hmet q (Φq (y z'))) x
      = mfderiv I I y x :=
    (hysmd.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  have hchainA : mfderiv I I
      (fun z' : M => Submission.GlobalExp.GExp (cov := cov) hmet q (Φq (y z'))) x
      = (mfderiv (modelWithCornersSelf ℝ (TangentSpace I q)) I
            (fun w : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q w)
            (Φq (y x)))
        ∘SL (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
            (fun z' : M => Φq (y z')) x) :=
    mfderiv_comp x hGmd hΦymd
  -- ## Step 4: `mfderiv (Φq ∘ y) x ≠ 0`.
  have hFne : mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
      (fun z' : M => Φq (y z')) x ≠ 0 := by
    intro h0
    apply hyd x hpx hqx
    have key : (mfderiv (modelWithCornersSelf ℝ (TangentSpace I q)) I
          (fun w : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet q w)
          (Φq (y x)))
        ∘SL (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
            (fun z' : M => Φq (y z')) x) = mfderiv I I y x :=
      hchainA.symm.trans hchainB
    rw [h0, ContinuousLinearMap.comp_zero] at key
    exact key.symm
  -- ## Step 5: the labelling field `vE` agrees near `x` with `-c⁻¹ • (Φq ∘ y)`.
  have hreg : {z' : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z' ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z'} ∈ 𝓝 x := by
    have h1 : {z' : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z'} ∈ 𝓝 x :=
      ((Work.Diff.C.rdist_continuous (I := I) (M := M) p).isOpen_preimage _
        isOpen_Ioi).mem_nhds hpx
    have h2 : {z' : M | γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z'} ∈ 𝓝 x :=
      ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _
        isOpen_Ioi).mem_nhds hqx
    exact Filter.inter_mem h1 h2
  have hev2 : vE =ᶠ[𝓝 x] (fun z' : M => (-c⁻¹) • Φq (y z')) := by
    filter_upwards [hreg] with z' hz'
    exact hvform z' hz'.1 hz'.2
  have hvE : mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) vE x
      = (-c⁻¹) • mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
          (fun z' : M => Φq (y z')) x := by
    have h1 : HasMFDerivAt I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z' : M => (-c⁻¹) • Φq (y z')) x
        ((-c⁻¹) • mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
          (fun z' : M => Φq (y z')) x) :=
      hΦymd.hasMFDerivAt.const_smul (-c⁻¹)
    exact (h1.congr_of_eventuallyEq_abuse hev2).mfderiv
  -- ## Step 6: a non-zero scalar multiple of a non-zero map is non-zero.
  intro hzero
  have hcne : (-c⁻¹ : ℝ) ≠ 0 := by
    simp [inv_ne_zero (ne_of_gt hc)]
  have h1 : ((-c⁻¹) • mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
      (fun z' : M => Φq (y z')) x) = 0 := by
    rw [← hvE]; exact hzero
  rcases smul_eq_zero.mp h1 with h | h
  · exact hcne h
  · exact hFne h

end Work.Diff.Dim2
