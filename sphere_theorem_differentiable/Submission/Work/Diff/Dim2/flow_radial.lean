import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rgrad_rdist_eikonal

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! ## A bridge between the `curveVelocity` and the `IsMIntegralCurve` formulations

The seeded library states its ODE facts with `curveVelocity` (`= mfderiv γ t 1`), while Mathlib's
uniqueness theorem for integral curves is stated for `IsMIntegralCurveOn`.  The two match exactly
once the derivative is known to exist (a continuous linear map `ℝ →L T` is determined by its value
at `1`), which is what this lemma records. -/

lemma isMIntegralCurveOn_of_curveVelocity_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ}
    (hsm : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ,ℝ) I γ t)
    (hvel : ∀ t ∈ s, curveVelocity (I := I) γ t = v (γ t)) :
    IsMIntegralCurveOn γ v s := by
  intro t ht
  have h := (hsm t ht).hasMFDerivAt
  have hvel' : (mfderiv 𝓘(ℝ,ℝ) I γ t) (1 : ℝ) = v (γ t) := hvel t ht
  have hmf : mfderiv 𝓘(ℝ,ℝ) I γ t = (1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)) := by
    refine ContinuousLinearMap.ext_ring ?_
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply, one_smul]
    exact hvel'
  rw [hmf] at h
  exact h.hasMFDerivWithinAt

/-- **The flow of the radial field moves a point of the annulus along the geodesic ray through it.**

Let `Φp` be the exponential-coordinate projection at `p` (inverse to `GExp p` on the ball of radius
`ρ`), `V` a field equal to `∇d(p,·)` on the annulus `a/4 ≤ d(p,·) ≤ 3a/2`, and `Φ` the global flow
of `V`.  Then, for every `x` with `a/4 < d(p,x) ≤ 3a/4`, the flow line of `x` is the geodesic ray
from `p` through `x`: running it forward for time `a - d(p,x)` (i.e. applying `Φ 0` at the negative
time `-(d(p,x) - a)`) reaches the point of the ray at distance `a` from `p`, and that point has
`Φp`-coordinate `(a/d(p,x)) • Φp x`. -/
theorem flow_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {Φp : M → TangentSpace I p} {v ρ a : ℝ}
    (ha : 0 < a) (hρ0 : 0 < ρ) (haρ : a < ρ) (hρv : ρ ≤ v)
    (hsm : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hnorm : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖)
    (hround : ∀ w : TangentSpace I p, ‖w‖ < ρ →
      Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w) = w)
    (hray : ∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < ρ →
      Work.Diff.C.rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)) = t)
    (hrayv : ∀ (w : TangentSpace I p) (t : ℝ), ‖w‖ = 1 → 0 < t → t < ρ →
      curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t =
        Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)))
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hval : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ 3 * a / 2 →
      V y = Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y) :
    (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
      Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x =
        Submission.GlobalExp.GExp (cov := cov) hmet p
          (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x))) ∧
    (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
      Φp (Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x) =
        (a / Work.Diff.C.rdist (I := I) (M := M) p x) • Φp x) := by
  classical
  have key : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
      (Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x =
        Submission.GlobalExp.GExp (cov := cov) hmet p
          (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x))) ∧
      (Φp (Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x) =
        (a / Work.Diff.C.rdist (I := I) (M := M) p x) • Φp x) := by
    intro x hx1 hx2
    set t : ℝ := Work.Diff.C.rdist (I := I) (M := M) p x with ht
    -- ## Elementary bounds on `t`
    have htpos : 0 < t := by linarith
    have htlt : t < a := by linarith
    have htρ : t < ρ := lt_trans htlt haρ
    have htv : t < v := lt_of_lt_of_le htρ hρv
    -- ## Step 1: `x` lies on the geodesic ray from `p` in the direction `Φp x`
    obtain ⟨vv, hvGExp, hved⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p x
    have hvnorm : ‖vv‖ = t := by
      have h1 : (Manifold.riemannianEDist I p x).toReal = ‖vv‖ := by
        rw [hved, ENNReal.toReal_ofReal (norm_nonneg vv)]
      rw [← h1]
      exact ht.symm
    have hΦx : Φp x = vv := by
      have hρ' : ‖vv‖ < ρ := by rw [hvnorm]; exact htρ
      have hh := hround vv hρ'
      rwa [hvGExp] at hh
    have hΦnorm : ‖Φp x‖ = t := by
      have h := hnorm x (by rw [← ht]; exact htv)
      rw [← ht] at h
      exact h.symm
    -- ## Step 2: the unit direction `w` of the ray through `x`
    set w : TangentSpace I p := t⁻¹ • Φp x with hw
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), hΦnorm]
      exact inv_mul_cancel₀ (ne_of_gt htpos)
    have hwne : w ≠ 0 := by
      intro h0
      have h := hwnorm
      rw [h0, norm_zero] at h
      exact one_ne_zero h.symm
    have hwt : t • w = vv := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul, hΦx]
    -- ## Step 3: the flow line of `x` and the ray agree on a neighbourhood of `t`
    set d : ℝ := min ρ (3 * a / 2) with hd
    have htmem : t ∈ Set.Ioo (a / 4) d := by
      refine ⟨hx1, ?_⟩
      rw [hd]
      exact lt_min htρ (by linarith)
    have hamem : a ∈ Set.Ioo (a / 4) d := by
      refine ⟨by linarith, ?_⟩
      rw [hd]
      exact lt_min haρ (by linarith)
    -- the time-translated flow line is an integral curve of `V`
    have hbase : IsMIntegralCurve (fun τ : ℝ => Φ 0 τ x) V := fun τ => hΦderiv 0 τ x
    have hγint : IsMIntegralCurve (fun s : ℝ => Φ 0 (s + (-t)) x) V := hbase.comp_add (-t)
    have hγon : IsMIntegralCurveOn (fun s : ℝ => Φ 0 (s + (-t)) x) V (Set.Ioo (a / 4) d) :=
      hγint.isMIntegralCurveOn _
    -- the ray is an integral curve of `V`: its velocity is `∇d(p,·)`, which `V` equals there
    have hGsm : ContMDiff 𝓘(ℝ,ℝ) I ∞
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne
    have hGd : ∀ s : ℝ, MDifferentiableAt 𝓘(ℝ,ℝ) I
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) s :=
      fun s => (hGsm s).mdifferentiableAt (by simp)
    have hvelG : ∀ s ∈ Set.Ioo (a / 4) d,
        curveVelocity (I := I)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) s =
        V (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hs0 : 0 < s := by linarith
      have hsρ : s < ρ := by
        rw [hd] at hs2
        exact lt_of_lt_of_le hs2 (min_le_left _ _)
      have hs3 : s ≤ 3 * a / 2 := by
        rw [hd] at hs2
        exact le_of_lt (lt_of_lt_of_le hs2 (min_le_right _ _))
      have hray_pt : Work.Diff.C.rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) = s :=
        hray w s hwnorm (le_of_lt hs0) hsρ
      have h1 : a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) := by
        rw [hray_pt]; linarith
      have h2 : Work.Diff.C.rdist (I := I) (M := M) p
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) ≤ 3 * a / 2 := by
        rw [hray_pt]; exact hs3
      rw [hrayv w s hwnorm hs0 hsρ,
        hval (Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) h1 h2]
    have hGon : IsMIntegralCurveOn
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) V
        (Set.Ioo (a / 4) d) :=
      isMIntegralCurveOn_of_curveVelocity_eq (hsm := fun s _ => hGd s) hvelG
    -- ## Step 4: uniqueness of solutions of the ODE `z' = V z`
    have hv : ContMDiff I I.tangent 1 (fun y : M => (⟨y, V y⟩ : TangentBundle I M)) :=
      hVsm.of_le (by simp)
    have hagree : (fun s : ℝ => Φ 0 (s + (-t)) x) t
        = (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (s • w)) t := by
      show Φ 0 (t + -t) x = Submission.GlobalExp.GExp (cov := cov) hmet p (t • w)
      rw [add_neg_cancel, hΦself, hwt, hvGExp]
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := t) htmem hv hγon hGon hagree
    have haeq : Φ 0 (a + (-t)) x
        = Submission.GlobalExp.GExp (cov := cov) hmet p (a • w) := heq hamem
    -- ## Step 5: read off the two conclusions at time `a`
    have haw : ‖a • w‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hwnorm, mul_one]
      exact haρ
    refine ⟨?_, ?_⟩
    · have h1 : -(t - a) = a + (-t) := by ring
      simp only [h1, haeq]
    · have h1 : -(t - a) = a + (-t) := by ring
      rw [h1, haeq, hround (a • w) haw]
      simp only [hw, smul_smul, div_eq_mul_inv]
  exact ⟨fun x hx1 hx2 => (key x hx1 hx2).1, fun x hx1 hx2 => (key x hx1 hx2).2⟩

end Work.Diff.Dim2
