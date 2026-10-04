import Mathlib
import Submission.Work.Diff.C.geoCrux.TwoCentre.Setup

set_option backward.isDefEq.respectTransparency.types false

/-!
# The two families of Jacobi fields along the ray, and the bridges

* `tcFwd ξ` — the forward variation field of the family of rays out of `q` (`tcFwd ξ 0 = 0`,
  `∇tcFwd ξ (0) = ξ`);
* `tcPrayFld t η` — the forward variation field of the family of rays out of `γ t` in the *reversed*
  direction `-γ'(t)` (the "backward" family from the second centre `γ t`), together with its reversal
  `tcBwd`.

We collect: the Jacobi property, linearity in the direction, the Gauss pairing, the gradient
identities along the ray, the Wronskian constancy, and the *shape-operator identity* (the bridge
`Work.Diff.C.dmRadialBridge`) for both families.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## The ray out of the second centre -/

/-- The ray out of `γ t` in the reversed direction `-γ'(t)`: it retraces `tcGam`. -/
noncomputable def tcPray (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ) :
    ℝ → M :=
  fun u : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
    (u • (-(tcVel (cov := cov) hmet q v t)))

/-- The forward variation field of the family of rays out of `γ t` (a Jacobi field vanishing at
`u = 0`). -/
noncomputable def tcPrayFld (hmet : IsMetricCompatible cov) (q : M) (v : TangentSpace I q) (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    (u : ℝ) → TangentSpace I (tcPray (cov := cov) hmet q v t u) :=
  fun u : ℝ => Submission.Geodesic.curveVelocity (I := I)
    (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (u • (-(tcVel (cov := cov) hmet q v t) + r • η))) 0

lemma tcPrayFld_eq_bwd (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) (s : ℝ) :
    (show E from tcPrayFld (cov := cov) hmet q v t η (t - s))
      = (show E from tcBwd (cov := cov) hmet q v t
          (-(tcVel (cov := cov) hmet q v t)) η s) := rfl

/-! ## The forward family -/

lemma tcFwd_eq_mfderiv (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (s : ℝ) :
    tcFwd (cov := cov) hmet q v ξ s
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet q w)
          (s • v)) (s • ξ) :=
  Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet s v ξ

lemma tcFwd_add (hmet : IsMetricCompatible cov) (q : M) (v ξ ξ' : TangentSpace I q) (s : ℝ) :
    tcFwd (cov := cov) hmet q v (ξ + ξ') s
      = tcFwd (cov := cov) hmet q v ξ s + tcFwd (cov := cov) hmet q v ξ' s := by
  rw [tcFwd_eq_mfderiv, tcFwd_eq_mfderiv, tcFwd_eq_mfderiv, smul_add, map_add]

lemma tcFwd_smul (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (a s : ℝ) :
    tcFwd (cov := cov) hmet q v (a • ξ) s = a • tcFwd (cov := cov) hmet q v ξ s := by
  rw [tcFwd_eq_mfderiv, tcFwd_eq_mfderiv, smul_comm, map_smul]

lemma tcFwd_isJacobiAt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (hv0 : v ≠ 0) (hvn : ‖v‖ = 1) (ξ : TangentSpace I q) :
    ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcGam (cov := cov) hmet q v)
      (tcFwd (cov := cov) hmet q v ξ) s := by
  intro s
  change Submission.RauchGlobal.IsJacobiAt cov
    (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
    (fun s : ℝ => Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + r • ξ))) 0) s
  exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hv0 hvn s

lemma tcFwd_zero (hmet : IsMetricCompatible cov) {q : M} {v ξ : TangentSpace I q} :
    tcFwd (cov := cov) hmet q v ξ 0 = 0 := by
  have h := Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet
    (p := q) (u := v) (η := ξ)
  simpa only [tcFwd, zero_smul, add_zero] using h

lemma tcFwd_covAlong_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (hv0 : v ≠ 0) (ξ : TangentSpace I q) :
    Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) 0 = ξ := by
  have h := Work.OddBound.longHomotopy.covAlong_variation_zero (cov := cov) hmet htor
    (p := q) (u := v) (η := ξ) hv0
  rw [covAlong_congr_curve
    (γ₁ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + (0:ℝ) • ξ)))
    (γ₂ := tcGam (cov := cov) hmet q v)
    (by funext s; simp only [tcGam, zero_smul, add_zero]) (fun t => rfl) 0] at h
  exact h

lemma tcFwd_gauss (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (ξ : TangentSpace I q) (s : ℝ) :
    tcIn (tcGam (cov := cov) hmet q v s) (tcFwd (cov := cov) hmet q v ξ s)
        (tcVel (cov := cov) hmet q v s)
      = s * tcIn q ξ v := by
  have h := Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) hmet htor
    (p := q) (v := v) (η := ξ) s
  rw [← tcIn_eq, ← tcIn_eq] at h
  rw [tcIn_pt (X := Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + (0:ℝ) • ξ)))
    (Y := tcGam (cov := cov) hmet q v s)
    (by simp only [tcGam, zero_smul, add_zero])] at h
  exact h

/-! ## The gradients of the two distance functions along the ray -/

lemma tc_grad_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ rho0 c) :
    rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t)
      = tcVel (cov := cov) hmet q v t := by
  have hnormv : ‖(t • v : TangentSpace I q)‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le, hvn, mul_one]
  have htv_ne : (t • v : TangentSpace I q) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnormv; exact absurd hnormv.symm (ne_of_gt ht0)
  have hmin : Manifold.riemannianEDist I q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
        = ENNReal.ofReal ‖(t • v : TangentSpace I q)‖ := by
    haveI : RegularSpace M := inferInstance
    exact Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov) hmet
      htor (hcut q) (by rw [hnormv]; exact ht)
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v t) :=
    tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht0 ht
  have hunit : tcIn (tcGam (cov := cov) hmet q v t)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t)) = 1 :=
    tc_eik_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht0 ht
  have hunit' : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • (t • v))))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • (t • v)))) = 1 := by
    rw [one_smul, ← tcGam_eq (cov := cov) hmet q v t, ← tcIn_eq]
    exact hunit
  have hsm' : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) := by
    rw [← tcGam_eq (cov := cov) hmet q v t]; exact hsm
  have hcv := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet
    (p := q) (u := t • v) htv_ne hmin (by simpa only [one_smul] using hsm') hunit'
  rw [hnormv, one_smul] at hcv
  have hscale : Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (t • v))) 1
      = t • tcVel (cov := cov) hmet q v t := by
    have hfun : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (t • v)))
        = fun s : ℝ => (tcGam (cov := cov) hmet q v) (t * s) := by
      funext s; rw [tcGam, smul_smul, mul_comm s t]
    rw [hfun]
    have hcm := Submission.GlobalExp.curveVelocity_comp_mul (I := I)
      (γ := tcGam (cov := cov) hmet q v) (c := t) (t := 1)
      ((tcGam_contMDiff (cov := cov) hmet hv0).contMDiffAt.mdifferentiableAt (by decide))
    rw [mul_one] at hcm
    exact hcm
  have hcancel : t • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v t)
      = t • tcVel (cov := cov) hmet q v t := by
    rw [tcGam_eq, ← hcv, hscale]
  exact smul_eq_of_smul_eq (ne_of_gt ht0) hcancel



/-! ## The gradient for the second centre -/

lemma tc_grad_bwd (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t s : ℝ} (hs0 : 0 < s)
    (hst : s < t) (ht : t ≤ rho0 c) :
    rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z) (tcGam (cov := cov) hmet q v s)
      = -(tcVel (cov := cov) hmet q v s) := by
  have ht0 : 0 < t := lt_trans hs0 hst
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0 : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  have hdpos : 0 < t - s := sub_pos.mpr hst
  set u : TangentSpace I (tcGam (cov := cov) hmet q v t) :=
    (t - s) • (-(tcVel (cov := cov) hmet q v t)) with hudef
  have hnormu : ‖u‖ = t - s := by
    rw [hudef, norm_smul, Real.norm_of_nonneg hdpos.le, hwn, mul_one]
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnormu; exact absurd hnormu.symm (ne_of_gt hdpos)
  have hmin : Manifold.riemannianEDist I (tcGam (cov := cov) hmet q v t)
      (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t) u)
      = ENNReal.ofReal ‖u‖ := by
    haveI : RegularSpace M := inferInstance
    refine Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov) hmet
      htor (hcut (tcGam (cov := cov) hmet q v t)) ?_
    rw [hnormu]; linarith
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z) (tcGam (cov := cov) hmet q v s) :=
    tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht ht0 hs0 hst
  have hpt : Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      ((1 : ℝ) • u) = tcGam (cov := cov) hmet q v s := by
    rw [one_smul, hudef]
    exact tc_rev_point (cov := cov) hmet hvn t s
  have heik : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          ((1 : ℝ) • u)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z)
        (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          ((1 : ℝ) • u))) = 1 := by
    rw [hpt]
    refine Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor ?_ hsm
    rw [tc_rdist_bwd (cov := cov) hmet htor hcut hvn ht ht0 hs0.le hst]
    exact ne_of_gt hdpos
  have hsm' : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
      (tcGam (cov := cov) hmet q v t) z)
      (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        ((1 : ℝ) • u)) := by
    rw [hpt]; exact hsm
  have hcv := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov) hmet
    (p := tcGam (cov := cov) hmet q v t) (u := u) hu0 hmin hsm' heik
  rw [hnormu] at hcv
  have hscale : Submission.Geodesic.curveVelocity (I := I)
      (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        (s' • u)) 1
      = (t - s) • (-(tcVel (cov := cov) hmet q v s)) := by
    rw [hudef]
    have hfun : (fun s' : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
          (tcGam (cov := cov) hmet q v t)
          (s' • ((t - s) • (-(tcVel (cov := cov) hmet q v t)))))
        = fun s' : ℝ => (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
            (tcGam (cov := cov) hmet q v t)
            (r • (-(tcVel (cov := cov) hmet q v t)))) ((t - s) * s') := by
      funext s'
      rw [smul_smul, mul_comm]
    rw [hfun]
    have hcm := Submission.GlobalExp.curveVelocity_comp_mul (I := I)
      (γ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet
        (tcGam (cov := cov) hmet q v t) (r • (-(tcVel (cov := cov) hmet q v t))))
      (c := t - s) (t := 1)
      (((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
        (tcGam (cov := cov) hmet q v t) hw0).contMDiffAt).mdifferentiableAt (by decide))
    rw [mul_one] at hcm
    rw [hcm, tc_rev_vel (cov := cov) hmet hvn hv0 t s]
  rw [hscale, hpt] at hcv
  exact (smul_eq_of_smul_eq (ne_of_gt hdpos) hcv).symm

/-! ## The backward family (the forward variation field of the ray out of `γ t`) -/

lemma tcPrayFld_eq_mfderiv (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) (u : ℝ) :
    tcPrayFld (cov := cov) hmet q v t η u
      = (mfderiv 𝓘(ℝ, E) I (fun w : E =>
          Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t) w)
          (u • (-(tcVel (cov := cov) hmet q v t)))) (u • η) :=
  Work.OddBound.longHomotopy.curveVelocity_GExp_smul_variation (cov := cov) hmet u
    (-(tcVel (cov := cov) hmet q v t)) η

lemma tcPrayFld_add (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (t : ℝ)
    (η η' : TangentSpace I (tcGam (cov := cov) hmet q v t)) (u : ℝ) :
    tcPrayFld (cov := cov) hmet q v t (η + η') u
      = tcPrayFld (cov := cov) hmet q v t η u + tcPrayFld (cov := cov) hmet q v t η' u := by
  rw [tcPrayFld_eq_mfderiv, tcPrayFld_eq_mfderiv, tcPrayFld_eq_mfderiv, smul_add, map_add]

lemma tcPrayFld_smul (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) (a u : ℝ) :
    tcPrayFld (cov := cov) hmet q v t (a • η) u
      = a • tcPrayFld (cov := cov) hmet q v t η u := by
  rw [tcPrayFld_eq_mfderiv, tcPrayFld_eq_mfderiv, smul_comm, map_smul]

lemma tcPrayFld_isJacobiAt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    ∀ u : ℝ, Submission.RauchGlobal.IsJacobiAt cov (tcPray (cov := cov) hmet q v t)
      (tcPrayFld (cov := cov) hmet q v t η) u := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0 : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  intro u
  exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hw0 hwn u

lemma tcPrayFld_zero (hmet : IsMetricCompatible cov) {q : M} {v : TangentSpace I q} (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    tcPrayFld (cov := cov) hmet q v t η 0 = 0 := by
  have h := Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet
    (p := tcGam (cov := cov) hmet q v t) (u := -(tcVel (cov := cov) hmet q v t)) (η := η)
  simpa only [tcPrayFld, zero_smul, add_zero] using h

lemma tcPrayFld_covAlong_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (hv0 : v ≠ 0) (t : ℝ)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) 0 = η := by
  have h := Work.OddBound.longHomotopy.covAlong_variation_zero (cov := cov) hmet htor
    (p := tcGam (cov := cov) hmet q v t) (u := -(tcVel (cov := cov) hmet q v t)) (η := η)
    (by rw [neg_ne_zero]; exact tcVel_ne_zero (cov := cov) hmet hv0 t)
  rw [covAlong_congr_curve
    (γ₁ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (s • (-(tcVel (cov := cov) hmet q v t) + (0:ℝ) • η)))
    (γ₂ := tcPray (cov := cov) hmet q v t)
    (by funext s; simp only [tcPray, zero_smul, add_zero]) (fun s => rfl) 0] at h
  exact h

lemma tcPrayFld_gauss (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {q : M}
    {v : TangentSpace I q} (t : ℝ) (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) (u : ℝ) :
    tcIn (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
        (Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) u)
      = u * tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) := by
  have h := Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) hmet htor
    (p := tcGam (cov := cov) hmet q v t) (v := -(tcVel (cov := cov) hmet q v t)) (η := η) u
  rw [← tcIn_eq, ← tcIn_eq] at h
  rw [tcIn_pt (X := Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
      (u • (-(tcVel (cov := cov) hmet q v t) + (0:ℝ) • η)))
    (Y := tcPray (cov := cov) hmet q v t u)
    (by simp only [tcPray, zero_smul, add_zero])] at h
  exact h

/-! ## Nearby rays are minimising -/

lemma tc_minW_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) {ξ : TangentSpace I q} {d : ℝ}
    (hd0 : 0 < d) (hd : d < rho0 c) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + s • ξ)))
        = ‖d • (v + s • ξ)‖ := by
  haveI : RegularSpace M := inferInstance
  have hcont : Continuous (fun s : ℝ => d * ‖v + s • ξ‖) :=
    continuous_const.mul (continuous_norm.comp (continuous_const.add
      (continuous_id.smul continuous_const)))
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), d * ‖v + s • ξ‖ < rho0 c := by
    refine hcont.continuousAt (isOpen_Iio.mem_nhds ?_)
    show d * ‖v + (0 : ℝ) • ξ‖ < rho0 c
    rw [zero_smul, add_zero, hvn, mul_one]; exact hd
  filter_upwards [hev] with s hs
  have hwle : ‖(d • (v + s • ξ) : TangentSpace I q)‖ ≤ rho0 c := by
    rw [norm_smul, Real.norm_of_nonneg hd0.le]; exact hs.le
  have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov)
    hmet htor (hcut q) hwle
  rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal (norm_nonneg _)]

lemma tc_minW_bwd' (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c) {u : ℝ} (hu0 : 0 < u) (hu : u < rho0 c)
    (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t)
          (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
            (u • (-(tcVel (cov := cov) hmet q v t) + r • η)))
        = ‖u • (-(tcVel (cov := cov) hmet q v t) + r • η)‖ := by
  haveI : RegularSpace M := inferInstance
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hcont : Continuous (fun r : ℝ => u * ‖-(tcVel (cov := cov) hmet q v t) + r • η‖) :=
    continuous_const.mul (continuous_norm.comp (continuous_const.add
      (continuous_id.smul continuous_const)))
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), u * ‖-(tcVel (cov := cov) hmet q v t) + r • η‖ < rho0 c := by
    refine hcont.continuousAt (isOpen_Iio.mem_nhds ?_)
    show u * ‖-(tcVel (cov := cov) hmet q v t) + (0 : ℝ) • η‖ < rho0 c
    rw [zero_smul, add_zero, hwn, mul_one]; exact hu
  filter_upwards [hev] with r hr
  have hwle : ‖(u • (-(tcVel (cov := cov) hmet q v t) + r • η) :
      TangentSpace I (tcGam (cov := cov) hmet q v t))‖ ≤ rho0 c := by
    rw [norm_smul, Real.norm_of_nonneg hu0.le]; exact hr.le
  have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov)
    hmet htor (hcut (tcGam (cov := cov) hmet q v t)) hwle
  rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal (norm_nonneg _)]

lemma tc_minW_bwd (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t : ℝ} (ht0 : 0 < t)
    (ht : t < rho0 c) (η : TangentSpace I (tcGam (cov := cov) hmet q v t)) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t)
          (Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
            (t • (-(tcVel (cov := cov) hmet q v t) + r • η)))
        = ‖t • (-(tcVel (cov := cov) hmet q v t) + r • η)‖ := by
  haveI : RegularSpace M := inferInstance
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hcont : Continuous (fun r : ℝ => t * ‖-(tcVel (cov := cov) hmet q v t) + r • η‖) :=
    continuous_const.mul (continuous_norm.comp (continuous_const.add
      (continuous_id.smul continuous_const)))
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), t * ‖-(tcVel (cov := cov) hmet q v t) + r • η‖ < rho0 c := by
    refine hcont.continuousAt (isOpen_Iio.mem_nhds ?_)
    show t * ‖-(tcVel (cov := cov) hmet q v t) + (0 : ℝ) • η‖ < rho0 c
    rw [zero_smul, add_zero, hwn, mul_one]; exact ht
  filter_upwards [hev] with r hr
  have hwle : ‖(t • (-(tcVel (cov := cov) hmet q v t) + r • η) :
      TangentSpace I (tcGam (cov := cov) hmet q v t))‖ ≤ rho0 c := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le]; exact hr.le
  have h := Submission.GExpRay2.edist_GExp_eq_norm_of_le_of_injAtLeast (I := I) (cov := cov)
    hmet htor (hcut (tcGam (cov := cov) hmet q v t)) hwle
  rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal (norm_nonneg _)]


/-! ## The Wronskian of two Jacobi fields is constant -/

theorem tc_wronskian_const (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {J K : (t : ℝ) → TangentSpace I (γ t)}
    (hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ J t)
    (hK : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov γ K t) (t₀ t : ℝ) :
    tcIn (γ t) (Submission.JacobiGlobal.covAlong cov J t) (K t)
        - tcIn (γ t) (J t) (Submission.JacobiGlobal.covAlong cov K t)
      = tcIn (γ t₀) (Submission.JacobiGlobal.covAlong cov J t₀) (K t₀)
        - tcIn (γ t₀) (J t₀) (Submission.JacobiGlobal.covAlong cov K t₀) := by
  set F : ℝ → ℝ := fun s => Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s) (K s)
    - Inner.inner ℝ (J s) (Submission.JacobiGlobal.covAlong cov K s) with hF
  have hderiv : ∀ s : ℝ, HasDerivAt F 0 s := by
    intro s
    have h1 := Work.Diff.C.jml_hasDerivAt_inner_covAlong_two (I := I) (M := M) (cov := cov)
      hmet htor hγ hJ hK hne s
    have h2 := Work.Diff.C.jml_hasDerivAt_inner_covAlong_two (I := I) (M := M) (cov := cov)
      hmet htor hγ hK hJ hne s
    have h2' : HasDerivAt
        (fun s : ℝ => Inner.inner ℝ (J s) (Submission.JacobiGlobal.covAlong cov K s))
        (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov K s)
            (Submission.JacobiGlobal.covAlong cov J s)
          - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)) s := by
      simpa only [real_inner_comm] using h2
    have hsub := h1.sub h2'
    have hzero : Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J s)
          (Submission.JacobiGlobal.covAlong cov K s)
        - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (J s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)
            (Submission.Geodesic.curveVelocity (I := I) γ s)) (K s)
        - (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov K s)
              (Submission.JacobiGlobal.covAlong cov J s)
          - Inner.inner ℝ (Submission.CurvatureVec.curvVec cov (γ s) (K s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)
              (Submission.Geodesic.curveVelocity (I := I) γ s)) (J s)) = 0 := by
      have hsym := Submission.CurvatureSym.inner_curvVec_self_adjoint (cov := cov)
        (inferInstance : ContMDiffCovariantDerivative cov ∞) htor hmet (γ s) (J s)
        (Submission.Geodesic.curveVelocity (I := I) γ s) (K s)
      rw [real_inner_comm (x := Submission.JacobiGlobal.covAlong cov J s)
        (y := Submission.JacobiGlobal.covAlong cov K s)]
      rw [real_inner_comm (x := J s) (y := Submission.CurvatureVec.curvVec cov (γ s) (K s)
        (Submission.Geodesic.curveVelocity (I := I) γ s)
        (Submission.Geodesic.curveVelocity (I := I) γ s))]
      linarith [hsym]
    exact hsub.congr_deriv hzero
  have hdiff : Differentiable ℝ F := fun s => (hderiv s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hderiv s).deriv)
  have hct := hconst t t₀
  rw [hF] at hct
  dsimp only at hct
  rw [← tcIn_eq, ← tcIn_eq, ← tcIn_eq, ← tcIn_eq] at hct
  exact hct

/-! ## The bridge for the forward family -/

lemma tcFwd_bridge (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {ξ : TangentSpace I q} (horth : tcIn q v ξ = 0) {d : ℝ} (hd0 : 0 < d) (hd : d < rho0 c) :
    tcIn (tcGam (cov := cov) hmet q v d) (Submission.JacobiGlobal.covAlong cov
        (tcFwd (cov := cov) hmet q v ξ) d) (tcFwd (cov := cov) hmet q v ξ d)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
          (tcFwd (cov := cov) hmet q v ξ d) := by
  by_cases hz : tcFwd (cov := cov) hmet q v ξ d = 0
  · rw [hz, tcIn_zero_right]
    simp [rhess]
  · have hu : Inner.inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hvn]; norm_num
    have horth' : Inner.inner ℝ v ξ = 0 := by rw [← tcIn_eq]; exact horth
    have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (d • v)) := by
      rw [← tcGam_eq (cov := cov) hmet q v d]
      exact tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hd0 hd.le
    have hrgrad : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (d • v))
        = Submission.Geodesic.curveVelocity (I := I)
          (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) d := by
      rw [← tcGam_eq (cov := cov) hmet q v d]
      exact tc_grad_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hd0 hd.le
    have hcsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + s • ξ))) := by
      intro s
      have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := q)
        (u := v) (η := ξ) d s
      have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
          (fun s' : ℝ => (d, s')) s := by
        rw [contMDiffAt_iff_contDiffAt]; fun_prop
      exact (hfam.comp s hpair).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s' => rfl)
    have hne : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + s • ξ))) 0 ≠ 0 := hz
    have hminW := tc_minW_gam (cov := cov) hmet htor hcut hvn (ξ := ξ) hd0 hd
    have h := Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor (p := q)
      (d := d) hd0 hu horth' hsm hrgrad hcsm hne hminW
    rw [← tcIn_eq] at h
    rw [tcIn_pt (X := Submission.GlobalExp.GExp (cov := cov) hmet q (d • v))
      (Y := tcGam (cov := cov) hmet q v d) (by rw [tcGam_eq])] at h
    rw [show Submission.GlobalExp.GExp (cov := cov) hmet q (d • v) = tcGam (cov := cov) hmet q v d
      from (tcGam_eq (cov := cov) hmet q v d).symm] at h
    exact h

/-! ## The bridge for the backward family (in the parametrisation of the ray out of `γ t`) -/

lemma tcPrayFld_bridge (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t u : ℝ} (hu0 : 0 < u)
    (hut : u < t) (ht : t < rho0 c) (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0) :
    tcIn (tcPray (cov := cov) hmet q v t u)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
        (tcPrayFld (cov := cov) hmet q v t η u)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
          (tcPrayFld (cov := cov) hmet q v t η u) := by
  have ht0 : 0 < t := lt_trans hu0 hut
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0 : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  by_cases hz : tcPrayFld (cov := cov) hmet q v t η u = 0
  · rw [hz, tcIn_zero_right]
    simp [rhess]
  · have hu' : Inner.inner ℝ (-(tcVel (cov := cov) hmet q v t))
        (-(tcVel (cov := cov) hmet q v t)) = 1 := by
      rw [real_inner_self_eq_norm_sq, hwn]; norm_num
    have horth' : Inner.inner ℝ (-(tcVel (cov := cov) hmet q v t)) η = 0 := by
      have hη' : tcIn (tcGam (cov := cov) hmet q v t) (-(tcVel (cov := cov) hmet q v t)) η = 0 := by
        rw [tcIn_symm]; exact hη
      rw [← tcIn_eq]; exact hη'
    have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M)
        (tcGam (cov := cov) hmet q v t) z) (tcPray (cov := cov) hmet q v t u) := by
      have hpt : tcPray (cov := cov) hmet q v t u = tcGam (cov := cov) hmet q v (t - u) := by
        have h := tc_rev_point (cov := cov) hmet hvn t (t - u)
        rwa [show t - (t - u) = u from by ring] at h
      rw [hpt]
      exact tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht.le ht0 (by linarith) (by linarith)
    have hrgrad : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M)
          (tcGam (cov := cov) hmet q v t) z) (tcPray (cov := cov) hmet q v t u)
        = Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) u := by
      have hpt : tcPray (cov := cov) hmet q v t u = tcGam (cov := cov) hmet q v (t - u) := by
        have h := tc_rev_point (cov := cov) hmet hvn t (t - u)
        rwa [show t - (t - u) = u from by ring] at h
      have hvel : Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) u
          = -(tcVel (cov := cov) hmet q v (t - u)) := by
        have h := tc_rev_vel (cov := cov) hmet hvn hv0 t (t - u)
        rw [show t - (t - u) = u from by ring] at h
        exact h
      rw [hpt, hvel]
      exact tc_grad_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 (by linarith) (by linarith)
        ht.le
    have hcsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (u • (-(tcVel (cov := cov) hmet q v t) + s • η))) := by
      intro s
      have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet
        (p := tcGam (cov := cov) hmet q v t) (u := -(tcVel (cov := cov) hmet q v t)) (η := η) u s
      have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
          (fun s' : ℝ => (u, s')) s := by
        rw [contMDiffAt_iff_contDiffAt]; fun_prop
      exact (hfam.comp s hpair).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s' => rfl)
    have hne : Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
          (u • (-(tcVel (cov := cov) hmet q v t) + s • η))) 0 ≠ 0 := hz
    have hminW := tc_minW_bwd' (cov := cov) hmet htor hcut hvn hv0 ht0 ht hu0 (lt_trans hut ht) η
    have h := Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor
      (p := tcGam (cov := cov) hmet q v t) (d := u) hu0 hu' horth' hsm hrgrad hcsm hne hminW
    rw [← tcIn_eq] at h
    exact h


/-! ## The polarised bridges -/

lemma tcFwd_bridge_bilin (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {ξ η : TangentSpace I q} (hξ : tcIn q v ξ = 0) (hη : tcIn q v η = 0)
    {d : ℝ} (hd0 : 0 < d) (hd : d < rho0 c) :
    tcIn (tcGam (cov := cov) hmet q v d) (Submission.JacobiGlobal.covAlong cov
        (tcFwd (cov := cov) hmet q v ξ) d) (tcFwd (cov := cov) hmet q v η d)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
          (tcFwd (cov := cov) hmet q v η d) := by
  have hξη : tcIn q v (ξ + η) = 0 := by rw [tcIn_add_right]; simp [hξ, hη]
  have hsum := tcFwd_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hξη hd0 hd
  have h1 := tcFwd_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hξ hd0 hd
  have h2 := tcFwd_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hη hd0 hd
  -- Jacobi and smoothness
  have hγ : ContMDiffOn 𝓘(ℝ) I ∞ (tcGam (cov := cov) hmet q v)
      (Set.Ioo (d - 1) (d + 1)) :=
    (tcGam_contMDiff (cov := cov) hmet hv0).contMDiffOn
  have hJξ := tcFwd_isJacobiAt (cov := cov) hmet htor hv0 hvn ξ
  have hJη := tcFwd_isJacobiAt (cov := cov) hmet htor hv0 hvn η
  have hsmξ := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJξ hγ
  have hsmη := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJη hγ
  have hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) (tcGam (cov := cov) hmet q v) t ≠ 0 :=
    fun t => tcVel_ne_zero (cov := cov) hmet hv0 t
  -- the Wronskian antisymmetry
  have hW := tc_wronskian_const (cov := cov) hmet htor (tcGam_contMDiff (cov := cov) hmet hv0) hne
    hJξ hJη 0 d
  have hW0 : tcIn (tcGam (cov := cov) hmet q v 0)
        (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) 0)
        (tcFwd (cov := cov) hmet q v η 0)
      - tcIn (tcGam (cov := cov) hmet q v 0) (tcFwd (cov := cov) hmet q v ξ 0)
        (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) 0) = 0 := by
    rw [tcFwd_zero, tcFwd_zero]
    simp only [tcIn_zero_left, tcIn_zero_right, sub_zero]
  rw [hW0] at hW
  have hW' : tcIn (tcGam (cov := cov) hmet q v d)
      (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) d)
      (tcFwd (cov := cov) hmet q v η d)
      = tcIn (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
        (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) d) := by
    linarith [hW]
  have hsym : tcIn (tcGam (cov := cov) hmet q v d)
      (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) d)
      (tcFwd (cov := cov) hmet q v η d)
      = tcIn (tcGam (cov := cov) hmet q v d)
        (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) d)
        (tcFwd (cov := cov) hmet q v ξ d) := by
    rw [tcIn_symm (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
      (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) d)] at hW'
    exact hW'
  -- expand the (ξ+η) bridge
  have hexp : tcIn (tcGam (cov := cov) hmet q v d)
      (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v (ξ + η)) d)
      (tcFwd (cov := cov) hmet q v (ξ + η) d)
      = tcIn (tcGam (cov := cov) hmet q v d)
          (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) d)
          (tcFwd (cov := cov) hmet q v ξ d)
        + tcIn (tcGam (cov := cov) hmet q v d)
          (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v ξ) d)
          (tcFwd (cov := cov) hmet q v η d)
        + tcIn (tcGam (cov := cov) hmet q v d)
          (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) d)
          (tcFwd (cov := cov) hmet q v ξ d)
        + tcIn (tcGam (cov := cov) hmet q v d)
          (Submission.JacobiGlobal.covAlong cov (tcFwd (cov := cov) hmet q v η) d)
          (tcFwd (cov := cov) hmet q v η d) := by
    have hfun : tcFwd (cov := cov) hmet q v (ξ + η)
        = fun s : ℝ => tcFwd (cov := cov) hmet q v ξ s + tcFwd (cov := cov) hmet q v η s := by
      funext s; exact tcFwd_add (cov := cov) hmet q v ξ η s
    rw [hfun, Submission.ConjEnergy.covAlong_add (cov := cov) htor hsmξ hsmη]
    simp only [tcIn_add_left, tcIn_add_right]
    abel
  have hexpR : rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v (ξ + η) d)
      (tcFwd (cov := cov) hmet q v (ξ + η) d)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
          (tcFwd (cov := cov) hmet q v ξ d)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
          (tcFwd (cov := cov) hmet q v η d)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v η d)
          (tcFwd (cov := cov) hmet q v ξ d)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v η d)
          (tcFwd (cov := cov) hmet q v η d) := by
    have hfun : tcFwd (cov := cov) hmet q v (ξ + η)
        = fun s : ℝ => tcFwd (cov := cov) hmet q v ξ s + tcFwd (cov := cov) hmet q v η s := by
      funext s; exact tcFwd_add (cov := cov) hmet q v ξ η s
    rw [hfun]
    simp only [Work.Diff.C.GeoCrux.rhess_add_left, Work.Diff.C.GeoCrux.rhess_add_right]
    abel
  rw [hexp, hexpR, h1, h2] at hsum
  have hRsym : rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
      (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v ξ d)
      (tcFwd (cov := cov) hmet q v η d)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
        (tcGam (cov := cov) hmet q v d) (tcFwd (cov := cov) hmet q v η d)
        (tcFwd (cov := cov) hmet q v ξ d) :=
    Work.Diff.C.rhess_symm (I := I) (M := M) (cov := cov) hmet htor
      (f := fun z : M ↦ rdist (I := I) (M := M) q z) (x := tcGam (cov := cov) hmet q v d)
      (tc_sm_gam (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hd0 hd.le)
      (tcFwd (cov := cov) hmet q v ξ d) (tcFwd (cov := cov) hmet q v η d)
  linarith [hsum, hsym, hRsym]


lemma tcPrayFld_bridge_bilin (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t u : ℝ} (hu0 : 0 < u)
    (hut : u < t) (ht : t < rho0 c)
    (η η' : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0)
    (hη' : tcIn (tcGam (cov := cov) hmet q v t) η' (-(tcVel (cov := cov) hmet q v t)) = 0) :
    tcIn (tcPray (cov := cov) hmet q v t u)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
        (tcPrayFld (cov := cov) hmet q v t η' u)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
          (tcPrayFld (cov := cov) hmet q v t η' u) := by
  have hsum0 : tcIn (tcGam (cov := cov) hmet q v t) (η + η')
      (-(tcVel (cov := cov) hmet q v t)) = 0 := by
    rw [tcIn_add_left]; simp [hη, hη']
  have hsum := tcPrayFld_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hu0 hut ht
    (η + η') hsum0
  have h1 := tcPrayFld_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hu0 hut ht η hη
  have h2 := tcPrayFld_bridge (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hu0 hut ht η' hη'
  have hwn0 : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0' : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn0; norm_num at hwn0
  have hγfull : ContMDiff 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
      (tcGam (cov := cov) hmet q v t) hw0'
  have hγ : ContMDiffOn 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) (Set.Ioo (u - 1) (u + 1)) :=
    hγfull.contMDiffOn
  have hnefull : ∀ r : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (tcPray (cov := cov) hmet q v t) r ≠ 0 := fun r =>
    Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hw0' r
  have hJη := tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η
  have hJη' := tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η'
  have hsmη := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJη hγ
  have hsmη' := Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJη' hγ
  have hW := tc_wronskian_const (cov := cov) hmet htor hγfull hnefull hJη hJη' 0 u
  have hW0 : tcIn (tcPray (cov := cov) hmet q v t 0)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) 0)
        (tcPrayFld (cov := cov) hmet q v t η' 0)
      - tcIn (tcPray (cov := cov) hmet q v t 0) (tcPrayFld (cov := cov) hmet q v t η 0)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') 0) = 0 := by
    rw [tcPrayFld_zero, tcPrayFld_zero]
    simp only [tcIn_zero_left, tcIn_zero_right, sub_zero]
  rw [hW0] at hW
  have hW' : tcIn (tcPray (cov := cov) hmet q v t u)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
      (tcPrayFld (cov := cov) hmet q v t η' u)
      = tcIn (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') u) := by
    linarith [hW]
  have hsym : tcIn (tcPray (cov := cov) hmet q v t u)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
      (tcPrayFld (cov := cov) hmet q v t η' u)
      = tcIn (tcPray (cov := cov) hmet q v t u)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') u)
        (tcPrayFld (cov := cov) hmet q v t η u) := by
    rw [tcIn_symm (tcPray (cov := cov) hmet q v t u)
      (tcPrayFld (cov := cov) hmet q v t η u)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') u)] at hW'
    exact hW'
  have hfun : tcPrayFld (cov := cov) hmet q v t (η + η')
      = fun r : ℝ => tcPrayFld (cov := cov) hmet q v t η r + tcPrayFld (cov := cov) hmet q v t η' r := by
    funext r; exact tcPrayFld_add (cov := cov) (q := q) (v := v) hmet t η η' r
  have hexp : tcIn (tcPray (cov := cov) hmet q v t u)
      (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t (η + η')) u)
      (tcPrayFld (cov := cov) hmet q v t (η + η') u)
      = tcIn (tcPray (cov := cov) hmet q v t u)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
          (tcPrayFld (cov := cov) hmet q v t η u)
        + tcIn (tcPray (cov := cov) hmet q v t u)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u)
          (tcPrayFld (cov := cov) hmet q v t η' u)
        + tcIn (tcPray (cov := cov) hmet q v t u)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') u)
          (tcPrayFld (cov := cov) hmet q v t η u)
        + tcIn (tcPray (cov := cov) hmet q v t u)
          (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η') u)
          (tcPrayFld (cov := cov) hmet q v t η' u) := by
    rw [hfun, Submission.ConjEnergy.covAlong_add (cov := cov) htor hsmη hsmη']
    simp only [tcIn_add_left, tcIn_add_right]
    abel
  have hexpR : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
      (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t (η + η') u)
      (tcPrayFld (cov := cov) hmet q v t (η + η') u)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
          (tcPrayFld (cov := cov) hmet q v t η u)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
          (tcPrayFld (cov := cov) hmet q v t η' u)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η' u)
          (tcPrayFld (cov := cov) hmet q v t η u)
        + rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η' u)
          (tcPrayFld (cov := cov) hmet q v t η' u) := by
    rw [hfun]
    simp only [Work.Diff.C.GeoCrux.rhess_add_left, Work.Diff.C.GeoCrux.rhess_add_right]
    abel
  rw [hexp, hexpR, h1, h2] at hsum
  have hRsym : rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
      (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u)
      (tcPrayFld (cov := cov) hmet q v t η' u)
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
        (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η' u)
        (tcPrayFld (cov := cov) hmet q v t η u) := by
    refine Work.Diff.C.rhess_symm (I := I) (M := M) (cov := cov) hmet htor ?_
      (tcPrayFld (cov := cov) hmet q v t η u) (tcPrayFld (cov := cov) hmet q v t η' u)
    have hpt : tcPray (cov := cov) hmet q v t u = tcGam (cov := cov) hmet q v (t - u) := by
      have h := tc_rev_point (cov := cov) hmet hvn t (t - u)
      rwa [show t - (t - u) = u from by ring] at h
    rw [hpt]
    exact tc_sm_bwd (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn ht.le (lt_trans hu0 hut)
      (by linarith) (by linarith)
  linarith [hsum, hsym, hRsym]


/-! ## The invertibility of the differential of the exponential map, and surjectivity -/

lemma tc_exists_equiv (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t u : ℝ} (hu0 : 0 < u)
    (hut : u < t) (ht : t < rho0 c) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = mfderiv 𝓘(ℝ, E) I
      (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t) w)
      (u • (-(tcVel (cov := cov) hmet q v t))) := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hnorm : ‖u • (-(tcVel (cov := cov) hmet q v t))‖ < rho0 c := by
    rw [norm_smul, Real.norm_of_nonneg hu0.le, hwn, mul_one]; linarith
  obtain ⟨e, he⟩ := Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt
    (I := I) (cov := cov) hmet htor (hcut (tcGam (cov := cov) hmet q v t)) hnorm
  exact ⟨e, he⟩

lemma tcPrayFld_surj (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t u : ℝ} (hu0 : 0 < u)
    (hut : u < t) (ht : t < rho0 c) {X : E}
    (hX : tcIn (tcPray (cov := cov) hmet q v t u) X
      (Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) u) = 0) :
    ∃ η : TangentSpace I (tcGam (cov := cov) hmet q v t),
      tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0 ∧
      tcPrayFld (cov := cov) hmet q v t η u = X := by
  obtain ⟨e, he⟩ := tc_exists_equiv (cov := cov) hmet htor hcut hvn hv0 hu0 hut ht
  have hval : ∀ y : E,
      tcPrayFld (cov := cov) hmet q v t ((1 / u) • (e.symm y)) u = y := by
    intro y
    have h1 : tcPrayFld (cov := cov) hmet q v t ((1 / u) • (e.symm y)) u
        = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet
            (tcGam (cov := cov) hmet q v t) w)
            (u • (-(tcVel (cov := cov) hmet q v t)))) (e.symm y) := by
      rw [tcPrayFld_eq_mfderiv]
      congr 1
      rw [smul_smul, show u * (1 / u) = 1 by
        rw [mul_one_div, div_self (ne_of_gt hu0)], one_smul]
    rw [h1, ← he]
    exact ContinuousLinearEquiv.apply_symm_apply e y
  refine ⟨(1 / u) • (e.symm X), ?_, hval X⟩
  have hG := tcPrayFld_gauss (cov := cov) (q := q) (v := v) hmet htor t ((1 / u) • (e.symm X)) u
  rw [hval X, hX, zero_eq_mul] at hG
  rcases hG with h | h
  · exact absurd h (ne_of_gt hu0)
  · exact h

lemma tcPrayFld_shape_all (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t u : ℝ} (hu0 : 0 < u)
    (hut : u < t) (ht : t < rho0 c) (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (tcGam (cov := cov) hmet q v t) η (-(tcVel (cov := cov) hmet q v t)) = 0)
    {X : E} (hX : tcIn (tcPray (cov := cov) hmet q v t u) X
      (Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) u) = 0) :
    tcIn (tcPray (cov := cov) hmet q v t u)
        (Submission.JacobiGlobal.covAlong cov (tcPrayFld (cov := cov) hmet q v t η) u) X
      = rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcPray (cov := cov) hmet q v t u) (tcPrayFld (cov := cov) hmet q v t η u) X := by
  obtain ⟨η', hη', hval⟩ := tcPrayFld_surj (cov := cov) hmet htor hcut hvn hv0 hu0 hut ht hX
  rw [← hval]
  exact tcPrayFld_bridge_bilin (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hu0 hut ht η η'
    hη hη'

/-- **The backward shape identity along `tcGam`.**  For the backward field `s ↦ Z_η(t - s)`
(vanishing at `s = t`) and any `X ⊥ γ'(σ)`,

`⟪∇_σ (Z_η(t - ·)), X⟫ = - Hess (rdist (γ t))(γ σ)(Z_η(t-σ), X)`. -/
lemma tcBwd_shape_gam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x (rho0 c))
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0) {t σ : ℝ} (hσ0 : 0 < σ)
    (hσt : σ < t) (ht : t < rho0 c) (η : TangentSpace I (tcGam (cov := cov) hmet q v t))
    (hη : tcIn (I := I) (M := M) (tcGam (cov := cov) hmet q v t) η
      (-(tcVel (cov := cov) hmet q v t)) = 0)
    {X : E} (hX : tcIn (I := I) (M := M) (tcGam (cov := cov) hmet q v σ) X
      (tcVel (cov := cov) hmet q v σ) = 0) :
    tcIn (I := I) (M := M) (tcGam (cov := cov) hmet q v σ)
        (Submission.JacobiGlobal.covAlong cov
          (γ := tcGam (cov := cov) hmet q v)
          (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) σ) X
      = - rhess cov (fun z : M ↦ rdist (I := I) (M := M) (tcGam (cov := cov) hmet q v t) z)
          (tcGam (cov := cov) hmet q v σ) (tcPrayFld (cov := cov) hmet q v t η (t - σ)) X := by
  have hu0 : 0 < t - σ := sub_pos.mpr hσt
  have hut : t - σ < t := by linarith
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  have hw0' : -(tcVel (cov := cov) hmet q v t) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; norm_num at hwn
  have hpt : ∀ s : ℝ, tcPray (cov := cov) hmet q v t (t - s) = tcGam (cov := cov) hmet q v s :=
    fun s => tc_rev_point (cov := cov) hmet hvn t s
  have hvel : Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t)
      (t - σ) = -(tcVel (cov := cov) hmet q v σ) :=
    tc_rev_vel (cov := cov) hmet hvn hv0 t σ
  have hX' : tcIn (tcPray (cov := cov) hmet q v t (t - σ)) X
      (Submission.Geodesic.curveVelocity (I := I) (tcPray (cov := cov) hmet q v t) (t - σ)) = 0 := by
    rw [hpt σ, hvel]
    rw [show (-(tcVel (cov := cov) hmet q v σ))
        = (-1 : ℝ) • (tcVel (cov := cov) hmet q v σ) from
      (neg_one_smul ℝ (tcVel (cov := cov) hmet q v σ)).symm]
    rw [tcIn_smul_right, hX, mul_zero]
  have hshape := tcPrayFld_shape_all (cov := cov) hmet htor hc0 hc1 hcut hsmC hvn hv0 hu0 hut ht
    η hη hX'
  have htr := covAlong_comp_sub (cov := cov) htor
    (γ := tcPray (cov := cov) hmet q v t)
    (V := tcPrayFld (cov := cov) hmet q v t η) (T := t) (t := σ)
    (by
      have hγfull : ContMDiff 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) :=
        Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
          (tcGam (cov := cov) hmet q v t) hw0'
      exact hγfull.contMDiffOn)
    (by
      exact Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hw0' (t - σ))
    (by
      have hJ := tcPrayFld_isJacobiAt (cov := cov) hmet htor hvn hv0 t η
      have hγfull : ContMDiff 𝓘(ℝ) I ∞ (tcPray (cov := cov) hmet q v t) :=
        Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet
          (tcGam (cov := cov) hmet q v t) hw0'
      exact Submission.JacobiGlobal.smoothAlongAt_of_isJacobiAt (cov := cov) htor hJ
        hγfull.contMDiffOn)
  rw [covAlong_congr_curve
    (γ₁ := fun s : ℝ => tcPray (cov := cov) hmet q v t (t - s))
    (γ₂ := tcGam (cov := cov) hmet q v)
    (by funext s; exact hpt s)
    (fun s => rfl) σ] at htr
  rw [hpt σ] at hshape
  have htr' : Submission.JacobiGlobal.covAlong cov
      (γ := tcPray (cov := cov) hmet q v t) (tcPrayFld (cov := cov) hmet q v t η) (t - σ)
      = - Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v)
        (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) σ := by
    rw [htr]
    simp
  rw [htr'] at hshape
  rw [show (-(Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v)
        (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) σ))
      = (-1 : ℝ) • (Submission.JacobiGlobal.covAlong cov
        (γ := tcGam (cov := cov) hmet q v)
        (fun s : ℝ => tcPrayFld (cov := cov) hmet q v t η (t - s)) σ) from
    (neg_one_smul ℝ _).symm, tcIn_smul_left] at hshape
  linarith [hshape]

end Work.Diff.C.geoCrux
