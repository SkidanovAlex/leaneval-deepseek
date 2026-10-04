import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.fcos_lipschitz
import Submission.HingeKey
import Submission.HopfRinow2
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option backward.isDefEq.respectTransparency false

/-- **Eikonal equation for the distance function (unit gradient).**  At a point `x ≠ q` where
`d(q,·)` is smooth, the gradient of the distance is a unit vector: `⟪∇d, ∇d⟫ = 1`.
(`d` is 1-Lipschitz so `|∇d| ≤ 1`; along a minimising geodesic from `q` to `x` the distance grows
at unit speed, so `|∇d| ≥ 1`.) -/
theorem rgrad_rdist_eikonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [CompactSpace M] [PathConnectedSpace M] [Nontrivial E]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} (hx : rdist (I := I) (M := M) q x ≠ 0)
    (hsm : CMDiffAt ∞ (fun y : M => rdist (I := I) (M := M) q y) x) :
    Inner.inner ℝ (rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) q y) x)
      (rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) q y) x) = 1 := by
  classical

  set F : M → ℝ := fun y : M => rdist (I := I) (M := M) q y with hFdef
  have hFsm : CMDiffAt ∞ F x := hsm
  have hFd : MDiffAt F x := hFsm.mdifferentiableAt (by decide)
  have hdelta : 0 < Submission.GlobalExp.geodDelta (cov := cov) hmet :=
    Submission.GlobalExp.geodDelta_pos (cov := cov) hmet
  have hlip_rdist : ∀ a b : M,
      |rdist (I := I) (M := M) q b - rdist (I := I) (M := M) q a|
        ≤ rdist (I := I) (M := M) a b :=
    fun a b => rdist_lipschitz (I := I) (M := M) (cov := cov) hmet htor q a b
  -- ## Part A : `|∇d| ≤ 1`
  have hbound_unit : ∀ w : TangentSpace I x, ‖w‖ = 1 → |mvfderiv I F x w| ≤ 1 := by
    intro w hw
    let G : ℝ → M := Submission.GlobalExp.geodCurve (cov := cov) hmet 1 (by norm_num) x w hw
    have hspec := Submission.GlobalExp.geodCurve_spec (cov := cov) hmet (1 : ℝ) (by norm_num) x w hw
    have hG0 : G 0 = x := hspec.1
    have hv0 : Submission.Geodesic.curveVelocity (I := I) G 0 = w := hspec.2.1
    have hGsm : ContMDiffOn 𝓘(ℝ) I ∞ G
        (Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
          (1 + Submission.GlobalExp.geodDelta (cov := cov) hmet)) := hspec.2.2.1
    have hvel : ∀ t ∈ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (1 + Submission.GlobalExp.geodDelta (cov := cov) hmet),
        ‖Submission.Geodesic.curveVelocity (I := I) G t‖ = 1 := hspec.2.2.2.2
    have hlip_phi : LipschitzOnWith 1 (fun t : ℝ => F (G t))
        (Icc (-(Submission.GlobalExp.geodDelta (cov := cov) hmet) / 2)
          (Submission.GlobalExp.geodDelta (cov := cov) hmet / 2)) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro t ht u hu
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      have htb : -(Submission.GlobalExp.geodDelta (cov := cov) hmet) < t := by
        linarith [ht.1, hdelta]
      have hte : t < 1 + Submission.GlobalExp.geodDelta (cov := cov) hmet := by
        linarith [ht.2, hdelta]
      have hub : -(Submission.GlobalExp.geodDelta (cov := cov) hmet) < u := by
        linarith [hu.1, hdelta]
      have hue : u < 1 + Submission.GlobalExp.geodDelta (cov := cov) hmet := by
        linarith [hu.2, hdelta]
      have hd : Manifold.riemannianEDist I (G u) (G t) ≤ ENNReal.ofReal |u - t| := by
        rcases le_total t u with hle | hle
        · have hsub : Icc t u ⊆ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
              (1 + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
            fun r hr => ⟨by linarith [hr.1, htb], by linarith [hr.2, hue]⟩
          have hγ : ContMDiffOn 𝓘(ℝ) I 1 G (Icc t u) := (hGsm.mono hsub).of_le (by decide)
          have hlen := Submission.HopfRinow.pathELength_of_unit_speed (I := I) (γ := G)
            (a := t) (b := u) (fun r hr => hvel r (hsub hr))
          calc Manifold.riemannianEDist I (G u) (G t)
              = Manifold.riemannianEDist I (G t) (G u) :=
                Manifold.riemannianEDist_comm (I := I) (x := G u) (y := G t)
            _ ≤ Manifold.pathELength I G t u :=
                Manifold.riemannianEDist_le_pathELength (I := I) (x := G t) (y := G u)
                  (a := t) (b := u) (γ := G) hγ rfl rfl hle
            _ = ENNReal.ofReal |u - t| := by
                rw [hlen]
                congr 1
                rw [abs_of_nonneg (by linarith)]
        · have hsub : Icc u t ⊆ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
              (1 + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
            fun r hr => ⟨by linarith [hr.1, hub], by linarith [hr.2, hte]⟩
          have hγ : ContMDiffOn 𝓘(ℝ) I 1 G (Icc u t) := (hGsm.mono hsub).of_le (by decide)
          have hlen := Submission.HopfRinow.pathELength_of_unit_speed (I := I) (γ := G)
            (a := u) (b := t) (fun r hr => hvel r (hsub hr))
          calc Manifold.riemannianEDist I (G u) (G t)
              ≤ Manifold.pathELength I G u t :=
                Manifold.riemannianEDist_le_pathELength (I := I) (x := G u) (y := G t)
                  (a := u) (b := t) (γ := G) hγ rfl rfl hle
            _ = ENNReal.ofReal |u - t| := by
                rw [hlen]
                congr 1
                rw [abs_of_nonpos (by linarith), neg_sub]
      have h1 : |F (G t) - F (G u)| ≤ rdist (I := I) (M := M) (G u) (G t) :=
        hlip_rdist (G u) (G t)
      have h2 : rdist (I := I) (M := M) (G u) (G t) ≤ |t - u| := by
        rw [Work.Diff.C.rdist]
        calc (Manifold.riemannianEDist I (G u) (G t)).toReal
            ≤ (ENNReal.ofReal |u - t|).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
          _ = |u - t| := ENNReal.toReal_ofReal (abs_nonneg _)
          _ = |t - u| := abs_sub_comm _ _
      linarith
    have hderiv_le : |deriv (fun t : ℝ => F (G t)) 0| ≤ 1 := by
      have hmem : Icc (-(Submission.GlobalExp.geodDelta (cov := cov) hmet) / 2)
          (Submission.GlobalExp.geodDelta (cov := cov) hmet / 2) ∈ 𝓝 (0 : ℝ) :=
        Icc_mem_nhds (by linarith [hdelta]) (by linarith [hdelta])
      have h := norm_deriv_le_of_lipschitzOn (𝕜 := ℝ) (f := fun t : ℝ => F (G t))
        (x₀ := 0) hmem hlip_phi
      simpa [Real.norm_eq_abs] using h
    have hchain : deriv (fun t : ℝ => F (G t)) 0 = mvfderiv I F x w := by
      have h0mem : (0 : ℝ) ∈ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
          (1 + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
        ⟨by linarith [hdelta], by linarith [hdelta]⟩
      have hGd : MDiffAt G 0 := (hGsm.contMDiffAt (isOpen_Ioo.mem_nhds h0mem)).mdifferentiableAt
        (by decide)
      have hFd' : MDiffAt F (G 0) := by rw [hG0]; exact hFd
      have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F)
        (γ := G) (t := 0) hFd' hGd
      have hv0' : (mfderiv 𝓘(ℝ) I G 0) 1 = w := by
        rw [← Submission.Geodesic.curveVelocity_apply]; exact hv0
      rw [hv0', hG0] at h
      exact h.symm
    rw [hchain] at hderiv_le
    exact hderiv_le
  have hbound : ∀ v : TangentSpace I x, |mvfderiv I F x v| ≤ ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]; simp
    · have hu := hbound_unit (Submission.GlobalExp.unitOf v hv)
        (Submission.GlobalExp.unitOf_norm v hv)
      have hdec : v = ‖v‖ • Submission.GlobalExp.unitOf v hv := by
        rw [Submission.GlobalExp.unitOf, smul_smul, mul_comm,
          inv_mul_cancel₀ (by simpa [norm_eq_zero] using hv), one_smul]
      conv_lhs => rw [hdec]
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg v)]
      exact mul_le_of_le_one_right (norm_nonneg v) hu
  set g : TangentSpace I x := rgrad (I := I) (M := M) F x with hgdef
  have hnorm_le : ‖g‖ ≤ 1 := by
    have h1 := hbound g
    have h4 : Inner.inner ℝ g g = mvfderiv I F x g := by
      rw [hgdef]
      exact inner_rgrad (I := I) (M := M) F x (rgrad (I := I) (M := M) F x)
    have h2 : mvfderiv I F x g = ‖g‖ ^ 2 := by
      rw [← h4, real_inner_self_eq_norm_sq]
    rw [h2, abs_of_nonneg (sq_nonneg _)] at h1
    nlinarith [h1, norm_nonneg g]
  -- ## Part B : `|∇d| ≥ 1`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q x
  have hs_eq : rdist (I := I) (M := M) q x = ‖v‖ := by
    rw [Work.Diff.C.rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hs_ne : ‖v‖ ≠ 0 := by rw [← hs_eq]; exact hx
  have hv_ne : v ≠ 0 := fun h => hs_ne (by rw [h, norm_zero])
  have hs_pos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hs_ne)
  set ξ : TangentSpace I q := Submission.GlobalExp.unitOf v hv_ne with hξdef
  have hξ : ‖ξ‖ = 1 := Submission.GlobalExp.unitOf_norm v hv_ne
  have hsξ : ‖v‖ • ξ = v := by
    rw [hξdef, Submission.GlobalExp.unitOf, smul_smul, mul_comm,
      inv_mul_cancel₀ hs_ne, one_smul]
  let G : ℝ → M :=
    Submission.GlobalExp.geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) q ξ hξ
  have hspecB := Submission.GlobalExp.geodCurve_spec (cov := cov) hmet ‖v‖ (norm_nonneg v) q ξ hξ
  have hG0 : G 0 = q := hspecB.1
  have hGs : G ‖v‖ = x := by
    have h := Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet (x := q) hξ
      (T := ‖v‖) (norm_nonneg v) (r := ‖v‖) (norm_nonneg v) le_rfl
    rw [hsξ] at h
    change Submission.GlobalExp.geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) q ξ hξ ‖v‖ = x
    rw [← h]; exact hvG
  subst hGs
  have hvelB : ‖Submission.Geodesic.curveVelocity (I := I) G ‖v‖‖ = 1 := by
    have hmem : ‖v‖ ∈ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (‖v‖ + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
      ⟨by linarith [hdelta], by linarith [hdelta]⟩
    exact hspecB.2.2.2.2 ‖v‖ hmem
  have hGdB : MDiffAt G ‖v‖ := by
    have hmem : ‖v‖ ∈ Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (‖v‖ + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
      ⟨by linarith [hdelta], by linarith [hdelta]⟩
    exact (hspecB.2.2.1.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).mdifferentiableAt (by decide)
  have hminB : Manifold.riemannianEDist I q (G ‖v‖) = ENNReal.ofReal ‖v‖ := hvd
  have hsub := Submission.HingeKey.geodCurve_sub_arc_minimising' (I := I) (cov := cov) hmet
    (T := ‖v‖) (norm_nonneg v) hξ (s := ‖v‖) (norm_nonneg v) le_rfl hminB
  have hpsi : ∀ t ∈ Icc (0 : ℝ) ‖v‖, F (G t) = t := by
    intro t ht
    have h := hsub 0 ⟨le_refl (0 : ℝ), norm_nonneg v⟩ t ⟨ht.1, ht.2⟩ ht.1
    rw [hspecB.1, sub_zero] at h
    change rdist (I := I) (M := M) q
      (Submission.GlobalExp.geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) q ξ hξ t) = t
    rw [Work.Diff.C.rdist, h, ENNReal.toReal_ofReal ht.1]
  have hpsi_diff : DifferentiableAt ℝ (fun t : ℝ => F (G t)) ‖v‖ :=
    (hFd.comp ‖v‖ hGdB).differentiableAt
  have hderiv_one : deriv (fun t : ℝ => F (G t)) ‖v‖ = 1 := by
    have h1 : HasDerivWithinAt (fun t : ℝ => F (G t)) 1 (Iic ‖v‖) ‖v‖ := by
      refine (hasDerivWithinAt_id ‖v‖ (Iic ‖v‖)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          (nhdsWithin_le_nhds (Ioi_mem_nhds (show ‖v‖ / 2 < ‖v‖ by linarith)))] with t hts ht
        exact hpsi t ⟨le_of_lt (lt_trans (by linarith) ht), hts⟩
      · exact hpsi ‖v‖ ⟨norm_nonneg v, le_rfl⟩
    have h2 : HasDerivWithinAt (fun t : ℝ => F (G t))
        (deriv (fun t : ℝ => F (G t)) ‖v‖) (Iic ‖v‖) ‖v‖ :=
      hpsi_diff.hasDerivAt.hasDerivWithinAt
    have e1 := h1.derivWithin (uniqueDiffWithinAt_Iic ‖v‖)
    have e2 := h2.derivWithin (uniqueDiffWithinAt_Iic ‖v‖)
    rw [← e2]; exact e1
  have hchainB : deriv (fun t : ℝ => F (G t)) ‖v‖
      = mvfderiv I F (G ‖v‖) (Submission.Geodesic.curveVelocity (I := I) G ‖v‖) := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F)
      (γ := G) (t := ‖v‖) hFd hGdB
    rw [show F ∘ G = (fun t : ℝ => F (G t)) from rfl] at h
    rw [Submission.Geodesic.curveVelocity_apply]
    exact h.symm
  have hvel_eq : mvfderiv I F (G ‖v‖)
      (Submission.Geodesic.curveVelocity (I := I) G ‖v‖) = 1 := by
    rw [← hchainB]; exact hderiv_one
  have hinner : Inner.inner ℝ g (Submission.Geodesic.curveVelocity (I := I) G ‖v‖) = 1 := by
    rw [hgdef, inner_rgrad (I := I) (M := M) F (G ‖v‖)
      (Submission.Geodesic.curveVelocity (I := I) G ‖v‖)]
    exact hvel_eq
  have hge_one : 1 ≤ ‖g‖ := by
    have hcs := real_inner_le_norm g (Submission.Geodesic.curveVelocity (I := I) G ‖v‖)
    rw [hinner, hvelB, mul_one] at hcs
    exact hcs
  have hnorm_eq : ‖g‖ = 1 := le_antisymm hnorm_le hge_one
  rw [real_inner_self_eq_norm_sq, hnorm_eq]
  norm_num

end Work.Diff.C
