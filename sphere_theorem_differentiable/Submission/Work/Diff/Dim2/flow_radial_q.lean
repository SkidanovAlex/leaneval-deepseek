import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.ConjEnergy

set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-! ## A bridge between the `curveVelocity` and the `IsMIntegralCurve` formulations

The seeded library states its ODE facts with `curveVelocity` (`= mfderiv γ t 1`), while Mathlib's
uniqueness theorem for integral curves is stated for `IsMIntegralCurveOn`.  The two match exactly
once the derivative is known to exist (a continuous linear map `ℝ →L T` is determined by its value
at `1`), which is what this lemma records. -/

private lemma isMIntegralCurveOn_of_curveVelocity_eq
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

theorem flow_radial_q
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {Φq : M → TangentSpace I q} {v ρ γ : ℝ}
    (hρ0 : 0 < ρ) (h0γ : 0 < γ) (hγρ : 3 * γ / 2 < ρ) (hρv : ρ ≤ v)
    (hsmΦq : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y)
    (hsm : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hnorm : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
      Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖)
    (hround : ∀ w : TangentSpace I q, ‖w‖ < ρ →
      Φq (Submission.GlobalExp.GExp (cov := cov) hmet q w) = w)
    (hray : ∀ (w : TangentSpace I q) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < ρ →
      Work.Diff.C.rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • w)) = t)
    (hrayv : ∀ (w : TangentSpace I q) (t : ℝ), ‖w‖ = 1 → 0 < t → t < ρ →
      curveVelocity (I := I) (fun s : ℝ =>
          Submission.GlobalExp.GExp (cov := cov) hmet q (s • w)) t =
        Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • w)))
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hval : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y) :
    (∀ x : M, γ / 2 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 4 →
      Φ 0 (Work.Diff.C.rdist (I := I) (M := M) q x - γ / 2) x =
        Submission.GlobalExp.GExp (cov := cov) hmet q
          ((γ / 2) • ((Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • Φq x))) ∧
    (∀ x : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 →
      mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q))
        (fun z : M => (Work.Diff.C.rdist (I := I) (M := M) q z)⁻¹ • Φq z) x (V x) = 0) := by
  classical
  constructor
  · -- ## Part 1: the flow line of `V = -∇d(q,·)` runs along the geodesic ray through `x`
    intro x hx1 hx2
    set t : ℝ := Work.Diff.C.rdist (I := I) (M := M) q x with ht
    have htpos : 0 < t := by rw [ht]; linarith only [hx1, h0γ]
    have ht3 : t ≤ 3 * γ / 4 := by rw [ht]; exact hx2
    have htρ : t < ρ := by linarith only [hγρ, ht3, h0γ]
    have htv : t < v := lt_of_lt_of_le htρ hρv
    obtain ⟨vv, hvGExp, hved⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q x
    have hvnorm : ‖vv‖ = t := by
      have h1 : (Manifold.riemannianEDist I q x).toReal = ‖vv‖ := by
        rw [hved, ENNReal.toReal_ofReal (norm_nonneg vv)]
      rw [← h1]
      exact ht.symm
    have hΦx : Φq x = vv := by
      have hρ' : ‖vv‖ < ρ := by rw [hvnorm]; exact htρ
      have hh := hround vv hρ'
      rwa [hvGExp] at hh
    have hΦnorm : ‖Φq x‖ = t := by
      have h := hnorm x (by rw [← ht]; exact htv)
      rw [← ht] at h
      exact h.symm
    set w : TangentSpace I q := t⁻¹ • Φq x with hw
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), hΦnorm]
      field_simp
    have hwne : w ≠ 0 := by
      intro h0
      have h := hwnorm
      rw [h0, norm_zero] at h
      exact one_ne_zero h.symm
    have hwt : t • w = vv := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul, hΦx]
    have hGExpw : Submission.GlobalExp.GExp (cov := cov) hmet q (t • w) = x := by
      rw [hwt]; exact hvGExp
    set Ξ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • w) with hΞ
    set Ξr : ℝ → M := fun s : ℝ => Ξ ((-1) * s + t) with hΞr
    have hΞsm : ContMDiff 𝓘(ℝ,ℝ) I ∞ Ξ :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hwne
    have hΞrsm : ContMDiff 𝓘(ℝ,ℝ) I ∞ Ξr := by
      have haff : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => (-1) * s + t) :=
        ((contMDiff_const (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,ℝ)) (n := ∞) (c := (-1 : ℝ))).mul
          contMDiff_id).add (contMDiff_const (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,ℝ)) (n := ∞) (c := t))
      have h := hΞsm.comp haff
      rw [hΞr]
      exact h
    set d : ℝ := min ρ (5 * γ / 2) with hd
    set J : Set ℝ := Set.Ioo (t - d) (t - γ / 4) with hJ
    have htd : t < d := by rw [hd]; exact lt_min htρ (by linarith only [ht3, h0γ])
    have hγ2d : γ / 2 < d := by
      rw [hd]; exact lt_min (by linarith only [hγρ, h0γ]) (by linarith only [h0γ])
    have hγ4t : γ / 4 < t := by linarith only [hx1, ht, h0γ]
    have h0mem : (0 : ℝ) ∈ J := by
      rw [hJ]
      exact ⟨by linarith only [htd], by linarith only [hγ4t]⟩
    have hmem2 : t - γ / 2 ∈ J := by
      rw [hJ]
      exact ⟨by linarith only [hγ2d], by linarith only [h0γ]⟩
    have hvel : ∀ τ ∈ J, curveVelocity (I := I) Ξr τ = V (Ξr τ) := by
      intro τ hτ
      change curveVelocity (I := I) (fun s : ℝ => Ξ ((-1) * s + t)) τ = V (Ξ ((-1) * τ + t))
      rw [hJ] at hτ
      obtain ⟨hτ1, hτ2⟩ := hτ
      have hs1 : γ / 4 < t - τ := by linarith only [hτ2]
      have hs2 : t - τ < d := by linarith only [hτ1]
      have hspos : 0 < t - τ := by linarith only [hs1, h0γ]
      have hsρ : t - τ < ρ := lt_of_lt_of_le hs2 (by rw [hd]; exact min_le_left _ _)
      have hs5 : t - τ ≤ 5 * γ / 2 :=
        le_of_lt (lt_of_lt_of_le hs2 (by rw [hd]; exact min_le_right _ _))
      have harg : (-1 : ℝ) * τ + t = t - τ := by ring
      have hmd : MDifferentiableAt 𝓘(ℝ,ℝ) I Ξ ((-1) * τ + t) :=
        (hΞsm _).mdifferentiableAt (by simp)
      have hcv := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := Ξ) (c := -1)
        (d := t) (t := τ) hmd
      have hrayv' : curveVelocity (I := I) Ξ (t - τ) =
          Work.Diff.C.rgrad (I := I) (M := M)
            (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (Ξ (t - τ)) :=
        hrayv w (t - τ) hwnorm hspos hsρ
      have hraypt : Work.Diff.C.rdist (I := I) (M := M) q (Ξ (t - τ)) = t - τ :=
        hray w (t - τ) hwnorm (le_of_lt hspos) hsρ
      have hval' : V (Ξ (t - τ)) = - Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (Ξ (t - τ)) :=
        hval (Ξ (t - τ)) (by rw [hraypt]; linarith only [hs1])
          (by rw [hraypt]; linarith only [hs1, hs5])
      rw [hcv, harg, hrayv', hval']
      rw [neg_smul, one_smul]
    have hΞon : IsMIntegralCurveOn Ξr V J :=
      isMIntegralCurveOn_of_curveVelocity_eq
        (v := V) (γ := Ξr) (s := J)
        (fun τ hτ => (hΞrsm τ).mdifferentiableAt (by simp)) hvel
    have hγon : IsMIntegralCurveOn (fun τ : ℝ => Φ 0 τ x) V J :=
      IsMIntegralCurve.isMIntegralCurveOn (γ := fun τ : ℝ => Φ 0 τ x) (v := V)
        (fun τ : ℝ => hΦderiv 0 τ x) J
    have hv : ContMDiff I I.tangent 1
        (fun y : M => (⟨y, V y⟩ : TangentBundle I M)) := hVsm.of_le (by simp)
    have h0 : (fun τ : ℝ => Φ 0 τ x) 0 = Ξr 0 := by
      rw [hΞr]
      show Φ 0 0 x = Ξ ((-1) * 0 + t)
      rw [hΦself, show (-1) * 0 + t = t by ring]
      show x = Submission.GlobalExp.GExp (cov := cov) hmet q (t • w)
      exact hGExpw.symm
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (I := I) (M := M)
      (t₀ := 0) (a := t - d) (b := t - γ / 4) (γ := fun τ : ℝ => Φ 0 τ x) (γ' := Ξr) (v := V)
      h0mem hv hγon hΞon h0
    have hfin : Φ 0 (t - γ / 2) x = Ξr (t - γ / 2) := heq hmem2
    show Φ 0 (Work.Diff.C.rdist (I := I) (M := M) q x - γ / 2) x =
      Submission.GlobalExp.GExp (cov := cov) hmet q
        ((γ / 2) • ((Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • Φq x))
    rw [← ht]
    rw [hfin, hΞr]
    show Ξ ((-1) * (t - γ / 2) + t) =
      Submission.GlobalExp.GExp (cov := cov) hmet q ((γ / 2) • (t⁻¹ • Φq x))
    rw [show (-1) * (t - γ / 2) + t = γ / 2 by ring]
  · -- ## Part 2: the unit direction `Φq · / d(q,·)` is constant along `V`
    intro x hx1 hx2
    set t : ℝ := Work.Diff.C.rdist (I := I) (M := M) q x with ht
    have htpos : 0 < t := by rw [ht]; linarith only [hx1, h0γ]
    have htρ : t < ρ := by rw [ht]; linarith only [hx2, hγρ]
    have htv : t < v := lt_of_lt_of_le htρ hρv
    obtain ⟨vv, hvGExp, hved⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q x
    have hvnorm : ‖vv‖ = t := by
      have h1 : (Manifold.riemannianEDist I q x).toReal = ‖vv‖ := by
        rw [hved, ENNReal.toReal_ofReal (norm_nonneg vv)]
      rw [← h1]
      exact ht.symm
    have hΦx : Φq x = vv := by
      have hρ' : ‖vv‖ < ρ := by rw [hvnorm]; exact htρ
      have hh := hround vv hρ'
      rwa [hvGExp] at hh
    have hΦnorm : ‖Φq x‖ = t := by
      have h := hnorm x (by rw [← ht]; exact htv)
      rw [← ht] at h
      exact h.symm
    set w : TangentSpace I q := t⁻¹ • Φq x with hw
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), hΦnorm]
      field_simp
    have hwne : w ≠ 0 := by
      intro h0
      have h := hwnorm
      rw [h0, norm_zero] at h
      exact one_ne_zero h.symm
    have hwt : t • w = vv := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul, hΦx]
    have hGExpw : Submission.GlobalExp.GExp (cov := cov) hmet q (t • w) = x := by
      rw [hwt]; exact hvGExp
    set Ξ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • w) with hΞ
    have hΞsm : ContMDiff 𝓘(ℝ,ℝ) I ∞ Ξ :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hwne
    have hΞmd : MDifferentiableAt 𝓘(ℝ,ℝ) I Ξ t := (hΞsm t).mdifferentiableAt (by simp)
    have hΞt : Ξ t = x := by rw [hΞ]; exact hGExpw
    set F : M → TangentSpace I q :=
      fun z : M => (Work.Diff.C.rdist (I := I) (M := M) q z)⁻¹ • Φq z with hF
    have hFsm : ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ F x := by
      have h1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
          (fun z : M => (Work.Diff.C.rdist (I := I) (M := M) q z)⁻¹) x :=
        (hsm x (by rw [← ht]; exact htpos) (by rw [← ht]; exact htv)).inv₀
          (by rw [← ht]; exact ne_of_gt htpos)
      exact h1.smul (hsmΦq x (by rw [← ht]; exact htv))
    have hFmd : MDifferentiableAt I (modelWithCornersSelf ℝ (TangentSpace I q)) F x :=
      hFsm.mdifferentiableAt (by simp)
    have hEv : (fun s : ℝ => F (Ξ s)) =ᶠ[𝓝 t] (fun _ : ℝ => w) := by
      have hmem : Set.Ioo (γ / 8) ρ ∈ 𝓝 t :=
        Ioo_mem_nhds (by linarith only [hx1, ht, h0γ]) htρ
      filter_upwards [hmem] with s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hs0 : 0 < s := by linarith only [hs1, h0γ]
      have h1 : ‖s • w‖ < ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hwnorm, mul_one]
        exact hs2
      have h2 : Work.Diff.C.rdist (I := I) (M := M) q (Ξ s) = s := by
        rw [hΞ]; exact hray w s hwnorm (le_of_lt hs0) hs2
      have h3 : Φq (Ξ s) = s • w := by
        rw [hΞ]; exact hround (s • w) h1
      rw [hF]
      show (Work.Diff.C.rdist (I := I) (M := M) q (Ξ s))⁻¹ • Φq (Ξ s) = w
      rw [h2, h3, inv_smul_smul₀ (ne_of_gt hs0)]
    have hderiv0 : deriv (fun s : ℝ => F (Ξ s)) t = 0 := by
      rw [hEv.deriv_eq, deriv_const]
    have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := F) (γ := Ξ) (t := t) (by rw [hΞt]; exact hFmd) hΞmd
    have hcvΞ : (mfderiv 𝓘(ℝ,ℝ) I Ξ t) (1 : ℝ) =
        Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (Ξ t) := by
      rw [hΞ]
      rw [show (mfderiv 𝓘(ℝ,ℝ) I
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • w)) t) (1 : ℝ) =
          Work.Diff.C.rgrad (I := I) (M := M)
            (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • w)) from by
        rw [← curveVelocity_apply]
        exact hrayv w t hwnorm htpos htρ]
    have h3 : mvfderiv I F (Ξ t) ((mfderiv 𝓘(ℝ,ℝ) I Ξ t) 1) = 0 := hchain.trans hderiv0
    have h4 : (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) F x)
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x) = 0 := by
      rw [← hΞt, ← hcvΞ]
      exact h3
    have hVx : V x = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x :=
      hval x hx1 (by linarith only [hx2, h0γ])
    show (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) F x) (V x) = 0
    calc (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) F x) (V x)
        = (mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) F x)
            (-(Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x)) := by rw [hVx]
      _ = -((mfderiv I (modelWithCornersSelf ℝ (TangentSpace I q)) F x)
            (Work.Diff.C.rgrad (I := I) (M := M)
              (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x)) := by
            rw [map_neg]
      _ = 0 := by rw [h4]; exact neg_zero

end Work.Diff.Dim2
