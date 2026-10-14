import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.intervalIntegrable_vortLInf_ansatzV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology NNReal

/-- **The `L^∞`-in-space norm of the vorticity of the ansatz is the closed-ball supremum of
`‖solVort‖`**: on the pre-window the vorticity of `ansatzV P = BS(solVort P · )` is `solVort P · `
(`vorticity_ansatzV`), which is supported in `B(0,R)` (`solVort_supp`) and bounded by
`M / λ̄(t)` (`solVort_bdd`). -/
theorem vortLInf_ansatzV_eq_ciSup_closedBall {α : NNReal} (P : ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ s ∈ preWindow P.T,
      Work.LWP.vortLInf (ansatzV P) s
        = ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖ := by
  intro s hs
  rw [Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall
    (u := ansatzV P) (R := P.R) (t := s) (M := P.M / P.lam s) P.hR ?_ ?_]
  · simp_rw [vorticity_ansatzV P hlaw s hs]
  · intro x
    rw [show FiniteTimeSingularity.vorticity (ansatzV P · s) x = solVort P x s from
      vorticity_ansatzV P hlaw s hs x]
    rw [le_div_iff₀ (P.hlam s hs), mul_comm]
    exact solVort_bdd P s hs x
  · intro x hx
    exact solVort_supp P s x (by
      intro h0
      exact hx (by
        rw [show FiniteTimeSingularity.vorticity (ansatzV P · s) x = solVort P x s from
          vorticity_ansatzV P hlaw s hs x]
        exact h0))

/-- **Continuity of the closed-ball supremum of `‖solVort‖`** on any time interval contained in
the pre-window: it is a jointly continuous family (`solVort_cont` on the core region `B(0,R+1)`)
supremised over the *compact* ball `B(0,R)`
(`Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall`). -/
theorem continuousOn_ciSup_solVort_closedBall {α : NNReal} (P : ProfileData α) {a b : ℝ}
    (hab : Set.Icc a b ⊆ preWindow P.T) :
    ContinuousOn (fun s => ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖)
      (Set.Icc a b) := by
  refine Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall
    (F := fun x s => ‖solVort P x s‖) (R := P.R) (a := a) (b := b) P.hR ?_
  refine (solVort_cont P).norm.mono ?_
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  refine ⟨?_, hab hs⟩
  have hx' : ‖x‖ ≤ P.R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  rw [Work.StabilityFar.mem_coreRegion]
  linarith

/-- **The vorticity sup-norm of the ansatz is interval integrable on `[0,t]` for `t < T`**:
on `[0,t]` it coincides with the closed-ball supremum of `‖solVort‖`, which is continuous there
(hence interval integrable). -/
theorem intervalIntegrable_vortLInf_ansatzV {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Set.Ico 0 P.T,
      IntervalIntegrable (Work.LWP.vortLInf (Work.ConstructionInstance.ansatzV P))
        MeasureTheory.volume 0 t := by
  intro t ht
  have hsub : Set.Icc 0 t ⊆ preWindow P.T :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
  have hcont : ContinuousOn (fun s => ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖)
      (Set.Icc 0 t) :=
    continuousOn_ciSup_solVort_closedBall P hsub
  have hcont' : ContinuousOn (Work.LWP.vortLInf (ansatzV P)) (Set.Icc 0 t) :=
    hcont.congr fun s hs =>
      vortLInf_ansatzV_eq_ciSup_closedBall P hlaw s (hsub hs)
  refine (hcont'.mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le ht.1]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Real Topology
open FiniteTimeSingularity

namespace Work.ConstructionInstance

/-! ## The slice lemma: `∂ₜ(∂ₜω)` on the self-similar ansatz -/

/-- **The second time derivative of the constructed (cut) self-similar vorticity.**

For the cut field `ω = selfSimVort p g L lam`, and at a time `t` of the half-window
`preWindow T = (-2,T)`:

* every time slice `s ↦ ∂ₜω(y,s)` is differentiable at `t`, with derivative `∂ₜ²ω(y,t)`
  (the second-order chain rule for `s ↦ λ̄(s)⁻¹·F(c/λ̄(s))`, `hasDerivAt_inv_mul_comp2`; on the
  symmetry axis `radial y = 0` the field vanishes identically);
* and the second derivative obeys the box

  `‖∂ₜ²ω(y,t)‖ ≤ K₂(20p+Cg+Cg')/m² + K²(2(5p+Cg')+Cg'')/m³ + 2K²(20p+Cg+Cg')/m³`

  for every `m` with `0 < m ≤ λ̄(t)` (the weighted boxes of the profile and of `λ̄`).

The hypotheses on `g` are exactly the `St1` data of `ProfileData`: the box `|g| ≤ Cg`, the weighted
first derivative box `|z∂_z g| ≤ Cg'`, the weighted second derivative box `|z²∂_z²F| ≤ Cg''` of
the *full* profile, and the two differentiability clauses. -/
theorem timeDeriv_timeDeriv_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {L : ℝ} {lam : ℝ → ℝ} {T m : ℝ} {Cg Cg' Cg'' K K₂ : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ| ≤ Cg'')
    (hgdiff : ∀ z θ : ℝ, 0 < z → HasDerivAt (fun z' => profile p g z' θ)
      (Work.Spaces.pz (profile p g) z θ) z)
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (profile p g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ) z)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamdif2 : ∀ t ∈ preWindow T, HasDerivAt (deriv lam) (deriv (deriv lam) t) t)
    (hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K)
    (hlamd2 : ∀ t ∈ preWindow T, |deriv (deriv lam) t| ≤ K₂)
    (hK : 0 ≤ K) (hK₂ : 0 ≤ K₂)
    {t : ℝ} (ht : t ∈ preWindow T) (hm : 0 < m) (hmle : m ≤ lam t) (y : R3) :
    HasDerivAt (fun s => timeDeriv (selfSimVort p g L lam) y s)
      (timeDeriv (timeDeriv (selfSimVort p g L lam)) y t) t ∧
    ‖timeDeriv (timeDeriv (selfSimVort p g L lam)) y t‖
      ≤ K₂ * (20 * p + Cg + Cg') / m ^ 2 + K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3
        + 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 := by
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂' : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 t ht)
  have hpne : p ≠ 0 := ne_of_gt hp
  set Λ : ℝ := K₂ * (20 * p + Cg + Cg') / m ^ 2 + K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3
      + 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * p + Cg + Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂' (by linarith)) (by positivity)
    have h2 : 0 ≤ K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 := by positivity
    linarith
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => (0 : R3) := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    have htd : timeDeriv (selfSimVort p g L lam) y = fun _ => (0 : R3) := by
      funext s
      rw [FiniteTimeSingularity.timeDeriv, hω0]
      exact deriv_const s 0
    have h0 : timeDeriv (timeDeriv (selfSimVort p g L lam)) y t = 0 := by
      rw [FiniteTimeSingularity.timeDeriv, htd]
      simp
    refine ⟨?_, ?_⟩
    · rw [htd, h0]
      exact hasDerivAt_const t 0
    · rw [h0, norm_zero]
      exact hΛ
  · -- off the axis: `ω(y,·) = (a · Φ) • e` with `Φ(s) = λ̄(s)⁻¹ F(c/λ̄(s))`
    have hy : y ≠ 0 := by
      intro h0; exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have ha0 : 0 ≤ a := by rw [ha]; exact Work.Stability.chi_nonneg _
    have ha1 : |a| ≤ 1 := by rw [abs_of_nonneg ha0, ha]; exact Work.Stability.chi_le_one _
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hlt : 0 < lam t := hlam t ht
    have hne : lam t ≠ 0 := ne_of_gt hlt
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    have hθabs : |θ| ≤ Real.pi / 2 := by
      rw [hθdef, abs_le]
      exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    -- the three weighted boxes of the profile
    have hGbd : |profile p g (c / lam t) θ + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ|
        ≤ 20 * p + Cg + Cg' :=
      profile_add_z_pz_abs_le hp hp1 hgbdd hg2 hgdiff hzpos hθabs
    have hd1 : |(c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ| ≤ 5 * p + Cg' :=
      z_pz_profile_abs_le hp hp1 hg2 hgdiff (c / lam t) θ hzpos hθabs
    have hd2 : |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ|
        ≤ Cg'' :=
      zsq_pz_pz_profile_abs_le hpne hg0 hgdiff2 hg3 (c / lam t) θ hzpos hθabs
    have hddbd : |(c / lam t) * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
        + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)|
        ≤ 2 * (5 * p + Cg') + Cg'' := by
      have hkey : (c / lam t) * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)
          = 2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
            + (c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ := by
        ring
      rw [hkey]
      calc |2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
              + (c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ|
          ≤ |2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)|
              + |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ| :=
            abs_add_le _ _
        _ = 2 * |(c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ|
              + |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ 2 * (5 * p + Cg') + Cg'' := by linarith
    -- the scalar factors of the ansatz, and their first derivatives
    set φ₀ : ℝ → ℝ := fun s => (lam s)⁻¹ * profile p g (c / lam s) θ with hφ0def
    set φ₁ : ℝ → ℝ := fun s => -(deriv lam s * (profile p g (c / lam s) θ
        + c / lam s * Work.Spaces.pz (profile p g) (c / lam s) θ) / (lam s) ^ 2) with hφ1def
    have hφ : ∀ s ∈ preWindow T, HasDerivAt φ₀ (φ₁ s) s := by
      intro s hs
      have hspos : 0 < c / lam s := div_pos hcpos (hlam s hs)
      have h := hasDerivAt_inv_mul_comp (F := fun z => profile p g z θ) (c := c)
        (hlamdif s hs) (ne_of_gt (hlam s hs)) (hgdiff (c / lam s) θ hspos)
      rw [hφ0def, hφ1def]
      exact h
    have hcut : selfSimVort p g L lam y = fun s => (a * φ₀ s) • e := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, ← ha, ← hc, ← hθdef, ← he, hφ0def]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    set X : ℝ := -(deriv (deriv lam) t * (profile p g (c / lam t) θ
          + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2
        + deriv lam t * (-(deriv lam t / lam t) * ((c / lam t)
            * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
              + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)))
            / (lam t) ^ 2
        - 2 * deriv lam t ^ 2 * (profile p g (c / lam t) θ
            + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 3) with hXdef
    have hX : HasDerivAt φ₁ X t := by
      rw [hφ1def, hXdef]
      exact hasDerivAt_inv_mul_comp2 (hlamdif t ht) (hlamdif2 t ht) hne
        (hgdiff (c / lam t) θ hzpos) (hgdiff2 (c / lam t) θ hzpos)
    have hXbd : |X| ≤ Λ := by
      rw [hXdef, hΛdef]
      exact abs_secondDeriv_rescale_le hm hmle hK hK₂ hGbd hddbd (hlamd t ht) (hlamd2 t ht)
    have hΦ : HasDerivAt (fun s => (a * φ₁ s) • e) ((a * X) • e) t :=
      (hX.const_mul a).smul_const e
    -- `∂ₜω(y,·)` agrees near `t` with `a · φ₁ · e`
    have hev : (fun s => timeDeriv (selfSimVort p g L lam) y s) =ᶠ[𝓝 t] (fun s => (a * φ₁ s) • e) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) ?_
      intro s hs
      have h1 : HasDerivAt (fun u => (a * φ₀ u) • e) ((a * φ₁ s) • e) s :=
        ((hφ s hs).const_mul a).smul_const e
      have h2 : timeDeriv (selfSimVort p g L lam) y s = deriv (fun u => (a * φ₀ u) • e) s := by
        rw [FiniteTimeSingularity.timeDeriv]
        exact congrArg (fun f => deriv f s) hcut
      change timeDeriv (selfSimVort p g L lam) y s = (a * φ₁ s) • e
      rw [h2, h1.deriv]
    have hfin : HasDerivAt (fun s => timeDeriv (selfSimVort p g L lam) y s) ((a * X) • e) t :=
      hΦ.congr_of_eventuallyEq hev
    have hderiv : timeDeriv (timeDeriv (selfSimVort p g L lam)) y t = (a * X) • e := by
      rw [FiniteTimeSingularity.timeDeriv]
      exact hfin.deriv
    refine ⟨?_, ?_⟩
    · rw [hderiv]; exact hfin
    · rw [hderiv]
      have hb : ‖(a * X) • e‖ ≤ Λ := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, he, Work.Cyl.norm_eTheta y hrad, mul_one]
        calc |a| * |X| ≤ 1 * |X| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
          _ = |X| := one_mul _
          _ ≤ Λ := hXbd
      exact hb

/-! ## The requested theorem -/

/-- **The time-Hölder regularity of `∂ₜω` from second-order data.**

The residual `SelfSimTimeHolderDeriv P` of finding (H) follows from the second-order profile and
modulation data: `F` twice differentiable in `z` with `|z²∂_z²F| ≤ Cg''` on the quadrant
(`hgdiff2`, `hg3`), and `λ̄` twice differentiable with `|λ̄''| ≤ K₂` on `preWindow T`
(`hlamdif2`, `hlamd2`).

The proof bounds `∂ₜ²ω` on each strip by the slice lemma `timeDeriv_timeDeriv_selfSimVort`
(with `m` the minimum of `λ̄` on the strip, `lam_pos_le_on_window`) and applies the mean value
theorem to `∂ₜω` (`timeHolderOnBall_timeDeriv_of_secondDeriv`). -/
theorem selfSimTimeHolderDeriv_of_secondOrderData {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ) z)
    {Cg'' K₂ : ℝ}
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ| ≤ Cg'')
    (hlamdif2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      HasDerivAt (deriv P.lam) (deriv (deriv P.lam) t) t)
    (hlamd2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      |deriv (deriv P.lam) t| ≤ K₂) :
    Work.ConstructionInstance.SelfSimTimeHolderDeriv P := by
  intro S hS hST
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := le_trans (abs_nonneg _) (bdd_g P 0 0 le_rfl hI0)
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂ : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 0 ⟨by norm_num, P.hT⟩)
  have hsub : Work.StabilityFar.window S ⊆ preWindow P.T := window_subset_preWindow hST
  -- the uniform lower bound of `λ̄` on the strip, and the resulting box `Λ`
  obtain ⟨m, hmpos, hmle⟩ := lam_pos_le_on_window hS hST P.hlam P.hlamdif
  set Λ : ℝ := K₂ * (20 * profExp α + P.Cg + P.Cg') / m ^ 2
      + P.K ^ 2 * (2 * (5 * profExp α + P.Cg') + Cg'') / m ^ 3
      + 2 * P.K ^ 2 * (20 * profExp α + P.Cg + P.Cg') / m ^ 3 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * profExp α + P.Cg + P.Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂ (by linarith)) (by positivity)
    have h2 : 0 ≤ P.K ^ 2 * (2 * (5 * profExp α + P.Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg P.K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * P.K ^ 2 * (20 * profExp α + P.Cg + P.Cg') / m ^ 3 := by positivity
    linarith
  have hdiff : ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
      HasDerivAt (fun t => timeDeriv (solVort P) z t)
        (timeDeriv (timeDeriv (solVort P)) z s) s := by
    intro z _ s hs
    exact (timeDeriv_timeDeriv_selfSimVort (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam P.hlamdif hlamdif2 P.hlamd
      hlamd2 P.hK hK₂ (hsub hs) hmpos (hmle s hs) z).1
  have hbd : ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
      ‖timeDeriv (timeDeriv (solVort P)) z s‖ ≤ Λ := by
    intro z _ s hs
    rw [hΛdef]
    exact (timeDeriv_timeDeriv_selfSimVort (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam P.hlamdif hlamdif2 P.hlamd
      hlamd2 P.hK hK₂ (hsub hs) hmpos (hmle s hs) z).2
  exact timeHolderOnBall_timeDeriv_of_secondDeriv (α := (α : ℝ)) (Λ := Λ) (R := P.R) (S := S)
    (ω := solVort P) P.hα hα1 hΛ hdiff hbd

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.GalerkinODE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false


/-- The abstract global-existence theorem for an ODE with an a-priori (trajectory) bound: a vector
field which is Lipschitz, bounded and time-continuous on the ball of radius `R'` admits a solution
on all of `[0,∞)` starting from any `x₀` in the ball of radius `R < R'`, provided every solution
stays in the ball of radius `R`.  This is the interface through which the ODE chapter is used. -/
def GlobalODEExistence : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (x₀ : E) (R R' L K : ℝ) (hR : 0 < R) (hR' : R < R') (hL : 0 < L)
    (hK : 0 ≤ K),
    x₀ ∈ Metric.closedBall (0 : E) R →
    (∀ t : ℝ, 0 ≤ t → LipschitzOnWith ⟨K, hK⟩ (f t) (Metric.closedBall (0 : E) R')) →
    (∀ (t : ℝ), 0 ≤ t → ∀ x ∈ Metric.closedBall (0 : E) R', ‖f t x‖ ≤ L) →
    (∀ x ∈ Metric.closedBall (0 : E) R', ContinuousOn (fun t : ℝ => f t x) (Set.Ici 0)) →
    (∀ (T : ℝ), 0 ≤ T → ∀ α : ℝ → E, IsSolOn f x₀ T α →
      ∀ t ∈ Set.Icc 0 T, α t ∈ Metric.closedBall (0 : E) R) →
    ∃ α : ℝ → E, IsSolGlob f x₀ α ∧ ∀ t, 0 ≤ t → α t ∈ Metric.closedBall (0 : E) R


/-! ## From the `ℋ⁴`-bound on the Galerkin profiles to the coefficient ball

The bundle's a-priori field `hCoeffBound` is a statement about the *coefficients*; the paper's
a-priori estimate is a statement about the `ℋ⁴`-norm of the Galerkin *profile*.  The two are related
by the exact energy identity `IP (∑ cₖφₖ) (∑ cₖφₖ) = ∑ cₖ²` and the upper bound
`IP f f ≤ C|f|²_{ℋ⁴}` of the admissible inner product: this is how N5 is expected to discharge
`hCoeffBound`. -/





end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_DzIter_Hz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-- The `θ`-variable is a dummy in `fun z _ => Hz z`: the iterated plain `z`-derivative of the
`θ`-slice is the iterated derivative of the one-variable function `Hz`. -/
theorem pzIter_Hz_eq (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ
      = deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z := by
  induction n generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter k (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z' θ)
        = deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz from funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv k Work.FTS.Nonlinear.FstarPkg.Hz).symm z

/-- The radial factor `Hz = 2z(1-z)/(1+z)³` is `C^∞` on `(-1,∞)` (its only pole is `z = -1`).
This is the smoothness hypothesis of the Stirling expansion
`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`. -/
theorem contDiffOn_Hz :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 2 * z * (1 - z)) (Set.Ioi (-1)) := by fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (-1)) := by fun_prop
  exact h1.div h2 (fun x hx => by
    have hx' : -1 < x := hx
    have : 0 < 1 + x := by linarith
    positivity)

/-- **The Stirling expansion of `D_z^m` on the radial factor.**  For `z > -1` and every `m`,
`D_z^m (fun z _ => Hz z) = ∑_{k≤m} S(m,k) z^k ∂_z^k Hz`, the `θ`-variable being a dummy. -/
theorem DzIter_Hz_eq_sum (m : ℕ) (z θ : ℝ) (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ
      = ∑ k ∈ Finset.range (m + 1), (Work.Spaces.scoef m k : ℝ) *
          (z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ) (Set.Ioi (-1)) :=
    contDiffOn_Hz
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth
    (h := fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) (θ := θ) hsmooth m z hz]
  exact Finset.sum_congr rfl fun k _ => by rw [pzIter_Hz_eq]

/-- **The weighted `D_z`-bounds of the radial factor `Hz`.**  There is a universal constant `C`
with
`|D_z^m (fun z _ => Hz z) z θ| ≤ C · z/(1+z)²` for every `m ≤ 4`, every `z ≥ 0` and every
angle `θ`. -/
theorem abs_DzIter_Hz_le : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 ≤ z → ∀ θ : ℝ,
    |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      ≤ C * (z / (1 + z) ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := abs_zpow_deriv_Hz_le
  refine ⟨100 * C₀ + 1, by linarith, ?_⟩
  intro m hm z hz θ
  have hz' : z ∈ Set.Ioi (-1) := by
    simp only [Set.mem_Ioi]; linarith
  have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hMnn : 0 ≤ C₀ * (z / (1 + z) ^ 2) := mul_nonneg hC₀pos.le hw
  rw [DzIter_Hz_eq_sum m z θ hz']
  have hsum := Work.Spaces.abs_sum_scoef_mul_le m (C₀ * (z / (1 + z) ^ 2))
    (fun k => z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
    (fun k hk => hC₀ k (le_trans hk hm) z hz)
  have hbell : (Work.Spaces.bell m : ℝ) ≤ 15 := by
    exact_mod_cast Work.FTS.H2.WPQ.bell_le_15 m hm
  calc |∑ k ∈ Finset.range (m + 1), (Work.Spaces.scoef m k : ℝ) *
        (z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)|
      ≤ (Work.Spaces.bell m : ℝ) * (C₀ * (z / (1 + z) ^ 2)) := hsum
    _ ≤ 15 * (C₀ * (z / (1 + z) ^ 2)) := mul_le_mul_of_nonneg_right hbell hMnn
    _ ≤ (100 * C₀ + 1) * (z / (1 + z) ^ 2) := by
        have h15 : (15 : ℝ) * C₀ ≤ 100 * C₀ + 1 := by nlinarith
        calc (15 : ℝ) * (C₀ * (z / (1 + z) ^ 2))
            = (15 * C₀) * (z / (1 + z) ^ 2) := by ring
          _ ≤ (100 * C₀ + 1) * (z / (1 + z) ^ 2) :=
              mul_le_mul_of_nonneg_right h15 hw

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.OpenPkg.AprioriOpen.GalSpanOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Bilinearity of `UnifIP` in its second argument, on the class `RegQ` -/

/-- Additivity of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_add_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g₁ g₂ : Fn} (hf : RegQ α 4 f) (h1 : RegQ α 4 g₁) (h2 : RegQ α 4 g₂) :
    IP α f (fun z θ => g₁ z θ + g₂ z θ) = IP α f g₁ + IP α f g₂ := by
  rw [show IP α f (fun z θ => g₁ z θ + g₂ z θ) = IP α f (g₁ + g₂) from rfl,
    hIP.symm α f (g₁ + g₂), hIP.add_fst α hα g₁ g₂ f h1 h2 hf,
    hIP.symm α g₁ f, hIP.symm α g₂ f]

/-- Scalar homogeneity of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_smul_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    (c : ℝ) {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α f (fun z θ => c * g z θ) = c * IP α f g := by
  rw [hIP.symm α f (fun z θ => c * g z θ), hIP.smul_fst α hα c g f hg hf, hIP.symm α g f]

/-- Negation of `UnifIP` in its first argument, on `RegQ`. -/
theorem ip_neg_fst {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α (fun z θ => -f z θ) g = -IP α f g := by
  have h := hIP.smul_fst α hα (-1) f g hf hg
  simpa using h

/-- Negation of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_neg_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α f (fun z θ => -g z θ) = -IP α f g := by
  have h := ip_smul_snd hIP hα (-1) hf hg
  simpa using h

/-- **The quadratic expansion of `IP` on a difference**: `|f - g|²_IP = |f|²_IP - 2(f,g)_IP +
|g|²_IP`. -/
theorem ip_sub_self {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α (fun z θ => f z θ - g z θ) (fun z θ => f z θ - g z θ)
      = IP α f f - 2 * IP α f g + IP α g g := by
  have hgn : RegQ α 4 (fun z θ => -g z θ) := regQ_neg hg
  have hsum : RegQ α 4 (fun z θ => f z θ + (-g z θ)) := regQ_add hf hgn
  have hEq : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + (-g z θ)) := rfl
  rw [hEq]
  rw [show (fun z θ => f z θ + (-g z θ)) = (f + fun z θ => -g z θ) from rfl]
  rw [hIP.add_fst α hα f (fun z θ => -g z θ) (f + fun z θ => -g z θ) hf hgn hsum,
    show (f + fun z θ => -g z θ) = fun z θ => f z θ + (-g z θ) from rfl,
    ip_add_snd hIP hα hf hf hgn, ip_add_snd hIP hα hgn hf hgn,
    ip_neg_snd hIP hα hf hg,
    show IP α (fun z θ => -g z θ) f = -IP α f g from by
      rw [ip_neg_fst hIP hα hg hf, hIP.symm α g f],
    show IP α (fun z θ => -g z θ) (fun z θ => -g z θ) = IP α g g from by
      rw [ip_neg_fst hIP hα hg hgn, ip_neg_snd hIP hα hg hg]; ring]
  ring

/-! ## The Galerkin span -/

/-- **Every test function of a `GalBasis` is in the interior class `RegQ α 4`.** -/
theorem regQ_phi {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hφ : GalBasis α IP φ)
    (i : ℕ) : RegQ α 4 (φ i) := by
  have h := hφ.cls (i + 1) (Pi.single ⟨i, Nat.lt_succ_self i⟩ (1 : ℝ))
  have h2 : galFun φ (Pi.single ⟨i, Nat.lt_succ_self i⟩ (1 : ℝ)) = φ i :=
    Work.FTS.Galerkin.galFun_single φ ⟨i, Nat.lt_succ_self i⟩
  rw [h2] at h
  exact regQ_mono (k := 6) (by norm_num) h.reg

/-- **Coefficient extraction**: the `k`-th coefficient of a Galerkin combination is its pairing
with the `k`-th test function, under the restricted bilinearity of `UnifIP`. -/
theorem ip_galFun_phi {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hφ : GalBasis α IP φ)
    (n : ℕ) (d : Fin n → ℝ) (k : Fin n) : IP α (galFun φ d) (φ (k : ℕ)) = d k := by
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  have key : ∀ s : Finset (Fin n),
      IP α (fun z θ => ∑ i ∈ s, d i * φ (i : ℕ) z θ) (φ (k : ℕ))
        = ∑ i ∈ s, d i * (if i = k then (1 : ℝ) else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := hIP.smul_fst α hα (0 : ℝ) (0 : Fn) (φ (k : ℕ))
          (regQ_zero α 4) (hphi (k : ℕ))
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', d i * φ (i : ℕ) z θ)
            = (fun z θ => d a * φ (a : ℕ) z θ)
              + (fun z θ => ∑ i ∈ s', d i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
          rfl
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => d a * φ (a : ℕ) z θ) := regQ_smul (d a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', d i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' d (fun i => φ i) (fun i _ => hphi i)
        rw [hIP.add_fst α hα _ _ _ h1 h2 (hphi (k : ℕ)),
          hIP.smul_fst α hα (d a) (φ (a : ℕ)) (φ (k : ℕ)) (hphi (a : ℕ)) (hphi (k : ℕ)),
          hφ.orth a k, ih, Finset.sum_insert ha]
        simp only [Fin.ext_iff]
  have hmain : IP α (galFun φ d) (φ (k : ℕ))
      = ∑ i : Fin n, d i * (if i = k then (1 : ℝ) else 0) := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α (galFun φ d) (φ (k : ℕ))
        = IP α (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            d i * φ (i : ℕ) z θ) (φ (k : ℕ)) from rfl]
    exact h
  rw [hmain, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **The Galerkin span is `UnifIP`-orthonormal**: for a `GalBasis`, the pairing of two Galerkin
combinations is the Euclidean pairing of their coefficient vectors.  This is the counterpart, in
the corrected class-restricted vocabulary, of `Work.FTS.Galerkin.isIPOrthonormal_of_orth`. -/
theorem isIPOrthonormal_of_galBasis {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    {φ : ℕ → Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hφ : GalBasis α IP φ) : Work.FTS.Galerkin.IsIPOrthonormal (IP α) φ := by
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  intro n d c
  have hrd : RegQ α 4 (galFun φ d) := regQ_mono (k := 6) (by norm_num) (hφ.cls n d).reg
  have key : ∀ s : Finset (Fin n),
      IP α (galFun φ d) (fun z θ => ∑ i ∈ s, c i * φ (i : ℕ) z θ)
        = ∑ i ∈ s, c i * (IP α (galFun φ d) (φ (i : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := ip_smul_snd hIP hα (0 : ℝ) hrd (regQ_zero α 4)
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', c i * φ (i : ℕ) z θ)
            = fun z θ => c a * φ (a : ℕ) z θ
              + (∑ i ∈ s', c i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => c a * φ (a : ℕ) z θ) := regQ_smul (c a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', c i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' c (fun i => φ i) (fun i _ => hphi i)
        rw [ip_add_snd hIP hα hrd h1 h2,
          ip_smul_snd hIP hα (c a) hrd (hphi (a : ℕ)), ih, Finset.sum_insert ha]
  have hmain : IP α (galFun φ d) (galFun φ c)
      = ∑ i : Fin n, c i * (IP α (galFun φ d) (φ (i : ℕ))) := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α (galFun φ d) (galFun φ c)
        = IP α (galFun φ d) (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            c i * φ (i : ℕ) z θ) from rfl]
    exact h
  rw [hmain]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ip_galFun_phi hIP hα hφ n d i]
  ring

/-- **Bessel's inequality for the Galerkin projection** (design §4 L-N5.6): the coefficients of the
projection of `g₀` onto the Galerkin span have `ℓ²`-norm bounded by `IP α g₀ g₀`. -/
theorem bessel_galBasis {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    {g₀ : Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hφ : GalBasis α IP φ) (hg : RegQ α 4 g₀) (n : ℕ) :
    ∑ k : Fin n, (IP α g₀ (φ (k : ℕ))) ^ 2 ≤ IP α g₀ g₀ := by
  classical
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  set c : Fin n → ℝ := fun k => IP α g₀ (φ (k : ℕ)) with hc
  have hS : RegQ α 4 (galFun φ c) := regQ_mono (k := 6) (by norm_num) (hφ.cls n c).reg
  have hSS : RegQ α 4 (fun z θ => g₀ z θ - galFun φ c z θ) := regQ_sub hg hS
  -- the second-argument expansion of `IP g₀ (-)`
  have key : ∀ s : Finset (Fin n),
      IP α g₀ (fun z θ => ∑ i ∈ s, c i * φ (i : ℕ) z θ)
        = ∑ i ∈ s, c i * (IP α g₀ (φ (i : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := ip_smul_snd hIP hα (0 : ℝ) hg (regQ_zero α 4)
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', c i * φ (i : ℕ) z θ)
            = fun z θ => c a * φ (a : ℕ) z θ
              + (∑ i ∈ s', c i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => c a * φ (a : ℕ) z θ) := regQ_smul (c a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', c i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' c (fun i => φ i) (fun i _ => hphi i)
        rw [ip_add_snd hIP hα hg h1 h2, ip_smul_snd hIP hα (c a) hg (hphi (a : ℕ)), ih,
          Finset.sum_insert ha]
  have hexp1 : IP α g₀ (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α g₀ (galFun φ c)
        = IP α g₀ (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            c i * φ (i : ℕ) z θ) from rfl]
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    ring
  have hexp2 : IP α (galFun φ c) (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := by
    rw [(isIPOrthonormal_of_galBasis hIP hα hφ) n c c]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnonneg : 0 ≤ IP α (fun z θ => g₀ z θ - galFun φ c z θ)
      (fun z θ => g₀ z θ - galFun φ c z θ) := hIP.nonneg α hα _ hSS
  rw [ip_sub_self hIP hα hg hS, hexp1, hexp2] at hnonneg
  linarith

end Work.FTS.OpenPkg.AprioriOpen
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.DerivConstPhi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.DerivConstPhi`

The angular model `ψ` (`L₀ψ = Γ̄`, encoded by `hode` below) makes the first integral of the
`Φ`-equation constant: with `v = ψ / sin 2θ` and `μ = sin²θ cos³θ`, the function

`θ ↦ μ(θ) v(θ) - G₀(θ)/2`

has vanishing derivative on `(0, π/2)`.  This is the elementary content behind
`PsiDivS2EqPfun` (where the constant is turned into a formula for `deriv v`).

The computation: `hode` reads `sin 2θ · v' = (6 sin²θ − 4 cos²θ) v − Γ̄`, hence

`(μ v)' = μ' v + μ v' = sinθ cos²θ · [ (2cos²θ − 3sin²θ) v + (3sin²θ − 2cos²θ) v ] + ½ sinθ cos²θ Γ̄`,

the bracket cancels identically, while `G₀' = − sinθ cos²θ Γ̄` supplies the other half.
-/

noncomputable section

open scoped Real ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem DerivConstPhi {α : ℝ} (hα : 0 ≤ α) {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * θ) * deriv (fun t => deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
            * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ - Work.FTS.VocabO.GamBar α θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun t => Real.sin t ^ 2 * Real.cos t ^ 3
          * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t - Work.FTS.PhiStar.Gzero α t / 2) θ = 0 := by
  intro θ hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hne : 2 * Real.sin θ * Real.cos θ ≠ 0 := by
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
    positivity
  -- name the divided function `u = ψ / sin 2θ`
  set u : ℝ → ℝ := fun t => ψ t / Real.sin (2 * t) with hu
  -- `u` is smooth on the open interval
  have husm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    rw [hu]
    refine (hsm n).div (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos]))
  -- hence `deriv u` is differentiable at `θ`
  have huAt : ContDiffAt ℝ 2 u θ :=
    (husm 2).contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩)
  have hu1 : ContDiffAt ℝ 1 (deriv u) θ := huAt.derivWithin (m := 1) (by norm_num)
  have hudiff : DifferentiableAt ℝ (deriv u) θ := hu1.differentiableAt_one
  -- the ODE, phrased in terms of `u`
  have hode_u : Real.sin (2 * θ) * deriv (deriv u) θ
      = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv u θ
        - Work.FTS.VocabO.GamBar α θ := by
    rw [hu]
    exact hode θ ⟨hθ1, hθ2⟩
  -- the derivative of `μ = sin²θ cos³θ`
  have hsin_deriv : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3)
      (2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_sin θ).pow 2
      rw [show ((fun t : ℝ => Real.sin t) ^ 2) = fun t : ℝ => Real.sin t ^ 2 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have h2 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = fun t : ℝ => Real.cos t ^ 3 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hv : HasDerivAt (deriv u) (deriv (deriv u) θ) θ := hudiff.hasDerivAt
  have hprod : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 * deriv u t)
      ((2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) * deriv u θ
        + (Real.sin θ ^ 2 * Real.cos θ ^ 3) * deriv (deriv u) θ) θ := hsin_deriv.mul hv
  have hG := hasDerivAt_Gzero α hα ⟨hθ1, hθ2⟩
  have hF : HasDerivAt (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 * deriv u t
        - Gzero α t / 2)
      ((2 * Real.sin θ * Real.cos θ ^ 4 - 3 * Real.sin θ ^ 3 * Real.cos θ ^ 2) * deriv u θ
        + (Real.sin θ ^ 2 * Real.cos θ ^ 3) * deriv (deriv u) θ
        - (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) / 2) θ :=
    hprod.sub (hG.div_const 2)
  rw [hF.deriv]
  -- solve the ODE for the second derivative and substitute
  have hd2 : deriv (deriv u) θ = ((6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv u θ
      - Work.FTS.VocabO.GamBar α θ) / (2 * Real.sin θ * Real.cos θ) := by
    rw [eq_div_iff hne, mul_comm, ← Real.sin_two_mul]
    exact hode_u
  rw [hd2]
  field_simp
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.GzProfile_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- **The angular moment of the profile is smooth.**  For `0 < α ≤ 1` the angular moment
`F_*(Construction.Fstar α)` is the explicit rational function `z ↦ α·(2z/(1+z)²)/3`, hence
`C^∞` on `(0,∞)`. -/
theorem ellFstar_GzProfile_smooth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.Construction.Fstar α)) (Set.Ioi 0) := by
  intro m
  rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1]
  have : (fun z : ℝ => α * Work.FM.Fstar z / 3)
      = fun z : ℝ => ((α / 3) * (2 * z)) / (1 + z) ^ 2 := by
    funext z; simp only [Work.FM.Fstar]; ring
  rw [this]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact ContDiffOn.mul contDiffOn_const (contDiffOn_const.mul contDiffOn_id)
  · exact (contDiffOn_const.add contDiffOn_id).pow 2
  · intro z hz
    have : (0 : ℝ) < 1 + z := by simp only [Set.mem_Ioi] at hz; linarith
    positivity

/-- **The density `F_*/r` of the profile is integrable.**  On `(0,∞)` it equals
`(2α/3)·(1+r)^{-2}`, which is integrable there. -/
theorem ellFstar_GzProfile_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar (Work.Construction.Fstar α) r / r)
      (Set.Ioi 0) := by
  have hA : IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := 1)
      (by norm_num) (by norm_num)
  refine IntegrableOn.congr_fun (hA.const_mul (2 * α / 3)) ?_ measurableSet_Ioi
  intro s hs
  simp only [Set.mem_Ioi] at hs
  rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1]
  simp only [Work.FM.Fstar]
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  rw [show (s + 1) ^ (-2 : ℝ) = ((s + 1) ^ 2)⁻¹ from by
    rw [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat]]
  field_simp
  ring

/-- **The explicit radial profile `GzProfile` is `C^∞` on `(0,∞)`.**

`GzProfile α = -Gsing α (Construction.Fstar α)`, and `Gsing_smooth_ode_of_facts` gives the
`C^∞`-smoothness of `Gsing α F` as soon as the angular moment `F_*` of the source is smooth on
`(0,∞)` and `r ↦ F_*(r)/r` is integrable there — both established above for the profile
`F = Construction.Fstar α`. -/
theorem GzProfile_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.GzProfile α) (Set.Ioi 0) := by
  have hα1' : α ≤ 1 := by linarith
  have hFsm := ellFstar_GzProfile_smooth α hα hα1'
  have hFint := ellFstar_GzProfile_integrable α hα hα1'
  have hGs := (Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α
    (Work.Construction.Fstar α) hα hFsm hFint
    (Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts _ hFsm hFint)).1
  intro n
  exact (hGs n).neg

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.GzProfile_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## The auxiliary model integral `At`/`Pi` -/

/-- **Pointwise comparison for the model integral.**  For `N ≥ 2`, `z ≥ 1` and `t ∈ [0,1]`,

`z² · t^N/(1+zt)² ≤ t^(N-2)`.

This is the integrand form of `(tz)² ≤ (1+tz)²` after writing `t^N = t^(N-2)·t²`. -/
theorem At_pointwise (N : ℝ) (hN : 2 ≤ N) {z t : ℝ} (hz : 1 ≤ z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    z ^ 2 * (t ^ N / (1 + z * t) ^ 2) ≤ t ^ (N - 2) := by
  have hz0 : 0 < z := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    rw [Real.zero_rpow (ne_of_gt hN0), zero_div, mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · have ht2 : t ^ N = t ^ (N - 2) * t ^ (2 : ℝ) := by
      rw [← Real.rpow_add h0 (N - 2) 2]
      congr 1
      ring
    have hkey : z ^ 2 * (t ^ N / (1 + z * t) ^ 2)
        = t ^ (N - 2) * ((z * t) ^ 2 / (1 + z * t) ^ 2) := by
      rw [ht2, Real.rpow_two, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hkey]
    refine mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt h0) _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [mul_nonneg (le_of_lt hz0) (le_of_lt h0)]

/-- **The decay bound for `Pi`.**  For `N ≥ 2` and `z ≥ 1` one has `Pi N z ≤ 1/z`. -/
theorem Pi_le_inv (N : ℝ) (hN : 2 ≤ N) {z : ℝ} (hz : 1 ≤ z) :
    Work.FTS.H2.PhiStarE.Pi N z ≤ 1 / z := by
  have hz0 : 0 < z := by linarith
  have hN2 : (0 : ℝ) ≤ N - 2 := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcont1 : ContinuousOn (fun t : ℝ => t ^ N / (1 + z * t) ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div
      (Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN0).continuousOn
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact pow_ne_zero 2 (ne_of_gt (by linarith [mul_nonneg (le_of_lt hz0) ht.1]))
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ N / (1 + z * t) ^ 2) volume 0 1 :=
    hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => z * (t ^ N / (1 + z * t) ^ 2)) volume 0 1 :=
    hint1.const_mul z
  have hint3 : IntervalIntegrable (fun t : ℝ => t ^ (N - 2) / z) volume 0 1 :=
    ((Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN2).intervalIntegrable 0 1).div_const z
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      z * (t ^ N / (1 + z * t) ^ 2) ≤ t ^ (N - 2) / z := by
    intro t ht
    rw [le_div_iff₀ hz0]
    calc z * (t ^ N / (1 + z * t) ^ 2) * z
        = z ^ 2 * (t ^ N / (1 + z * t) ^ 2) := by ring
      _ ≤ t ^ (N - 2) := At_pointwise N hN hz ht
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint2 hint3 hpt
  have hAt : Work.FTS.H2.PhiStarE.At N 0 z
      = ∫ t in (0 : ℝ)..1, t ^ N / (1 + z * t) ^ 2 := by
    rw [Work.FTS.H2.PhiStarE.At_def]
    simp only [Nat.cast_zero, add_zero, zero_add]
  rw [Work.FTS.H2.PhiStarE.Pi_def, hAt, ← intervalIntegral.integral_const_mul]
  refine hmono.trans ?_
  rw [intervalIntegral.integral_div]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt hz0)
  calc (∫ t in (0 : ℝ)..1, t ^ (N - 2))
      ≤ ∫ t in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          ((Work.FTS.H2.PhiStarE.continuous_rpow_const_nonneg hN2).intervalIntegrable 0 1)
          intervalIntegrable_const
          (fun t ht => Real.rpow_le_one ht.1 ht.2 hN2)
    _ = 1 := by simp

/-- `Pi N z ≥ 0` for `z ≥ 0` (`At N 0` is an integral of a nonnegative integrand). -/
theorem Pi_nonneg (N : ℝ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FTS.H2.PhiStarE.Pi N z := by
  rw [Work.FTS.H2.PhiStarE.Pi_def]
  refine mul_nonneg hz ?_
  rw [Work.FTS.H2.PhiStarE.At_def]
  refine intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1) fun t ht => ?_
  exact div_nonneg (Real.rpow_nonneg ht.1 _)
    (pow_nonneg (by linarith [mul_nonneg hz ht.1]) _)

/-- **`Pi N z → 0` as `z → ∞` for `N ≥ 2`** (in fact for any `N > 1`). -/
theorem tendsto_Pi_atTop (N : ℝ) (hN : 2 ≤ N) :
    Tendsto (Work.FTS.H2.PhiStarE.Pi N) atTop (𝓝 (0 : ℝ)) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact Pi_nonneg N hz
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have h := Pi_le_inv N hN hz
    rwa [one_div] at h

/-! ## The decay of `Aprof` and of the main theorem -/

/-- **The flat profile decays.**  `Aprof α = −Ḡ` equals `(1/2)·Pi (5/α)` on `(0,∞)` and
`5/α ≥ 2` for `0 < α ≤ 5/2`, so `Aprof α z → 0`. -/
theorem tendsto_Aprof {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Tendsto (Aprof α) atTop (𝓝 (0 : ℝ)) := by
  have hN : (2 : ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]
    linarith
  have hPi := tendsto_Pi_atTop (5 / α) hN
  have h2 : Tendsto (fun z => (1 / 2) * Work.FTS.H2.PhiStarE.Pi (5 / α) z) atTop (𝓝 (0 : ℝ)) := by
    have h := hPi.const_mul (1 / 2)
    simpa using h
  have hev : (fun z => (1 / 2) * Work.FTS.H2.PhiStarE.Pi (5 / α) z)
      =ᶠ[atTop] Aprof α := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [Aprof_eqOn_negDk hα hα1 (show z ∈ Set.Ioi 0 from hz)]
    simp only [Work.FTS.H2.PhiStarE.Dk_zero, Work.FTS.H2.PhiStarE.Pi_def]
    ring
  exact h2.congr' hev

/-- `ThetaProfile z = 1/(2(1+z)) → 0`. -/
theorem tendsto_ThetaProfile : Tendsto ThetaProfile atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun z : ℝ => 1 / (1 + z)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_zero, pow_one] using
      tendsto_pow_div_pow_atTop (k := 0) (m := 1) (by norm_num)
  have h2 : Tendsto (fun z : ℝ => (1 / 2) * (1 / (1 + z))) atTop (𝓝 (0 : ℝ)) := by
    have h := h.const_mul (1 / 2)
    simpa using h
  refine h2.congr' ?_
  filter_upwards with z
  rw [ThetaProfile, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- **The explicit radial profile `GzProfile α` decays at infinity**: `GzProfile α z → 0` as
`z → ∞`, for `0 < α ≤ 1/4`.

Since `GzProfile α = Aprof α + ThetaProfile` and both summands tend to `0`, the limit follows. -/
theorem GzProfile_tendsto {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    Filter.Tendsto (fun z => Work.FTS.PhiStar.GzProfile α z) Filter.atTop (nhds (0 : ℝ)) := by
  have hα1' : α ≤ 1 := by linarith
  have hsum := (tendsto_Aprof hα hα1').add tendsto_ThetaProfile
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with z
  simp only [Aprof]
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.Gzero_rpow_pi_div_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open MeasureTheory Set
open scoped Real Topology

set_option autoImplicit false

/-! ## Two elementary ingredients -/

/-- Within the interval between `θ` and `π/2`, the distance to `π/2` is at most the
distance of `θ` to `π/2`: `|x − π/2| ≤ |θ − π/2|` for `x ∈ uIoc θ (π/2)`. -/
lemma abs_sub_pi_div_two_le_of_mem_uIoc {θ x : ℝ} (hx : x ∈ Set.uIoc θ (Real.pi / 2)) :
    |x - Real.pi / 2| ≤ |θ - Real.pi / 2| := by
  rcases le_or_gt θ (Real.pi / 2) with h | h
  · rw [Set.uIoc_of_le h] at hx
    rw [abs_of_nonpos (by linarith [hx.2] : x - Real.pi / 2 ≤ 0),
      abs_of_nonpos (by linarith : θ - Real.pi / 2 ≤ 0)]
    linarith [hx.1]
  · rw [show Set.uIoc θ (Real.pi / 2) = Set.Ioc (Real.pi / 2) θ from by
      simp only [Set.uIoc, min_eq_right h.le, max_eq_left h.le]] at hx
    rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - Real.pi / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ - Real.pi / 2)]
    linarith [hx.2]

/-- **The `cos²·Γ` bound**: for `sin t ≥ 0` and `α > 0`,
`cos²t · Γ(t) ≤ |cos t|^{2+2α/3}`.

Indeed `Γ(t) = (sin t cos²t)^{α/3} ≤ (cos²t)^{α/3} = |cos t|^{2α/3}`, and
`cos²t = |cos t|²`; the two powers combine by `Real.rpow_add'`. -/
lemma cos_sq_mul_Gam_le_cos_rpow (α t : ℝ) (hα : 0 < α) (hs : 0 ≤ Real.sin t) :
    Real.cos t ^ 2 * Work.Spaces.Gam α t ≤ |Real.cos t| ^ (2 + 2 * (α / 3)) := by
  have hcosabs : 0 ≤ |Real.cos t| := abs_nonneg _
  have hbase : 0 ≤ Real.sin t * Real.cos t ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hcos2 : |Real.cos t| ^ (2 : ℝ) = Real.cos t ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  have hcle : Real.sin t * Real.cos t ^ 2 ≤ |Real.cos t| ^ (2 : ℝ) := by
    rw [hcos2]
    exact mul_le_of_le_one_left (by positivity) (Real.sin_le_one t)
  have hstep : (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      ≤ (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) :=
    Real.rpow_le_rpow hbase hcle (by linarith)
  have hsimp : (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) = |Real.cos t| ^ (2 * (α / 3)) := by
    rw [← Real.rpow_mul hcosabs]
  have hfinal : |Real.cos t| ^ (2 : ℝ) * |Real.cos t| ^ (2 * (α / 3))
      = |Real.cos t| ^ (2 + 2 * (α / 3)) := by
    rw [← Real.rpow_add' hcosabs (by linarith : 2 + 2 * (α / 3) ≠ 0)]
  have h1 : Real.cos t ^ 2 * (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      = |Real.cos t| ^ (2 : ℝ) * (Real.sin t * Real.cos t ^ 2) ^ (α / 3) := by
    rw [hcos2]
  rw [Work.Spaces.Gam, h1]
  calc |Real.cos t| ^ (2 : ℝ) * (Real.sin t * Real.cos t ^ 2) ^ (α / 3)
      ≤ |Real.cos t| ^ (2 : ℝ) * (|Real.cos t| ^ (2 : ℝ)) ^ (α / 3) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hcosabs _)
    _ = |Real.cos t| ^ (2 : ℝ) * |Real.cos t| ^ (2 * (α / 3)) := by rw [hsimp]
    _ = |Real.cos t| ^ (2 + 2 * (α / 3)) := hfinal

/-! ## The pointwise bound on the integrand near `π/2` -/

/-- **The integrand bound near the right endpoint.**  For `0 < α ≤ 1/4` and
`|t − π/2| ≤ 1/2`,
`|sin t · cos²t · Γ̄(t)| ≤ (1/c + 5/2)·|t − π/2|^{2+2α/3}`. -/
private lemma abs_sin_cos_sq_GamBar_le_rpow_prv (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {t : ℝ}
    (ht : |t - Real.pi / 2| ≤ 1 / 2) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      ≤ (1 / Work.Spaces.c α + 5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
  have hcpos : 0 < Work.Spaces.c α := by
    have := (Work.Spaces.c_bounds α hα (by linarith)).1
    linarith
  have htlo : 0 < t := by
    have h := (abs_le.mp ht).1
    linarith [Real.pi_gt_three]
  have hthi : t < Real.pi := by
    have h := (abs_le.mp ht).2
    linarith [Real.pi_gt_three]
  have hsin0 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htlo hthi
  have hsinle : Real.sin t ≤ 1 := Real.sin_le_one t
  have hc2 : 0 ≤ Real.cos t ^ 2 := sq_nonneg _
  have hgamnn : 0 ≤ Work.Spaces.Gam α t :=
    Real.rpow_nonneg (mul_nonneg hsin0.le hc2) _
  have hcosabs : 0 ≤ |Real.cos t| := abs_nonneg _
  -- `|Γ̄| ≤ Γ/c + (5/2)|cos t|`
  have hGB : |Work.FTS.VocabO.GamBar α t|
      ≤ Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t| := by
    rw [Work.FTS.VocabO.GamBar]
    have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α - 5 / 4 * Real.sin (2 * t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5 : ℝ) / 4 * Real.sin (2 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α)
          (-((5 : ℝ) / 4 * Real.sin (2 * t)))
    have h2 : |Work.Spaces.Gam α t / Work.Spaces.c α| = Work.Spaces.Gam α t / Work.Spaces.c α :=
      abs_of_nonneg (div_nonneg hgamnn hcpos.le)
    have h3 : |(5 : ℝ) / 4 * Real.sin (2 * t)| ≤ (5 / 2) * |Real.cos t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
      have h4 : |Real.sin (2 * t)| ≤ 2 * |Real.cos t| := by
        rw [Real.sin_two_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h5 := Real.abs_sin_le_one t
        nlinarith [abs_nonneg (Real.cos t)]
      linarith
    linarith
  -- `|cos t| ≤ |t − π/2|`
  have hcosle : |Real.cos t| ≤ |t - Real.pi / 2| := by
    rw [show Real.cos t = Real.sin (Real.pi / 2 - t) from (Real.sin_pi_div_two_sub t).symm,
      abs_sub_comm t (Real.pi / 2)]
    exact Real.abs_sin_le_abs
  have ht1 : |t - Real.pi / 2| ≤ 1 := by linarith
  have hp0 : (0 : ℝ) ≤ 2 + 2 * (α / 3) := by linarith
  have hp3 : 2 + 2 * (α / 3) ≤ 3 := by linarith
  -- `cos²t·Γ ≤ |cos t|^p`
  have hgam2 : Real.cos t ^ 2 * Work.Spaces.Gam α t ≤ |Real.cos t| ^ (2 + 2 * (α / 3)) :=
    cos_sq_mul_Gam_le_cos_rpow α t hα hsin0.le
  -- `|cos t|³ ≤ |t − π/2|^p`
  have hcs : |Real.cos t| ^ 3 ≤ |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
    have h3 : |Real.cos t| ^ 3 ≤ |t - Real.pi / 2| ^ 3 :=
      pow_le_pow_left₀ hcosabs hcosle 3
    have h4 : |t - Real.pi / 2| ^ 3 ≤ |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
      rw [show |t - Real.pi / 2| ^ 3 = |t - Real.pi / 2| ^ (3 : ℝ) from
        (Real.rpow_natCast _ 3).symm]
      exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) ht1 hp0 hp3
    linarith
  have hpc : (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
      ≤ (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hcosabs hcosle hp0) (by positivity)
  -- assembly
  have e1 : |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      = Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hsin0.le, abs_of_nonneg hc2]
  have step1 : Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t|
      ≤ Real.sin t * Real.cos t ^ 2
        * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|) :=
    mul_le_mul_of_nonneg_left hGB (mul_nonneg hsin0.le hc2)
  have h5 : Real.cos t ^ 2 * |Real.cos t| = |Real.cos t| ^ 3 := by
    rw [show Real.cos t ^ 2 = |Real.cos t| ^ 2 from (sq_abs (Real.cos t)).symm]
    ring
  have hmul2 : Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t)
      ≤ Real.cos t ^ 2 * Work.Spaces.Gam α t :=
    mul_le_of_le_one_left (mul_nonneg hc2 hgamnn) hsinle
  have hmul3 : Real.sin t * (Real.cos t ^ 2 * |Real.cos t|)
      ≤ Real.cos t ^ 2 * |Real.cos t| :=
    mul_le_of_le_one_left (mul_nonneg hc2 hcosabs) hsinle
  have step2 : Real.sin t * Real.cos t ^ 2
        * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|)
      ≤ (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |Real.cos t| ^ 3 := by
    have heq : Real.sin t * Real.cos t ^ 2
          * (Work.Spaces.Gam α t / Work.Spaces.c α + (5 / 2) * |Real.cos t|)
        = (1 / Work.Spaces.c α) * (Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t))
          + (5 / 2) * (Real.sin t * (Real.cos t ^ 2 * |Real.cos t|)) := by ring
    rw [heq]
    have hA : (1 / Work.Spaces.c α) * (Real.sin t * (Real.cos t ^ 2 * Work.Spaces.Gam α t))
        ≤ (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3)) :=
      mul_le_mul_of_nonneg_left (le_trans hmul2 hgam2) (by positivity)
    have hB : (5 / 2) * (Real.sin t * (Real.cos t ^ 2 * |Real.cos t|))
        ≤ (5 / 2) * |Real.cos t| ^ 3 :=
      mul_le_mul_of_nonneg_left (le_trans hmul3 (le_of_eq h5)) (by norm_num)
    linarith
  have step3 : (1 / Work.Spaces.c α) * |Real.cos t| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |Real.cos t| ^ 3
      ≤ (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by
    have hB : (5 / 2) * |Real.cos t| ^ 3
        ≤ (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
    linarith
  have step4 : (1 / Work.Spaces.c α) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
        + (5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3))
      = (1 / Work.Spaces.c α + 5 / 2) * |t - Real.pi / 2| ^ (2 + 2 * (α / 3)) := by ring
  linarith [e1, step1, step2, step3, step4]

/-! ## The target -/

/-- Two-sided power bound for `G₀` near the right endpoint of `Iθ`:
`|G₀(θ)| ≤ C|θ-π/2|^{3+2α/3}` for `|θ-π/2| ≤ 1/2`.

Here `G₀(θ) = ∫_θ^{π/2} sin t cos²t Γ̄(t) dt`, and on the interval between `θ` and `π/2` the
integrand satisfies `|sin t cos²t Γ̄(t)| ≤ cos²t(cos^{2α/3}t/c + (5/2)|cos t|)` (using
`|sin t| ≤ 1` and `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ cos^{2α/3}t`), which is
`≤ C|π/2-t|^{2+2α/3}` because `|cos t| ≤ |π/2 - t|` there; integrating from `θ` to `π/2`
(or from `π/2` to `θ` when `θ > π/2`) gives `C|θ - π/2|^{3+2α/3}`, the
`(5/2)|cos t|³` term being of higher order (`3 ≥ 2+2α/3`).  This is the quantitative
improvement of the existing `Gzero_abs_le` (`|G₀ θ| ≤ (1/c+5/4)(π/2-θ)cos²θ`, which only
gives `O(|θ-π/2|³)`), and the exponent `3+2α/3` is sharp. -/
theorem Gzero_rpow_pi_div_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |θ - Real.pi / 2| ≤ 1 / 2 →
      |Work.FTS.PhiStar.Gzero α θ| ≤ C * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := by
  have hKpos : 0 < 1 / Work.Spaces.c α + 5 / 2 := by
    have hcpos : 0 < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    have : 0 < 1 / Work.Spaces.c α := by positivity
    linarith
  refine ⟨13, by norm_num, fun θ hθ => ?_⟩
  have hp0 : (0 : ℝ) ≤ 2 + 2 * (α / 3) := by linarith
  have hpne : 2 + 2 * (α / 3) + 1 ≠ 0 := by linarith
  -- the pointwise bound on the integrand, pulled back to the interval `uIoc θ (π/2)`
  have hbound : ‖∫ t in θ..(Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t‖
      ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
        * |Real.pi / 2 - θ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    have hx1 : |x - Real.pi / 2| ≤ 1 / 2 :=
      le_trans (abs_sub_pi_div_two_le_of_mem_uIoc hx) hθ
    calc ‖Real.sin x * Real.cos x ^ 2 * Work.FTS.VocabO.GamBar α x‖
        = |Real.sin x * Real.cos x ^ 2 * Work.FTS.VocabO.GamBar α x| := Real.norm_eq_abs _
      _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |x - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
          abs_sin_cos_sq_GamBar_le_rpow_prv α hα hα1 hx1
      _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) (abs_sub_pi_div_two_le_of_mem_uIoc hx) hp0)
            hKpos.le
  have hfin : (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
        * |Real.pi / 2 - θ|
      = (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := by
    rw [abs_sub_comm (Real.pi / 2) θ,
      show (3 : ℝ) + 2 * (α / 3) = (2 + 2 * (α / 3)) + 1 by ring,
      Real.rpow_add' (abs_nonneg _) hpne, Real.rpow_one]
    ring
  have h13 : (1 / Work.Spaces.c α + 5 / 2) ≤ 13 := by
    have hcpos : 0 < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    have h10 : 1 / Work.Spaces.c α ≤ 10 := by
      rw [div_le_iff₀ hcpos]
      have := (Work.Spaces.c_bounds α hα (by linarith)).1
      linarith
    linarith
  calc |Work.FTS.PhiStar.Gzero α θ|
      = ‖∫ t in θ..(Real.pi / 2),
          Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t‖ := by
        rw [Work.FTS.PhiStar.Gzero, Real.norm_eq_abs]
    _ ≤ (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (2 + 2 * (α / 3))
          * |Real.pi / 2 - θ| := hbound
    _ = (1 / Work.Spaces.c α + 5 / 2) * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) := hfin
    _ ≤ 13 * |θ - Real.pi / 2| ^ (3 + 2 * (α / 3)) :=
        mul_le_mul_of_nonneg_right h13 (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.H1_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real
open MeasureTheory Set

set_option autoImplicit false

/-!
# The `H¹`-endpoint bound for `Ψ_Γ(θ) = ∫_θ^{π/2} sin t cos²t Γ(t) dt`

For `0 < α ≤ 1/4` and `π/4 < θ < π/2` we prove

`|3 Ψ_Γ(θ)/cos³θ − Γ(θ)| ≤ 3α cos^{2α/3}θ`,   `Γ(θ) = (sin θ cos²θ)^{α/3}`.

## The mathematics

Write `u(θ) = sin θ cos²θ` (so `Γ = u^{α/3}`) and let `A = ∫_θ^{π/2} u Γ`,
`Q = ∫_θ^{π/2} u (Γ(t) − Γ(θ))`.  The elementary integral `∫_θ^{π/2} u = cos³θ/3`
turns the desired difference into a *pure* integral of `u (Γ − Γ(t))`:

`3 A / cos³θ − Γ(θ) = 3 Q / cos³θ`.

Since `u` is strictly decreasing on `[π/4, π/2]` (because `u = f(sin θ)` with
`f(s) = s − s³` and `sin θ ∈ [√2/2, 1] ⊂ [1/√3, 1]`), one has `Γ(t) ≤ Γ(θ)` on
`[θ, π/2]`, hence `Q ≤ 0`.  In the other direction, Bernoulli's inequality
`(1 + x)^p ≤ 1 + p x` (`0 ≤ p ≤ 1`, `x ≥ −1`) applied with `1 + x = u(θ)/u(t)`,
`p = α/3` gives the pointwise bound

`u(t) (Γ(θ) − Γ(t)) ≤ u(t) p u(t)^{p−1} (u(θ) − u(t)) ≤ (α/3) Γ(θ) u(θ)`,

and integrating over `t ∈ [θ, π/2]` yields

`−Q ≤ (α/3) Γ(θ) u(θ) (π/2 − θ) ≤ (π/2) α Γ(θ) cos³θ`.

Together with `Γ(θ) = sin^{α/3}θ cos^{2α/3}θ ≤ cos^{2α/3}θ` and `π/2 ≤ 3` this gives
the claim.
-/

/-! ## The angular profile `u(θ) = sin θ cos²θ` is decreasing on `[π/4, π/2]` -/

/-- `u(θ) = sin θ cos²θ` is antitone on `[π/4, π/2]`. -/
lemma sin_mul_cos_sq_anti {θ t : ℝ} (hθ : Real.pi / 4 ≤ θ) (hθt : θ ≤ t)
    (ht : t ≤ Real.pi / 2) :
    Real.sin t * Real.cos t ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 := by
  have h1 : Real.sin θ ≤ Real.sin t :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], ht⟩ hθt
  have hy : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin
      (show Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (show θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hθ
    rwa [Real.sin_pi_div_four] at h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by nlinarith [hy, hsq, Real.sqrt_nonneg 2]
  have hsy : (1 : ℝ) / 2 ≤ Real.sin θ * Real.sin t := by
    nlinarith [hs2, h1, Real.sqrt_nonneg 2]
  have hxy : 0 ≤ Real.sin t - Real.sin θ := by linarith
  have hprod : (Real.sin t - Real.sin θ) *
      (1 - (Real.sin t ^ 2 + Real.sin t * Real.sin θ + Real.sin θ ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hxy
      (by nlinarith [hs2, hsy, sq_nonneg (Real.sin t), h1])
  rw [Real.cos_sq' t, Real.cos_sq' θ]
  nlinarith [hprod]

/-- `Γ` is antitone on `[π/4, π/2]`. -/
lemma Gam_anti {α θ t : ℝ} (hα : 0 < α) (hθ : Real.pi / 4 ≤ θ) (hθt : θ ≤ t)
    (ht : t ≤ Real.pi / 2) :
    Work.Spaces.Gam α t ≤ Work.Spaces.Gam α θ := by
  have hs0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Work.Spaces.Gam, Work.Spaces.Gam]
  exact Real.rpow_le_rpow (mul_nonneg hs0 (sq_nonneg _)) (sin_mul_cos_sq_anti hθ hθt ht)
    (by linarith)

/-- `Γ(θ) = sin^{α/3}θ cos^{2α/3}θ ≤ cos^{2α/3}θ`. -/
lemma Gam_le_cos_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], le_of_lt hθ.2⟩
  have h1 : Work.Spaces.Gam α θ =
      Real.sin θ ^ (α / 3) * (Real.cos θ ^ 2) ^ (α / 3) := by
    change (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) = _
    rw [Real.mul_rpow hs0 (by positivity)]
  have h2 : (Real.cos θ ^ 2) ^ (α / 3) = Real.cos θ ^ (2 * (α / 3)) := by
    rw [← Real.rpow_natCast (Real.cos θ) 2]
    exact (Real.rpow_mul hc0 (2 : ℝ) (α / 3)).symm
  have h3 : Real.sin θ ^ (α / 3) ≤ 1 :=
    Real.rpow_le_one hs0 (Real.sin_le_one θ) (by linarith)
  have h4 : (0 : ℝ) ≤ Real.cos θ ^ (2 * (α / 3)) := Real.rpow_nonneg hc0 _
  rw [h1, h2]
  calc Real.sin θ ^ (α / 3) * Real.cos θ ^ (2 * (α / 3))
      ≤ 1 * Real.cos θ ^ (2 * (α / 3)) := mul_le_mul_of_nonneg_right h3 h4
    _ = Real.cos θ ^ (2 * α / 3) := by
        rw [one_mul]
        congr 1
        ring

/-! ## The pointwise convexity (Bernoulli) bound -/

/-- **Key pointwise bound.**  For `π/4 ≤ θ ≤ t ≤ π/2`,

`u(t) (Γ(θ) − Γ(t)) ≤ (α/3) Γ(θ) u(θ)`,   `u(s) = sin s cos²s`.

This is the quantitative form of the concavity of `x ↦ x^{α/3}`: with
`a = u(θ)`, `b = u(t)`, `p = α/3`, Bernoulli's inequality gives
`a^p − b^p ≤ p b^{p−1}(a−b)`, and multiplying by `b ≥ 0` turns this into the
statement. -/
lemma key_pointwise {α θ t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hθ : Real.pi / 4 ≤ θ)
    (hθt : θ ≤ t) (ht : t ≤ Real.pi / 2) :
    Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α θ - Work.Spaces.Gam α t)
      ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) := by
  have hp0 : 0 ≤ α / 3 := by linarith
  have hp1 : α / 3 ≤ 1 := by linarith
  set a := Real.sin θ * Real.cos θ ^ 2 with ha
  set b := Real.sin t * Real.cos t ^ 2 with hb
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (sq_nonneg _)
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (sq_nonneg _)
  have hGθ0 : 0 ≤ Work.Spaces.Gam α θ := by
    rw [Work.Spaces.Gam]; exact Real.rpow_nonneg ha0 _
  have hsub : Work.Spaces.Gam α θ = a ^ (α / 3) := by rw [Work.Spaces.Gam, ha]
  have hsubt : Work.Spaces.Gam α t = b ^ (α / 3) := by rw [Work.Spaces.Gam, hb]
  have hGa : b ^ (α / 3) ≤ a ^ (α / 3) := by
    have h := Gam_anti hα hθ hθt ht
    rw [hsubt, hsub] at h
    exact h
  rcases eq_or_lt_of_le hb0 with hbz | hbz
  · rw [← hbz, zero_mul]
    exact mul_nonneg (mul_nonneg hp0 hGθ0) ha0
  · rw [hsubt, hsub]
    set x := (a - b) / b with hxdef
    have hx1 : -1 ≤ x := by rw [hxdef, le_div_iff₀ hbz]; linarith
    have hbx : b * (1 + x) = a := by rw [hxdef]; field_simp; try ring
    have hx0 : 0 ≤ 1 + x := by linarith
    have hBern := rpow_one_add_le_one_add_mul_self hx1 hp0 hp1
    have hbp : 0 ≤ b ^ (α / 3) := Real.rpow_nonneg hb0 _
    have h2 : b * (b ^ (α / 3) * (1 + x) ^ (α / 3)) ≤
        b * (b ^ (α / 3) * (1 + (α / 3) * x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBern hbp) (le_of_lt hbz)
    have h3 : b * (b ^ (α / 3) * (1 + (α / 3) * x)) =
        b ^ (α / 3) * b + (α / 3) * b ^ (α / 3) * (a - b) := by
      rw [hxdef]; field_simp; try ring
    have h4 : b * b ^ (α / 3) = b ^ (α / 3) * b := by ring
    have h5 : b * (a ^ (α / 3) - b ^ (α / 3)) = b * a ^ (α / 3) - b * b ^ (α / 3) := by ring
    have h1 : b * a ^ (α / 3) = b * (b * (1 + x)) ^ (α / 3) := by rw [hbx]
    have h1'' : b * (b * (1 + x)) ^ (α / 3) = b * (b ^ (α / 3) * (1 + x) ^ (α / 3)) := by
      rw [Real.mul_rpow (le_of_lt hbz) hx0]
    have h6 : b ^ (α / 3) * (a - b) ≤ a ^ (α / 3) * a := by
      have h1' : b ^ (α / 3) * (a - b) ≤ b ^ (α / 3) * a :=
        mul_le_mul_of_nonneg_left (by linarith) hbp
      have h2' : b ^ (α / 3) * a ≤ a ^ (α / 3) * a := mul_le_mul_of_nonneg_right hGa ha0
      linarith
    nlinarith [h1, h1'', h2, h3, h4, h5, h6, hp0]

/-! ## The elementary integral -/

/-- `∫_θ^{π/2} sin t cos²t dt = cos³θ/3`. -/
lemma integral_sin_cos_sq_eq (θ : ℝ) (hθ : θ ≤ Real.pi / 2) :
    ∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 = Real.cos θ ^ 3 / 3 := by
  have hderiv : ∀ x ∈ Set.Ioo θ (Real.pi / 2),
      HasDerivAt (fun t : ℝ => -(Real.cos t ^ 3 / 3)) (Real.sin x * Real.cos x ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos x ^ 2 * (-Real.sin x)) x := by
      have h := (Real.hasDerivAt_cos x).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = (fun t : ℝ => Real.cos t ^ 3) from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have hh : HasDerivAt (fun t : ℝ => -(Real.cos t ^ 3 / 3))
        (-(3 * Real.cos x ^ 2 * (-Real.sin x) / 3)) x := (h1.div_const 3).neg
    exact hh.congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => -(Real.cos t ^ 3 / 3)) (Set.Icc θ (Real.pi / 2)) := by
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2) volume θ
      (Real.pi / 2) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ hcont hderiv hint
  rw [h, Real.cos_pi_div_two]
  ring

/-! ## The target estimate -/

theorem H1_bound {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1/4) (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    |3 * (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
        / Real.cos θ ^ 3 - Work.Spaces.Gam α θ| ≤ 3 * α * Real.cos θ ^ (2 * α / 3) := by
  have hθ1 : Real.pi / 4 ≤ θ := le_of_lt hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hGam_cont : Continuous (Work.Spaces.Gam α) := by
    change Continuous (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3))
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith))
  have hu_cont : Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2) := by fun_prop
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) volume θ
      (Real.pi / 2) := (hu_cont.mul hGam_cont).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ) volume θ
      (Real.pi / 2) := (hu_cont.mul continuous_const).intervalIntegrable _ _
  have hIntg : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        (Work.Spaces.Gam α t - Work.Spaces.Gam α θ)) volume θ (Real.pi / 2) :=
    (hu_cont.mul (hGam_cont.sub continuous_const)).intervalIntegrable _ _
  have hIntN : IntervalIntegrable
      (fun t : ℝ => -(Real.sin t * Real.cos t ^ 2 *
        (Work.Spaces.Gam α t - Work.Spaces.Gam α θ))) volume θ (Real.pi / 2) := hIntg.neg
  have hIu : (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2) = Real.cos θ ^ 3 / 3 :=
    integral_sin_cos_sq_eq θ hθ2
  set A := ∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t with hA
  set Q := ∫ t in θ..(Real.pi / 2),
      Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ) with hQ
  set P := Real.cos θ ^ 3 with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _
  have hGθint : (∫ t in θ..(Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ)
      = Work.Spaces.Gam α θ * (Real.cos θ ^ 3 / 3) := by
    rw [show (∫ t in θ..(Real.pi / 2),
          Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ)
        = Work.Spaces.Gam α θ *
            (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2) from by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring), hIu]
  have hId : A - Work.Spaces.Gam α θ * (P / 3) = Q := by
    rw [hA, hQ, hP, ← hGθint, ← intervalIntegral.integral_sub hInt1 hInt2]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hQ_le : Q ≤ 0 := by
    rw [hQ]
    have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (Real.pi / 2) :=
      intervalIntegrable_const
    have hle : ∀ t ∈ Set.Icc θ (Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ) ≤ (0 : ℝ) := by
      intro t ht
      have hu0 : 0 ≤ Real.sin t * Real.cos t ^ 2 :=
        mul_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.1, hθ1, Real.pi_pos],
            by linarith [ht.2, Real.pi_pos]⟩)
          (sq_nonneg _)
      have hG : Work.Spaces.Gam α t - Work.Spaces.Gam α θ ≤ 0 := by
        have := Gam_anti hα hθ1 ht.1 ht.2
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hu0 hG
    have hmono := intervalIntegral.integral_mono_on hθ2 hIntg h0 hle
    simpa using hmono
  have hQ_low : -Q ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
      (Real.pi / 2 - θ) := by
    rw [hQ, ← intervalIntegral.integral_neg]
    have hle : ∀ t ∈ Set.Icc θ (Real.pi / 2),
        -(Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ))
          ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) := by
      intro t ht
      have := key_pointwise hα hα1 hθ1 ht.1 ht.2
      linarith
    have hconst : IntervalIntegrable
        (fun _ : ℝ => (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2))
        volume θ (Real.pi / 2) := intervalIntegrable_const
    have h1 := intervalIntegral.integral_mono_on hθ2 hIntN hconst hle
    have h2 : (∫ _ in θ..(Real.pi / 2),
          (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2))
        = (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
            (Real.pi / 2 - θ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rwa [h2] at h1
  have hkey : 3 * A / P - Work.Spaces.Gam α θ = 3 * Q / P := by
    have h1 : 3 * A - Work.Spaces.Gam α θ * P = 3 * Q := by linarith [hId]
    field_simp
    linarith
  have hcos2 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hδ : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith) (by linarith)
    rw [Real.sin_pi_div_two_sub] at h
    have h' : (Real.pi / 2) * ((2 / Real.pi) * (Real.pi / 2 - θ)) ≤
        (Real.pi / 2) * Real.cos θ :=
      mul_le_mul_of_nonneg_left h (by linarith [Real.pi_pos])
    have h'' : (Real.pi / 2) * ((2 / Real.pi) * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h', h''.le, h''.ge]
  have hup : Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ) ≤ (Real.pi / 2) * P := by
    rw [hP]
    have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
      nlinarith [Real.sin_le_one θ, hcos2, hsin0]
    calc Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ)
        ≤ Real.cos θ ^ 2 * (Real.pi / 2 - θ) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ Real.cos θ ^ 2 * ((Real.pi / 2) * Real.cos θ) :=
          mul_le_mul_of_nonneg_left hδ hcos2
      _ = (Real.pi / 2) * Real.cos θ ^ 3 := by ring
  have hGam_le : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) :=
    Gam_le_cos_rpow hα ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hcos23 : (0 : ℝ) ≤ Real.cos θ ^ (2 * α / 3) := Real.rpow_nonneg (le_of_lt hcos) _
  have hπ2le3 : Real.pi / 2 ≤ 3 := by linarith [Real.pi_lt_four]
  have habs : |3 * A / P - Work.Spaces.Gam α θ| = 3 * (-Q) / P := by
    rw [hkey, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonpos hQ_le,
      abs_of_pos hPpos]
  have hfinal : 3 * (-Q) / P ≤ 3 * α * Real.cos θ ^ (2 * α / 3) := by
    have hstep : 3 * (-Q) ≤ 3 * α * Real.cos θ ^ (2 * α / 3) * P := by
      have h1 : -Q ≤ (α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P) := by
        have hAG : 0 ≤ (α / 3) * Work.Spaces.Gam α θ := mul_nonneg (by linarith) hGam0
        have h1' : (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
              (Real.pi / 2 - θ)
            ≤ (α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P) := by
          have hE : (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
                (Real.pi / 2 - θ)
              = (α / 3) * Work.Spaces.Gam α θ *
                (Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ)) := by ring
          rw [hE]
          exact mul_le_mul_of_nonneg_left hup hAG
        linarith [hQ_low, h1']
      have h2 : 3 * ((α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P))
          ≤ 3 * α * Real.cos θ ^ (2 * α / 3) * P := by
        have hAG : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg (le_of_lt hα) hGam0
        have h3 : (Real.pi / 2) * (α * Work.Spaces.Gam α θ) ≤
            3 * (α * Real.cos θ ^ (2 * α / 3)) := by
          have h4 : α * Work.Spaces.Gam α θ ≤ α * Real.cos θ ^ (2 * α / 3) :=
            mul_le_mul_of_nonneg_left hGam_le (le_of_lt hα)
          have h5 : 0 ≤ α * Real.cos θ ^ (2 * α / 3) := mul_nonneg (le_of_lt hα) hcos23
          nlinarith [h4, h5, hπ2le3]
        nlinarith [h3, le_of_lt hPpos]
      linarith [h1, h2]
    rw [div_le_iff₀ hPpos]
    linarith [hstep]
  rw [habs]
  exact hfinal

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.H2_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

/-!
# `H2_bound`: the elementary `sin 2θ`-moment estimate at the right endpoint

For `θ ∈ (π/4, π/2)` we prove

`|(5/4)·sin 2θ − 15·(∫_θ^{π/2} sin²t cos³t dt)/(2 cos³θ)| ≤ 10·sin 2θ`.

The integral is the elementary polynomial `Ψ_S θ = 2/15 − sin³θ/3 + sin⁵θ/5`
(`Work.FTS.PhiStar.PsiS_eq_integral`), so the whole statement is a polynomial inequality
in `s = sin θ`, `c = cos θ` on the range where `s² > 1/2`.

Writing `B := 15·Ψ_S θ/(2c³) = (2 − 5s³ + 3s⁵)/(2c³)` and `sin 2θ = 2sc`, the two halves of
`|A − B| ≤ C` reduce to

* `B ≤ (45/4)·(2sc)`, i.e. `2 − 5s³ + 3s⁵ ≤ 45 s c⁴`, which after `c² = 1 − s²` is the
  perfect-square identity `45sc⁴ − 2 + 5s³ − 3s⁵ = (s−1)²(42s³ + 84s² + 41s − 2) ≥ 0`
  (with `84s² > 42 > 2` supplying the constant term);
* `B ≥ 0`, i.e. `2 − 5s³ + 3s⁵ = (1−s)²(3s³ + 6s² + 4s + 2) ≥ 0`.

Both are pure polynomial positivity; the only analysis is the range restriction, which is
used exactly through `s > 0`, `c > 0` and `s² > 1/2` (the latter from `cos 2θ < 0`).
-/

theorem H2_bound {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    |(5 / 4) * Real.sin (2 * θ)
      - 15 * (∫ t in θ..(Real.pi / 2), Real.sin t ^ 2 * Real.cos t ^ 3)
        / (2 * Real.cos θ ^ 3)| ≤ 10 * Real.sin (2 * θ) := by
  have hle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  rw [← Work.FTS.PhiStar.PsiS_eq_integral θ hle]
  set s := Real.sin θ with hs_def
  set c := Real.cos θ with hc_def
  have hs : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have hc : 0 < c := by
    rw [hc_def]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hs2 : (1 : ℝ) / 2 < s ^ 2 := by
    rw [hs_def]
    have h1 : Real.pi / 2 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi + Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
    have hcos : Real.cos (2 * θ) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2
    have h : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
      rw [Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq θ]
    linarith
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    rw [hs_def, hc_def]; exact Real.sin_sq_add_cos_sq θ
  have hPsiS : Work.FTS.PhiStar.PsiS θ = 2 / 15 - s ^ 3 / 3 + s ^ 5 / 5 := by
    simp only [Work.FTS.PhiStar.PsiS]
    rw [← hs_def]
  rw [hPsiS, Real.sin_two_mul]
  rw [← hs_def, ← hc_def]
  -- the key polynomial inequality `2 − 5s³ + 3s⁵ ≤ 45 s c⁴`
  have hkey : 2 - 5 * s ^ 3 + 3 * s ^ 5 ≤ 45 * s * c ^ 4 := by
    have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
    have hc4 : c ^ 4 = (1 - s ^ 2) ^ 2 := by
      have h1 : c ^ 4 = (c ^ 2) ^ 2 := by ring
      rw [h1, hc2]
    have hfac : 45 * s * c ^ 4 - 2 + 5 * s ^ 3 - 3 * s ^ 5
        = (s - 1) ^ 2 * (42 * s ^ 3 + 84 * s ^ 2 + 41 * s - 2) := by
      rw [hc4]; ring
    have hQ : 0 ≤ 42 * s ^ 3 + 84 * s ^ 2 + 41 * s - 2 := by
      have hs3 : 0 ≤ s ^ 3 := by positivity
      nlinarith [hs, hs2, hs3]
    have h2 := mul_nonneg (sq_nonneg (s - 1)) hQ
    linarith [hfac, h2]
  have hB : 15 * (2 / 15 - s ^ 3 / 3 + s ^ 5 / 5) / (2 * c ^ 3) ≤ (45 / 4) * (2 * s * c) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * c ^ 3)]
    nlinarith [hkey]
  have hB0 : 0 ≤ 15 * (2 / 15 - s ^ 3 / 3 + s ^ 5 / 5) / (2 * c ^ 3) := by
    apply div_nonneg _ (by positivity)
    have hfac2 : 2 - 5 * s ^ 3 + 3 * s ^ 5 = (1 - s) ^ 2 * (3 * s ^ 3 + 6 * s ^ 2 + 4 * s + 2) :=
      by ring
    have hpos : 0 < 3 * s ^ 3 + 6 * s ^ 2 + 4 * s + 2 := by positivity
    have hprod := mul_nonneg (sq_nonneg (1 - s)) (le_of_lt hpos)
    linarith [hfac2, hprod]
  rw [abs_le]
  constructor
  · nlinarith [hB]
  · have hx : 0 < 2 * s * c := by positivity
    nlinarith [hB0, hx]

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.PsiDivS2Sup.derivG_reg_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.PsiDivS2Sup

/-- The difference telescopes:
`(c + G₀/2)/(S²C³) - c/S² = (c(1 - C³) + G₀/2)/(S²C³)`. -/
private lemma PsiDivS2Sup_derivG_ident (c θ g : ℝ) (hS : Real.sin θ ≠ 0)
    (hC : Real.cos θ ≠ 0) :
    (c + g / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3) - c / Real.sin θ ^ 2
      = (c * (1 - Real.cos θ ^ 3) + g / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
  field_simp
  ring

theorem derivG_reg_bound {α c θ : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    |(c + Work.FTS.PhiStar.Gzero α θ / 2) / (Real.sin θ ^ 2 * Real.cos θ ^ 3)
      - c / Real.sin θ ^ 2| ≤ 24 * |c| + 7 * Real.pi ^ 2 := by
  obtain ⟨hθ0, hθh⟩ := hθ
  have hπ2 : θ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hSpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθh, Real.pi_gt_three])
  have hCpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθh, Real.pi_gt_three]⟩
  have hG := Work.FTS.PhiStar.Gzero_abs_le_sq α hα hα4 (le_of_lt hθ0) (by linarith)
  -- `cos θ ≥ 1/2` on `(0, 1/2)`
  have hChalf : (1 / 2 : ℝ) ≤ Real.cos θ := by
    have hθ3 : θ ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 3)
      (le_of_lt hθ0) (by linarith [Real.pi_pos]) hθ3
    rwa [Real.cos_pi_div_three] at h
  have hC3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by nlinarith [hChalf, sq_nonneg (Real.cos θ)]
  have hCle1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hC3le1 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hCpos) hCle1
  have hCm : 1 - Real.cos θ ^ 3 ≤ 3 * Real.sin θ ^ 2 := by
    have h1mC : 0 ≤ 1 - Real.cos θ := by linarith
    nlinarith [Real.sin_sq_add_cos_sq θ, h1mC, hCle1, hCpos]
  -- `sin θ ≥ 2θ/π` on `(0, 1/2)`
  have hS2 : (4 : ℝ) * θ ^ 2 / Real.pi ^ 2 ≤ Real.sin θ ^ 2 := by
    have h := Real.mul_le_sin (le_of_lt hθ0) hπ2
    have hpos : 0 ≤ 2 / Real.pi * θ := by positivity
    have h2 := pow_le_pow_left₀ hpos h 2
    have hval : (2 / Real.pi * θ) ^ 2 = 4 * θ ^ 2 / Real.pi ^ 2 := by field_simp; ring
    linarith [h2, hval.le, hval.symm.le]
  have hden : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_pos (pow_pos hSpos 2) (pow_pos hCpos 3)
  rw [PsiDivS2Sup_derivG_ident c θ (Work.FTS.PhiStar.Gzero α θ) (ne_of_gt hSpos) (ne_of_gt hCpos),
    abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hnum : |c * (1 - Real.cos θ ^ 3) + Work.FTS.PhiStar.Gzero α θ / 2|
      ≤ |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2 := by
    have h1 : |c * (1 - Real.cos θ ^ 3)| ≤ |c| * (3 * Real.sin θ ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.cos θ ^ 3)]
      exact mul_le_mul_of_nonneg_left hCm (abs_nonneg c)
    have h2 : |Work.FTS.PhiStar.Gzero α θ / 2| ≤ 7 * θ ^ 2 / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc |c * (1 - Real.cos θ ^ 3) + Work.FTS.PhiStar.Gzero α θ / 2|
        ≤ |c * (1 - Real.cos θ ^ 3)| + |Work.FTS.PhiStar.Gzero α θ / 2| := abs_add_le _ _
      _ ≤ |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2 := by linarith
  have hrhs : |c| * (3 * Real.sin θ ^ 2) + 7 * θ ^ 2 / 2
      ≤ (24 * |c| + 7 * Real.pi ^ 2) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    have hS2nn : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
    have h1 : |c| * (3 * Real.sin θ ^ 2) ≤ |c| * 24 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
      have h3 : 3 * Real.sin θ ^ 2 ≤ 24 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
        nlinarith [hC3, hS2nn]
      have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
      linarith [h4]
    have h2 : 7 * θ ^ 2 / 2 ≤ 7 * Real.pi ^ 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
      have hπ2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
      have hmul : 4 * θ ^ 2 / Real.pi ^ 2 * (1 / 8) ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
        mul_le_mul hS2 hC3 (by norm_num) hS2nn
      have hv : 4 * θ ^ 2 / Real.pi ^ 2 * (1 / 8) = θ ^ 2 / (2 * Real.pi ^ 2) := by
        field_simp; ring
      rw [hv, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)] at hmul
      nlinarith [hmul, hπ2pos]
    nlinarith [h1, h2]
  linarith

end Work.FTS.PhiStar.PsiDivS2Sup
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.radGreen_phiA_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary integral computations -/

/-- `∫_0^z t^{p-2} dt = z^{p-1}/(p-1)` for `p ≥ 3`, `z > 0`. -/
theorem rpowInt_zero_to_z_sub_two {p z : ℝ} (hp : 3 ≤ p) (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z, t ^ (p - 2) = z ^ (p - 1) / (p - 1) := by
  have h := integral_rpow (a := (0 : ℝ)) (b := z) (r := p - 2)
    (Or.inl (by linarith : (-1 : ℝ) < p - 2))
  rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (by linarith : p - 1 ≠ 0)] at h
  simpa using h

/-- `∫_{Ioi z} t^{-q-2} dt = z^{-q-1}/(q+1)` for `q > 0`, `z > 0`. -/
theorem rpowInt_Ioi_neg_two {q z : ℝ} (hq : 0 < q) (hz : 0 < z) :
    ∫ t in Set.Ioi z, t ^ (-q - 2) = z ^ (-q - 1) / (q + 1) := by
  have h := integral_Ioi_rpow_of_lt (a := -q - 2) (c := z) (by linarith) hz
  rw [show -q - 2 + 1 = -q - 1 by ring] at h
  rw [h]
  have h1 : (-q - 1 : ℝ) ≠ 0 := by linarith
  have h2 : (q + 1 : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-! ## Comparison of an integral with a pointwise majorant -/

/-- **Interval-integral comparison.**  If `|f| ≤ g` on `Ioc a b` and `g` is interval integrable,
then `|∫_a^b f| ≤ ∫_a^b g`. -/
theorem abs_intervalIntegral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioc a b, |f t| ≤ g t) (hg : IntervalIntegrable g volume a b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  have h' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t :=
    Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := intervalIntegral.norm_integral_le_of_norm_le hab h' hg
  simpa [Real.norm_eq_abs] using h2

/-- **Set-integral comparison on a tail `Ioi z`.**  If `|f| ≤ g` on `Ioi z` and `g` is integrable
there, then `|∫_{Ioi z} f| ≤ ∫_{Ioi z} g`. -/
theorem abs_setIntegral_Ioi_le {f g : ℝ → ℝ} {z : ℝ}
    (h : ∀ t ∈ Set.Ioi z, |f t| ≤ g t) (hg : IntegrableOn g (Set.Ioi z) volume) :
    |∫ t in Set.Ioi z, f t| ≤ ∫ t in Set.Ioi z, g t := by
  have h' : ∀ᵐ t ∂(volume.restrict (Set.Ioi z)), ‖f t‖ ≤ g t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := MeasureTheory.norm_integral_le_of_norm_le hg h'
  simpa [Real.norm_eq_abs] using h2

/-! ## A rational identity used for the normalising factor -/

private lemma one_div_mul_one_div (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    1 / (a * b) * (1 / c) = 1 / (b * (a * c)) := by
  field_simp

/-! ## The Green-function estimate -/

/-- **The mode-`m` radial Green's function of a source with `1/t` decay.**  If `|c t| ≤ M/t` for
every `t > 0`, then for `0 < α ≤ 1` and `m ≥ 1`

  `|radGreen α m c z| ≤ M / (z·(m+1)²)`   for every `z > 0`.

(The estimate is uniform in `α`: the `α`-dependence of the two indicial exponents cancels against
the normalising factor `1/(α(4m+5))`.) -/
private lemma radGreen_le_of_inv_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ t : ℝ, 0 < t → |c t| ≤ M / t) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ M / (z * ((m : ℝ) + 1) ^ 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp3 : (3 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    rw [le_div_iff₀ hα]
    nlinarith
  set p : ℝ := (2 * (m : ℝ) + 5) / α with hp
  set q : ℝ := 2 * (m : ℝ) / α with hq
  have hp3' : (3 : ℝ) ≤ p := hp ▸ hp3
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hq0 : (0 : ℝ) < q := by
    rw [hq]
    positivity
  have hKpos : (0 : ℝ) < 1 / (α * (4 * (m : ℝ) + 5)) := by positivity
  -- integrability of the two majorants
  have hInt1 : IntervalIntegrable (fun t : ℝ => M * t ^ (p - 2)) volume (0 : ℝ) z := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const (fun t _ => Or.inr (by linarith : (0 : ℝ) ≤ p - 2)))
  have hInt2 : IntegrableOn (fun t : ℝ => M * t ^ (-q - 2)) (Set.Ioi z) volume := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -q - 2) (c := z) (by linarith) hz
    exact h.const_mul M
  -- pointwise comparison of the integrands with the majorants
  have hpoint1 : ∀ t ∈ Set.Ioc (0 : ℝ) z, |c t * t ^ (p - 1)| ≤ M * t ^ (p - 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hpown : (0 : ℝ) ≤ t ^ (p - 1) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg hpown]
    calc |c t| * t ^ (p - 1)
        ≤ (M / t) * t ^ (p - 1) := mul_le_mul_of_nonneg_right (hc t ht0) hpown
      _ = M * (t ^ (-1 : ℝ) * t ^ (p - 1)) := by
            rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
      _ = M * t ^ ((-1 : ℝ) + (p - 1)) := by rw [Real.rpow_add ht0]
      _ = M * t ^ (p - 2) := by rw [show (-1 : ℝ) + (p - 1) = p - 2 by ring]
  have hpoint2 : ∀ t ∈ Set.Ioi z, |c t * t ^ (-q - 1)| ≤ M * t ^ (-q - 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hz ht
    have hpown : (0 : ℝ) ≤ t ^ (-q - 1) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg hpown]
    calc |c t| * t ^ (-q - 1)
        ≤ (M / t) * t ^ (-q - 1) := mul_le_mul_of_nonneg_right (hc t ht0) hpown
      _ = M * (t ^ (-1 : ℝ) * t ^ (-q - 1)) := by
            rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
      _ = M * t ^ ((-1 : ℝ) + (-q - 1)) := by rw [Real.rpow_add ht0]
      _ = M * t ^ (-q - 2) := by rw [show (-1 : ℝ) + (-q - 1) = -q - 2 by ring]
  -- the two integral bounds
  have hA : |∫ t in (0 : ℝ)..z, c t * t ^ (p - 1)| ≤ M * (z ^ (p - 1) / (p - 1)) := by
    have h := abs_intervalIntegral_le (f := fun t => c t * t ^ (p - 1))
      (g := fun t => M * t ^ (p - 2)) hz.le hpoint1 hInt1
    rwa [intervalIntegral.integral_const_mul, rpowInt_zero_to_z_sub_two hp3' hz] at h
  have hB : |∫ t in Set.Ioi z, c t * t ^ (-q - 1)| ≤ M * (z ^ (-q - 1) / (q + 1)) := by
    have h := abs_setIntegral_Ioi_le (f := fun t => c t * t ^ (-q - 1))
      (g := fun t => M * t ^ (-q - 2)) hpoint2 hInt2
    rwa [MeasureTheory.integral_const_mul, rpowInt_Ioi_neg_two hq0 hz] at h
  -- the definitional unfolding
  have hunfold : Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) *
        (z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
          + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))) := by
    have e1 : -(2 * (m : ℝ) + 5) / α = -p := by rw [hp]; ring
    have e2 : (2 * (m : ℝ) + 5) / α - 1 = p - 1 := by rw [hp]
    have e3 : 2 * (m : ℝ) / α = q := by rw [hq]
    have e4 : -(2 * (m : ℝ) / α) - 1 = -q - 1 := by rw [hq]
    unfold Work.FTS.PhiStar.Radial.radGreen
    rw [e1, e2, e3, e4]
  have hznp : (0 : ℝ) ≤ z ^ (-p) := Real.rpow_nonneg hz.le _
  have hzq : (0 : ℝ) ≤ z ^ q := Real.rpow_nonneg hz.le _
  -- triangle inequality + the two estimates
  have htri : |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
        + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))|
      ≤ z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
        + z ^ q * (M * (z ^ (-q - 1) / (q + 1))) := by
    have h1 : |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))|
        ≤ z ^ (-p) * (M * (z ^ (p - 1) / (p - 1))) := by
      rw [abs_mul, abs_of_nonneg hznp]
      exact mul_le_mul_of_nonneg_left hA hznp
    have h2 : |z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))|
        ≤ z ^ q * (M * (z ^ (-q - 1) / (q + 1))) := by
      rw [abs_mul, abs_of_nonneg hzq]
      exact mul_le_mul_of_nonneg_left hB hzq
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- `z`-power clearing
  have hzpow1 : z ^ (-p) * z ^ (p - 1) = z ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hz, show -p + (p - 1) = (-1 : ℝ) by ring]
  have hzpow2 : z ^ q * z ^ (-q - 1) = z ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hz, show q + (-q - 1) = (-1 : ℝ) by ring]
  have hstepH : z ^ (-p) * (M * (z ^ (p - 1) / (p - 1))) = (M / z) * (1 / (p - 1)) := by
    rw [show z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
        = M * (z ^ (-p) * z ^ (p - 1)) / (p - 1) by ring, hzpow1, Real.rpow_neg_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hstepT : z ^ q * (M * (z ^ (-q - 1) / (q + 1))) = (M / z) * (1 / (q + 1)) := by
    rw [show z ^ q * (M * (z ^ (-q - 1) / (q + 1)))
        = M * (z ^ q * z ^ (-q - 1)) / (q + 1) by ring, hzpow2, Real.rpow_neg_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- the normalising factor times the two indicial reciprocals
  have hp1eq : α * (p - 1) = 2 * (m : ℝ) + 5 - α := by
    rw [hp]
    field_simp
  have hq1eq : α * (q + 1) = 2 * (m : ℝ) + α := by
    rw [hq]
    field_simp
  have hcoefH : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (p - 1))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α)) := by
    rw [one_div_mul_one_div α (4 * (m : ℝ) + 5) (p - 1) (ne_of_gt hα) (by positivity)
      (ne_of_gt hp1)]
    rw [hp1eq]
  have hcoefT : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (q + 1))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α)) := by
    rw [one_div_mul_one_div α (4 * (m : ℝ) + 5) (q + 1) (ne_of_gt hα) (by positivity)
      (by positivity)]
    rw [hq1eq]
  have hS : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
      + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))
      ≤ 1 / ((4 * (m : ℝ) + 5) * (m : ℝ)) := by
    have h5 : (2 : ℝ) * (m : ℝ) ≤ 2 * (m : ℝ) + 5 - α := by linarith
    have h1 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
        ≤ 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have h2 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))
        ≤ 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) * (m : ℝ) ≤ 2 * (m : ℝ) + α)
        (by positivity)
    have h3 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ)))
        + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) = 1 / ((4 * (m : ℝ) + 5) * (m : ℝ)) := by
      field_simp
      ring
    linarith [h1, h2, h3.le]
  have hmge : ((m : ℝ) + 1) ^ 2 ≤ (4 * (m : ℝ) + 5) * (m : ℝ) := by nlinarith [hmR]
  have hMz : (0 : ℝ) ≤ M / z := div_nonneg hM hz.le
  have hdiv : M / z * (1 / ((4 * (m : ℝ) + 5) * (m : ℝ)))
      = M / (z * ((4 * (m : ℝ) + 5) * (m : ℝ))) := by
    field_simp
  have hXY : z * ((m : ℝ) + 1) ^ 2 ≤ z * ((4 * (m : ℝ) + 5) * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hmge hz.le
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = |(1 / (α * (4 * (m : ℝ) + 5))) *
          (z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
            + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1)))| := by rw [hunfold]
    _ = 1 / (α * (4 * (m : ℝ) + 5)) *
          |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
            + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))| := by
          rw [abs_mul, abs_of_pos hKpos]
    _ ≤ 1 / (α * (4 * (m : ℝ) + 5)) *
          (z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
            + z ^ q * (M * (z ^ (-q - 1) / (q + 1)))) :=
          mul_le_mul_of_nonneg_left htri hKpos.le
    _ = 1 / (α * (4 * (m : ℝ) + 5))
          * ((M / z) * (1 / (p - 1)) + (M / z) * (1 / (q + 1))) := by
          rw [hstepH, hstepT]
    _ = M / z * (1 / (α * (4 * (m : ℝ) + 5)) * (1 / (p - 1))
          + 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (q + 1))) := by ring
    _ = M / z * (1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
          + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))) := by rw [hcoefH, hcoefT]
    _ ≤ M / z * (1 / ((4 * (m : ℝ) + 5) * (m : ℝ))) := mul_le_mul_of_nonneg_left hS hMz
    _ = M / (z * ((4 * (m : ℝ) + 5) * (m : ℝ))) := hdiv
    _ ≤ M / (z * ((m : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_left hM (by positivity) hXY

/-! ## The source bound for `𝒜φ` -/

/-- `|𝒜φ(α,t)| = |phiA α t| ≤ 24/t` for every `t > 0` and `0 < α ≤ 1`. -/
private lemma phiA_abs_le_inv_prv (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 < t) :
    |Work.FTS.VocabO.phiA α t| ≤ 24 / t := by
  by_cases h1 : t ≤ 1
  · have h := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_small hα hα1 ht h1
    rw [le_div_iff₀ ht]
    nlinarith [h, ht, h1]
  · have h2 : 1 ≤ t := by linarith
    exact Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_large hα hα1 h2

/-! ## The target -/

theorem radGreen_phiA_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (m : ℕ), 1 ≤ m →
      (∀ z : ℝ, 0 < z →
        |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
          ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ, 1 ≤ z →
        |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
          ≤ C / (z * ((m : ℝ) + 1))) := by
  refine ⟨24, by norm_num, ?_⟩
  intro α hα hα1 m hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hgen : ∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := by
    intro z hz
    exact radGreen_le_of_inv_bound hα hα1 hm (M := 24) (by norm_num)
      (fun t ht => phiA_abs_le_inv_prv α t hα hα1 ht) hz
  have hpow : ((m : ℝ) + 1) ^ (-(2 : ℝ)) = 1 / ((m : ℝ) + 1) ^ 2 := by
    have h2 : ((m : ℝ) + 1) ^ (2 : ℝ) = ((m : ℝ) + 1) ^ 2 := Real.rpow_natCast _ 2
    rw [one_div, ← h2, ← Real.rpow_neg (le_of_lt hm1)]
  constructor
  · intro z hz
    have h := hgen z hz
    rw [hpow]
    have hle : 1 / z ≤ 1 + 1 / z := by linarith
    have hcoef : (0 : ℝ) ≤ 24 / ((m : ℝ) + 1) ^ 2 := by positivity
    calc |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := h
      _ = 24 / ((m : ℝ) + 1) ^ 2 * (1 / z) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, one_div, mul_inv]
            ring
      _ ≤ 24 / ((m : ℝ) + 1) ^ 2 * (1 + 1 / z) := mul_le_mul_of_nonneg_left hle hcoef
      _ = 24 * (1 + 1 / z) * (1 / ((m : ℝ) + 1) ^ 2) := by ring
  · intro z hz1
    have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have h := hgen z hz
    have hXY : z * ((m : ℝ) + 1) ≤ z * ((m : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hm1]) hz.le
    calc |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := h
      _ ≤ 24 / (z * ((m : ℝ) + 1)) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hXY

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.contDiffAt_model =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

/-- The radial profile `φ(z) = 2z/(1+z)²` is `C^n` at every `z ≠ -1` (in particular on `z > 0`),
since it is a quotient of polynomials with non-vanishing denominator. -/
theorem contDiffAt_phiR {n : ℕ} {z : ℝ} (hz : -1 < z) :
    ContDiffAt ℝ n Work.FTS.VocabO.phiR z := by
  show ContDiffAt ℝ n (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
  have hden : (1 + z) ^ 2 ≠ 0 := by
    have : 1 + z ≠ 0 := by linarith
    positivity
  exact ((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_id).div
    (((contDiffAt_const (c := (1 : ℝ))).add contDiffAt_id).pow 2) hden

theorem contDiffAt_model {α : ℝ} {Gz ψ : ℝ → ℝ} {z θ : ℝ} (n : ℕ) (hz : 0 < z)
    (hG : ContDiffAt ℝ n Gz z) (hψ : ContDiffAt ℝ n ψ θ) :
    ContDiffAt ℝ n (Function.uncurry (Work.FTS.PhiStar.Model α Gz ψ)) (z, θ) := by
  have hphi : ContDiffAt ℝ n Work.FTS.VocabO.phiR z := contDiffAt_phiR (by linarith)
  show ContDiffAt ℝ n (fun p : ℝ × ℝ =>
    Gz p.1 * Real.sin (2 * p.2) + α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ)
  have hsin : ContDiffAt ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) :=
    (((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_snd)).sin
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ => Gz p.1 * Real.sin (2 * p.2)) (z, θ) :=
    (hG.comp (z, θ) contDiffAt_fst).mul hsin
  have h2 : ContDiffAt ℝ n (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ) :=
    ((contDiffAt_const (c := α)).mul (hphi.comp (z, θ) contDiffAt_fst)).mul
      (hψ.comp (z, θ) contDiffAt_snd)
  exact h1.add h2

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.contDiffOn_model =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.contDiffOn_model`

The joint `C^n`-regularity of the two-term model `Model α Gz ψ` on the open quadrant:
the model is `(z,θ) ↦ Gz z · sin 2θ + α φ(z) ψ(θ)`, so on `Q0 = (0,∞) × (0,π/2)` it is
`C^n` as soon as `Gz` is `C^n` on `(0,∞)` and `ψ` is `C^n` on `(0,π/2)` — the radial factor
`φ = 2z/(1+z)²` being a rational function with non-vanishing denominator for `z > 0`.

Note (`open scoped Real`): the statement below writes `π` for the angular endpoint; the
`Real` scope is opened so that `π` denotes `Real.pi` (as it does in the definition of
`Work.FTS.EllipticEst.Q0` and in the sibling statement `contDiffAt_model`).
-/

open scoped Real Topology

namespace Work.FTS.PhiStar

/-- **Joint regularity of the model part.**  If `Gz` is `C^n` on `(0,∞)` and `ψ` is `C^n` on
`(0,π/2)`, then the uncurried model `(z,θ) ↦ Gz z · sin 2θ + α φ(z) ψ(θ)` is `C^n` on the
open quadrant `Q0 = (0,∞) × (0,π/2)`.

Every factor is smooth on exactly the interval on which its coordinate ranges over `Q0`:
`sin (2·)` is smooth everywhere, `φ = 2z/(1+z)²` is smooth on `Ioi 0`, and the composition
of `hGz`, `hψ` with the two projections through `ContDiffOn.comp` plus closure of
`ContDiffOn` under products and sums gives the claim. -/
theorem contDiffOn_model {α : ℝ} {Gz ψ : ℝ → ℝ} (n : ℕ)
    (hGz : ContDiffOn ℝ n Gz (Set.Ioi 0)) (hψ : ContDiffOn ℝ n ψ (Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.FTS.PhiStar.Model α Gz ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ => Gz p.1) Work.FTS.EllipticEst.Q0 :=
    hGz.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hPsi : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.2) Work.FTS.EllipticEst.Q0 :=
    hψ.comp contDiffOn_snd fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_snd).sin
  have hden : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    positivity
  have hnum : ContDiffOn ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.1) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_fst
  have hden2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_fst).pow 2
  have hphi : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    hnum.div hden2 hden
  have hall : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Gz p.1 * Real.sin (2 * p.2) + α * (2 * p.1 / (1 + p.1) ^ 2) * ψ p.2)
      Work.FTS.EllipticEst.Q0 :=
    (hG.mul hsin).add (((contDiffOn_const (c := α)).mul hphi).mul hPsi)
  show ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Gz p.1 * Real.sin (2 * p.2) + α * Work.FTS.VocabO.phiR p.1 * ψ p.2)
      Work.FTS.EllipticEst.Q0
  simpa only [Work.FTS.VocabO.phiR] using hall

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.FstarSlotBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
Sharp pointwise bounds for the fixed profile `F_* = Construction.Fstar α` and its slots,
in terms of the radial factor `hKer z = z/(1+z)^2` (`Work.Spaces.hKer`).

ROUTE.  `Fstar_eq_factored` (`Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored`) gives
`Fstar α z θ = (2α/c α) * Gam α θ * hKer z`, `Dz_Fstar_eq_Hz` (`FstarPkg.Dz_Fstar_eq_Hz`)
gives `Dz (Fstar α) z θ = (α/c α) * Gam α θ * Hz z` with `Hz z = 2z(1-z)/(1+z)^3`, and
`pzIter_DthIter_Fstar_eq α 1 0` gives `Dth (Fstar α) z θ = (2α/c α) * dthU (Gam α) θ * hKer z`.
Then `|hKer z| ≤ 1/(1+z)` is trivial, `|Hz z| ≤ 2*hKer z` for `z ≥ 0`, `Gam_bounds` gives
`0 ≤ Gam ≤ 1`, `c_bounds` gives `1/c ≤ 10`, and `Work.Spaces.dthU_Gam_le 1 le_rfl α hα hα1 θ hθ`
gives `|dthU (Gam α) θ| ≤ α * tBound 0 0 * Gam α θ` with `tBound 0 0 ≥ 0`.
The templates `Fstar_abs_le`, `DzFstar_abs_le`, `DthFstar_abs_le` in
`Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.FstarSlotPt` prove the same
statements with `1/(1+z)` instead of `hKer z` — adapt them.
The last conjunct is `FK (Fstar α) z = α * FM.Fstar z = 2α * hKer z` exactly
(`FK F z = ∫ θ in Iθ, F z θ * K θ` and `c α = ∫ θ in Iθ, Gam α θ * K θ`, use
`MeasureTheory.integral_const_mul`).
-/

/-! ## Elementary facts about the radial factor and the angular interval -/

/-- The radial factor `hKer z = z/(1+z)²` is nonnegative for `z > 0`. -/
lemma hKer_nonneg_of_pos {z : ℝ} (hz : 0 < z) : 0 ≤ Work.Spaces.hKer z := by
  rw [Work.Spaces.hKer_apply]
  exact div_nonneg hz.le (by positivity)

/-- For `z > 0` the absolute value of `hKer z` is `hKer z` itself. -/
lemma abs_hKer_of_pos {z : ℝ} (hz : 0 < z) :
    |Work.Spaces.hKer z| = Work.Spaces.hKer z :=
  abs_of_nonneg (hKer_nonneg_of_pos hz)

/-- The radial factor `Hz(z) = 2z(1-z)/(1+z)³` of `D_zF_*` obeys the sharp bound
`|Hz(z)| ≤ 2 hKer z = 2z/(1+z)²` for `z > 0` (sharper than the `2/(1+z)` used elsewhere). -/
lemma Hz_abs_le_hKer {z : ℝ} (hz : 0 < z) :
    |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 * Work.Spaces.hKer z := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, Work.Spaces.hKer_apply, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
  have hrew : 2 * (z / (1 + z) ^ 2) = 2 * z / (1 + z) ^ 2 := by ring
  rw [hrew, div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)
    (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  have hnum : |2 * z * (1 - z)| ≤ 2 * z * (1 + z) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le]
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
  calc |2 * z * (1 - z)| * (1 + z) ^ 2 ≤ (2 * z * (1 + z)) * (1 + z) ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * z * (1 + z) ^ 3 := by ring

/-- `cos θ ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- On `Iθ` the angular weight `K θ = 3 sin θ cos²θ` converts `|∂_θ F|` into
`(3/2) cos θ` times the `D_θ`-slot `|sin(2θ) ∂_θF|`. -/
lemma K_mul_abs_pth_eq (F : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * |Work.Spaces.pth F z θ|
      = (3 / 2) * Real.cos θ * |Real.sin (2 * θ) * Work.Spaces.pth F z θ| := by
  have hsin := sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.Spaces.K, abs_mul, abs_of_nonneg hsin, Real.sin_two_mul]
  ring

/-- `|D_θF_*(z,θ)| ≤ 20 tBound 0 0 · hKer z` for `0 < α ≤ 1`, `z > 0`, `θ ∈ Iθ`: the sharp
`hKer`-version of `FstarSlotPt.DthFstar_abs_le`. -/
lemma DthFstar_abs_le_hKer {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
      ≤ 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by
  have hid : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = (2 * α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          * Work.Spaces.hKer z := by
    have h := Work.FTS.Nonlinear.FstarPkg.pzIter_DthIter_Fstar_eq α 1 0 z θ
    simpa using h
  rw [hid, abs_mul, abs_mul, abs_hKer_of_pos hz]
  have hc := Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hT : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
  have hK : 0 ≤ Work.Spaces.hKer z := hKer_nonneg_of_pos hz
  have hdth : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    have h := Work.Spaces.dthU_Gam_le 1 le_rfl α hα hα1 θ hθ
    have h1 : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := by simpa using h
    calc |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := h1
      _ ≤ α * Work.Spaces.tBound 0 0 * 1 :=
          mul_le_mul_of_nonneg_left hG.2 (mul_nonneg hα.le hT)
      _ = α * Work.Spaces.tBound 0 0 := by ring
  calc (|2 * α / Work.Spaces.c α|
        * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|) * Work.Spaces.hKer z
      ≤ ((20 * α) * (α * Work.Spaces.tBound 0 0)) * Work.Spaces.hKer z :=
        mul_le_mul (mul_le_mul hc hdth (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
          le_rfl hK (by positivity)
    _ = 20 * (α ^ 2) * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by ring
    _ ≤ 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by
        have hsq : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
        have h1 : 20 * (α ^ 2) * Work.Spaces.tBound 0 0 ≤ 20 * 1 * Work.Spaces.tBound 0 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hT
        calc 20 * (α ^ 2) * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z
            ≤ 20 * 1 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z :=
              mul_le_mul_of_nonneg_right h1 hK
          _ = 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by ring

theorem FstarSlotBounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {z θ : ℝ}, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar α z θ| ≤ C * (z / (1 + z) ^ 2) ∧
      |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ C * (z / (1 + z) ^ 2) ∧
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ C * (z / (1 + z) ^ 2) ∧
      Work.Spaces.K θ * |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ C * (z / (1 + z) ^ 2) * Real.cos θ ∧
      |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ C * (z / (1 + z) ^ 2) := by
  refine ⟨30 * (Work.Spaces.tBound 0 0 + 1), by
    have h := Work.Spaces.tBound_nonneg 0 0; linarith, ?_⟩
  rintro α hαI z θ hz hθ
  obtain ⟨hα, hα1⟩ := hαI
  have hT : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
  have hK : 0 ≤ Work.Spaces.hKer z := hKer_nonneg_of_pos hz
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hcoef := Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hcoefZ : |α / Work.Spaces.c α| ≤ 10 * α := by
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- the slot `F_*`
  have hF : |Work.Construction.Fstar α z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    simp only [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored]
    rw [abs_mul, abs_mul, abs_of_nonneg hG.1, abs_hKer_of_pos hz]
    have h20 : 20 * α ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by nlinarith
    calc (|2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ) * Work.Spaces.hKer z
        ≤ ((20 * α) * 1) * Work.Spaces.hKer z :=
          mul_le_mul (mul_le_mul hcoef hG.2 hG.1 (mul_nonneg (by norm_num) hα.le)) le_rfl hK
            (by positivity)
      _ = 20 * α * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h20 hK
  -- the slot `D_θF_*`
  have hDth := DthFstar_abs_le_hKer hα hα1 hz hθ
  have h2 : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    have heq : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
      rw [Work.Spaces.Dth]
    rw [heq]
    have h20 : 20 * Work.Spaces.tBound 0 0 ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by
      linarith
    exact le_trans hDth (mul_le_mul_of_nonneg_right h20 hK)
  -- the slot `D_zF_*`
  have h3 : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1 : ℝ) < z),
      abs_mul, abs_mul, abs_of_nonneg hG.1]
    have hHz := Hz_abs_le_hKer hz
    have h20 : 20 * α ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by nlinarith
    calc |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ
          * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
        ≤ (10 * α) * (1 * (2 * Work.Spaces.hKer z)) :=
          mul_le_mul hcoefZ (mul_le_mul hG.2 hHz (abs_nonneg _) (by norm_num))
            (mul_nonneg hG.1 (abs_nonneg _)) (mul_nonneg (by norm_num) hα.le)
      _ = 20 * α * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h20 hK
  -- the slot `K θ · |∂_θF_*|`
  have h4 : Work.Spaces.K θ * |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z * Real.cos θ := by
    rw [K_mul_abs_pth_eq (Work.Construction.Fstar α) hθ]
    have heq : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
      rw [Work.Spaces.Dth]
    rw [heq]
    have hcos := cos_nonneg_of_mem_Iθ hθ
    calc (3 / 2) * Real.cos θ * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        ≤ (3 / 2) * Real.cos θ * (20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z) :=
          mul_le_mul_of_nonneg_left hDth (mul_nonneg (by norm_num) hcos)
      _ = 30 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z * Real.cos θ := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z * Real.cos θ := by
          have h1 : 30 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z
              ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
            mul_le_mul_of_nonneg_right (by linarith) hK
          exact mul_le_mul_of_nonneg_right h1 hcos
  -- the slot `(F_*, K)_{L²_θ}`
  have h5 : |Work.Construction.FK (Work.Construction.Fstar α) z|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    have hz2 : (2 : ℝ) * z / (1 + z) ^ 2 = 2 * Work.Spaces.hKer z := by
      rw [Work.Spaces.hKer_apply]; ring
    rw [hz2, abs_of_nonneg (mul_nonneg hα.le (mul_nonneg (by norm_num) hK))]
    have h2le : (2 : ℝ) ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by linarith
    calc α * (2 * Work.Spaces.hKer z) ≤ 1 * (2 * Work.Spaces.hKer z) :=
          mul_le_mul_of_nonneg_right hα1 (mul_nonneg (by norm_num) hK)
      _ = 2 * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h2le hK
  exact ⟨hF, h2, h3, h4, h5⟩

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongPersist.DzFstar_W6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z F_*` package at order `6`: `DzFstar_W6`

The radial derivative of the fundamental profile,
`D_z F_*(z,θ) = α · (Γ(θ)/c(α)) · H(z)` with `H(z) = 2z(1-z)/(1+z)³`
(`Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz`), satisfies

  `D_z F_* ∈ 𝒲^{6,∞}`  and  `|D_z F_*|_{𝒲^{6,∞}} ≤ C α`,  `C` universal, for every `0 < α ≤ 1`.

The level-`4` version of this statement is `Work.FTS.Nonlinear.FstarPkg.DzFstar_W`.  Nothing in
that proof used the bound `4`: the generic estimate
`Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial` is stated for an *arbitrary* level `l`, the
radial weighted bound `Hz_deriv_bound` holds for *every* `k`, and the norms only depend on the
values on `z > -1` (`WlInf_congr`).  So the whole `𝒲^{6,∞}`-bound follows by re-running the
assembly with `4 ↦ 6`.  We prove the general statement `DzFstar_Wl l` once and specialize.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-! ## The universal constant -/

/-- The universal (`α`-independent) constant multiplying `|α/c|` in the `𝒲^{l,∞}`-bound for
`D_z F_*`: the sum over the slots of `𝒲^{l,∞}` of the radial bound `HB` times the angular
coefficient `tBound (j-1) 0`.  This is the level-`l` analogue of
`Work.FTS.Nonlinear.FstarPkg.KBdz`. -/
noncomputable def DzKB (l : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), Work.FTS.Nonlinear.FstarPkg.HB k)
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.FTS.Nonlinear.FstarPkg.HB k * Work.Spaces.tBound (j - 1) 0 else 0)

lemma DzKB_nonneg (l : ℕ) : 0 ≤ DzKB l := by
  rw [DzKB]
  refine add_nonneg (Finset.sum_nonneg fun k _ => Work.FTS.Nonlinear.FstarPkg.HB_nonneg k) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.FTS.Nonlinear.FstarPkg.HB_nonneg k) (Work.Spaces.tBound_nonneg _ _)
  · norm_num

/-! ## The estimate at a general level -/

/-- `D_z F_* ∈ 𝒲^{l,∞}` with `|D_z F_*|_{𝒲^{l,∞}} ≤ (10 · DzKB l + 1) α`, for all `0 < α ≤ 1`.

The proof is the level-`4` proof of `Work.FTS.Nonlinear.FstarPkg.DzFstar_W` with `4 ↦ l`:
`D_z F_*` agrees on `z > -1` with the separated product `(α/c) · Γ ⊗ Hz`, whose `𝒲^{l,∞}`-norm
is bounded by `|α/c| · DzKB l` by `WlInf_Gamma_radial`, and `|α/c| ≤ 10 α` by `c_bounds`. -/
theorem DzFstar_Wl (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α l (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α l (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α := by
  refine ⟨10 * DzKB l + 1, by linarith [DzKB_nonneg l], fun α hα hα1 => ?_⟩
  -- `c(α) ≥ 1/10`, hence `|α/c| ≤ 10α`.
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- `WlInf` (and `WlInfMem`) only see `z > -1`, where `D_z F_*` is the product
  -- `(α/c) · Γ ⊗ Hz`.
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr
    (f := Work.Spaces.Dz (Work.Construction.Fstar α))
    (g := fun z θ => (α / Work.Spaces.c α)
      * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z))
    (fun z hz θ => Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz) α l
  -- the `Γ ⊗ Hz` estimate, with `B = HB` from the radial bound
  obtain ⟨hmem, hbound⟩ := Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial (l := l)
    (H := Work.FTS.Nonlinear.FstarPkg.Hz) (B := Work.FTS.Nonlinear.FstarPkg.HB)
    (D := α / Work.Spaces.c α) (α := α) hα hα1
    (fun k _ z hz => Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound k z hz)
  refine ⟨hcongr.2.mpr hmem, ?_⟩
  rw [hcongr.1]
  calc Work.Spaces.WlInf α l
        (fun z θ => (α / Work.Spaces.c α)
          * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z))
      ≤ |α / Work.Spaces.c α| * DzKB l := hbound
    _ ≤ 10 * α * DzKB l := mul_le_mul_of_nonneg_right hcoef (DzKB_nonneg l)
    _ = 10 * DzKB l * α := by ring
    _ ≤ (10 * DzKB l + 1) * α := by nlinarith [hα, DzKB_nonneg l]

/-! ## The requested statement -/

theorem DzFstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
  DzFstar_Wl 6

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.L12Iter.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.L12Iter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial weight of the standing bound -/

/-- The radial weight `z^{3/2}/(1+z)²` appearing in the standing pointwise bound
`|mixed b a (F n) z θ| ≤ C₀ · Rwt z`. -/
def Rwt (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

theorem Rwt_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Rwt z := by
  rw [Rwt]
  exact div_nonneg (Real.rpow_nonneg hz _) (by positivity)

theorem Rwt_pos {z : ℝ} (hz : 0 < z) : 0 < Rwt z := by
  rw [Rwt]
  exact div_pos (Real.rpow_pos_of_pos hz _) (by positivity)

/-- `Rwt s / s = s^{1/2}/(1+s)²`. -/
theorem Rwt_div (s : ℝ) (hs : 0 < s) : Rwt s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h1 : s ^ ((3 : ℝ) / 2) / s = s ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_sub hs ((3 : ℝ) / 2) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  rw [Rwt, div_div, mul_comm ((1 + s) ^ 2) s, ← div_div, h1]

/-! ## Finite-order smoothness of the `D_z`-iterates -/

/-- `D_z^k f` is `C¹` on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem contDiffOn_one_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 k 1
    (h4.of_le (Nat.cast_le.mpr (by omega : 1 + k ≤ 4)))

/-- `D_z^k f` is continuous on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem continuousOn_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_one_DzIter h4 hk).continuousOn

/-! ## Differentiability of the radial slices -/



/-! ## The angular weight `K(θ) = 3 sin θ cos²θ` -/

theorem abs_Ktheta_le_three (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hcos, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  rw [Work.Elliptic.Ktheta, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [hsin, hcos2, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ ^ 2)]

theorem Ktheta_zero_left : Work.Elliptic.Ktheta 0 = 0 := by
  rw [Work.Elliptic.Ktheta]; norm_num

theorem Ktheta_zero_right : Work.Elliptic.Ktheta (Real.pi / 2) = 0 := by
  rw [Work.Elliptic.Ktheta, Real.cos_pi_div_two]; norm_num

/-! ## Pointwise bounds on the angular slices -/

/-- The pointwise bound of a `K(θ)·D_z^k f (z,θ)` slice, valid a.e. on `Iθ`, for `k ≤ 2`:
`‖K(θ)·D_z^k f (z,θ)‖ ≤ 3·C₀·Rwt z`.  (At the two endpoints `K` vanishes, so the bound holds
there too, but only the a.e. statement is needed.) -/
theorem abs_Ktheta_mul_DzIter_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖ ≤ 3 * (C0 * Rwt z) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun θ hθ => ?_
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Ktheta_zero_left, zero_mul, norm_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg hC0 (Rwt_nonneg hz.le))
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      rw [Ktheta_zero_right, zero_mul, norm_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg hC0 (Rwt_nonneg hz.le))
    · rw [Real.norm_eq_abs, abs_mul]
      have := mul_le_mul (abs_Ktheta_le_three θ) (hbd k hk z θ hz h0 h1)
        (abs_nonneg (Work.Spaces.DzIter k f z θ)) (by norm_num : (0 : ℝ) ≤ 3)
      simpa [mul_assoc] using this

/-- The `θ`-slice `θ ↦ K(θ)·D_z^k f (z,θ)` is a.e. strongly measurable for the restriction of
Lebesgue measure to `Iθ` (it is continuous on the open interval). -/
theorem aesm_Ktheta_mul_DzIter {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Elliptic.Ktheta]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_DzIter h4 hk
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hK.mul hD) hz

/-- **`θ`-integrability of the angular slices.** -/
theorem integrable_Ktheta_mul_DzIter {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
  MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * (C0 * Rwt z)))
    (aesm_Ktheta_mul_DzIter h4 (by omega) hz)
    (abs_Ktheta_mul_DzIter_le hC0 hbd hk hz)

/-! ## Continuity of the angular moments -/

/-- **Continuity of `z ↦ Qang f k z` on `(0,∞)` for `k ≤ 2`.**  Dominated convergence in `θ`,
the domination being the constant `3·C₀·(2z)^{3/2}` on the neighbourhood
`(z/2, 2z) ∋ z` (where the standing bound gives `|D_z^k f (x,θ)| ≤ C₀ x^{3/2}/(1+x)² ≤
C₀ (2z)^{3/2}`). -/
theorem Qang_continuousAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ContinuousAt (fun z => Work.Elliptic.Qang f k z) z := by
  have hCnn : 0 ≤ 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)) := by positivity
  have hmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ)
      (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
    exact aesm_Ktheta_mul_DzIter h4 (by omega) hx
  have hbound : ∀ᶠ x in 𝓝 z, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ‖
        ≤ 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show z ∈ Set.Ioo (z / 2) (2 * z) from ⟨by linarith, by linarith⟩)] with x hx
    have hxz : 0 < x := by linarith [hx.1]
    have hxle : x ≤ 2 * z := hx.2.le
    have hRwt : Rwt x ≤ (2 * z) ^ ((3 : ℝ) / 2) := by
      rw [Rwt, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 2)]
      have h1 : x ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hxz.le hxle (by norm_num)
      have h2 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
      have h3 : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
        Real.rpow_nonneg (by linarith) _
      nlinarith [h1, h2, h3]
    refine (abs_Ktheta_mul_DzIter_le hC0 hbd hk hxz).mono fun θ hθ => ?_
    have h2 : C0 * Rwt x ≤ C0 * (2 * z) ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hRwt hC0
    linarith [hθ, mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3)]
  have hcont : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ContinuousAt (fun x => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ) z := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hzero : (fun x : ℝ => Work.Elliptic.Ktheta 0 * Work.Spaces.DzIter k f x 0)
          = fun _ => (0 : ℝ) := by
        funext x; rw [Ktheta_zero_left, zero_mul]
      rw [hzero]
      exact continuousAt_const
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hzero : (fun x : ℝ => Work.Elliptic.Ktheta (Real.pi / 2)
            * Work.Spaces.DzIter k f x (Real.pi / 2)) = fun _ => (0 : ℝ) := by
          funext x; rw [Ktheta_zero_right, zero_mul]
        rw [hzero]
        exact continuousAt_const
      · have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
              = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
            funext p; rw [Work.Elliptic.Ktheta]
          rw [hfun]
          exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
            ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
        have hjoint : ContinuousWithinAt
            (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter k f p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (z, θ) :=
          (hK.mul (continuousOn_DzIter h4 (by omega : k ≤ 3))).continuousWithinAt
            (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩)
        have hmap : ContinuousWithinAt (fun x : ℝ => (x, θ)) (Set.Ioi 0) z :=
          continuousWithinAt_id.prodMk continuousWithinAt_const
        have hcomp : ContinuousWithinAt
            ((fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter k f p.1 p.2)
              ∘ fun x : ℝ => (x, θ)) (Set.Ioi 0) z :=
          hjoint.comp (x := z) hmap (fun x hx =>
            Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, h0, h1⟩)
        have heqfun : ((fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
              * Work.Spaces.DzIter k f p.1 p.2) ∘ fun x : ℝ => (x, θ))
            = fun x : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ := by
          funext x; rfl
        rw [heqfun] at hcomp
        exact hcomp.continuousAt (isOpen_Ioi.mem_nhds hz)
  have key := MeasureTheory.continuousAt_of_dominated
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f x θ)
    (bound := fun _ => 3 * (C0 * (2 * z) ^ ((3 : ℝ) / 2)))
    (x₀ := z) hmeas hbound (MeasureTheory.integrable_const _) hcont
  simpa only [Work.Elliptic.Qang] using key

/-! ## The angular moment at level `0`, and the density of `L₁₂` -/

/-- The bound `|Qang f 0 s| ≤ 3(π/2) C₀ Rwt s`, by the `θ`-integral mean inequality. -/
theorem abs_Qang_zero_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Qang f 0 s| ≤ 3 * (Real.pi / 2) * (C0 * Rwt s) := by
  have hint := integrable_Ktheta_mul_DzIter hC0 h4 hbd (k := 0) (by omega) hs
  have hbnd := abs_Ktheta_mul_DzIter_le hC0 hbd (k := 0) (by omega) hs
  have h1 : ‖Work.Elliptic.Qang f 0 s‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 0 f s θ‖ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ
        * Work.Spaces.DzIter 0 f s θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (C0 * Rwt s) :=
    MeasureTheory.integral_mono_ae hint.norm (MeasureTheory.integrable_const _) hbnd
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * (C0 * Rwt s))
      = 3 * (Real.pi / 2) * (C0 * Rwt s) := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, le_of_eq h3]

/-- `Work.FM.L12dens Work.Spaces.K f` is the elliptic density `Work.Elliptic.L12dens f`, i.e.
`Qang f 0 s / s`. -/
theorem L12dens_eq_Qang_zero (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K f s = Work.Elliptic.Qang f 0 s / s :=
  Work.Elliptic.L12dens_eq_Qang_div f s

/-- The pointwise bound on the density of `L₁₂`:
`|L12dens (f) s| ≤ 3(π/2) C₀ s^{1/2}/(1+s)²`. -/
theorem abs_L12dens_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {s : ℝ} (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
  have h := abs_Qang_zero_le hC0 h4 hbd hs
  have hstep : (3 * (Real.pi / 2) * (C0 * Rwt s)) / s
      = 3 * (Real.pi / 2) * C0 * (Rwt s / s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  calc |Work.FM.L12dens Work.Spaces.K f s|
      = |Work.Elliptic.Qang f 0 s| / s := by
        rw [L12dens_eq_Qang_zero, abs_div, abs_of_pos hs]
    _ ≤ (3 * (Real.pi / 2) * (C0 * Rwt s)) / s := div_le_div_of_nonneg_right h hs.le
    _ = 3 * (Real.pi / 2) * C0 * (Rwt s / s) := hstep
    _ = 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
        rw [Rwt_div s hs]

/-- Continuity of the density of `L₁₂` on `(0,∞)`. -/
theorem L12dens_continuousOn {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z) :
    ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := by
  refine ContinuousOn.congr (s := Set.Ioi 0)
    (f := fun s => Work.Elliptic.Qang f 0 s / s)
    (g := Work.FM.L12dens Work.Spaces.K f) ?_ ?_
  · intro s hs
    exact ((Qang_continuousAt hC0 h4 hbd (k := 0) (by omega) hs).div continuousAt_id
      (ne_of_gt hs)).continuousWithinAt
  · intro s _
    exact L12dens_eq_Qang_zero f s

/-! ## Integrability of the density and of the majorant -/

/-- `s ↦ s^{1/2}/(1+s)²` is integrable on `(a,∞)` for `a > 0` (it is dominated by
`s^{-3/2}`). -/
theorem integrable_majorant {a : ℝ} (ha : 0 < a) :
    Integrable (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi a)) := by
  have hbase : Integrable (fun s : ℝ => s ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi a)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) ha
  refine MeasureTheory.Integrable.mono' hbase ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (s := Set.Ioi a) ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt (ha.trans hs)))
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro s hs
      exact pow_ne_zero 2 (by linarith [ha.trans hs] : (1 : ℝ) + s ≠ 0)
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hs' : 0 < s := ha.trans hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ s ^ ((1 : ℝ) / 2) / s ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)
        (by positivity : (0 : ℝ) < s ^ 2)]
      have h2 : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h2 : s ^ ((1 : ℝ) / 2) / s ^ 2 = s ^ (-(3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast s 2]
      rw [← Real.rpow_sub hs']
      norm_num
    linarith [h1, le_of_eq h2]

/-- **Integrability of the `L₁₂`-density** on `(a,∞)` for `a > 0`. -/
theorem L12dens_integrableOn {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {a : ℝ} (ha : 0 < a) :
    Integrable (Work.FM.L12dens Work.Spaces.K f) (volume.restrict (Set.Ioi a)) := by
  have hcont := L12dens_continuousOn hC0 h4 hbd
  have haesm : AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi a)) :=
    (hcont.mono (Set.Ioi_subset_Ioi ha.le)).aestronglyMeasurable measurableSet_Ioi
  have hmaj : Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (volume.restrict (Set.Ioi a)) :=
    (integrable_majorant ha).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  rw [Real.norm_eq_abs]
  exact abs_L12dens_le hC0 h4 hbd (ha.trans hs)

/-! ## The derivative of `L₁₂` -/

/-- **`∂_z L₁₂(f)(z) = - L12dens (f)(z)`** for `z > 0`. -/
theorem Construction_L12_hasDerivAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Work.Construction.L12 f z)
      (-(Work.Construction.L12dens f z)) z := by
  have hint : Integrable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi (z / 2))) :=
    L12dens_integrableOn hC0 h4 hbd (by linarith)
  have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    (L12dens_continuousOn hC0 h4 hbd).continuousAt (isOpen_Ioi.mem_nhds hz)
  simpa only [Work.Construction.L12, Work.Construction.L12dens] using
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) hint hcont (by linarith)

end Work.FTS_RegExport.RXT.L12Iter
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.Basic` — the angular kernel and the derivative of `𝔽K`

First half of the jet package of `L12_FK_jets_of_datum`: the elementary bounds of the angular
integrals `∫_θ K(θ)g(θ) dθ`, the angular-moment bound `|Qang F m z| ≤ 18C` for `m ≤ 2` under
the datum bounds `|D_z^k F| ≤ C`, the identity `Qang F 0 = 𝔽K(F)`, the slice differentiability
of an open-quadrant `C¹` function, and the fundamental identity
`∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The crude bound `|∫_θ K(θ)g(θ)| ≤ 6 C` when `|g| ≤ C` a.e. on `Iθ`.  (The sharp constant
is `C`, by `∫_θ K = 1`; `6` is enough for the whole development.) -/
theorem lfj_abs_integral_K_mul_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |g θ| ≤ C) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g θ| ≤ 6 * C := by
  have hbd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖Work.Spaces.K θ * g θ‖ ≤ 3 * C := by
    filter_upwards [hb] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    have hK : |Work.Spaces.K θ| ≤ 3 := by
      rw [← Work.Elliptic.Ktheta_eq_K]
      exact Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le θ
    exact mul_le_mul hK hθ (abs_nonneg _) (by norm_num)
  have h1 := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict Work.Spaces.Iθ) hbd
  rw [Work.FTS_RegExport.RXT.Slots.real_univ_restrict_Iθ] at h1
  rw [Real.norm_eq_abs] at h1
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have h2 : 3 * C * (Real.pi / 2) ≤ 6 * C := by nlinarith
  linarith

/-- `DatumBnd F C` gives the bound on every `D_z`-slot of order `≤ 2`. -/
theorem DatumBnd.DzIter_le {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumBnd F C) {k : ℕ} (hk : k ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter k F z θ| ≤ C := by
  interval_cases k
  · simpa only [Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).1
  · simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).2.1
  · simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).2.2

/-- The angular moment bound: `|Qang F m z| ≤ 18 C` for `m ≤ 2`. -/
theorem lfj_Qang_abs_le {F : ℝ → ℝ → ℝ} {C z : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    {m : ℕ} (hm : m ≤ 2) (hz : 0 < z) :
    |Work.Elliptic.Qang F m z| ≤ 18 * C := by
  have hb' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |Work.Spaces.DzIter m F z θ| ≤ C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hb m hm z θ hz hθ.1 hθ.2)
  have h1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter m F z θ| ≤ 6 * C :=
    lfj_abs_integral_K_mul_le hC hb'
  have hQg : Work.Elliptic.Qang F m z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter m F z θ := by
    rw [Work.Elliptic.Qang, Work.Elliptic.Ktheta_eq_K]
  rw [hQg]
  linarith [h1]

/-- The angular moment at level `0` is the angular moment `(F,K)` of the datum. -/
theorem lfj_Qang_zero_eq_FK (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang F 0 z = Work.Construction.FK F z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Ktheta_eq_K, Work.Construction.FK]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => by rw [Work.Spaces.DzIter_zero]; ring)

/-- `Qang f (k+1) z = z · ∫_θ K(θ)∂_z(D_z^k f)(z,θ) dθ`, by linearity of the `θ`-integral. -/
theorem lfj_Qang_succ_eq (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    Work.Elliptic.Qang f (k + 1) z
      = z * ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ := by
  have h1 : Work.Elliptic.Qang f (k + 1) z
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) := rfl
  rw [h1, show (fun θ => Work.Elliptic.Ktheta θ
        * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ))
      = fun θ => z * (Work.Elliptic.Ktheta θ
          * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul]

/-- The level one angular moment against `∂_zF`:
`Qang F 1 z = z ∫_θ ∂_zF(z,θ)K(θ) dθ`. -/
theorem lfj_Qang_one_eq (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang F 1 z
      = z * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ := by
  rw [lfj_Qang_succ_eq F 0 z]
  simp only [Work.Spaces.DzIter_zero]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [Work.Elliptic.Ktheta_eq_K]; ring)

/-- `K(θ) = 3 sinθ cos²θ` is continuous as a function of the *pair* `(z,θ)`. -/
theorem lfj_continuousOn_Ktheta_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Elliptic.Ktheta]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- The same, for the weight `K` of `Spaces`. -/
theorem lfj_continuousOn_K_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 := by
    funext p; rw [Work.Elliptic.Ktheta_eq_K]
  rw [hfun]
  exact lfj_continuousOn_Ktheta_jet

/-- The radial slice of a `C¹` function on the open quadrant is differentiable with
derivative `pz`. -/
theorem lfj_slice_hasDerivAt {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {x θ : ℝ} (hx : 0 < x) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt (fun y => g y θ) (Work.Spaces.pz g x θ) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, h0, h1⟩))
  have h2 : HasFDerivAt (fun y : ℝ => (y, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x θ
  have h3 : HasDerivAt (fun y : ℝ => Function.uncurry g (y, θ))
      ((fderiv ℝ (Function.uncurry g) (x, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) x := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp x h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (x, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1
      = Work.Spaces.pz g x θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.Spaces.deriv_slice_fst (Function.uncurry g) x θ hd).symm
  rw [hval] at h3
  exact h3

/-- **`∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`** for a datum which is `C²` on the open quadrant
with `|D_z^k F| ≤ C` (`k ≤ 2`) there and `C ≥ 0`. -/
theorem lfj_hasDerivAt_FK {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    (hC : 0 ≤ C) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.FK F z')
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x := fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have h1 : ContDiffOn ℝ 1 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := h2.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz F)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 1) h2
  have hcg : ContinuousOn (Function.uncurry (fun x θ => F x θ * Work.Spaces.K θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 * Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 from h2.continuousOn.mul lfj_continuousOn_K_jet
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Spaces.pz F x θ * Work.Spaces.K θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2 * Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 from hpz.continuousOn.mul lfj_continuousOn_K_jet
  have hKbd : ∀ θ : ℝ, |Work.Spaces.K θ| ≤ 3 := by
    intro θ; rw [← Work.Elliptic.Ktheta_eq_K]
    exact Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le θ
  have hint : Integrable (fun θ => F z θ * Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * C))
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hcg hz) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |F z θ| * |Work.Spaces.K θ| ≤ C * 3 :=
          mul_le_mul (hb 0 (by norm_num) z θ hz hθ.1 hθ.2) (hKbd θ) (abs_nonneg _) hC
      _ = 3 * C := by ring
  have hpzbd : ∀ x ∈ Set.Ioi (z / 2), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz F x θ| ≤ 2 * C / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := hVpos x hx
    have hxz : z / 2 < x := Set.mem_Ioi.mp hx
    have h := hb 1 (by norm_num) x θ hx0 hθ.1 hθ.2
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] at h
    rw [abs_mul, abs_of_pos hx0] at h
    have hle : |Work.Spaces.pz F x θ| ≤ C / x := by
      rw [le_div_iff₀ hx0]; rw [mul_comm]; exact h
    have h2' : C / x ≤ 2 * C / z := by
      have h3 : C / x ≤ C / (z / 2) := div_le_div_of_nonneg_left hC hz2 hxz.le
      have h4 : C / (z / 2) = 2 * C / z := by field_simp
      linarith [h3, le_of_eq h4]
    linarith
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Spaces.pz F x θ * Work.Spaces.K θ‖ ≤ 3 * (2 * C / z) := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h3 := hpzbd x hx θ hθ
    have h4 : 0 ≤ 2 * C / z := by positivity
    calc |Work.Spaces.pz F x θ| * |Work.Spaces.K θ| ≤ (2 * C / z) * 3 :=
          mul_le_mul h3 (hKbd θ) (abs_nonneg _) h4
      _ = 3 * (2 * C / z) := by ring
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => F y θ * Work.Spaces.K θ)
        (Work.Spaces.pz F x θ * Work.Spaces.K θ) x :=
    fun θ hθ x hx =>
      (lfj_slice_hasDerivAt h1 (hVpos x hx) hθ.1 hθ.2).mul_const (Work.Spaces.K θ)
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2))
    isOpen_Ioi hVmem hVpos hcg hcg' hint hbound hdiff
  simpa only [Work.Construction.FK] using key

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

/-- **The `z`-derivative of the slice of a mixed jet.**  For a datum `f` which is `C⁴` on the
open quadrant `Q0` and a mixed jet `D_z^jD_θ^i f` of total order `j + i ≤ 3`, the slice
`z' ↦ D_z^jD_θ^i f (z',θ)` is differentiable at every `z > 0` (and every interior `θ`), with
derivative `D_z^{j+1}D_θ^i f (z,θ)/z`.

Indeed `D_z^{j+1}D_θ^i f = D_z(D_z^jD_θ^i f)` is definitionally `z · ∂_z(D_z^jD_θ^i f)`, and the
slice is differentiable because `D_z^jD_θ^i f` is `C^{4-j-i}`, in particular `C¹`, on `Q0`. -/
theorem hasDerivAt_mixed_z {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Spaces.mixed j i f z' θ)
      (Work.Spaces.mixed (j + 1) i f z θ / z) z := by
  -- the point lies in the open quadrant
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ, hθ'⟩
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ, hθ'⟩
  -- index arithmetic (`j + i ≤ 3`)
  have hi4 : i ≤ 4 := by omega
  have hjle : j ≤ 4 - i := by omega
  have hone : 1 ≤ (4 - i) - j := by omega
  -- `D_θ^i f` is `C^{4-i}` on the open quadrant
  have hDth : ContDiffOn ℝ (4 - i) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 := by
    have hle : (4 - i) + i ≤ 4 := le_of_eq (Nat.sub_add_cancel hi4)
    have h : ContDiffOn ℝ ((4 - i) + i) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
      hf.of_le (Nat.cast_le.mpr hle)
    exact Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift Work.FTS.EllipticEst.isOpen_Q0
      i (4 - i) h
  -- `D_z^j D_θ^i f` is `C^{(4-i)-j}` on the open quadrant
  have hDz : ContDiffOn ℝ ((4 - i) - j)
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)))
      Work.FTS.EllipticEst.Q0 := by
    have hle : ((4 - i) - j) + j ≤ 4 - i := le_of_eq (Nat.sub_add_cancel hjle)
    have h' : ContDiffOn ℝ (((4 - i) - j) + j)
        (Function.uncurry (Work.Spaces.DthIter i f)) Work.FTS.EllipticEst.Q0 :=
      hDth.of_le (Nat.cast_le.mpr hle)
    exact Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0
      j ((4 - i) - j) h'
  -- in particular `D_z^jD_θ^i f` is `C¹`
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f))
      Work.FTS.EllipticEst.Q0 :=
    hDz.of_le (Nat.cast_le.mpr hone)
  -- hence its slice at the interior angle `θ` is `C¹` and differentiable at `z > 0`
  have hslice : ContDiffOn ℝ 1 (fun z' : ℝ => Work.Spaces.mixed j i f z' θ) (Set.Ioi 0) := by
    have hmap : ContDiffOn ℝ 1 (fun x : ℝ => (x, θ)) (Set.Ioi 0) :=
      (contDiffOn_id : ContDiffOn ℝ 1 (fun z : ℝ => z) (Set.Ioi 0)).prodMk
        (contDiffOn_const (c := θ))
    have h := h1.comp hmap (fun x hx => ⟨hx, hθIoo⟩)
    rw [show (Function.uncurry (Work.Spaces.mixed j i f)) ∘ (fun x : ℝ => (x, θ))
        = fun z' => Work.Spaces.mixed j i f z' θ from rfl] at h
    exact h
  have hdiff : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.mixed j i f z' θ) z :=
    (hslice.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hH : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed j i f z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed j i f) z θ) z := by
    simpa [Work.Spaces.pz] using hdiff.hasDerivAt
  -- `D_z^{j+1}D_θ^i f = D_z(D_z^jD_θ^i f) = z · ∂_z(D_z^jD_θ^i f)` definitionally
  have hval : Work.Spaces.mixed (j + 1) i f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i f) z θ := rfl
  rw [hval, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  exact hH

end Work.FTS_RegExport.RXT.Sys
end
end
