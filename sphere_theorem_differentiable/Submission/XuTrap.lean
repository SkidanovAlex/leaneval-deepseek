import Submission.XuMain
import Submission.UniformInj
import Submission.KlingenbergXu

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.XuLift

namespace Submission.XuTrap

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **THE TRAP.** -/
theorem lift_mem_ball (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {u : E} {r δ a b : ℝ} (hr : 0 < r) (hab : a ≤ b)
    (hinj : Set.InjOn (gexpMap (cov := cov) hmet p) (Metric.closedBall u r))
    (huniq : ∀ y : M,
      Manifold.riemannianEDist I (gexpMap (cov := cov) hmet p u) y < ENNReal.ofReal δ →
      ∃! w : E, w ∈ Metric.ball u r ∧ gexpMap (cov := cov) hmet p w = y)
    {γ : ℝ → M} {Γ : ℝ → E}
    (hΓc : ContinuousOn Γ (Set.Icc a b))
    (hΓmem : ∀ σ ∈ Set.Icc a b, Γ σ ∈ Submission.SegmentDomain.segmentDomain hmet p)
    (hΓG : ∀ σ ∈ Set.Icc a b, GExp (cov := cov) hmet p (Γ σ) = γ σ)
    (hδ : ∀ σ ∈ Set.Icc a b,
      Manifold.riemannianEDist I (gexpMap (cov := cov) hmet p u) (γ σ) < ENNReal.ofReal δ)
    (ha : Γ a ∈ Metric.ball u r) :
    ∀ σ ∈ Set.Icc a b, Γ σ ∈ Metric.ball u r := by
  intro σ₀ hσ₀
  -- the set of `τ ∈ [a,σ₀]` with `Γ τ` in the ball
  set G : Set ℝ := Set.Icc a σ₀ ∩ {τ : ℝ | Γ τ ∈ Metric.ball u r} with hG
  have hsub : Set.Icc a σ₀ ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hσ₀.2
  -- `G` is nonempty
  have hGne : G.Nonempty := ⟨a, ⟨⟨le_rfl, hσ₀.1⟩, ha⟩⟩
  -- `G` is bounded above
  have hGbdd : BddAbove G := ⟨σ₀, fun τ hτ => hτ.1.2⟩
  -- `G` is closed
  have hGclosed : IsClosed G := by
    refine IsSeqClosed.isClosed fun τ x hτ hτlim => ?_
    have hx : x ∈ Set.Icc a σ₀ :=
      isClosed_Icc.mem_of_tendsto hτlim (Eventually.of_forall fun n => (hτ n).1)
    have hxb : x ∈ Set.Icc a b := hsub hx
    -- `Γ (τ n) → Γ x`
    have hΓlim : Tendsto (fun n => Γ (τ n)) atTop (𝓝 (Γ x)) :=
      (hΓc.continuousWithinAt hxb).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within τ hτlim
          (Eventually.of_forall fun n => hsub (hτ n).1))
    -- `Γ x ∈ closedBall`
    have hclosed : Γ x ∈ Metric.closedBall u r :=
      isClosed_closedBall.mem_of_tendsto hΓlim
        (Eventually.of_forall fun n => Metric.ball_subset_closedBall (hτ n).2)
    -- the unique lift of `γ x` in the small ball
    obtain ⟨w₀, ⟨hw₀ball, hw₀eq⟩, _⟩ := huniq (γ x) (hδ x hxb)
    have hΓx : gexpMap (cov := cov) hmet p (Γ x) = γ x := by
      rw [gexpMap_apply]; exact hΓG x hxb
    have heq : Γ x = w₀ :=
      hinj hclosed (Metric.ball_subset_closedBall hw₀ball) (by rw [hΓx, hw₀eq])
    refine ⟨hx, ?_⟩
    have : Γ x ∈ Metric.ball u r := by rw [heq]; exact hw₀ball
    exact this
  have hsup : sSup G ∈ G := hGclosed.csSup_mem hGne hGbdd
  have hle : sSup G ≤ σ₀ := csSup_le hGne fun τ hτ => hτ.1.2
  -- if the sup were strictly below `σ₀`, openness would produce a bigger element
  have hnotlt : ¬ sSup G < σ₀ := by
    intro hlt
    have hx : sSup G ∈ Set.Icc a b := hsub ⟨hsup.1.1, hlt.le⟩
    have hdist_lt : dist (Γ (sSup G)) u < r := Metric.mem_ball.mp hsup.2
    have hη : 0 < r - dist (Γ (sSup G)) u := by linarith
    have hcont : ContinuousWithinAt Γ (Set.Icc a b) (sSup G) := hΓc.continuousWithinAt hx
    rw [Metric.continuousWithinAt_iff] at hcont
    obtain ⟨ε, hεpos, hε⟩ := hcont (r - dist (Γ (sSup G)) u) hη
    set e : ℝ := min (ε / 2) ((σ₀ - sSup G) / 2) with he
    have hepos : 0 < e := lt_min (by linarith) (by linarith)
    have heε : e < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have heσ : sSup G + e < σ₀ := by
      have h2 : e ≤ (σ₀ - sSup G) / 2 := min_le_right _ _
      linarith
    have hεmem : sSup G + e ∈ Set.Icc a b :=
      ⟨by linarith [hsup.1.1], by linarith [heσ.le, hσ₀.2]⟩
    have hdist : dist (sSup G + e) (sSup G) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hmem : Γ (sSup G + e) ∈ Metric.ball u r := by
      rw [Metric.mem_ball]
      calc dist (Γ (sSup G + e)) u
          ≤ dist (Γ (sSup G + e)) (Γ (sSup G)) + dist (Γ (sSup G)) u := dist_triangle _ _ _
        _ < (r - dist (Γ (sSup G)) u) + dist (Γ (sSup G)) u := by
            linarith [hε hεmem hdist]
        _ = r := by ring
    have hle' : sSup G + e ≤ sSup G :=
      le_csSup hGbdd ⟨⟨by linarith [hsup.1.1], heσ.le⟩, hmem⟩
    linarith
  have hsup_eq : sSup G = σ₀ := le_antisymm hle (le_of_not_gt hnotlt)
  have hmem : σ₀ ∈ G := hsup_eq ▸ hsup
  exact hmem.2

/-- **The lift of a curve through the segment domain is continuous.** -/
theorem continuousOn_lift_coe_of_mem_segmentDomain
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {γ : ℝ → M} {Γ : ℝ → TangentSpace I p} {a b : ℝ}
    (hΓmem : ∀ σ ∈ Set.Icc a b, Γ σ ∈ Submission.SegmentDomain.segmentDomain hmet p)
    (hΓG : ∀ σ ∈ Set.Icc a b, GExp (cov := cov) hmet p (Γ σ) = γ σ)
    (hγc : ContinuousOn γ (Set.Icc a b)) :
    ContinuousOn (fun σ => (show E from Γ σ)) (Set.Icc a b) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.XuMain.exists_pos_model_fibre_norm (I := I) p
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hdiff : ∀ x y : TangentSpace I p,
      ‖(show E from x) - (show E from y)‖ ≤ ‖x - y‖ / Real.sqrt lam := by
    intro x y
    have h := (hbnd (x - y)).1
    rwa [show (show E from (x - y)) = (show E from x) - (show E from y) from rfl] at h
  intro σ hσ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Submission.XuMain.exists_pos_edist_lt_imp_norm_sub_lt
    (cov := cov) hmet htor (p := p) (v := Γ σ) (hΓmem σ hσ)
    (by positivity : 0 < ε * Real.sqrt lam)
  have hnbhd : {y : M | Manifold.riemannianEDist I (GExp (cov := cov) hmet p (Γ σ)) y
      < ENNReal.ofReal δ₁} ∈ 𝓝 (GExp (cov := cov) hmet p (Γ σ)) :=
    (isOpen_Iio.preimage (Submission.HopfRinow.continuous_riemannianEDist_left (I := I)
      (GExp (cov := cov) hmet p (Γ σ)))).mem_nhds (by
        show Manifold.riemannianEDist I (GExp (cov := cov) hmet p (Γ σ))
          (GExp (cov := cov) hmet p (Γ σ)) < ENNReal.ofReal δ₁
        rw [Manifold.riemannianEDist_self]
        exact ENNReal.ofReal_pos.mpr hδ₁pos)
  have hnbhd' : {y : M | Manifold.riemannianEDist I (GExp (cov := cov) hmet p (Γ σ)) y
      < ENNReal.ofReal δ₁} ∈ 𝓝 (γ σ) := by
    rw [← hΓG σ hσ]; exact hnbhd
  have h2 : {σ' : ℝ | Manifold.riemannianEDist I (GExp (cov := cov) hmet p (Γ σ)) (γ σ')
      < ENNReal.ofReal δ₁} ∈ 𝓝[Set.Icc a b] σ :=
    (hγc.continuousWithinAt hσ).eventually hnbhd'
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhdsWithin_iff.mp h2
  refine ⟨δ₂, hδ₂pos, fun σ' hσ' hdist => ?_⟩
  have hd : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (Γ σ)) (γ σ')
      < ENNReal.ofReal δ₁ :=
    hδ₂ ⟨by rwa [Metric.mem_ball], hσ'⟩
  rw [← hΓG σ' hσ'] at hd
  have hε' := hδ₁ (Γ σ') (hΓmem σ' hσ') hd
  calc dist (show E from Γ σ') (show E from Γ σ)
      = ‖(show E from Γ σ') - (show E from Γ σ)‖ := dist_eq_norm _ _
    _ ≤ ‖Γ σ' - Γ σ‖ / Real.sqrt lam := hdiff _ _
    _ < (ε * Real.sqrt lam) / Real.sqrt lam := div_lt_div_of_pos_right hε' hsq
    _ = ε := by field_simp

/-- **Xu's Theorem B.** -/
theorem xuCornerExcluded (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] :
    Submission.KlingenbergXu.XuCornerExcluded (I := I) (cov := cov) hmet := by
  classical
  intro p m hm hinj hmax ξ η hξ hη hξη hminξ hminη hmeet hnc
  by_contra hne
  have hξ0 : ξ ≠ 0 := by intro h; rw [h, norm_zero] at hξ; norm_num at hξ
  have hη0 : η ≠ 0 := by intro h; rw [h, norm_zero] at hη; norm_num at hη
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set x₀ : M := GExp (cov := cov) hmet p (m • ξ) with hx₀def
  have hx₀ξ : GExp (cov := cov) hmet p (m • ξ) = x₀ := hx₀def.symm
  have hx₀η : GExp (cov := cov) hmet p (m • η) = x₀ := by rw [hx₀def]; exact hmeet.symm
  -- invertibility of the differential at `m • ξ`
  have hmξ0 : m • ξ ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨ne_of_gt hm, hξ0⟩
  have hnorm_mξ : ‖m • ξ‖ = m := by rw [norm_smul, Real.norm_of_nonneg hm.le, hξ, mul_one]
  have hunit : unitOf (m • ξ) hmξ0 = ξ := by
    rw [unitOf, smul_smul, hnorm_mξ, inv_mul_cancel₀ (ne_of_gt hm), one_smul]
  have hInv : (mfderiv 𝓘(ℝ, E) I (gexpMap (cov := cov) hmet p)
      (show E from (m • ξ))).IsInvertible := by
    by_contra hsing
    have hconj := Submission.SingularConj.singular_imp_conjTime (cov := cov) hmet htor
      (p := p) (v := m • ξ) hmξ0 hsing
    rw [hnorm_mξ] at hconj
    have hfun : (fun s : ℝ => GExp (cov := cov) hmet p (s • unitOf (m • ξ) hmξ0))
        = (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) := by
      funext s; rw [hunit]
    rw [hfun] at hconj
    exact hnc hconj
  -- the inverse function theorem
  obtain ⟨r₀, hr₀, hballIF⟩ := Submission.XuMain.exists_pos_ball_lift_GExp_forall_le
    (cov := cov) hmet p (v := m • ξ) hInv
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.XuMain.exists_pos_model_fibre_norm (I := I) p
  have hsqrtlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hd0 : 0 < ‖ξ - η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hξη)
  have hdm : 0 < ‖m • ξ - m • η‖ := by
    have h1 : ‖m • ξ - m • η‖ = m * ‖ξ - η‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hm.le]
    rw [h1]; exact mul_pos hm hd0
  set r : ℝ := min r₀ (‖m • ξ - m • η‖ / (4 * Real.sqrt Lam)) with hrdef
  have hr : 0 < r := lt_min hr₀ (by positivity)
  obtain ⟨δ, hδpos, hInjOn, hUniq⟩ := hballIF r hr (min_le_left _ _)
  -- the uniform injectivity radius
  obtain ⟨ρ, hρpos, hρinj⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  -- the radius of the small arc
  obtain ⟨δ₀, hδ₀pos, hδ₀m2, hδ₀ρ, hδ₀δ, hδ₀rl, hδ₀η⟩ :
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ m / 2 ∧ δ₀ ≤ ρ / 2 ∧ δ₀ ≤ δ / 4 ∧
        δ₀ ≤ r * Real.sqrt lam / 2 ∧ δ₀ ≤ m * ‖ξ - η‖ / 8 :=
    ⟨min (m / 2) (min (ρ / 2) (min (δ / 4) (min (r * Real.sqrt lam / 2)
        (m * ‖ξ - η‖ / 8)))),
      lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
        (lt_min (by positivity) (by positivity)))),
      min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))⟩
  have hδ₀m : δ₀ < m := by linarith
  have hδ₀ρlt : δ₀ < ρ := by linarith
  have hδ₀δlt : δ₀ < δ := by linarith
  have hδ₀rllt : δ₀ < r * Real.sqrt lam := by linarith
  set τ₀ : ℝ := m - δ₀ with hτ₀def
  have hτ₀pos : 0 < τ₀ := by rw [hτ₀def]; linarith
  have hτ₀m : τ₀ < m := by rw [hτ₀def]; linarith
  set q : M := GExp (cov := cov) hmet p (τ₀ • ξ) with hqdef
  have hcutξ : m ≤ Submission.CutTime.cutTime (I := I) hmet p ξ :=
    Submission.CutTime.injAtLeast_le_cutTime (I := I) (cov := cov) hmet htor hinj hξ
  have hcutη : m ≤ Submission.CutTime.cutTime (I := I) hmet p η :=
    Submission.CutTime.injAtLeast_le_cutTime (I := I) (cov := cov) hmet htor hinj hη
  have hξmem : τ₀ • ξ ∈ Submission.SegmentDomain.segmentDomain hmet p := by
    have hv : τ₀ • ξ ≠ 0 := by
      rw [smul_ne_zero_iff]; exact ⟨ne_of_gt hτ₀pos, hξ0⟩
    refine Submission.SegmentDomain.mem_segmentDomain_of_norm_lt (I := I) hmet hv ?_
    have hn : ‖τ₀ • ξ‖ = τ₀ := by rw [norm_smul, Real.norm_of_nonneg hτ₀pos.le, hξ, mul_one]
    have hu : unitOf (τ₀ • ξ) hv = ξ := by
      rw [unitOf, smul_smul, hn, inv_mul_cancel₀ (ne_of_gt hτ₀pos), one_smul]
    rw [hu, hn]
    exact lt_of_lt_of_le hτ₀m hcutξ
  have hminξI : ∀ t ∈ Set.Icc (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t :=
    fun t ht => Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hξ ht.1 ht.2 hminξ
  have hminηI : ∀ t ∈ Set.Icc (0 : ℝ) m,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • η)) = ENNReal.ofReal t :=
    fun t ht => Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hη ht.1 ht.2 hminη
  have hqmin : Manifold.riemannianEDist I p q = ENNReal.ofReal τ₀ := by
    rw [hqdef]; exact hminξI τ₀ ⟨hτ₀pos.le, hτ₀m.le⟩
  have hxqm : Manifold.riemannianEDist I p x₀ = ENNReal.ofReal m := by
    rw [hx₀def]; exact hminξI m ⟨hm.le, le_rfl⟩
  have hqx₀ : Manifold.riemannianEDist I q x₀ = ENNReal.ofReal δ₀ := by
    have h := Submission.LensSync.edist_eq_sub_of_minimising_ray (cov := cov) hmet hξ
      hτ₀pos.le hτ₀m.le (hminξI τ₀ ⟨hτ₀pos.le, hτ₀m.le⟩) (hminξI m ⟨hm.le, le_rfl⟩)
    rw [hqdef, hx₀def, h, hτ₀def]
    norm_num
  -- the intermediate parameter and the target point
  obtain ⟨s, hsdef, hs0, hsm, hτ₀s, hms⟩ : ∃ s : ℝ, s = m - δ₀ / 2 ∧ 0 < s ∧ s < m ∧ τ₀ < s ∧
      m - s = δ₀ / 2 :=
    ⟨m - δ₀ / 2, rfl, by linarith, by linarith, by linarith, by ring⟩
  have hβs_min : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • η)) = ENNReal.ofReal s :=
    hminηI s ⟨hs0.le, hsm.le⟩
  have hcorn : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (τ₀ • ξ))
      (GExp (cov := cov) hmet p (s • η)) < ENNReal.ofReal ((m - τ₀) + (m - s)) :=
    Submission.XuLift.edist_lt_of_velocity_ne_neg (cov := cov) hmet htor hξ hη hm hτ₀pos hτ₀m
      hs0 hsm hmeet hminξI hminηI hne
  have hqβs_lt : Manifold.riemannianEDist I q (GExp (cov := cov) hmet p (s • η))
      < ENNReal.ofReal (δ₀ + (m - s)) := by
    rw [show q = GExp (cov := cov) hmet p (τ₀ • ξ) from hqdef] at *
    rw [show m - τ₀ = δ₀ from by rw [hτ₀def]; ring] at hcorn
    exact hcorn
  -- the minimising geodesic from `q` to `βs`
  set βs : M := GExp (cov := cov) hmet p (s • η) with hβsdef
  obtain ⟨v_s, hv_s_G, hv_s_d⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (cov := cov) hmet htor q βs
  set l_s : ℝ := ‖v_s‖ with hlsdef
  have hv_s_ne : v_s ≠ 0 := by
    intro h0
    have h1 : Manifold.riemannianEDist I q βs = 0 := by
      rw [hv_s_d, hlsdef, h0, norm_zero, ENNReal.ofReal_zero]
    have h2 : q = βs := (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h1
    have h3 : ENNReal.ofReal τ₀ = ENNReal.ofReal s := by
      rw [← hqmin, h2, hβsdef]; exact hβs_min
    have h4 : τ₀ = s :=
      (ENNReal.ofReal_eq_ofReal_iff hτ₀pos.le hs0.le).mp h3
    linarith [hτ₀s]
  set ξ_s : TangentSpace I q := unitOf v_s hv_s_ne with hξsdef
  have hξ_s_norm : ‖ξ_s‖ = 1 := unitOf_norm v_s hv_s_ne
  have hξ_s_ne : ξ_s ≠ 0 := by
    intro h; rw [h, norm_zero] at hξ_s_norm; norm_num at hξ_s_norm
  have hls_smul : l_s • ξ_s = v_s := by
    rw [hξsdef, hlsdef, unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv_s_ne), one_smul]
  set γ_s : ℝ → M := fun t => GExp (cov := cov) hmet q (t • ξ_s) with hγsdef
  have hγs_0 : γ_s 0 = q := by rw [hγsdef]; simp
  have hγs_ls : γ_s l_s = βs := by
    have h : γ_s l_s = GExp (cov := cov) hmet q (l_s • ξ_s) := rfl
    rw [h, hls_smul]; exact hv_s_G
  have hv_s_d' : Manifold.riemannianEDist I q (GExp (cov := cov) hmet q (l_s • ξ_s))
      = ENNReal.ofReal l_s := by rw [hls_smul, hv_s_G]; exact hv_s_d
  have hmin_σ : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      Manifold.riemannianEDist I q (γ_s σ) = ENNReal.ofReal σ := by
    intro σ hσ
    have h := Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hξ_s_norm
      (ξ := ξ_s) (s := σ) (t := l_s) hσ.1 hσ.2 hv_s_d'
    have e : γ_s σ = GExp (cov := cov) hmet q (σ • ξ_s) := rfl
    rw [e]
    exact h
  have hdist_σ : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      Manifold.riemannianEDist I (γ_s σ) βs = ENNReal.ofReal (l_s - σ) := by
    intro σ hσ
    have h := Submission.LensSync.edist_eq_sub_of_minimising_ray (cov := cov) hmet hξ_s_norm
      (ξ := ξ_s) (ℓ := σ) (t := l_s) hσ.1 hσ.2 (hmin_σ σ hσ)
      (by rw [hls_smul, hv_s_G]; exact hv_s_d)
    have e : GExp (cov := cov) hmet q (l_s • ξ_s) = βs := by rw [hls_smul]; exact hv_s_G
    rw [e] at h
    have e2 : γ_s σ = GExp (cov := cov) hmet q (σ • ξ_s) := rfl
    rw [e2]
    exact h
  have hγc : ContinuousOn γ_s (Set.Icc (0 : ℝ) l_s) := by
    have h1 : Continuous (fun t : ℝ => GExp (cov := cov) hmet q (t • ξ_s)) :=
      (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hξ_s_ne).continuous
    have h2 : γ_s = fun t : ℝ => GExp (cov := cov) hmet q (t • ξ_s) := hγsdef
    rw [h2]; exact h1.continuousOn
  -- CLAIM A: the whole minimising geodesic lies in the image of the segment domain
  have hmem_image : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      ∃ v : TangentSpace I p, v ∈ Submission.SegmentDomain.segmentDomain hmet p
        ∧ GExp (cov := cov) hmet p v = γ_s σ := by
    intro σ hσ
    refine Submission.XuMain.mem_image_segmentDomain_of_minimising (cov := cov) hmet htor
      (p := p) (m := m) (τ := τ₀) (s := s) hm hτ₀pos.le hτ₀m.le hs0.le hsm.le hinj
      (q := q) (β := βs) (y := γ_s σ) hqmin ?_ ?_ ?_
    · rw [hβsdef]; exact hβs_min
    · rw [hβsdef]
      rw [show m - τ₀ = δ₀ from by rw [hτ₀def]; ring]
      exact hqβs_lt
    · have e1 : Manifold.riemannianEDist I q (γ_s σ) = ENNReal.ofReal σ := hmin_σ σ hσ
      have e2 : Manifold.riemannianEDist I (γ_s σ) βs = ENNReal.ofReal (l_s - σ) :=
        hdist_σ σ hσ
      have h3 : ENNReal.ofReal σ + ENNReal.ofReal (l_s - σ) = ENNReal.ofReal l_s := by
        rw [← ENNReal.ofReal_add hσ.1 (sub_nonneg.mpr hσ.2)]
        congr 1; ring
      rw [e1, e2, h3]
      exact le_of_eq hv_s_d.symm
  -- the lift of `γ_s` through the segment domain
  set Γ_s : ℝ → TangentSpace I p := fun σ =>
    if h : ∃ v : TangentSpace I p,
        v ∈ Submission.SegmentDomain.segmentDomain hmet p
          ∧ GExp (cov := cov) hmet p v = γ_s σ
      then Classical.choose h else 0 with hΓsdef
  have hΓs_spec : ∀ σ (h : ∃ v : TangentSpace I p,
      v ∈ Submission.SegmentDomain.segmentDomain hmet p
        ∧ GExp (cov := cov) hmet p v = γ_s σ),
      Γ_s σ ∈ Submission.SegmentDomain.segmentDomain hmet p
        ∧ GExp (cov := cov) hmet p (Γ_s σ) = γ_s σ := by
    intro σ h
    have hch := Classical.choose_spec h
    have hΓ : Γ_s σ = Classical.choose h := by simp only [hΓsdef, dif_pos h]
    rw [hΓ]; exact hch
  have hΓmem : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      Γ_s σ ∈ Submission.SegmentDomain.segmentDomain hmet p :=
    fun σ hσ => (hΓs_spec σ (hmem_image σ hσ)).1
  have hΓG : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      GExp (cov := cov) hmet p (Γ_s σ) = γ_s σ :=
    fun σ hσ => (hΓs_spec σ (hmem_image σ hσ)).2
  have hΓc : ContinuousOn (fun σ => (show E from Γ_s σ)) (Set.Icc (0 : ℝ) l_s) :=
    Submission.XuTrap.continuousOn_lift_coe_of_mem_segmentDomain (cov := cov) hmet htor
      hΓmem hΓG hγc
  have hΓ0 : Γ_s 0 = τ₀ • ξ := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) l_s := ⟨le_rfl, norm_nonneg _⟩
    refine Submission.SegmentDomain.injOn_GExp_segmentDomain (cov := cov) hmet htor p
      (hΓmem 0 h0) hξmem ?_
    change GExp (cov := cov) hmet p (Γ_s 0) = GExp (cov := cov) hmet p (τ₀ • ξ)
    rw [hΓG 0 h0, hγs_0, hqdef]
  -- the initial point lies in the small ball
  have ha : Γ_s 0 ∈ Metric.ball (show E from (m • ξ)) r := by
    have h : (show E from (τ₀ • ξ)) ∈ Metric.ball (show E from (m • ξ)) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : (show E from (τ₀ • ξ)) - (show E from (m • ξ))
          = (show E from (τ₀ • ξ - m • ξ)) := rfl
      rw [hsub]
      have hbound := (hbnd (τ₀ • ξ - m • ξ)).1
      have h3 : ‖τ₀ • ξ - m • ξ‖ = δ₀ := by
        rw [← sub_smul, norm_smul]
        have h4 : τ₀ - m = -δ₀ := by rw [hτ₀def]; ring
        rw [h4, norm_neg, Real.norm_of_nonneg hδ₀pos.le, hξ, mul_one]
      calc ‖(show E from (τ₀ • ξ - m • ξ))‖ ≤ ‖τ₀ • ξ - m • ξ‖ / Real.sqrt lam := hbound
        _ = δ₀ / Real.sqrt lam := by rw [h3]
        _ < r := by
            rw [div_lt_iff₀ hsqrtlam]
            linarith
    rw [hΓ0]
    exact h
  -- the sub-curve stays within the small metric ball
  have hδtrap : ∀ σ ∈ Set.Icc (0 : ℝ) l_s,
      Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ)) (γ_s σ)
        < ENNReal.ofReal δ := by
    intro σ hσ
    have hl_s_lt : l_s < δ₀ + δ₀ / 2 := by
      have h5 : l_s < δ₀ + (m - s) := by
        have h6 : ENNReal.ofReal l_s < ENNReal.ofReal (δ₀ + (m - s)) := by
          rw [← hv_s_d, hβsdef]; exact hqβs_lt
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp h6
      rwa [hms] at h5
    have h2 : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ)) βs
        = ENNReal.ofReal (m - s) := by
      rw [hβsdef]
      have h := Submission.LensSync.edist_eq_sub_of_minimising_ray (cov := cov) hmet hη
        hs0.le hsm.le (hminηI s ⟨hs0.le, hsm.le⟩) (hminηI m ⟨hm.le, le_rfl⟩)
      rw [Manifold.riemannianEDist_comm, hx₀η, hx₀def] at h
      exact h
    have h3 : Manifold.riemannianEDist I βs (γ_s σ) = ENNReal.ofReal (l_s - σ) := by
      rw [Manifold.riemannianEDist_comm]
      exact hdist_σ σ hσ
    calc Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ)) (γ_s σ)
        ≤ Manifold.riemannianEDist I (GExp (cov := cov) hmet p (m • ξ)) βs
          + Manifold.riemannianEDist I βs (γ_s σ) :=
          Manifold.riemannianEDist_triangle (I := I)
            (x := GExp (cov := cov) hmet p (m • ξ)) (y := βs) (z := γ_s σ)
      _ = ENNReal.ofReal (m - s) + ENNReal.ofReal (l_s - σ) := by rw [h2, h3]
      _ ≤ ENNReal.ofReal (2 * δ₀) := by
          rw [← ENNReal.ofReal_add (by linarith [hms]) (by linarith [hσ.2])]
          apply ENNReal.ofReal_le_ofReal
          linarith [hms, hσ.1, hσ.2, hl_s_lt]
      _ < ENNReal.ofReal δ := by
          apply (ENNReal.ofReal_lt_ofReal_iff hδpos).mpr
          linarith [hδ₀δ, hδpos]
  -- THE TRAP
  have hb : (fun σ => (show E from Γ_s σ)) l_s ∈ Metric.ball (show E from (m • ξ)) r :=
    Submission.XuTrap.lift_mem_ball (cov := cov) hmet htor (p := p) (u := (show E from (m • ξ)))
      (r := r) (δ := δ) (a := 0) (b := l_s) hr (norm_nonneg v_s) hInjOn hUniq
      (γ := γ_s) (Γ := fun σ => (show E from Γ_s σ)) hΓc
      (fun σ hσ => hΓmem σ hσ) (fun σ hσ => hΓG σ hσ) hδtrap ha
      l_s ⟨norm_nonneg v_s, le_rfl⟩
  -- but the lift at the endpoint is `s • η`, which is *outside* the small ball
  have hΓls : Γ_s l_s = s • η := by
    have hl : l_s ∈ Set.Icc (0 : ℝ) l_s := ⟨norm_nonneg _, le_rfl⟩
    have hηmem : s • η ∈ Submission.SegmentDomain.segmentDomain hmet p := by
      have hv : s • η ≠ 0 := by
        rw [smul_ne_zero_iff]; exact ⟨ne_of_gt hs0, hη0⟩
      refine Submission.SegmentDomain.mem_segmentDomain_of_norm_lt (I := I) hmet hv ?_
      have hn : ‖s • η‖ = s := by rw [norm_smul, Real.norm_of_nonneg hs0.le, hη, mul_one]
      have hu : unitOf (s • η) hv = η := by
        rw [unitOf, smul_smul, hn, inv_mul_cancel₀ (ne_of_gt hs0), one_smul]
      rw [hu, hn]
      exact lt_of_lt_of_le hsm hcutη
    refine Submission.SegmentDomain.injOn_GExp_segmentDomain (cov := cov) hmet htor p
      (hΓmem l_s hl) hηmem ?_
    change GExp (cov := cov) hmet p (Γ_s l_s) = GExp (cov := cov) hmet p (s • η)
    rw [hΓG l_s hl, hγs_ls, hβsdef]
  have hsη_not : (show E from (s • η)) ∉ Metric.ball (show E from (m • ξ)) r := by
    intro hmem
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have hns : (show E from (s • η)) - (show E from (m • ξ))
        = (show E from (s • η - m • ξ)) := rfl
    rw [hns] at hmem
    -- the fibre norm of `s • η - m • ξ` is bounded below
    have hfib : m * ‖ξ - η‖ - δ₀ / 2 ≤ ‖s • η - m • ξ‖ := by
      have h1 : ‖m • (η - ξ)‖ ≤ ‖s • η - m • ξ‖ + ‖(s - m) • η‖ := by
        have hh : ‖(s • η - m • ξ) - (s - m) • η‖
            ≤ ‖s • η - m • ξ‖ + ‖(s - m) • η‖ := norm_sub_le _ _
        have h2 : s • η - m • ξ - (s - m) • η = m • (η - ξ) := by
          rw [smul_sub, sub_smul, sub_sub_sub_cancel_left]
        rwa [h2] at hh
      have h2 : ‖m • (η - ξ)‖ = m * ‖ξ - η‖ := by
        rw [norm_smul, Real.norm_of_nonneg hm.le, norm_sub_rev]
      have h3 : ‖(s - m) • η‖ = δ₀ / 2 := by
        have hsm' : s - m = -(δ₀ / 2) := by linarith [hms]
        rw [norm_smul, hsm', norm_neg, Real.norm_of_nonneg (by linarith [hδ₀pos]), hη, mul_one]
      rw [h2, h3] at h1
      linarith
    have hrle : r ≤ m * ‖ξ - η‖ / (4 * Real.sqrt Lam) := by
      have h := min_le_right r₀ (‖m • ξ - m • η‖ / (4 * Real.sqrt Lam))
      have h1 : ‖m • ξ - m • η‖ = m * ‖ξ - η‖ := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg hm.le, norm_sub_rev]
      rwa [← hrdef, h1] at h
    have hbound := (hbnd (s • η - m • ξ)).2
    have hmain : r < ‖(show E from (s • η - m • ξ))‖ := by
      have h4 : m * ‖ξ - η‖ - δ₀ / 2 ≥ (15/16) * (m * ‖ξ - η‖) := by
        have h5 : δ₀ ≤ m * ‖ξ - η‖ / 8 := hδ₀η
        linarith
      have h6 : (15/16) * (m * ‖ξ - η‖) / Real.sqrt Lam
          ≤ ‖s • η - m • ξ‖ / Real.sqrt Lam :=
        div_le_div_of_nonneg_right (le_trans h4 hfib) (Real.sqrt_nonneg Lam)
      have h7 : ‖s • η - m • ξ‖ / Real.sqrt Lam
          ≤ ‖(show E from (s • η - m • ξ))‖ := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr hLam)]
        rw [mul_comm]
        exact hbound
      have h8 : r < (15/16) * (m * ‖ξ - η‖) / Real.sqrt Lam := by
        have h9 : 4 * (r * Real.sqrt Lam) ≤ m * ‖ξ - η‖ := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt Lam)] at hrle
          linarith [hrle]
        have hspos : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
        rw [lt_div_iff₀ hspos]
        nlinarith [hd0, Real.sqrt_pos.mpr hLam]
      linarith
    linarith
  exact hsη_not (by rw [← hΓls]; exact hb)

end
end Submission.XuTrap
