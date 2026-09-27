import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sgSweepDefs
import Submission.Work.Drive.sgSystem
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.sgPiecesDefs
import Submission.Work.Drive.sgFace_gatherCLM
import Submission.Work.Drive.gatherCLM_mem_unitBox
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.finite_loopChainMeet_of_transverse
import Submission.Work.Drive.range_mfderiv_comp_surjective_linear
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_subset_of_isCompact_subset_isOpen
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi

/-!
# Goodness of a chart perturbation at an arbitrary base configuration

`Work.Drive.sgGoodPair_of_small` (`Submission/Work/Drive/sgAssembly.lean`) proves that for every `ε > 0`
there is a chart perturbation `p` of norm `< ε` at which the pair `(Ξ p ∘ Q, rotCapping w ∘ Q)` is a
`GoodPair` — i.e. `GoodAt Ξ Q c w (p, 0)`.  The present module generalises the statement to an
**arbitrary base configuration** `(s₁, s₂)`:

> for every `ε > 0` there is `p` with `‖p‖ < ε` and `GoodAt Ξ Q c w (s₁ + p, s₂)`.

## The mathematical content

The construction is the parametric Sard of `Submission/Work/Drive/sgSystem.lean`, but — unlike
`sgAssembly.lean` — it is run *at the base configuration* `(s₁, s₂)`, i.e. for the loop family
`q ↦ sgLoop Ξ Q (s₁ + q)` against the fixed sweep of the chart `Ξ s₂ ∘ Q`.  The base configuration is
handled by the `psg`-style device of `Submission/Work/Drive/psg_family_regular.lean`: instead of
trying to relate the *unperturbed* values to the chart cover (which is where `sgAssembly.lean` uses
`Ξ 0 = id`), the compact sets carrying the Sard clauses are *projections*

`K i = {z | ∃ q, ‖q‖ ≤ ε ∧ (q,z) ∈ S i}`,

cut out by the condition that the *values* at some small parameter `q` lie in the cover pieces
`C0 i ⊆ C1 i`.  A meet at parameter `q` has `loopVal (q,z) = chainVal (q,z)`, and the chain value is
*independent of the Sard parameter*, so the value itself lies in some `C0 i`; the meet is therefore a
zero of the `i`-th cut-off system with the cut-off equal to `1`, which is all the Sard clause needs.
The uniform parameter-ball containment of the chart region is then the thickening lemma
`Work.Drive.exists_pos_norm_subset_of_isCompact_subset_isOpen`.

The new analytic inputs are the *shifted* versions of the loop-family lemmas of
`Submission/Work/Drive/sgSystem.lean`: joint smoothness of `(q,z) ↦ sgLoop Ξ Q (s₁ + q) (sqPart z)`, the
surjectivity of its charted parameter-derivative (`hsurj_sgLoop_shift`, a chain-rule consequence of
`hsurj_sgLoop` and `ChartPert`'s surjectivity at *every* parameter), and the resulting smoothness of
the cut-off-scaled charted difference system.
-/

namespace Work.Drive

open Manifold Filter Set Metric
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 8000000

noncomputable section

/-! ## Small helpers -/

private lemma gpn_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma gpn_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- The chart `chr p` is `C^∞` on its source. -/
private lemma gpn_contMDiffOn_chr (p : CappingSpace) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- The point `(a, b)` of `ℝ²`. -/
private def gpnSq2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]

@[simp] private lemma gpnSq2_apply_zero (a b : ℝ) : gpnSq2 a b 0 = a := rfl

/-- The point `a` of `ℝ¹`. -/
private def gpnMk1 (a : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => a)

@[simp] private lemma gpnMk1_apply (a : ℝ) (i : Fin 1) : gpnMk1 a i = a := by
  simp [gpnMk1]


/-- **A smooth cut-off which is `1` on a compact set of a normed space and supported in a prescribed
open superset** (the `𝔼^n`-version `Work.Drive.exists_cutoff_one_on_of_subset` generalised to the
product space `𝔼^m × ℝ^5`). -/
theorem gpn_exists_cutoff_one_on_of_subset {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : X → ℝ, ContDiff ℝ Ctop f ∧ (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ V := by
  classical
  have hpt : ∀ x : K, ∃ r : ℝ, 0 < r ∧ Metric.closedBall (x : X) (2 * r) ⊆ V := by
    intro x
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.2))
    exact ⟨r / 4, by linarith, fun z hz => hrsub (by
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hz
      linarith)⟩
  choose r hrpos hrsub using hpt
  have hbump : ∀ x : K, ∃ b : ContDiffBump (x : X), b.rIn = r x ∧ b.rOut = 2 * r x := fun x =>
    ⟨⟨r x, 2 * r x, hrpos x, by linarith [hrpos x]⟩, rfl, rfl⟩
  choose b hb1 hb2 using hbump
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : X) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrpos ⟨x, hx⟩)⟩)
  refine ⟨fun y => 1 - ∏ x ∈ s, (1 - b x y), ?_, ?_, ?_⟩
  · have hcont : ContDiff ℝ Ctop (fun y : X => ∏ x ∈ s, (1 - b x y)) :=
      contDiff_prod (𝕜 := ℝ) (𝔸' := ℝ) (fun x _ => contDiff_const.sub (b x).contDiff)
    exact contDiff_const.sub hcont
  · intro y hy
    obtain ⟨x, hxs, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hbx : b x y = 1 := by
      refine (b x).one_of_mem_closedBall ?_
      rw [hb1 x, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hxy)
    have hz : (1 - b x y) = 0 := by rw [hbx]; ring
    show 1 - ∏ x ∈ s, (1 - b x y) = 1
    rw [Finset.prod_eq_zero hxs hz]
    ring
  · have hsupp : Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y)) ⊆
        ⋃ x ∈ s, tsupport (⇑(b x)) := by
      intro y hy
      by_contra hcon
      have h1 : (∏ x ∈ s, (1 - b x y)) = 1 :=
        Finset.prod_eq_one (fun x hx => by
          have hb0 : b x y = 0 := by
            by_contra hne
            exact hcon (Set.mem_iUnion₂.mpr ⟨x, hx, subset_tsupport _ hne⟩)
          rw [hb0]; ring)
      simp only [Function.mem_support, ne_eq] at hy
      exact hy (by rw [h1]; ring)
    have hclosed : IsClosed (⋃ x ∈ s, tsupport (⇑(b x))) :=
      isClosed_biUnion_finset (fun x _ => isClosed_tsupport _)
    calc tsupport (fun y => 1 - ∏ x ∈ s, (1 - b x y))
        = closure (Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y))) := rfl
      _ ⊆ closure (⋃ x ∈ s, tsupport (⇑(b x))) := closure_mono hsupp
      _ = ⋃ x ∈ s, tsupport (⇑(b x)) := hclosed.closure_eq
      _ ⊆ V := by
          rintro z hz
          obtain ⟨x, hxs, hxz⟩ := Set.mem_iUnion₂.mp hz
          exact hrsub x (by rw [(b x).tsupport_eq, hb2 x] at hxz; exact hxz)


/-! ## The shifted loop family -/

/-- **Joint smoothness of the *shifted* loop family** `(q, z) ↦ sgLoop Ξ Q (s₁ + q) (sqPart z)`: the
composite of the joint smoothness of `sgLoop` in its parameter with the affine shift `q ↦ s₁ + q`. -/
theorem contMDiff_sgLoop_shift {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s₁ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => sgLoop Ξ Q (s₁ + q.1) (sqPart q.2)) := by
  have hshift : ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => (s₁ + q.1, q.2)) := by fun_prop
  have h := (contMDiff_sgLoop_fam Ξ Q hΞ hQ).comp (contMDiff_iff_contDiff.mpr hshift)
  simpa [Function.comp_def] using h

/-- **The charted parameter-derivative of the shifted loop value is onto.**  The unshifted statement
is `Work.Drive.hsurj_sgLoop` (whose content is `ChartPert`'s surjectivity at *every* parameter and
point); composing with the translation `q ↦ s₁ + q` (whose derivative is the identity) transfers it to
the shifted family. -/
theorem hsurj_sgLoop_shift {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (p : CappingSpace) (s₁ t : EuclideanSpace ℝ (Fin m)) (u : EuclideanSpace ℝ (Fin 2))
    (hsrc : sgLoop Ξ Q (s₁ + t) u ∈ (chr p).source) :
    Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (sgLoop Ξ Q (s₁ + t') u)) t) := by
  set F : EuclideanSpace ℝ (Fin m) → Tgt 4 := fun w => chr p (sgLoop Ξ Q w u) with hF
  have hsurjF : Function.Surjective (fderiv ℝ F (s₁ + t)) := by
    have h := hsurj_sgLoop Ξ Q hΞ hQ p (s₁ + t) u
      (by simpa [hF, sgLoop, coreLoop, pertChart, Function.comp_def] using hsrc)
    simpa [hF, sgLoop, coreLoop, pertChart, Function.comp_def] using h
  have hFat : ContDiffAt ℝ Ctop F (s₁ + t) := by
    have h1 : ContMDiffAt (𝓡 m) (𝓡 4) Ctop (fun w : EuclideanSpace ℝ (Fin m) => sgLoop Ξ Q w u)
        (s₁ + t) :=
      (contMDiff_sgLoop Ξ Q hΞ hQ).contMDiffAt.comp (s₁ + t)
        (contMDiffAt_id.prodMk contMDiffAt_const)
    have h2 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (sgLoop Ξ Q (s₁ + t) u) :=
      (gpn_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hsrc)
    exact contMDiffAt_iff_contDiffAt.mp (h2.comp (s₁ + t) h1)
  have hdF : HasFDerivAt F (fderiv ℝ F (s₁ + t)) (s₁ + t) :=
    (hFat.differentiableAt gpn_top_ne_zero).hasFDerivAt
  have hshift : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => s₁ + t')
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) t :=
    (hasFDerivAt_id t).const_add s₁
  have hcomp := hdF.comp t hshift
  have hgoal : (fun t' : EuclideanSpace ℝ (Fin m) => chr p (sgLoop Ξ Q (s₁ + t') u))
      = F ∘ (fun t' : EuclideanSpace ℝ (Fin m) => s₁ + t') := by
    funext t'; rfl
  rw [hgoal, hcomp.fderiv]
  simpa only [ContinuousLinearMap.comp_id] using hsurjF

/-! ## Smoothness of the cut-off-scaled shifted charted difference system -/

/-- **Joint smoothness of the charted difference of the shifted loop family with a fixed chain**, at a
point where both values lie in the chart's source. -/
theorem chartDiff_shift_joint_contDiffAt {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s₁ : EuclideanSpace ℝ (Fin m))
    (Sweep : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hSweep : ContMDiff (𝓡 3) (𝓡 4) Ctop Sweep)
    (p : CappingSpace) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4)
    (hreg : sgLoop Ξ Q (s₁ + q₀.1) (sqPart q₀.2) ∈ (chr p).source ∧
      Sweep (cbPart q₀.2) ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        chartDiff p (sgLoop Ξ Q (s₁ + q.1)) Sweep q.2) q₀ := by
  have hloop : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => sgLoop Ξ Q (s₁ + q.1) (sqPart q.2)) :=
    contMDiff_sgLoop_shift Ξ Q hΞ hQ s₁
  have h1 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        chr p (sgLoop Ξ Q (s₁ + q.1) (sqPart q.2))) q₀ :=
    contMDiffAt_iff_contDiffAt.mp
      (((gpn_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg.1)).comp q₀
        hloop.contMDiffAt)
  have h2 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => chr p (Sweep (cbPart q.2))) q₀ := by
    have hsw : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep (cbPart q.2)) :=
      hSweep.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    exact contMDiffAt_iff_contDiffAt.mp
      (((gpn_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg.2)).comp q₀
        hsw.contMDiffAt)
  exact h1.sub h2

/-- **Global smoothness of the cut-off-scaled shifted charted difference system.** -/
theorem contDiff_cutoff_chartDiff_shift {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s₁ : EuclideanSpace ℝ (Fin m))
    (Sweep : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hSweep : ContMDiff (𝓡 3) (𝓡 4) Ctop Sweep)
    (p : CappingSpace) {V : Set (EuclideanSpace ℝ (Fin m) × Amb 4)}
    (hV : V ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      sgLoop Ξ Q (s₁ + q.1) (sqPart q.2) ∈ (chr p).source ∧ Sweep (cbPart q.2) ∈ (chr p).source})
    {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ} (hχ : ContDiff ℝ Ctop χ)
    (hχsupp : tsupport χ ⊆ V) :
    ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        χ q • chartDiff p (sgLoop Ξ Q (s₁ + q.1)) Sweep q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases h0 : q₀ ∈ tsupport χ
  · exact hχ.contDiffAt.smul
      (chartDiff_shift_joint_contDiffAt Ξ Q hΞ hQ s₁ Sweep hSweep p q₀ (hV (hχsupp h0)))
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [gpn_eventually_eq_zero_of_notMem_tsupport h0] with q hq
    rw [hq, zero_smul]


/-! ## The base-point version of the Sard existence

The remainder of this file proves `Work.Drive.sgGoodPair_of_small_shift`: the parametric-Sard
existence of `sgAssembly.lean`, run at the base configuration `(s₁, s₂)` with the `psg`-style compact
sets carrying the Sard clauses (projections of `S i ∩ {‖q‖ ≤ ε}`). -/

/-- **The base-point version of `Work.Drive.sgGoodPair_of_small`.**  For every `ε₀ > 0` there is a chart
perturbation `p` of norm `< ε₀` at which the pair `(Ξ (s₁ + p) ∘ Q, rotCapping w ∘ Ξ s₂ ∘ Q)` is a
`GoodPair`. -/
theorem sgGoodPair_of_small_shift {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (w : UnitAddCircle) (s₁ s₂ : EuclideanSpace ℝ (Fin m)) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε₀ ∧
      GoodPair (pertChart Ξ Q (s₁ + p)) (fun z : ℂ => rotCapping w (pertChart Ξ Q s₂ z)) c := by
  classical
  -- ## 0. the sweep: the chart `Ξ s₂ ∘ Q` and its fixed chain
  have hQ₂sm : IsSmoothChart (pertChart Ξ Q s₂) := hΞ.2.1.comp (contMDiff_const.prodMk hQ)
  let Sweep : EuclideanSpace ℝ (Fin 3) → CappingSpace := sgSweep0 (pertChart Ξ Q s₂) c w
  have hSweep_sm : ContMDiff (𝓡 3) (𝓡 4) Ctop Sweep :=
    contMDiff_sgSweep0 (pertChart Ξ Q s₂) c w hQ₂sm
  have hcb_cont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => cbPart q.2) := by
    have h : (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => cbPart q.2)
        = fun q => cbPartCLM q.2 := by
      funext q; rw [cbPartCLM_eq_cbPart]
    rw [h]
    exact cbPartCLM.continuous.comp continuous_snd
  have hSweep_cont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep (cbPart q.2)) :=
    hSweep_sm.continuous.comp hcb_cont
  -- the loop value of the shifted family
  let LoopVal : EuclideanSpace ℝ (Fin m) → Amb 4 → CappingSpace :=
    fun q z => sgLoop Ξ Q (s₁ + q) (sqPart z)
  have hLoopVal_sm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => LoopVal q.1 q.2) :=
    contMDiff_sgLoop_shift Ξ Q hΞ hQ s₁
  have hLoopVal_cont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => LoopVal q.1 q.2) :=
    hLoopVal_sm.continuous
  -- ## 1. the compact value set and its chart cover
  have hValComp : IsCompact (Sweep '' Submission.Drive.unitBox 2) :=
    (isCompact_unitBox 2).image hSweep_sm.continuous
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover (Sweep '' Submission.Drive.unitBox 2) hValComp
  -- ## 2. the compact parameter sets `S i`, the chart regions `U i` and the thickenings
  let S : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q |
    ‖q.1‖ ≤ 1 ∧ q.2 ∈ Submission.Drive.unitBox 4 ∧
      LoopVal q.1 q.2 ∈ C0 i ∧ Sweep (cbPart q.2) ∈ C1 i}
  have hScomp : ∀ i, IsCompact (S i) := by
    intro i
    have hEq : S i = ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ
          Submission.Drive.unitBox 4)
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => LoopVal q.1 q.2) ⁻¹' (C0 i)))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep (cbPart q.2)) ⁻¹' (C1 i)) := by
      ext q
      simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      tauto
    refine IsCompact.of_isClosed_subset
      ((isCompact_closedBall 0 1).prod (isCompact_unitBox 4)) ?_ ?_
    · rw [hEq]
      refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
      · exact Metric.isClosed_closedBall.prod (isClosed_unitBox 4)
      · exact (hC0c i).isClosed.preimage hLoopVal_cont
      · exact (hC1c i).isClosed.preimage hSweep_cont
    · intro q hq
      rw [hEq] at hq
      exact hq.1.1
  let U : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q |
    LoopVal q.1 q.2 ∈ (chr (pch i)).source ∧ Sweep (cbPart q.2) ∈ (chr (pch i)).source}
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    have hEq : U i = ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => LoopVal q.1 q.2) ⁻¹'
          ((chr (pch i)).source))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep (cbPart q.2)) ⁻¹'
          ((chr (pch i)).source)) := by
      ext q; simp only [U, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hEq]
    exact ((chr (pch i)).open_source.preimage hLoopVal_cont).inter
      ((chr (pch i)).open_source.preimage hSweep_cont)
  have hSU : ∀ i, S i ⊆ U i := by
    intro i q hq
    have hq' : LoopVal q.1 q.2 ∈ C0 i ∧ Sweep (cbPart q.2) ∈ C1 i := by
      have h := hq
      dsimp only [S] at h
      simpa only [Set.mem_setOf_eq] using ⟨h.2.2.1, h.2.2.2⟩
    exact ⟨hC1sub i (interior_subset (hC0int i hq'.1)), hC1sub i hq'.2⟩
  have hthick : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      (q, z) ∈ S i → ‖q' - q‖ ≤ δ → (q', z) ∈ U i := fun i =>
    exists_pos_norm_subset_of_isCompact_subset_isOpen (hScomp i) (hUopen i) (hSU i)
  choose δ hδpos hδ using hthick
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    have hmem : Sweep 0 ∈ Sweep '' Submission.Drive.unitBox 2 :=
      ⟨0, fun _ => ⟨le_refl 0, zero_le_one⟩, rfl⟩
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp (hcover hmem)
    have hlt : i.1 < r := i.isLt
    omega
  set δ₀ : ℝ := Finset.univ.inf' ⟨⟨0, hrpos⟩, Finset.mem_univ _⟩ δ with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact (Finset.lt_inf'_iff ⟨⟨0, hrpos⟩, Finset.mem_univ _⟩).mpr (fun i _ => hδpos i)
  have hδ₀le : ∀ i, δ₀ ≤ δ i := by
    intro i
    rw [hδ₀def]
    exact Finset.inf'_le δ (Finset.mem_univ i)
  -- ## 3. the radii of the Sard argument
  set ε : ℝ := min (min (ε₀ / 2) (δ₀ / 2)) (1 / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεε₀ : ε ≤ ε₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ : 2 * ε ≤ δ₀ := by
    have h1 : ε ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεδi : ∀ i, 2 * ε ≤ δ i := fun i => le_trans hεδ (hδ₀le i)
  -- ## 4. the compact Sard sets `K i`, the cut-offs and the face pieces
  let K : Fin r → Set (Amb 4) := fun i => {z | ∃ q : EuclideanSpace ℝ (Fin m),
    ‖q‖ ≤ ε ∧ (q, z) ∈ S i}
  have hKcomp : ∀ i, IsCompact (K i) := by
    intro i
    have hEq : K i = Prod.snd '' (S i ∩
        {q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) := by
      ext z
      constructor
      · rintro ⟨q, hq, hqz⟩
        exact ⟨(q, z), ⟨hqz, hq⟩, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.1, by simpa using hq.2, hq.1⟩
    rw [hEq]
    exact ((hScomp i).inter_right (isClosed_le (continuous_norm.comp continuous_fst)
      continuous_const)).image continuous_snd
  have hKsub : ∀ i, Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ×ˢ K i ⊆ U i := by
    intro i
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    obtain ⟨q₀, hq₀, hq₀S⟩ := hz
    have hqq : ‖q - q₀‖ ≤ δ i := by
      have hqε : ‖q‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hq
      have h1 : ‖q - q₀‖ ≤ ‖q‖ + ‖q₀‖ := norm_sub_le q q₀
      linarith [hεδi i]
    exact hδ i q₀ q z hq₀S hqq
  have hcut : ∀ i, ∃ χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ, ContDiff ℝ Ctop χ ∧
      (∀ q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ K i, χ q = 1) ∧
      tsupport χ ⊆ U i := fun i =>
    gpn_exists_cutoff_one_on_of_subset ((isCompact_closedBall 0 ε).prod (hKcomp i))
      (hUopen i) (hKsub i)
  choose χ hχsm hχone hχsupp using hcut
  let Kzero : (i : Fin r) → (Fin 4 × Fin 2) → Set (EuclideanSpace ℝ (Fin 3)) := fun i j =>
    Submission.Drive.unitBox 2 ∩ (sgFace j.1 j.2 ⁻¹' K i)
  have hKzero_compact : ∀ (i : Fin r) (j : Fin 4 × Fin 2), IsCompact (Kzero i j) := by
    intro i j
    exact (isCompact_unitBox 2).inter_right
      ((hKcomp i).isClosed.preimage (continuous_sgFace j.1 j.2))
  let Phi : Fin r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun i q =>
    χ i q • chartDiff (pch i) (sgLoop Ξ Q (s₁ + q.1)) Sweep q.2
  have hΦsm : ∀ i, ContDiff ℝ Ctop (Phi i) := fun i =>
    contDiff_cutoff_chartDiff_shift Ξ Q hΞ hQ s₁ Sweep hSweep_sm (pch i) (fun q hq => hq)
      (hχsm i) (hχsupp i)
  -- ## 5. the parameter-surjectivity hypothesis of the parametric Sard theorem
  have hsurjPhi : ∀ (i : Fin r) (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ < ε →
      (z ∈ K i ∨ ∃ j : Fin 4 × Fin 2, z ∈ sgFace j.1 j.2 '' Kzero i j) → Phi i (q, z) = 0 →
      Function.Surjective (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => Phi i (q', z)) q) := by
    intro i q z hq hz h0
    have hzK : z ∈ K i := hz.elim id fun h => by
      obtain ⟨j, y, hy, rfl⟩ := h
      exact hy.2
    have hχ1 : χ i (q, z) = 1 := hχone i (q, z)
      ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hq, hzK⟩
    have hreg := hKsub i (show (q, z) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ×ˢ K i
      from ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hq, hzK⟩)
    have hcd0 : chartDiff (pch i) (sgLoop Ξ Q (s₁ + q)) Sweep z = 0 := by
      have h := h0
      dsimp only [Phi] at h
      rw [hχ1, one_smul] at h
      exact h
    have hχat : ContDiffAt ℝ Ctop (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) q :=
      (hχsm i).contDiffAt.comp q (contDiffAt_id.prodMk contDiffAt_const)
    have hcdat : ContDiffAt ℝ Ctop
        (fun q' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) q := by
      have hjoint : ContDiffAt ℝ Ctop
          (fun qq : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + qq.1)) Sweep qq.2) (q, z) :=
        chartDiff_shift_joint_contDiffAt Ξ Q hΞ hQ s₁ Sweep hSweep_sm (pch i) (q, z) hreg
      have hpair : ContDiffAt ℝ Ctop
          (fun q' : EuclideanSpace ℝ (Fin m) => (q', z)) q :=
        contDiffAt_id.prodMk contDiffAt_const
      simpa only [Function.comp_def] using hjoint.comp q hpair
    have hχfd : HasFDerivAt (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z))
        (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) q) q :=
      (hχat.differentiableAt gpn_top_ne_zero).hasFDerivAt
    have hcdfd : HasFDerivAt
        (fun q' : EuclideanSpace ℝ (Fin m) => chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z)
        (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) q) q :=
      (hcdat.differentiableAt gpn_top_ne_zero).hasFDerivAt
    have hsmul := hχfd.smul hcdfd
    have h1 : (χ i (q, z)) • (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) q)
        + (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) q).smulRight
            (chartDiff (pch i) (sgLoop Ξ Q (s₁ + q)) Sweep z)
        = fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) q := by
      rw [hχ1, one_smul, hcd0]
      simp
    rw [h1] at hsmul
    have hsurjinner : Function.Surjective (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
        chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) q) := by
      have hfun : (fun q' : EuclideanSpace ℝ (Fin m) =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z)
          = (fun q' : EuclideanSpace ℝ (Fin m) =>
            chr (pch i) (sgLoop Ξ Q (s₁ + q') (sqPart z)) - chr (pch i) (Sweep (cbPart z))) := rfl
      rw [hfun, fderiv_sub_const]
      exact hsurj_sgLoop_shift Ξ Q hΞ hQ (pch i) s₁ q (sqPart z) (by simpa using hreg.1)
    have hgoal : (fun q' : EuclideanSpace ℝ (Fin m) => Phi i (q', z))
        = fun q' : EuclideanSpace ℝ (Fin m) =>
            χ i (q', z) • chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z := rfl
    rw [hgoal]
    rw [show (fun q' : EuclideanSpace ℝ (Fin m) =>
          χ i (q', z) • chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z)
        = (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) •
          (fun q' : EuclideanSpace ℝ (Fin m) =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + q')) Sweep z) from rfl]
    rw [hsmul.fderiv]
    exact hsurjinner
  -- ## 6. the parametric Sard theorem
  have hfin3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) < 4 := by
    rw [finrank_euclideanSpace]
    norm_num
  obtain ⟨pst, hpst, hregS, havoidS⟩ :=
    exists_forall_good_and_notMem_family_multi (m := m) (n := 4) (r := r)
      (K := K) (hK := hKcomp)
      (ι := fun _ => Fin 4 × Fin 2) (X := fun _ _ => EuclideanSpace ℝ (Fin 3))
      (hX := fun _ _ => hfin3)
      (B := fun _ j => sgFace j.1 j.2) (hB := fun _ j => contDiff_sgFace j.1 j.2)
      (K₀ := Kzero) (hK₀ := hKzero_compact) (Φ := Phi) (hΦ := hΦsm)
      (ε := ε) (hε := hεpos) (hsurj := hsurjPhi)
  -- ## 7. the perturbed charts and the meet analysis
  let Q₁ : ℂ → CappingSpace := pertChart Ξ Q (s₁ + pst)
  let Q₂ : ℂ → CappingSpace := pertChart Ξ Q s₂
  let Q₂' : ℂ → CappingSpace := fun z => rotCapping w (Q₂ z)
  have hQ₁sm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q₁ := hΞ.2.1.comp (contMDiff_const.prodMk hQ)
  have hQ₂sm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q₂ := hΞ.2.1.comp (contMDiff_const.prodMk hQ)
  have hQ₂rotsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q₂' :=
    (contMDiff_rotCapping_const w).comp hQ₂sm
  have hloop₁sm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) Ctop (coreLoop Q₁) := contMDiff_coreLoop hQ₁sm
  have hpst_le : ‖pst‖ ≤ ε := le_of_lt hpst
  have hpst_le1 : ‖pst‖ ≤ 1 := by
    have h : ε ≤ 1 := by linarith [hε1]
    linarith
  -- ### the data of a meet
  have hmeetdata : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂'),
      ∃ i : Fin r, Sweep q.2 ∈ C0 i ∧ meetPt q ∈ K i ∧
        ((sgLoop Ξ Q (s₁ + pst)) (sqPart (meetPt q)) ∈ (chr (pch i)).source ∧
          Sweep (cbPart (meetPt q)) ∈ (chr (pch i)).source) ∧
        (sgLoop Ξ Q (s₁ + pst)) (sqPart (meetPt q)) = Sweep (cbPart (meetPt q)) ∧
        Phi i (pst, meetPt q) = 0 := by
    rintro q ⟨hq1, hq2, hmeet⟩
    have hy : Sweep q.2 ∈ Sweep '' Submission.Drive.unitBox 2 := ⟨q.2, hq2, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hy)
    have hbox : meetPt q ∈ Submission.Drive.unitBox 4 := meetPt_mem_unitBox_of hq1 hq2
    have hloop : LoopVal pst (meetPt q) = Sweep q.2 := by
      have h1 : LoopVal pst (meetPt q) = sgLoop Ξ Q (s₁ + pst) (sqPart (meetPt q)) := rfl
      rw [h1]
      have h2 : sgLoop Ξ Q (s₁ + pst) (sqPart (meetPt q)) = coreLoop Q₁ q.1 := by
        simp only [Function.comp_apply, sgLoop, coreLoop, Q₁, pertChart, sqPart_apply,
          sqIdx_zero, meetPt_apply_zero]
      rw [h2]
      exact hmeet
    have hchain : Sweep (cbPart (meetPt q)) = Sweep q.2 := by rw [cbPart_meetPt]
    have hzS : (pst, meetPt q) ∈ S i := by
      refine ⟨hpst_le1, hbox, ?_, ?_⟩
      · show LoopVal pst (meetPt q) ∈ C0 i
        rw [hloop]; exact hi
      · show Sweep (cbPart (meetPt q)) ∈ C1 i
        rw [hchain]; exact interior_subset (hC0int i hi)
    have hzK : meetPt q ∈ K i := ⟨pst, hpst_le, hzS⟩
    have hzU : (sgLoop Ξ Q (s₁ + pst)) (sqPart (meetPt q)) ∈ (chr (pch i)).source ∧
        Sweep (cbPart (meetPt q)) ∈ (chr (pch i)).source := by
      have h := hKsub i
        (show (pst, meetPt q) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ×ˢ K i from
          ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩)
      have h' := h
      dsimp only [U, LoopVal] at h'
      simpa only [Set.mem_setOf_eq] using h'
    have heq : (sgLoop Ξ Q (s₁ + pst)) (sqPart (meetPt q)) = Sweep (cbPart (meetPt q)) := by
      rw [hchain]
      exact hloop
    have hPhi0 : Phi i (pst, meetPt q) = 0 := by
      show χ i (pst, meetPt q) • chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep (meetPt q) = 0
      have hχ1 : χ i (pst, meetPt q) = 1 := hχone i (pst, meetPt q)
        ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩
      rw [hχ1, one_smul]
      exact (chartDiff_eq_zero_iff (x := meetPt q) hzU).mpr heq
    exact ⟨i, hi, hzK, hzU, heq, hPhi0⟩
  -- ### the transversality clause
  have hTrans : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂'),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
          (clampedSweep c (fun t => 1 - t) (diskPlane Q₂')) q.2).toLinearMap = ⊤ := by
    rintro q hq
    obtain ⟨i, hiC0, hzK, hzU, heq, hPhi0⟩ := hmeetdata q hq
    have hzderiv : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q)) := by
      have hS := hregS i (meetPt q) hzK hPhi0
      have hχ1 : χ i (pst, meetPt q) = 1 := hχone i (pst, meetPt q)
        ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩
      have hcdat : ContDiffAt ℝ Ctop
          (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q) := by
        have hjoint : ContDiffAt ℝ Ctop
            (fun zz : EuclideanSpace ℝ (Fin m) × Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q (s₁ + zz.1)) Sweep zz.2) (pst, meetPt q) :=
          chartDiff_shift_joint_contDiffAt Ξ Q hΞ hQ s₁ Sweep hSweep_sm (pch i) (pst, meetPt q) hzU
        have hpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (pst, z')) (meetPt q) :=
          contDiffAt_const.prodMk contDiffAt_id
        simpa only [Function.comp_def] using hjoint.comp (meetPt q) hpair
      have hcd0 : chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep (meetPt q) = 0 :=
        (chartDiff_eq_zero_iff hzU).mpr heq
      have hcdp : HasFDerivAt
          (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z')
          (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q)) (meetPt q) :=
        (hcdat.differentiableAt gpn_top_ne_zero).hasFDerivAt
      have hχat : ContDiffAt ℝ Ctop (fun z' : Amb 4 => χ i (pst, z')) (meetPt q) := by
        have hpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (pst, z')) (meetPt q) :=
          contDiffAt_const.prodMk contDiffAt_id
        exact (hχsm i).contDiffAt.comp (meetPt q) hpair
      have hbp : HasFDerivAt (fun z' : Amb 4 => χ i (pst, z'))
          (fderiv ℝ (fun z' : Amb 4 => χ i (pst, z')) (meetPt q)) (meetPt q) :=
        (hχat.differentiableAt gpn_top_ne_zero).hasFDerivAt
      have hsmul := hbp.smul hcdp
      have h1 : (χ i (pst, meetPt q)) • (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q))
          + (fderiv ℝ (fun z' : Amb 4 => χ i (pst, z')) (meetPt q)).smulRight
              (chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep (meetPt q))
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q) := by
        rw [hχ1, one_smul, hcd0]
        simp
      rw [h1] at hsmul
      have hfd : fderiv ℝ (fun z' : Amb 4 =>
            χ i (pst, z') • chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q)
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q) := hsmul.fderiv
      change Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
          χ i (pst, z') • chartDiff (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep z') (meetPt q)) at hS
      rw [hfd] at hS
      exact hS
    have hbridge := range_sup_eq_top_of_chartDiff_surjective (pch i) (sgLoop Ξ Q (s₁ + pst)) Sweep
      (contMDiff_sgLoop_fixed Ξ Q hΞ hQ (s₁ + pst)) hSweep_sm hzU heq hzderiv
    have hconv : LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (sgLoop Ξ Q (s₁ + pst))
          (sqPart (meetPt q))).toLinearMap
        = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap := by
      have h := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)
        (fun a => ⟨gpnSq2 a 0, by simp [PiLp.proj_apply]⟩) (sqPart (meetPt q))
      have h3 : (fun x : EuclideanSpace ℝ (Fin 2) =>
            coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) x))
          = sgLoop Ξ Q (s₁ + pst) := by
        funext x; simp only [Function.comp_apply, sgLoop, coreLoop, Q₁, pertChart, PiLp.proj_apply]
      rw [h3] at h
      have h2 : (sqPart (meetPt q)) 0 = q.1 := by rw [sqPart_meetPt]; rfl
      rw [PiLp.proj_apply, h2] at h
      exact h
    rw [hconv, cbPart_meetPt] at hbridge
    rw [show (clampedSweep c (fun t => 1 - t) (diskPlane Q₂')) = Sweep from rfl]
    exact hbridge
  -- ### the finiteness of the meet set
  have hFin : (coreMeet Q₁ c (diskPlane Q₂')).Finite := by
    let L : EuclideanSpace ℝ (Fin 1) → CappingSpace :=
      fun x => coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) x)
    have hLsm : ContMDiff (𝓡 1) (𝓡 4) Ctop L :=
      hloop₁sm.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contMDiff
    have htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 → L u = Sweep x →
        LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4) Sweep x).toLinearMap = ⊤ := by
      intro u x hu hx heq
      have huI : (u 0) ∈ Set.Icc (0 : ℝ) 1 := by simpa [Submission.Drive.unitBox] using hu
      have hq : (u 0, x) ∈ coreMeet Q₁ c (diskPlane Q₂') := ⟨huI, hx, by
        have h1 : L u = coreLoop Q₁ (u 0) := by simp [L, PiLp.proj_apply]
        rw [← h1]
        exact heq⟩
      have h := hTrans (u 0, x) hq
      have hconv : LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap
          = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) (u 0)).toLinearMap := by
        have hh := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0)
          (fun a => ⟨gpnMk1 a, by simp [gpnMk1]⟩) u
        have h2 : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) u = u 0 := rfl
        rw [h2] at hh
        exact hh
      rw [hconv]
      exact h
    have hfin1 := finite_loopChainMeet_of_transverse L Sweep hLsm hSweep_sm htrans
    have himg : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        (p.1 0, p.2)) '' {p | p.1 ∈ Submission.Drive.unitBox 0 ∧
          p.2 ∈ Submission.Drive.unitBox 2 ∧ L p.1 = Sweep p.2} = coreMeet Q₁ c (diskPlane Q₂') := by
      ext q
      constructor
      · rintro ⟨p, ⟨hp1, hp2, hpm⟩, rfl⟩
        exact ⟨by simpa [Submission.Drive.unitBox] using hp1, hp2, hpm⟩
      · rintro ⟨hq1, hq2, hqm⟩
        refine ⟨(gpnMk1 q.1, q.2), ⟨?_, hq2, ?_⟩, ?_⟩
        · have hp1 : (gpnMk1 q.1 : EuclideanSpace ℝ (Fin 1)) ∈ Submission.Drive.unitBox 0 := by
            simpa [Submission.Drive.unitBox, gpnMk1] using hq1
          exact hp1
        · have h1 : L (gpnMk1 q.1) = coreLoop Q₁ q.1 := by simp [L, gpnMk1]
          rw [h1]
          exact hqm
        · simp [gpnMk1]
    rw [← himg]
    exact hfin1.image _
  -- ### the interiority of the meets
  have hInt : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂'),
      q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ j : Fin 3, q.2 j ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro q hq
    obtain ⟨hq1, hq2, hmeet⟩ := hq
    obtain ⟨i, hiC0, hzK, hzU, heq, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
    have hzbox : ∀ k : Fin 5, k ≠ 1 → meetPt q k ∈ Set.Icc (0 : ℝ) 1 :=
      fun k _ => meetPt_mem_unitBox_of hq1 hq2 k
    have hcontra : ∀ (k : Fin 4) (t : Fin 2), (t : ℝ) = meetPt q (boxIdx k) → False := by
      intro k t ht
      have hybox : gatherCLM k (meetPt q) ∈ Submission.Drive.unitBox 2 :=
        gatherCLM_mem_unitBox hzbox
      have hface : sgFace k t (gatherCLM k (meetPt q)) ∈ K i := by
        rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht]
        exact hzK
      have hyK : gatherCLM k (meetPt q) ∈ Kzero i (k, t) := by
        refine ⟨hybox, ?_⟩
        show sgFace (k, t).1 (k, t).2 (gatherCLM k (meetPt q)) ∈ K i
        exact hface
      have hne := havoidS i (k, t) (gatherCLM k (meetPt q)) hyK
      rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht] at hne
      exact hne hPhi0
    refine ⟨?_, fun j => ?_⟩
    · refine ⟨?_, ?_⟩
      · by_contra h
        push_neg at h
        exact hcontra 0 ⟨0, by norm_num⟩ (by
          rw [boxIdx_zero, meetPt_apply_zero, le_antisymm h hq1.1]; norm_num)
      · by_contra h
        push_neg at h
        exact hcontra 0 ⟨1, by norm_num⟩ (by
          rw [boxIdx_zero, meetPt_apply_zero, le_antisymm hq1.2 h]; norm_num)
    · refine ⟨?_, ?_⟩
      · by_contra h
        push_neg at h
        exact hcontra (Fin.succ j) ⟨0, by norm_num⟩ (by
          rw [← cbIdx_eq_boxIdx j, meetPt_cbIdx, le_antisymm h (hq2 j).1]; norm_num)
      · by_contra h
        push_neg at h
        exact hcontra (Fin.succ j) ⟨1, by norm_num⟩ (by
          rw [← cbIdx_eq_boxIdx j, meetPt_cbIdx, le_antisymm (hq2 j).2 h]; norm_num)
  -- ## 8. the `GoodPair`
  exact ⟨pst, by linarith [hpst, hεε₀, hε₀], hQ₁sm, hQ₂rotsm, hFin, hInt, hTrans⟩


/-! ## The target lemma -/

theorem goodPair_pertChart_exists_near {Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace}
    {Q : ℂ → Work.Drive.CappingSpace}
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (hQ : Work.Drive.IsSmoothChart Q) (c : ℝ) (w : UnitAddCircle)
    (s₁ s₂ : EuclideanSpace ℝ (Fin 4)) :
    ∀ ε : ℝ, 0 < ε → ∃ p : EuclideanSpace ℝ (Fin 4), ‖p‖ < ε ∧
      Work.Drive.GoodAt Ξ Q c w (s₁ + p, s₂) := by
  intro ε hε
  obtain ⟨p, hp, hgood⟩ := sgGoodPair_of_small_shift Ξ Q c hΞ hQ w s₁ s₂ ε hε
  exact ⟨p, hp, hgood⟩


end

end Work.Drive
