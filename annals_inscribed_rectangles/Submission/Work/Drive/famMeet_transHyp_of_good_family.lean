import Mathlib
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.FamBox.Smooth
import Submission.Work.Drive.FamBox.Engine
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.transHyp_of_good_family
import Submission.Work.Drive.exists_forall_good_on_compact_ball

set_option maxHeartbeats 1000000

namespace Work.Drive

open scoped Manifold ContDiff Topology BigOperators
open Manifold Set Metric Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Elementary helpers -/

/-- The differentiability order `⊤` is not zero. -/
private lemma famMeet_top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma famMeet_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X]
    [Zero Y] {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **A smooth cut-off equal to `1` on a compact set and supported in a prescribed open
superset.** -/
private lemma famMeet_exists_cutoff_one_on_of_subset {n : ℕ}
    {K V : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ Ctop f ∧ (∀ x ∈ K, f x = 1) ∧
      tsupport f ⊆ V := by
  classical
  have hpt : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ V := by
    intro x
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.2))
    refine ⟨r / 4, by linarith, ?_⟩
    intro z hz
    apply hrsub
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  choose r hrpos hrsub using hpt
  have hbump : ∀ x : K, ∃ b : ContDiffBump (x : EuclideanSpace ℝ (Fin n)),
      b.rIn = r x ∧ b.rOut = 2 * r x := fun x =>
    ⟨⟨r x, 2 * r x, hrpos x, by linarith [hrpos x]⟩, rfl, rfl⟩
  choose b hb1 hb2 using hbump
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : EuclideanSpace ℝ (Fin n)) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrpos ⟨x, hx⟩)⟩)
  refine ⟨fun y => 1 - ∏ x ∈ s, (1 - b x y), ?_, ?_, ?_⟩
  · have hcont : ContDiff ℝ Ctop
        (fun y : EuclideanSpace ℝ (Fin n) => ∏ x ∈ s, (1 - b x y)) :=
      contDiff_prod (𝕜 := ℝ) (𝔸' := ℝ)
        (fun x _ => contDiff_const.sub (b x).contDiff)
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

/-! ## Joint smoothness of the parametrised charted difference map of the family -/

/-- The chart `chr p` is `C^∞` on its source. -/
private lemma famMeet_contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- A charted smooth map on the parameter space is jointly smooth where its value lies in the
chart source. -/
private lemma famMeet_contDiffAt_chart_fam {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) × Amb 4 → M)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop f)
    (p : M) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4) (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (famMeet_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-- The loop side of the family, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma famMeet_contMDiff_famLoop_fam (m : ℕ) (L : EuclideanSpace ℝ (Fin 2) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop L) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop L q.2) := by
  have h2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) 𝓘(ℝ, Amb 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => q.2) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)).contMDiff
  have h := (FamBox.contMDiff_famLoop L hL).comp h2
  simpa only [Function.comp_def] using h

/-- The block map `(q : ℝ^m × ℝ⁵) ↦ (q.1, chainArgCLM q.2)`. -/
private def famMeet_chainCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × Amb 4 →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4))
    (FamBox.chainArgCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)))

private lemma famMeet_chainCLM_apply (m : ℕ) (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    famMeet_chainCLM m q = (q.1, FamBox.chainArgCLM q.2) := by
  simp [famMeet_chainCLM]

/-- The chain side of the family, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma famMeet_contMDiff_famChain_fam (m : ℕ)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) := by
  have h := hN.comp ((famMeet_chainCLM m).contMDiff (n := Ctop))
  simpa only [Function.comp_def, famMeet_chainCLM_apply, FamBox.chainArgCLM_apply, famChain,
    Prod.mk.eta] using h

/-- A single slice of the chain family is a smooth chain `ℝ⁴ → M`. -/
private lemma famMeet_contMDiff_slice (m : ℕ)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 4) (𝓡 4) Ctop (N t) := by
  have h0 : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) Ctop
      (fun _ : EuclideanSpace ℝ (Fin 4) => (t, (0 : EuclideanSpace ℝ (Fin 4)))) :=
    contMDiff_const
  have h1 : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) Ctop
      (fun y : EuclideanSpace ℝ (Fin 4) => ((0 : EuclideanSpace ℝ (Fin m)), y)) :=
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 4))).contMDiff
  have h := hN.comp (h0.add h1)
  simpa only [Function.comp_def, Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
    using h

/-- **Joint smoothness of the parametrised charted difference map of the family.** -/
private lemma famMeet_chartDif_joint_contDiffAt (m : ℕ)
    (L : EuclideanSpace ℝ (Fin 2) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop L)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) (t₀ : EuclideanSpace ℝ (Fin m)) {y₀ : Amb 4}
    (hreg : famLoop L y₀ ∈ (chr p).source ∧ famChain (N t₀) y₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2) (t₀, y₀) := by
  have h1 := famMeet_contDiffAt_chart_fam (m := m)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop L q.2)
    (famMeet_contMDiff_famLoop_fam m L hL) p (t₀, y₀) hreg.1
  have h2 := famMeet_contDiffAt_chart_fam (m := m)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2)
    (famMeet_contMDiff_famChain_fam m N hN) p (t₀, y₀) hreg.2
  show ContDiffAt ℝ Ctop
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      chr p (famLoop L q.2) - chr p (famChain (N q.1) q.2)) (t₀, y₀)
  exact h1.sub h2

/-- **Global smoothness of the cut-off-scaled charted difference map.** -/
private lemma famMeet_contDiff_cutoff (m : ℕ)
    (L : EuclideanSpace ℝ (Fin 2) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop L)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ Ctop γ)
    {β : Amb 4 → ℝ} (hβ : ContDiff ℝ Ctop β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (Amb 4)}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famLoop L q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ q.1 * β q.2) • FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : famLoop L q₀.2 ∈ (chr p).source ∧
          famChain (N q₀.1) q₀.2 ∈ (chr p).source := hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2) q₀ :=
        famMeet_chartDif_joint_contDiffAt m L hL N hN p q₀.1 hreg
      have hg : ContDiffAt ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (famMeet_eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (famMeet_eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

/-! ## The target theorem -/

theorem famMeet_transHyp_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 2) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) (K : Set (Work.Drive.Amb 4)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      Work.Drive.famLoop L y ∈ (Work.Drive.chr p).source ∧
      Work.Drive.famChain (N t) y ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      Work.Drive.FamBox.chartDif p (Work.Drive.famLoop L) (Work.Drive.famChain (N t)) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.FamBox.chartDif p (Work.Drive.famLoop L) (Work.Drive.famChain (N t')) y) t)) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε ∧
      ∀ y : Work.Drive.Amb 4, y ∈ K → Work.Drive.famLoop L y = Work.Drive.famChain (N t) y →
        Function.Surjective
          (Work.Drive.FamBox.Lf (Work.Drive.famLoop L) (Work.Drive.famChain (N t)) y) := by
  classical
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := famMeet_top_ne_zero_order
  -- ## Step 1: the containment region and the compact tube around `{0} × K`
  have hFcd : ContMDiff (𝓡 5) (𝓡 4) Ctop (famLoop L) := FamBox.contMDiff_famLoop L hL
  have hcont1 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop L q.2) :=
    hFcd.continuous.comp continuous_snd
  have hGcd : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) :=
    famMeet_contMDiff_famChain_fam m N hN
  have hcont2 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) :=
    hGcd.continuous
  have hWopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famLoop L q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source} :=
    (hcont1.isOpen_preimage _ (chr p).open_source).inter
      (hcont2.isOpen_preimage _ (chr p).open_source)
  have hWsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2) ×ˢ K ⊆
      {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        famLoop L q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have htlt : ‖t‖ < ε := by
      have h := Metric.mem_closedBall.mp ht
      rw [dist_zero_right] at h
      linarith
    exact hcontain t y htlt hy
  obtain ⟨U, V, hUopen, hVopen, hUsub, hVsub, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2)) hK
      hWopen hWsub
  -- ## Step 2: the two cut-off functions
  obtain ⟨γ, hγsm, hγone, hγsupp⟩ :=
    famMeet_exists_cutoff_one_on_of_subset
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2)) hUopen hUsub
  obtain ⟨β, hβsm, hβone, hβsupp⟩ :=
    famMeet_exists_cutoff_one_on_of_subset hK hVopen hVsub
  -- ## Step 3: global smoothness of the cut-off-scaled family
  have hΦsm : ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ q.1 * β q.2) • FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2) :=
    famMeet_contDiff_cutoff m L hL N hN p hγsm hβsm hUV hγsupp hβsupp
  -- ## Step 4: the parameter-surjectivity hypothesis of the Sard theorem
  have hsurjΦ : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Amb 4), ‖t‖ ≤ ε / 2 → y ∈ K →
      (γ t * β y) • FamBox.chartDif p (famLoop L) (famChain (N t)) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β y) • FamBox.chartDif p (famLoop L) (famChain (N t')) y) t) := by
    intro t y ht hy h0
    have htlt : ‖t‖ < ε := by linarith
    have hγv : γ t = 1 := hγone t (by rw [Metric.mem_closedBall, dist_zero_right]; exact ht)
    have hβv : β y = 1 := hβone y hy
    have hχ0 : FamBox.chartDif p (famLoop L) (famChain (N t)) y = 0 := by
      have h := h0
      rw [hγv, hβv, mul_one, one_smul] at h
      exact h
    have hreg : famLoop L y ∈ (chr p).source ∧ famChain (N t) y ∈ (chr p).source :=
      hcontain t y htlt hy
    have hχat : ContDiffAt ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2) (t, y) :=
      famMeet_chartDif_joint_contDiffAt m L hL N hN p t hreg
    have hcomp : ContDiffAt ℝ Ctop
        ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2)
          ∘ fun t' : EuclideanSpace ℝ (Fin m) => (t', y)) t :=
      hχat.comp t (contDiffAt_id.prodMk (contDiffAt_const (c := y)))
    have hχp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        FamBox.chartDif p (famLoop L) (famChain (N t')) y)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop L) (famChain (N t')) y) t) t := by
      have h := (hcomp.differentiableAt htop).hasFDerivAt
      simpa only [Function.comp_def] using h
    have hγβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β y)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β y) t) t :=
      ((hγsm.contDiffAt.mul contDiffAt_const).differentiableAt htop).hasFDerivAt
    have hsmul := hγβp.smul hχp
    have h1 : (γ t * β y) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop L) (famChain (N t')) y) t)
        + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β y) t).smulRight
            (FamBox.chartDif p (famLoop L) (famChain (N t)) y)
        = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop L) (famChain (N t')) y) t := by
      rw [hγv, hβv, one_mul, hχ0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β y) • FamBox.chartDif p (famLoop L) (famChain (N t')) y) t
        = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop L) (famChain (N t')) y) t := hsmul.fderiv
    rw [hfd]
    exact hsurj t y htlt hy hχ0
  -- ## Step 5: parametric Sard
  obtain ⟨t, ht4, hgood⟩ :=
    exists_forall_good_on_compact_ball m 4 K hK (ε / 2) (ε / 4)
      (by linarith) (by linarith) (by linarith)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ q.1 * β q.2) • FamBox.chartDif p (famLoop L) (famChain (N q.1)) q.2)
      hΦsm hsurjΦ
  -- ## Step 6: transfer to the intrinsic difference of derivatives
  refine ⟨t, by linarith, ?_⟩
  intro y hyK heq
  have htlt : ‖t‖ < ε := by linarith
  have hγv : γ t = 1 := hγone t (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
  have hβv : β y = 1 := hβone y hyK
  have hreg : y ∈ FamBox.chartReg p (famLoop L) (famChain (N t)) := hcontain t y htlt hyK
  have hzy : FamBox.chartDif p (famLoop L) (famChain (N t)) y = 0 :=
    (FamBox.chartDif_eq_zero_iff hreg).mpr heq
  have hΦ0 : (γ t * β y) • FamBox.chartDif p (famLoop L) (famChain (N t)) y = 0 := by
    rw [hγv, hβv, mul_one, hzy, smul_zero]
  have hgoody : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
      (γ t * β z') • FamBox.chartDif p (famLoop L) (famChain (N t)) z') y) :=
    hgood y hyK hΦ0
  have hNt : ContMDiff (𝓡 4) (𝓡 4) Ctop (N t) := famMeet_contMDiff_slice m N hN t
  have hGt : ContMDiff (𝓡 5) (𝓡 4) Ctop (famChain (N t)) :=
    FamBox.contMDiff_famChain (N t) hNt
  have hχat : ContDiffAt ℝ Ctop
      (fun z' : Amb 4 => FamBox.chartDif p (famLoop L) (famChain (N t)) z') y :=
    (FamBox.contDiffOn_chartDif p (famLoop L) (famChain (N t)) hFcd hGt).contDiffAt
      ((FamBox.isOpen_chartReg p (famLoop L) (famChain (N t)) hFcd.continuous hGt.continuous).mem_nhds
        hreg)
  have hχp : HasFDerivAt (fun z' : Amb 4 =>
      FamBox.chartDif p (famLoop L) (famChain (N t)) z')
      (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop L) (famChain (N t)) z') y) y :=
    (hχat.differentiableAt htop).hasFDerivAt
  have hβp : HasFDerivAt (fun z' : Amb 4 => γ t * β z')
      (fderiv ℝ (fun z' : Amb 4 => γ t * β z') y) y :=
    ((contDiffAt_const.mul hβsm.contDiffAt).differentiableAt htop).hasFDerivAt
  have hsmul := hβp.smul hχp
  have h1 : (γ t * β y) • (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop L) (famChain (N t)) z') y)
      + (fderiv ℝ (fun z' : Amb 4 => γ t * β z') y).smulRight
          (FamBox.chartDif p (famLoop L) (famChain (N t)) y)
      = fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop L) (famChain (N t)) z') y := by
    rw [hγv, hβv, mul_one, hzy]
    simp
  rw [h1] at hsmul
  have hfd : fderiv ℝ (fun z' : Amb 4 =>
        (γ t * β z') • FamBox.chartDif p (famLoop L) (famChain (N t)) z') y
      = fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop L) (famChain (N t)) z') y := hsmul.fderiv
  have hsurjχ : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
      FamBox.chartDif p (famLoop L) (famChain (N t)) z') y) := by
    rw [← hfd]
    exact hgoody
  have heqfd : fderiv ℝ (FamBox.chartDif p (famLoop L) (famChain (N t))) y
      = (tangentCoordChange (𝓡 4) (famLoop L y) p (famLoop L y)).comp
          (FamBox.Lf (famLoop L) (famChain (N t)) y) :=
    ContinuousLinearMap.ext fun v =>
      FamBox.fderiv_chartDif_eq_Lf p (famLoop L) (famChain (N t)) hFcd hGt hreg heq v
  have hsurjComp : Function.Surjective
      ((tangentCoordChange (𝓡 4) (famLoop L y) p (famLoop L y)).comp
        (FamBox.Lf (famLoop L) (famChain (N t)) y)) := by
    rw [← heqfd]
    exact hsurjχ
  have hsrc1 : famLoop L y ∈ (extChartAt (𝓡 4) (famLoop L y)).source :=
    mem_extChartAt_source (I := 𝓡 4) _
  have hsrc2 : famLoop L y ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]
    exact hreg.1
  have hinj : Function.Injective (tangentCoordChange (𝓡 4) (famLoop L y) p (famLoop L y)) :=
    tangentCoordChange_injective (x := famLoop L y) (y := p) (z := famLoop L y) ⟨hsrc1, hsrc2⟩
  intro w
  obtain ⟨v, hv⟩ := hsurjComp (tangentCoordChange (𝓡 4) (famLoop L y) p (famLoop L y) w)
  exact ⟨v, hinj hv⟩

end

end Work.Drive
