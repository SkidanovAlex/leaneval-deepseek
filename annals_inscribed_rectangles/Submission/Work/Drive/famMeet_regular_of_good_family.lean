import Mathlib
import Submission.Work.Drive.famMeet_transHyp_of_good_family
import Submission.Work.Drive.famMeet_faceHyp_of_good_family
import Submission.Work.Drive.FamBox.Defs

namespace Work.Drive

open scoped Manifold ContDiff Topology BigOperators
open Manifold Set Metric Filter

set_option maxHeartbeats 1000000

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Elementary helpers -/

/-- The differentiability order `⊤` is not zero. -/
private lemma famMeetF_top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma famMeetF_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X]
    [Zero Y] {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **A smooth cut-off equal to `1` on a compact set and supported in a prescribed open
superset.** -/
private lemma famMeetF_exists_cutoff_one_on_of_subset {n : ℕ}
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
private lemma famMeetF_contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- A charted smooth map on the parameter space is jointly smooth where its value lies in the
chart source. -/
private lemma famMeetF_contDiffAt_chart_fam {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) × Amb 4 → M)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop f)
    (p : M) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4) (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (famMeetF_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-- The block map `(q : ℝ^m × ℝ⁵) ↦ (q.1, chainArgCLM q.2)`. -/
private def famMeetF_chainCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × Amb 4 →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4))
    (FamBox.chainArgCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)))

private lemma famMeetF_chainCLM_apply (m : ℕ) (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    famMeetF_chainCLM m q = (q.1, FamBox.chainArgCLM q.2) := by
  simp [famMeetF_chainCLM]

/-- The chain side of the family, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma famMeetF_contMDiff_famChain_fam (m : ℕ)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) := by
  have h := hN.comp ((famMeetF_chainCLM m).contMDiff (n := Ctop))
  simpa only [Function.comp_def, famMeetF_chainCLM_apply, FamBox.chainArgCLM_apply, famChain,
    Prod.mk.eta] using h

/-- The block map `(q : ℝ^m × ℝ⁵) ↦ (q.1, loopArgCLM q.2)`. -/
private def famMeetF_loopCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × Amb 4 →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4))
    (FamBox.loopArgCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)))

private lemma famMeetF_loopCLM_apply (m : ℕ) (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    famMeetF_loopCLM m q = (q.1, FamBox.loopArgCLM q.2) := by
  simp [famMeetF_loopCLM]

/-- The loop side of the family, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma famMeetF_contMDiff_famLoop_fam (m : ℕ)
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2) := by
  have h := hLf.comp ((famMeetF_loopCLM m).contMDiff (n := Ctop))
  simpa only [Function.comp_def, famMeetF_loopCLM_apply, FamBox.loopArgCLM_apply, famLoop,
    Prod.mk.eta] using h

/-- A single slice of the chain family is a smooth chain `ℝ⁴ → M`. -/
private lemma famMeetF_contMDiff_slice (m : ℕ)
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

/-- A single slice of the loop family is a smooth loop `ℝ² → M`. -/
private lemma famMeetF_contMDiff_slice_loop (m : ℕ)
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2))
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) Ctop (Lf t) := by
  have h0 : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) Ctop
      (fun _ : EuclideanSpace ℝ (Fin 2) => (t, (0 : EuclideanSpace ℝ (Fin 2)))) :=
    contMDiff_const
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => ((0 : EuclideanSpace ℝ (Fin m)), y)) :=
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 2))).contMDiff
  have h := hLf.comp (h0.add h1)
  simpa only [Function.comp_def, Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
    using h

/-- **Joint smoothness of the parametrised charted difference map of the family.** -/
private lemma famMeetF_chartDif_joint_contDiffAt (m : ℕ)
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2))
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) (t₀ : EuclideanSpace ℝ (Fin m)) {y₀ : Amb 4}
    (hreg : famLoop (Lf t₀) y₀ ∈ (chr p).source ∧ famChain (N t₀) y₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) (t₀, y₀) := by
  have h1 := famMeetF_contDiffAt_chart_fam (m := m)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2)
    (famMeetF_contMDiff_famLoop_fam m Lf hLf) p (t₀, y₀) hreg.1
  have h2 := famMeetF_contDiffAt_chart_fam (m := m)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2)
    (famMeetF_contMDiff_famChain_fam m N hN) p (t₀, y₀) hreg.2
  show ContDiffAt ℝ Ctop
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      chr p (famLoop (Lf q.1) q.2) - chr p (famChain (N q.1) q.2)) (t₀, y₀)
  exact h1.sub h2

/-- **Global smoothness of the cut-off-scaled charted difference map.** -/
private lemma famMeetF_contDiff_cutoff (m : ℕ)
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2))
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ Ctop γ)
    {β : Amb 4 → ℝ} (hβ : ContDiff ℝ Ctop β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (Amb 4)}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famLoop (Lf q.1) q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ q.1 * β q.2) • FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : famLoop (Lf q₀.1) q₀.2 ∈ (chr p).source ∧
          famChain (N q₀.1) q₀.2 ∈ (chr p).source := hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) q₀ :=
        famMeetF_chartDif_joint_contDiffAt m Lf hLf N hN p q₀.1 hreg
      have hg : ContDiffAt ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (famMeetF_eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (famMeetF_eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

/-! ## The bounded reparametrisation -/

/-- **A smooth bounded map whose derivative is surjective everywhere.** -/
private lemma famMeetF_squeeze_map (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      (∀ s, ‖σ s‖ ≤ δ) ∧
      (∀ s, Function.Surjective (fderiv ℝ σ s)) := by
  set c : ℝ := δ / (Real.pi * ((m : ℝ) + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)), ?_, ?_, ?_⟩
  · rw [contDiff_piLp]
    intro i
    exact (contDiff_const.mul
      (Real.contDiff_arctan.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).contDiff))
  · intro s
    have hb : ∀ i : Fin m,
        ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ (c * (Real.pi / 2)) ^ 2 := by
      intro i
      have h1 : |Real.arctan (s i)| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
          le_of_lt (Real.arctan_lt_pi_div_two _)⟩
      have h2 : |c * Real.arctan (s i)| ≤ c * (Real.pi / 2) := by
        rw [abs_mul, abs_of_nonneg hcpos.le]
        exact mul_le_mul_of_nonneg_left h1 hcpos.le
      have h3 : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          = (c * Real.arctan (s i)) ^ 2 := by
        simp only [Real.norm_eq_abs]
        rw [sq_abs]
      rw [h3]
      calc (c * Real.arctan (s i)) ^ 2 = |c * Real.arctan (s i)| ^ 2 := by rw [sq_abs]
        _ ≤ (c * (Real.pi / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hsq : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s‖ ^ 2 ≤ δ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (ι := Fin m) (β := fun _ : Fin m => ℝ)]
      calc ∑ i : Fin m, ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ ∑ _i : Fin m, (c * (Real.pi / 2)) ^ 2 := Finset.sum_le_sum (fun i _ => hb i)
        _ = (m : ℝ) * (c * (Real.pi / 2)) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ δ ^ 2 := by
              rw [hc]
              have h2 : (0 : ℝ) < Real.pi * ((m : ℝ) + 1) := by positivity
              field_simp
              nlinarith [sq_nonneg ((m : ℝ) + 1), hδ]
    nlinarith [norm_nonneg ((fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s),
      hδ, hsq]
  · intro s
    have hτ : HasFDerivAt
        (fun s' : EuclideanSpace ℝ (Fin m) => fun i : Fin m => c * Real.arctan (s' i))
        (ContinuousLinearMap.pi (fun i : Fin m =>
          (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s := by
      rw [hasFDerivAt_pi]
      intro i
      have h := (Real.hasDerivAt_arctan (s i)).comp_hasFDerivAt s
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt
      have h2 : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) => c * Real.arctan (s' i))
          (c • ((1 / (1 + (s i) ^ 2)) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s :=
        (h.const_smul c).congr_of_eventuallyEq (by
          filter_upwards with x
          rfl)
      rw [smul_smul, one_div] at h2
      exact h2
    have hσ : HasFDerivAt (fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)))
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm :
          (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
          (ContinuousLinearMap.pi fun i : Fin m =>
            (c * (1 + (s i) ^ 2)⁻¹) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i)) s :=
      (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (fun i : Fin m => c * Real.arctan (s i))).comp s hτ
    rw [hσ.fderiv]
    have hdτsurj : Function.Surjective (ContinuousLinearMap.pi (fun i : Fin m =>
        (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) := by
      intro w
      refine ⟨WithLp.toLp 2 (fun i => w i / (c * (1 + (s i) ^ 2)⁻¹)), ?_⟩
      funext i
      simp only [ContinuousLinearMap.pi_apply, smul_apply, PiLp.proj_apply]
      have hne : c * (1 + (s i) ^ 2)⁻¹ ≠ 0 := by
        have h2 : 0 < 1 + (s i) ^ 2 := by positivity
        positivity
      rw [smul_eq_mul]
      field_simp
    intro w
    obtain ⟨u, hu⟩ := hdτsurj w.ofLp
    refine ⟨u, ?_⟩
    rw [ContinuousLinearMap.comp_apply, hu]
    exact WithLp.toLp_ofLp 2 w

/-! ## The kernel direction at a face -/

/-- The converse of `Work.Drive.FamBox.chartDif_face_of_kernel`: surjectivity of the meet derivative
*and* of its restriction to the coordinate hyperplane `{v | v i = 0}` produce a kernel vector of the
difference of derivatives whose `i`-th coordinate does not vanish. -/
private theorem famMeetF_exists_sigma_of_faceSurjective (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {y : Amb 4} (hy : y ∈ FamBox.chartReg p F G) (heq : F y = G y) {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (FamBox.chartDif p F G) y))
    (hface : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (FamBox.chartDif p F G) y v.1)) :
    ∃ σ : Amb 4, FamBox.Lf F G y σ = 0 ∧ σ i ≠ 0 := by
  set Φ : Amb 4 →L[ℝ] Tgt 4 := fderiv ℝ (FamBox.chartDif p F G) y with hΦ
  refine ⟨Work.Drive.cofactorVec Φ, ?_, ?_⟩
  · have hker : fderiv ℝ (FamBox.chartDif p F G) y (Work.Drive.cofactorVec Φ) = 0 := by
      rw [← hΦ]
      exact Work.Drive.cofactorVec_mem_ker Φ
    have hTeq := FamBox.fderiv_chartDif_eq_Lf p F G hF hG hy heq (Work.Drive.cofactorVec Φ)
    rw [hker] at hTeq
    have hsrc : F y ∈ (extChartAt (𝓡 4) p).source := by
      have h := hy.1
      rwa [chr, ← extChartAt_source (I := 𝓡 4) p] at h
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (F y) p (F y)) :=
      tangentCoordChange_injective (x := F y) (y := p) (z := F y)
        ⟨mem_extChartAt_source (I := 𝓡 4) (F y), hsrc⟩
    refine hinj ?_
    rw [map_zero]
    exact hTeq.symm
  · exact (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero Φ hsurj i).mp hface

end

/-! ## The main theorem -/

/-- **The genericity (*parametric Sard*) statement for a joint family of loops and chains, in the
`FamBox` (`famLoop` vs `famChain`) layout, where the *loop* also depends on the Sard parameter.**

This is the verbatim merge of the two proved sibling statements
`Work.Drive.famMeet_transHyp_of_good_family` (the difference-map surjectivity) and
`Work.Drive.famMeet_faceHyp_of_good_family` (the face data), with the one change that the loop side is
a *family* `Lf : ℝ^m → ℝ² → M` carrying the Sard parameter instead of a fixed `2`-chain `L` — which is
what the germ route of `Work.Drive.sideGerm` needs, since there both the loop's chart and the sweep's
chart are perturbed along the path.

From the smooth families `Lf` and `N` (both jointly smooth in the parameter and the box variable), the
compact `K`, the chart containment `hcontain` and the *parameter-surjectivity* hypothesis `hsurj` (the
parameter-derivative of the charted difference map is onto at every zero in `K`), produce a small
parameter `t` such that, at every meet `famLoop (Lf t) y = famChain (N t) y` with `y ∈ K`:

* the difference of the two derivatives `FamBox.Lf (famLoop (Lf t)) (famChain (N t)) y` is surjective
  (the `htrans` input of `Work.Drive.odd_ncard_famMeet_iff`);
* if `y` is on the boundary of the five-box, exactly one coordinate of `y` is on a face and no two
  coordinates are, and there is a common tangent vector `σ` (`Lf … y σ = 0`, in the kernel form) whose
  face coordinate is non-zero (the `hface` input of the same engine).

Both clauses are *already proved* in the siblings for the case where the loop side is the fixed
`L`; the proof is the same — the tube lemma, the two cut-offs, the bounded reparametrisation `sq`, and
the merged genericity statement `Work.Drive.exists_forall_good_face_and_notMem_family` — with
`famLoop L` replaced by `famLoop (Lf (sq s))` on the parameter space. -/
theorem famMeet_regular_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2))
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : M) (K : Set (Work.Drive.Amb 4)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      Work.Drive.famLoop (Lf t) y ∈ (Work.Drive.chr p).source ∧
      Work.Drive.famChain (N t) y ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      Work.Drive.FamBox.chartDif p (Work.Drive.famLoop (Lf t)) (Work.Drive.famChain (N t)) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.FamBox.chartDif p (Work.Drive.famLoop (Lf t'))
          (Work.Drive.famChain (N t')) y) t)) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε ∧
      (∀ y : Work.Drive.Amb 4, y ∈ K →
        Work.Drive.famLoop (Lf t) y = Work.Drive.famChain (N t) y →
        Function.Surjective
          (Work.Drive.FamBox.Lf (Work.Drive.famLoop (Lf t)) (Work.Drive.famChain (N t)) y)) ∧
      (∀ y : Work.Drive.Amb 4, y ∈ K →
        Work.Drive.famLoop (Lf t) y = Work.Drive.famChain (N t) y →
        y ∈ Submission.Drive.unitBox 4 →
        ¬ (∃ i j : Fin 5, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1))) ∧
      (∀ y : Work.Drive.Amb 4, y ∈ K →
        Work.Drive.famLoop (Lf t) y = Work.Drive.famChain (N t) y →
        y ∈ Submission.Drive.unitBox 4 → ∀ i : Fin 5, (y i = 0 ∨ y i = 1) →
        (∀ j : Fin 5, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) →
        ∃ σ : Work.Drive.Amb 4,
          Work.Drive.FamBox.Lf (Work.Drive.famLoop (Lf t)) (Work.Drive.famChain (N t)) y σ = 0 ∧
          σ i ≠ 0) := by
  classical
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := famMeetF_top_ne_zero_order
  -- ## Step 0: the chart containment region of the family
  have hcont1 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2) :=
    (famMeetF_contMDiff_famLoop_fam m Lf hLf).continuous
  have hcont2 : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) :=
    (famMeetF_contMDiff_famChain_fam m N hN).continuous
  have hWopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famLoop (Lf q.1) q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source} :=
    (hcont1.isOpen_preimage _ (chr p).open_source).inter
      (hcont2.isOpen_preimage _ (chr p).open_source)
  have hWsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2) ×ˢ K ⊆
      {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        famLoop (Lf q.1) q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have htlt : ‖t‖ < ε := by
      have h := Metric.mem_closedBall.mp ht
      rw [dist_zero_right] at h
      linarith
    exact hcontain t y htlt hy
  -- ## Step 1: the tube lemma separates the parameter and the space variable
  obtain ⟨U, V, hUopen, hVopen, hUsub, hVsub, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2)) hK
      hWopen hWsub
  -- ## Step 2: the two cut-off functions
  obtain ⟨γ, hγsm, hγone, hγsupp⟩ :=
    famMeetF_exists_cutoff_one_on_of_subset
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 2)) hUopen hUsub
  obtain ⟨β, hβsm, hβone, hβsupp⟩ :=
    famMeetF_exists_cutoff_one_on_of_subset hK hVopen hVsub
  -- ## Step 3: the bounded reparametrisation
  obtain ⟨sq, hsqsm, hsqbound, hsqsurj⟩ :=
    famMeetF_squeeze_map (m := m) (δ := ε / 4) (by linarith)
  -- ## Step 4: smoothness of the cut-off family and of its pull-back
  have hΦsm : ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ q.1 * β q.2) • FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) :=
    famMeetF_contDiff_cutoff m Lf hLf N hN p hγsm hβsm hUV hγsupp hβsupp
  have hΨsm : ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ (sq q.1) * β q.2) •
          FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2) := by
    have hpair : ContDiff ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => (sq q.1, q.2)) :=
      (hsqsm.comp contDiff_fst).prodMk contDiff_snd
    simpa only [Function.comp_def] using hΦsm.comp hpair
  -- ## Step 5: the parametric-Sard hypothesis of the merged theorem
  have hsurjΨ : ∀ (s : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖s‖ < ε →
      (z ∈ K ∨ ∃ i : FaceIdx4,
        z ∈ (fun l : Fdir4 i => Fbase4 i + (l : Amb 4)) '' (Fcov4 K i)) →
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ (sq q.1) * β q.2) •
          FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)
        (s, z) = 0 →
      Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin m) =>
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          (γ (sq q.1) * β q.2) •
            FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)
          (s', z)) s) := by
    intro s z _ hzdisj hzero
    have hz : z ∈ K := hzdisj.elim id (fun h => by
      obtain ⟨i, l, hl, hlz⟩ := h
      rw [← hlz]
      exact hl)
    have hsqb : ‖sq s‖ ≤ ε / 4 := hsqbound s
    have hslt : ‖sq s‖ < ε := by linarith
    have hγv : γ (sq s) = 1 :=
      hγone (sq s) (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
    have hβv : β z = 1 := hβone z hz
    have hχ0 : FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z = 0 := by
      have h : (γ (sq s) * β z) •
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z = 0 :=
        hzero
      rw [hγv, hβv, one_mul, one_smul] at h
      exact h
    have hreg : famLoop (Lf (sq s)) z ∈ (chr p).source ∧
        famChain (N (sq s)) z ∈ (chr p).source :=
      hcontain (sq s) z hslt hz
    have hχat : ContDiffAt ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) (sq s, z) :=
      famMeetF_chartDif_joint_contDiffAt m Lf hLf N hN p (sq s) hreg
    have hχp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z) (sq s)) (sq s) := by
      have h := (hχat.comp (sq s) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt htop
      exact h.hasFDerivAt
    have hγβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)) (sq s) :=
      ((hγsm.contDiffAt.mul contDiffAt_const).differentiableAt htop).hasFDerivAt
    have hsmul : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β z) • FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z)
        ((γ (sq s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z) (sq s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)).smulRight
              (FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z)) (sq s) :=
      hγβp.smul hχp
    have h1 : (γ (sq s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z) (sq s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)).smulRight
              (FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z)
          = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z) (sq s) := by
      rw [hγv, hβv, one_mul, hχ0]
      simp
    rw [h1] at hsmul
    have hchain : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) =>
        (γ (sq s') * β z) •
          FamBox.chartDif p (famLoop (Lf (sq s'))) (famChain (N (sq s'))) z)
        ((fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) z) (sq s)).comp
            (fderiv ℝ sq s)) s := by
      simpa only [Function.comp_def] using hsmul.comp s
        (((hsqsm.differentiable (htop))).differentiableAt).hasFDerivAt
    rw [hchain.fderiv]
    exact (hsurj (sq s) z hslt hz hχ0).comp (hsqsurj s)
  -- ## Step 6: the merged genericity theorem, with the two-face skeleton of `K`
  obtain ⟨s, _hsnorm, hsgood, hsface, hsavoid⟩ :=
    exists_forall_good_face_and_notMem_family m 4 K hK FaceIdx4
      (fun t : FaceIdx4 => ↥(Fdir4 t)) (fun t => Fdir4_finrank_lt t)
      (fun t : FaceIdx4 => fun l : Fdir4 t => Fbase4 t + (l : Amb 4))
      (fun t => contDiff_Fparam4 t)
      (fun t : FaceIdx4 => Fcov4 K t) (fun t => Fcov4_isCompact K hK t)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ (sq q.1) * β q.2) •
          FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)
      hΨsm ε hε hsurjΨ
  -- ## Step 7: transfer the three clauses back to the parameter `sq s`
  have hslt : ‖sq s‖ < ε := by linarith [hsqbound s]
  have hγv : γ (sq s) = 1 :=
    hγone (sq s) (by rw [Metric.mem_closedBall, dist_zero_right]; linarith [hsqbound s])
  have hΨzero : ∀ y : Amb 4, y ∈ K → famLoop (Lf (sq s)) y = famChain (N (sq s)) y →
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ (sq q.1) * β q.2) •
          FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)
        (s, y) = 0 := by
    intro y hyK heq
    have hcont : y ∈ FamBox.chartReg p (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      hcontain (sq s) y hslt hyK
    have hzy : FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0 :=
      (FamBox.chartDif_eq_zero_iff hcont).mpr heq
    show (γ (sq s) * β y) •
      FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0
    rw [hγv, hβone y hyK, one_mul, hzy, smul_zero]
  refine ⟨sq s, hslt, ?_, ?_, ?_⟩
  · -- ### the transversality clause
    intro y hyK heq
    have hcont : y ∈ FamBox.chartReg p (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      hcontain (sq s) y hslt hyK
    have hzy : FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0 :=
      (FamBox.chartDif_eq_zero_iff hcont).mpr heq
    have hΨ0 := hΨzero y hyK heq
    have hgood : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        (γ (sq s) * β z') •
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) :=
      hsgood y hyK hΨ0
    have hFcdt : ContMDiff (𝓡 5) (𝓡 4) Ctop (famLoop (Lf (sq s))) :=
      FamBox.contMDiff_famLoop (Lf (sq s)) (famMeetF_contMDiff_slice_loop m Lf hLf (sq s))
    have hGt : ContMDiff (𝓡 5) (𝓡 4) Ctop (famChain (N (sq s))) :=
      FamBox.contMDiff_famChain (N (sq s)) (famMeetF_contMDiff_slice m N hN (sq s))
    have hχat : ContDiffAt ℝ Ctop
        (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y :=
      (FamBox.contDiffOn_chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) hFcdt hGt).contDiffAt
        ((FamBox.isOpen_chartReg p (famLoop (Lf (sq s))) (famChain (N (sq s))) hFcdt.continuous
          hGt.continuous).mem_nhds hcont)
    have hχp : HasFDerivAt (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z')
        (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) y :=
      (hχat.differentiableAt htop).hasFDerivAt
    have hβp : HasFDerivAt (fun z' : Amb 4 => γ (sq s) * β z')
        (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β z') y) y :=
      ((contDiffAt_const.mul hβsm.contDiffAt).differentiableAt htop).hasFDerivAt
    have hsmul := hβp.smul hχp
    have h1 : (γ (sq s) * β y) • (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y)
        + (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β z') y).smulRight
            (FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y)
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y := by
      rw [hγv, hβone y hyK, mul_one, hzy]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun z' : Amb 4 =>
          (γ (sq s) * β z') •
            FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y := hsmul.fderiv
    have hsurjχ : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) := by
      rw [← hfd]
      exact hgood
    have heqfd : fderiv ℝ (FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s)))) y
        = (tangentCoordChange (𝓡 4) (famLoop (Lf (sq s)) y) p (famLoop (Lf (sq s)) y)).comp
            (FamBox.Lf (famLoop (Lf (sq s))) (famChain (N (sq s))) y) :=
      ContinuousLinearMap.ext fun v =>
        FamBox.fderiv_chartDif_eq_Lf p (famLoop (Lf (sq s))) (famChain (N (sq s))) hFcdt hGt
          hcont heq v
    have hsurjComp : Function.Surjective
        ((tangentCoordChange (𝓡 4) (famLoop (Lf (sq s)) y) p (famLoop (Lf (sq s)) y)).comp
          (FamBox.Lf (famLoop (Lf (sq s))) (famChain (N (sq s))) y)) := by
      rw [← heqfd]
      exact hsurjχ
    have hsrc1 : famLoop (Lf (sq s)) y ∈ (extChartAt (𝓡 4) (famLoop (Lf (sq s)) y)).source :=
      mem_extChartAt_source (I := 𝓡 4) _
    have hsrc2 : famLoop (Lf (sq s)) y ∈ (extChartAt (𝓡 4) p).source := by
      rw [extChartAt_source]
      exact hcont.1
    have hinj : Function.Injective
        (tangentCoordChange (𝓡 4) (famLoop (Lf (sq s)) y) p (famLoop (Lf (sq s)) y)) :=
      tangentCoordChange_injective (x := famLoop (Lf (sq s)) y) (y := p)
        (z := famLoop (Lf (sq s)) y) ⟨hsrc1, hsrc2⟩
    intro w
    obtain ⟨v, hv⟩ := hsurjComp (tangentCoordChange (𝓡 4) (famLoop (Lf (sq s)) y) p
      (famLoop (Lf (sq s)) y) w)
    exact ⟨v, hinj hv⟩
  · -- ### the avoidance clause: no two face coordinates
    intro y hyK heq _hybox h2
    obtain ⟨t', l, hl, hlz⟩ := Fcov4_cover K hyK h2
    have hne := hsavoid t' l hl
    have hne' : (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        (γ (sq q.1) * β q.2) •
          FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)
        (s, Fbase4 t' + (l : Amb 4)) ≠ 0 := hne
    rw [show Fbase4 t' + (l : Amb 4) = y from hlz] at hne'
    exact hne' (hΨzero y hyK heq)
  · -- ### the face clause: the crossing direction
    intro y hyK heq _hybox i hyi _hinter
    have hcont : y ∈ FamBox.chartReg p (famLoop (Lf (sq s))) (famChain (N (sq s))) :=
      hcontain (sq s) y hslt hyK
    have hzy : FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y = 0 :=
      (FamBox.chartDif_eq_zero_iff hcont).mpr heq
    have hΨ0 := hΨzero y hyK heq
    have hgood : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        (γ (sq s) * β z') •
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) :=
      hsgood y hyK hΨ0
    have hface0 : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (fun z' : Amb 4 =>
          (γ (sq s) * β z') •
            FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y v.1) :=
      hsface i y hyK hΨ0 hyi
    have hFcdt : ContMDiff (𝓡 5) (𝓡 4) Ctop (famLoop (Lf (sq s))) :=
      FamBox.contMDiff_famLoop (Lf (sq s)) (famMeetF_contMDiff_slice_loop m Lf hLf (sq s))
    have hGt : ContMDiff (𝓡 5) (𝓡 4) Ctop (famChain (N (sq s))) :=
      FamBox.contMDiff_famChain (N (sq s)) (famMeetF_contMDiff_slice m N hN (sq s))
    have hχat : ContDiffAt ℝ Ctop
        (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y :=
      (FamBox.contDiffOn_chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) hFcdt hGt).contDiffAt
        ((FamBox.isOpen_chartReg p (famLoop (Lf (sq s))) (famChain (N (sq s))) hFcdt.continuous
          hGt.continuous).mem_nhds hcont)
    have hχp : HasFDerivAt (fun z' : Amb 4 =>
        FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z')
        (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y) y :=
      (hχat.differentiableAt htop).hasFDerivAt
    have hβp : HasFDerivAt (fun z' : Amb 4 => γ (sq s) * β z')
        (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β z') y) y :=
      ((contDiffAt_const.mul hβsm.contDiffAt).differentiableAt htop).hasFDerivAt
    have hsmul := hβp.smul hχp
    have h1 : (γ (sq s) * β y) • (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y)
        + (fderiv ℝ (fun z' : Amb 4 => γ (sq s) * β z') y).smulRight
            (FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) y)
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y := by
      rw [hγv, hβone y hyK, mul_one, hzy]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun z' : Amb 4 =>
          (γ (sq s) * β z') •
            FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (famLoop (Lf (sq s))) (famChain (N (sq s))) z') y := hsmul.fderiv
    rw [hfd] at hgood hface0
    exact famMeetF_exists_sigma_of_faceSurjective p (famLoop (Lf (sq s))) (famChain (N (sq s)))
      hFcdt hGt hcont heq hgood hface0

end Work.Drive
