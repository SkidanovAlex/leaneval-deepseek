import Mathlib
import Submission.Work.Drive.sgSystem
import Submission.Work.Drive.sgPiecesDefs
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_le_mem_of_compact
import Submission.Work.Drive.range_mfderiv_comp_surjective_linear
import Submission.Work.Drive.finite_loopChainMeet_of_transverse
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sgFace_gatherCLM
import Submission.Work.Drive.gatherCLM_mem_unitBox

/-!
# The assembly of the germ route's Sard existence

This module proves `Work.Drive.sideGerm_good_exists`: for every angle `w` and every chart perturbation
family `Ξ` of a chart `Q` of the capped plane, the good configurations accumulate at `0`.

The construction is the one designed in the module docstring of `sgSystem.lean`, applied to the
*charted difference system* of the perturbed loop family against the fixed chain, on the parameter
space box with the eight boundary faces of `sgPiecesDefs.lean`:

* the loop family `Work.Drive.sgLoop Ξ Q p` (a degenerate two-parameter presentation of the core loop
  of `Ξ p ∘ Q`) against the fixed chain `Work.Drive.sgSweep0 Q c w`;
* the chart cover `Work.Drive.exists_compact_chart_cover` of the meeting values (the chain's image over
  the box), with the cut-offs of `Work.Drive.exists_cutoff_one_on_of_subset`;
* the per-chart systems `Φ i (t, z) = (γ i t * β i z) • chartDiff (pch i) (sgLoop Ξ Q t) (sgSweep0) z`,
  whose `t`-derivative is onto at every zero (`Work.Drive.hsurj_sgCutoff`, from `ChartPert`), which is
  the hypothesis of the parametric-Sard brick `Work.Drive.exists_forall_good_and_notMem_family_multi`;
* the conversions: the Sard clause at a meet gives the intrinsic transversality through
  `Work.Drive.range_sup_eq_top_of_chartDiff_surjective`, the avoidance clause at the boundary pieces
  gives the interiority, and the transversality gives the finiteness through
  `Work.Drive.finite_loopChainMeet_of_transverse`.
-/

namespace Work.Drive

open Manifold Filter Set Metric
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Small auxiliary points -/

/-- The point `(a, b)` of `ℝ²`. -/
private def sq2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]

@[simp] private lemma sq2_apply_zero (a b : ℝ) : sq2 a b 0 = a := rfl
@[simp] private lemma sq2_apply_one (a b : ℝ) : sq2 a b 1 = b := rfl

/-- The point `a` of `ℝ¹`. -/
private def mk1 (a : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => a)

@[simp] private lemma mk1_apply (a : ℝ) (i : Fin 1) : mk1 a i = a := by
  simp [mk1]

/-- **The canonical representative in `Amb 4` of a meet parameter**: the loop parameter goes to the
first coordinate, the dummy coordinate to `0`, and the three chain parameters to their block. -/
def meetPt (q : ℝ × Amb 2) : Amb 4 :=
  mkPart (sq2 q.1 0) q.2

@[simp] lemma sqPart_meetPt (q : ℝ × Amb 2) : sqPart (meetPt q) = sq2 q.1 0 := by
  rw [meetPt, ← sqPartCLM_eq_sqPart, sqPartCLM_mkPart]

@[simp] lemma cbPart_meetPt (q : ℝ × Amb 2) : cbPart (meetPt q) = q.2 := by
  rw [meetPt, ← cbPartCLM_eq_cbPart, cbPartCLM_mkPart]

@[simp] lemma sqIdx_zero : sqIdx (0 : Fin 2) = (0 : Fin 5) := rfl
@[simp] lemma sqIdx_one : sqIdx (1 : Fin 2) = (1 : Fin 5) := rfl

@[simp] lemma meetPt_apply_zero (q : ℝ × Amb 2) : meetPt q 0 = q.1 := by
  change sqPart (meetPt q) (0 : Fin 2) = q.1
  rw [sqPart_meetPt]
  rfl

@[simp] lemma meetPt_apply_one (q : ℝ × Amb 2) : meetPt q 1 = 0 := by
  change sqPart (meetPt q) (1 : Fin 2) = 0
  rw [sqPart_meetPt]
  rfl

@[simp] lemma meetPt_cbIdx (q : ℝ × Amb 2) (j : Fin 3) : meetPt q (cbIdx j) = q.2 j := by
  change cbPart (meetPt q) j = q.2 j
  rw [cbPart_meetPt]

/-- The canonical representative reads the square block through `sqIdx`. -/
lemma meetPt_sqIdx (q : ℝ × Amb 2) (i : Fin 2) : meetPt q (sqIdx i) = sq2 q.1 0 i := by
  change sqPart (meetPt q) i = sq2 q.1 0 i
  rw [sqPart_meetPt]

/-- The box membership of the canonical representative of a meet parameter. -/
lemma meetPt_mem_unitBox_of {q : ℝ × Amb 2}
    (h1 : q.1 ∈ Set.Icc (0 : ℝ) 1) (h2 : q.2 ∈ Submission.Drive.unitBox 2) :
    meetPt q ∈ Submission.Drive.unitBox 4 := by
  intro k
  fin_cases k <;> dsimp only [meetPt, sq2]
  · exact h1
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact h2 0
  · exact h2 1
  · exact h2 2

lemma meetPt_apply_two (q : ℝ × Amb 2) : meetPt q (2 : Fin 5) = q.2 0 :=
  meetPt_cbIdx q 0

lemma meetPt_apply_three (q : ℝ × Amb 2) : meetPt q (3 : Fin 5) = q.2 1 :=
  meetPt_cbIdx q 1

lemma meetPt_apply_four (q : ℝ × Amb 2) : meetPt q (4 : Fin 5) = q.2 2 :=
  meetPt_cbIdx q 2

/-- **`z ↦ cbPart z` is continuous.** -/
lemma continuous_cbPart :
    Continuous (fun z : EuclideanSpace ℝ (Fin 5) => cbPart z) := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 5) => cbPart z)
      = (fun z : EuclideanSpace ℝ (Fin 5) => cbPartCLM z) := by
    funext z
    exact (cbPartCLM_eq_cbPart z).symm
  rw [hfun]
  exact cbPartCLM.continuous

/-- **A smooth cut-off which is `1` on a compact set and supported in a prescribed open superset.** -/
lemma exists_cutoff_one_on_of_subset {n : ℕ} {K V : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ V := by
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
  · have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
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

/-- **A finite family of positive reals has a positive lower bound.** -/
lemma exists_pos_forall_fin {r : ℕ} (P : Fin r → ℝ → Prop)
    (hmono : ∀ i (ε ε' : ℝ), ε' ≤ ε → P i ε → P i ε')
    (h : ∀ i, ∃ ε : ℝ, 0 < ε ∧ P i ε) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, P i ε := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with h0 | h0
  · exact ⟨1, one_pos, fun i => (h0.false i).elim⟩
  · choose e he using h
    refine ⟨(Finset.univ.image e).min' (Finset.univ_nonempty.image e), ?_, ?_⟩
    · rw [Finset.lt_min'_iff]
      intro b hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      exact (he i).1
    · intro i
      exact hmono i _ _
        (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)) (he i).2

/-- **The rotation of the capping space by a fixed angle is a smooth self-map.** -/
theorem contMDiff_rotCapping_const (w : UnitAddCircle) :
    ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : CappingSpace => rotCapping w p) := by
  obtain ⟨t, ht⟩ := Quotient.mk''_surjective w
  intro p
  have h := Work.Drive.contMDiffAt_rotCapping_comp (I := 𝓡 4)
    (id : CappingSpace → CappingSpace) (fun _ : CappingSpace => t) p contMDiffAt_id
    contMDiffAt_const
  simpa [ht] using h
/-- **The main construction**: for every `ε₀ > 0` there is a chart perturbation of norm `< ε₀` at which
the perturbed pair is a `GoodPair`. -/
theorem sgGoodPair_of_small {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (w : UnitAddCircle) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε₀ ∧
      GoodPair (pertChart Ξ Q p) (fun z : ℂ => rotCapping w (Q z)) c := by
  classical
  -- ## 0. smoothness and continuity
  have top_ne_zero_asm : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    rw [ne_eq, ← WithTop.coe_zero]
    intro h
    exact ENat.top_ne_zero (WithTop.coe_injective h)
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q := hQ
  have hrot : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : CappingSpace => rotCapping w p) := contMDiff_rotCapping_const w
  have hQ₂sm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => rotCapping w (Q z)) := hrot.comp hQsm
  have hchainsm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sgSweep0 Q c w) :=
    contMDiff_sgSweep0 Q c w hQ
  have hcontΞ : Continuous (fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2) :=
    hΞ.2.1.continuous
  have hloopsm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (coreLoop Q) :=
    contMDiff_coreLoop hQsm
  -- ## 1. the two compact sets and the chart cover
  let S : Set CappingSpace := coreLoop Q '' Set.Icc (0 : ℝ) 1
  have hScomp : IsCompact S := isCompact_Icc.image hloopsm.continuous
  let Ab : Set CappingSpace := sgSweep0 Q c w '' Submission.Drive.unitBox 2
  have hAbcomp : IsCompact Ab := (isCompact_unitBox 2).image hchainsm.continuous
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover Ab hAbcomp
  -- ## 2. the two smallness properties
  have hone : ∀ i : Fin r, ∃ ε : ℝ, 0 < ε ∧
      ∀ (p' : EuclideanSpace ℝ (Fin m)) (x : CappingSpace),
        ‖p'‖ ≤ ε → x ∈ S → Ξ p' x ∈ C0 i → x ∈ C1 i := fun i =>
    exists_pos_norm_le_mem_of_compact Ξ hcontΞ hΞ.1 (hC0c i).isClosed (hC1c i).isClosed hScomp
      (hC0int i)
  obtain ⟨εa, hεapos, hεa⟩ :
      ∃ εa : ℝ, 0 < εa ∧ ∀ (i : Fin r) (p' : EuclideanSpace ℝ (Fin m)) (x : CappingSpace),
        ‖p'‖ ≤ εa → x ∈ S → Ξ p' x ∈ C0 i → x ∈ C1 i :=
    exists_pos_forall_fin _
      (fun i ε ε' hle h p' x hp hx hmem => h p' x (le_trans hp hle) hx hmem) hone
  have htwo : ∀ i : Fin r, ∃ ε : ℝ, 0 < ε ∧ ∀ p' : EuclideanSpace ℝ (Fin m),
      ‖p'‖ ≤ ε → Ξ p' '' C1 i ⊆ (chr (pch i)).source := by
    intro i
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × CappingSpace |
        Ξ q.1 q.2 ∈ (chr (pch i)).source} :=
      hcontΞ.isOpen_preimage _ (chr (pch i)).open_source
    have hsub : ({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ C1 i ⊆
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | Ξ q.1 q.2 ∈ (chr (pch i)).source} := by
      rintro ⟨p', x⟩ ⟨hp', hx⟩
      have hp'0 : p' = 0 := by simpa using hp'
      show Ξ p' x ∈ (chr (pch i)).source
      rw [hp'0, hΞ.1]
      exact hC1sub i hx
    obtain ⟨U, V, hUo, hVo, hU0, hVC1, hUV⟩ :=
      generalized_tube_lemma isCompact_singleton (hC1c i) hopen hsub
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hUo 0 (by simpa using hU0)
    refine ⟨ε / 2, by linarith, fun p' hp' x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hpU : p' ∈ U := hεsub (by rw [Metric.mem_ball, dist_zero_right]; linarith)
    have hpair : (p', y) ∈ U ×ˢ V := ⟨hpU, hVC1 hy⟩
    exact hUV hpair
  obtain ⟨εb, hεbpos, hεb⟩ : ∃ εb : ℝ, 0 < εb ∧
      ∀ (i : Fin r) (p' : EuclideanSpace ℝ (Fin m)),
        ‖p'‖ ≤ εb → Ξ p' '' C1 i ⊆ (chr (pch i)).source :=
    exists_pos_forall_fin _
      (fun i ε ε' hle h p' hp => h p' (le_trans hp hle)) htwo
  -- ## 3. the radii
  set ε₁ : ℝ := min εa εb with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min hεapos hεbpos
  have hε₁a : ε₁ ≤ εa := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : ε₁ ≤ εb := by rw [hε₁def]; exact min_le_right _ _
  set εc : ℝ := min ε₀ ε₁ with hεcdef
  have hεcpos : 0 < εc := by rw [hεcdef]; exact lt_min hε₀ hε₁pos
  have hεc₀ : εc ≤ ε₀ := by rw [hεcdef]; exact min_le_left _ _
  have hεc₁ : εc ≤ ε₁ := by rw [hεcdef]; exact min_le_right _ _
  have hεca : εc ≤ εa := le_trans hεc₁ hε₁a
  have hεcb : εc ≤ εb := le_trans hεc₁ hε₁b
  set εbr : ℝ := εc / 8 with hεbrdef
  set εone : ℝ := εc / 4 with hεonedef
  set εtwo : ℝ := εc / 2 with hεtwodef
  have hεbrpos : 0 < εbr := by rw [hεbrdef]; linarith
  have hbr_one : εbr < εone := by rw [hεbrdef, hεonedef]; linarith
  have hone_two : εone < εtwo := by rw [hεonedef, hεtwodef]; linarith
  have htwo_c : εtwo ≤ εc := by rw [hεtwodef]; linarith
  have htwo_b : εtwo ≤ εb := le_trans htwo_c hεcb
  have hbr₁ : εbr ≤ ε₁ := by rw [hεbrdef]; linarith
  have hbr_a : εbr ≤ εa := le_trans hbr₁ hε₁a
  have hbr_b : εbr ≤ εb := le_trans hbr₁ hε₁b
  have hbr₀ : εbr < ε₀ := by rw [hεbrdef]; linarith
  -- ## 4. the charted regions, the cut-offs and the systems
  set O1 : Fin r → Set CappingSpace := fun i => {x : CappingSpace |
    ∀ p' : EuclideanSpace ℝ (Fin m), ‖p'‖ ≤ εtwo → Ξ p' x ∈ (chr (pch i)).source} with hO1def
  have hO1open : ∀ i : Fin r, IsOpen (O1 i) := by
    intro i
    rw [hO1def]
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × CappingSpace |
        Ξ q.1 q.2 ∈ (chr (pch i)).source} :=
      hcontΞ.isOpen_preimage _ (chr (pch i)).open_source
    have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) εtwo ×ˢ ({x} : Set CappingSpace) ⊆
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | Ξ q.1 q.2 ∈ (chr (pch i)).source} := by
      rintro ⟨p', y⟩ ⟨hp', hy⟩
      have hyx : y = x := by simpa using hy
      subst hyx
      exact hx p' (by rwa [Metric.mem_closedBall, dist_zero_right] at hp')
    obtain ⟨U, V, hUo, hVo, hUc, hVx, hUV⟩ :=
      generalized_tube_lemma (isCompact_closedBall 0 εtwo) isCompact_singleton hopen hsub
    refine Filter.mem_of_superset (hVo.mem_nhds (by simpa using hVx)) ?_
    intro y hy p' hp'
    have hpU : p' ∈ U := hUc (by rw [Metric.mem_closedBall, dist_zero_right]; exact hp')
    have hpair : (p', y) ∈ U ×ˢ V := ⟨hpU, hy⟩
    exact hUV hpair
  have hC1O1 : ∀ i : Fin r, C1 i ⊆ O1 i := by
    intro i x hx
    rw [hO1def]
    exact fun p' hp' => hεb i p' (le_trans hp' htwo_b) ⟨x, hx, rfl⟩
  have hγ : ∀ _i : Fin r, ∃ γ : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
        (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) εone, γ p = 1) ∧
        tsupport γ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) εtwo := fun _ =>
    exists_cutoff_one_on_of_subset (isCompact_closedBall 0 εone) Metric.isOpen_ball (fun x hx => by
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hx
      rw [dist_zero_right] at h ⊢
      linarith)
  choose γi hγism hγione hγisupp using hγ
  let Kset : Fin r → Set (Amb 4) := fun i => {z : Amb 4 |
    z ∈ Submission.Drive.unitBox 4 ∧ coreLoop Q (z 0) ∈ C1 i ∧
      sgSweep0 Q c w (cbPart z) ∈ C1 i}
  have hKset_compact : ∀ i : Fin r, IsCompact (Kset i) := by
    intro i
    refine IsCompact.of_isClosed_subset (isCompact_unitBox 4) ?_ (fun z hz => hz.1)
    refine IsClosed.inter (isClosed_unitBox 4) (IsClosed.inter ?_ ?_)
    · exact (hC1c i).isClosed.preimage (hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous))
    · exact (hC1c i).isClosed.preimage (hchainsm.continuous.comp
        continuous_cbPart)
  let Kzero : (i : Fin r) → (Fin 4 × Fin 2) → Set (EuclideanSpace ℝ (Fin 3)) := fun i j => {y |
    y ∈ Submission.Drive.unitBox 2 ∧ coreLoop Q ((sgFace j.1 j.2 y) 0) ∈ C1 i ∧
      sgSweep0 Q c w (cbPart (sgFace j.1 j.2 y)) ∈ C1 i}
  have hKzero_compact : ∀ (i : Fin r) (j : Fin 4 × Fin 2), IsCompact (Kzero i j) := by
    intro i j
    refine IsCompact.of_isClosed_subset (isCompact_unitBox 2) ?_ (fun y hy => hy.1)
    refine IsClosed.inter (isClosed_unitBox 2) (IsClosed.inter ?_ ?_)
    · exact (hC1c i).isClosed.preimage ((hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous)).comp (continuous_sgFace j.1 j.2))
    · exact (hC1c i).isClosed.preimage ((hchainsm.continuous.comp
        continuous_cbPart).comp
        (continuous_sgFace j.1 j.2))
  let Ktilde : Fin r → Set (Amb 4) := fun i =>
    Kset i ∪ ⋃ j : Fin 4 × Fin 2, sgFace j.1 j.2 '' Kzero i j
  have hKtilde_compact : ∀ i : Fin r, IsCompact (Ktilde i) := fun i =>
    (hKset_compact i).union (isCompact_iUnion fun j => (hKzero_compact i j).image
      (continuous_sgFace j.1 j.2))
  let Vset : Fin r → Set (Amb 4) := fun i => {z : Amb 4 |
    coreLoop Q (z 0) ∈ O1 i ∧ sgSweep0 Q c w (cbPart z) ∈ (chr (pch i)).source}
  have hVset_open : ∀ i : Fin r, IsOpen (Vset i) := by
    intro i
    exact ((hO1open i).preimage (hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous))).inter
      ((chr (pch i)).open_source.preimage (hchainsm.continuous.comp
        continuous_cbPart))
  have hKtilde_sub : ∀ i : Fin r, Ktilde i ⊆ Vset i := by
    rintro i z (hz | hz)
    · exact ⟨hC1O1 i hz.2.1, hC1sub i hz.2.2⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, hy, rfl⟩ := hj
      exact ⟨hC1O1 i hy.2.1, hC1sub i hy.2.2⟩
  have hβ : ∀ i : Fin r, ∃ β : Amb 4 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      (∀ z ∈ Ktilde i, β z = 1) ∧ tsupport β ⊆ Vset i := fun i =>
    exists_cutoff_one_on_of_subset (hKtilde_compact i) (hVset_open i) (hKtilde_sub i)
  choose βi hβism hβione hβisupp using hβ
  have hUV : ∀ i : Fin r, Metric.ball (0 : EuclideanSpace ℝ (Fin m)) εtwo ×ˢ Vset i ⊆
      {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr (pch i)).source ∧
        sgSweep0 Q c w (cbPart q.2) ∈ (chr (pch i)).source} := by
    rintro i ⟨p', z⟩ ⟨hp', hz⟩
    rw [Metric.mem_ball, dist_zero_right] at hp'
    refine ⟨?_, hz.2⟩
    have hO1 : ∀ p' : EuclideanSpace ℝ (Fin m),
        ‖p'‖ ≤ εtwo → Ξ p' (coreLoop Q (z 0)) ∈ (chr (pch i)).source := by
      have h := hz.1
      rw [hO1def] at h
      exact h
    have := hO1 p' (le_of_lt hp')
    simpa [sgLoop, coreLoop] using this
  let Phi : Fin r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun i q =>
    (γi i q.1 * βi i q.2) • chartDiff (pch i) (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2
  have hΦsm : ∀ i : Fin r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Phi i) := fun i =>
    contDiff_sgCutoff_chartDiff Ξ Q c w hΞ hQ (pch i) (hγism i) (hβism i) (hUV i)
      (hγisupp i) (hβisupp i)
  have hsurjB : ∀ (i : Fin r) (p' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      ‖p'‖ < εbr → (z ∈ Kset i ∨ ∃ j : Fin 4 × Fin 2, z ∈ sgFace j.1 j.2 '' Kzero i j) →
      Phi i (p', z) = 0 →
      Function.Surjective (fderiv ℝ (fun p'' : EuclideanSpace ℝ (Fin m) => Phi i (p'', z)) p') := by
    intro i p' z hp' hz h0
    have hγ1 : γi i p' = 1 := hγione i p'
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (lt_trans hp' hbr_one))
    have hzKt : z ∈ Ktilde i := by
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_iUnion.mpr h)
    have hβ1 : βi i z = 1 := hβione i z hzKt
    have hp'ts : p' ∈ tsupport (γi i) := subset_tsupport _ (by
      show γi i p' ≠ 0
      rw [hγ1]
      norm_num)
    have hzts : z ∈ tsupport (βi i) := subset_tsupport _ (by
      show βi i z ≠ 0
      rw [hβ1]
      norm_num)
    exact hsurj_sgCutoff Ξ Q c w hΞ hQ (pch i) (hγism i) (hβism i) (hUV i) (hγisupp i)
      (hβisupp i) hp'ts hzts hγ1 hβ1 h0
  have hfin3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) < 4 := by
    rw [finrank_euclideanSpace]
    norm_num
  obtain ⟨pst, hpst, hregS, havoidS⟩ :=
    exists_forall_good_and_notMem_family_multi (m := m) (n := 4) (r := r)
      (K := Kset) (hK := hKset_compact)
      (ι := fun _ => Fin 4 × Fin 2) (X := fun _ _ => EuclideanSpace ℝ (Fin 3))
      (hX := fun _ _ => hfin3)
      (B := fun _ j => sgFace j.1 j.2) (hB := fun _ j => contDiff_sgFace j.1 j.2)
      (K₀ := Kzero) (hK₀ := hKzero_compact) (Φ := Phi) (hΦ := hΦsm)
      (ε := εbr) (hε := hεbrpos) (hsurj := hsurjB)
  -- ## 5. the conversions at the parameter `pst`
  let Q₁ : ℂ → CappingSpace := fun z => Ξ pst (Q z)
  let Q₂ : ℂ → CappingSpace := fun z => rotCapping w (Q z)
  have hQ₁sm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q₁ :=
    hΞ.2.1.comp (contMDiff_const.prodMk hQsm)
  have hloop₁sm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (coreLoop Q₁) :=
    contMDiff_coreLoop hQ₁sm
  have hpsta : ‖pst‖ ≤ εa := le_trans (le_of_lt hpst) hbr_a
  have hpstb : ‖pst‖ ≤ εb := le_trans (le_of_lt hpst) hbr_b
  -- the cut-off does not change the `z`-derivative at a zero
  have cutDeriv : ∀ (i : Fin r) (z : Amb 4), βi i z = 1 →
      (sgLoop Ξ Q pst (sqPart z) ∈ (chr (pch i)).source ∧
        sgSweep0 Q c w (cbPart z) ∈ (chr (pch i)).source) →
      chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z = 0 →
      Function.Surjective (fderiv ℝ (fun z' : Amb 4 => Phi i (pst, z')) z) →
      Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z) := by
    intro i z hβ1 hreg hcd0 hsurj
    have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z := by
      have h1 := contDiffAt_sgChartDiff Ξ Q c w hΞ hQ (pch i) (q₀ := (pst, z)) hreg
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z' : Amb 4 => (pst, z')) z := contDiffAt_const.prodMk contDiffAt_id
      have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z :=
        h1.comp z h2
      exact hcomp
    have hγ1 : γi i pst = 1 := hγione i pst (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_trans hpst hbr_one))
    have hcdp : HasFDerivAt (fun z' : Amb 4 =>
        chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z')
        (fderiv ℝ (fun z' : Amb 4 =>
          chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z) z :=
      (hcd.differentiableAt top_ne_zero_asm).hasFDerivAt
    have hbp : HasFDerivAt (fun z' : Amb 4 => γi i pst * βi i z')
        (fderiv ℝ (fun z' : Amb 4 => γi i pst * βi i z') z) z :=
      ((contDiffAt_const.mul (hβism i).contDiffAt).differentiableAt top_ne_zero_asm).hasFDerivAt
    have hsmul := hbp.smul hcdp
    have h1 : (γi i pst * βi i z) •
          (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z)
        + (fderiv ℝ (fun z' : Amb 4 => γi i pst * βi i z') z).smulRight
            (chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z)
        = fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z := by
      rw [hγ1, hβ1, mul_one, hcd0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun z' : Amb 4 => (γi i pst * βi i z') •
          chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z
        = fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z := hsmul.fderiv
    change Function.Surjective (fderiv ℝ (fun z' : Amb 4 => (γi i pst * βi i z') •
      chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') z) at hsurj
    rw [hfd] at hsurj
    exact hsurj
  -- ### 5a. the data of a meet
  have hmeetdata : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂), ∃ i : Fin r,
      sgSweep0 Q c w q.2 ∈ C0 i ∧ meetPt q ∈ Kset i ∧
        coreLoop Q (q.1) ∈ C1 i ∧ sgSweep0 Q c w (cbPart (meetPt q)) ∈ C1 i ∧
        Phi i (pst, meetPt q) = 0 := by
    rintro q ⟨hq1, hq2, hmeet⟩
    have hv : sgSweep0 Q c w q.2 ∈ Ab := ⟨q.2, hq2, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
    have hzw : sgLoop Ξ Q pst (sqPart (meetPt q)) = sgSweep0 Q c w q.2 := by
      have h1 : sgLoop Ξ Q pst (sqPart (meetPt q)) = coreLoop Q₁ q.1 := by
        simp [sgLoop, coreLoop, Q₁, meetPt_apply_zero]
      rw [h1]
      exact hmeet
    have hc1 : coreLoop Q (q.1) ∈ C1 i := by
      refine hεa i pst (coreLoop Q q.1) hpsta ⟨q.1, hq1, rfl⟩ ?_
      have h2 : Ξ pst (coreLoop Q q.1) = sgSweep0 Q c w q.2 := by
        have h3 : Ξ pst (coreLoop Q q.1) = coreLoop Q₁ q.1 := rfl
        rw [h3]
        exact hmeet
      rw [h2]
      exact hi
    have hz : meetPt q ∈ Kset i := by
      refine ⟨meetPt_mem_unitBox_of hq1 hq2, ?_, ?_⟩
      · show coreLoop Q ((meetPt q) 0) ∈ C1 i
        rwa [meetPt_apply_zero]
      · show sgSweep0 Q c w (cbPart (meetPt q)) ∈ C1 i
        rw [cbPart_meetPt]
        exact interior_subset (hC0int i hi)
    have hsrc1 : sgLoop Ξ Q pst (sqPart (meetPt q)) ∈ (chr (pch i)).source := by
      have h := hεb i pst hpstb ⟨coreLoop Q (q.1), hc1, rfl⟩
      simpa [sgLoop, coreLoop, meetPt_apply_zero] using h
    have hsrc2 : sgSweep0 Q c w (cbPart (meetPt q)) ∈ (chr (pch i)).source :=
      hC1sub i (by rw [cbPart_meetPt]; exact interior_subset (hC0int i hi))
    have heq : sgLoop Ξ Q pst (sqPart (meetPt q)) = sgSweep0 Q c w (cbPart (meetPt q)) := by
      rw [cbPart_meetPt]
      exact hzw
    have hcd0 : chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) (meetPt q) = 0 :=
      (chartDiff_eq_zero_iff ⟨hsrc1, hsrc2⟩).mpr heq
    have hγ1 : γi i pst = 1 := hγione i pst (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_trans hpst hbr_one))
    have hβ1 : βi i (meetPt q) = 1 := hβione i (meetPt q) (Or.inl hz)
    exact ⟨i, hi, hz, hc1, by simpa [cbPart_meetPt] using interior_subset (hC0int i hi),
      by show (γi i pst * βi i (meetPt q)) • chartDiff (pch i) (sgLoop Ξ Q pst)
            (sgSweep0 Q c w) (meetPt q) = 0
         rw [hγ1, hβ1, mul_one, hcd0, smul_zero]⟩
  -- ### 5b. the transversality
  have hTrans : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
          (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) q.2).toLinearMap = ⊤ := by
    rintro q hq
    obtain ⟨hq1, hq2, hmeet⟩ := hq
    obtain ⟨i, hiC0, hzK, hc1, hcz, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
    have hsrc1 : sgLoop Ξ Q pst (sqPart (meetPt q)) ∈ (chr (pch i)).source := by
      have h := hεb i pst hpstb ⟨coreLoop Q (q.1), hc1, rfl⟩
      simpa [sgLoop, coreLoop, meetPt_apply_zero] using h
    have hsrc2 : sgSweep0 Q c w (cbPart (meetPt q)) ∈ (chr (pch i)).source := hC1sub i hcz
    have heq : sgLoop Ξ Q pst (sqPart (meetPt q)) = sgSweep0 Q c w (cbPart (meetPt q)) := by
      rw [cbPart_meetPt]
      have h1 : sgLoop Ξ Q pst (sqPart (meetPt q)) = coreLoop Q₁ q.1 := by
        simp [sgLoop, coreLoop, Q₁, meetPt_apply_zero]
      rw [h1]
      exact hmeet
    have hcd0 : chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) (meetPt q) = 0 :=
      (chartDiff_eq_zero_iff ⟨hsrc1, hsrc2⟩).mpr heq
    have hzderiv : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        chartDiff (pch i) (sgLoop Ξ Q pst) (sgSweep0 Q c w) z') (meetPt q)) :=
      cutDeriv i (meetPt q) (hβione i (meetPt q) (Or.inl hzK)) ⟨hsrc1, hsrc2⟩
        hcd0 (hregS i (meetPt q) hzK hPhi0)
    have hbridge := range_sup_eq_top_of_chartDiff_surjective (pch i) (sgLoop Ξ Q pst)
      (sgSweep0 Q c w) (contMDiff_sgLoop_fixed Ξ Q hΞ hQ pst) hchainsm ⟨hsrc1, hsrc2⟩ heq hzderiv
    have hconv : LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (sgLoop Ξ Q pst)
        (sqPart (meetPt q))).toLinearMap
        = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap := by
      have h := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) (fun a => ⟨sq2 a 0, by simp [PiLp.proj_apply]⟩)
        (sqPart (meetPt q))
      have h3 : (fun x : EuclideanSpace ℝ (Fin 2) =>
            coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) x)) = sgLoop Ξ Q pst := by
        funext x
        simp [sgLoop, coreLoop, Q₁, PiLp.proj_apply]
      rw [h3] at h
      have h2 : (sqPart (meetPt q)) 0 = q.1 := by rw [sqPart_meetPt]; rfl
      rw [PiLp.proj_apply, h2] at h
      exact h
    rw [hconv, cbPart_meetPt] at hbridge
    rw [show (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) = sgSweep0 Q c w from rfl]
    exact hbridge
  -- ### 5c. the finiteness
  have hFin : (coreMeet Q₁ c (diskPlane Q₂)).Finite := by
    let L : EuclideanSpace ℝ (Fin 1) → CappingSpace :=
      fun x => coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) x)
    have hLsm : ContMDiff (𝓡 1) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L :=
      hloop₁sm.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contMDiff
    have htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 → L u = sgSweep0 Q c w x →
        LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (sgSweep0 Q c w) x).toLinearMap = ⊤ := by
      intro u x hu hx heq
      have huI : (u 0) ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Submission.Drive.unitBox] using hu
      have hq : (u 0, x) ∈ coreMeet Q₁ c (diskPlane Q₂) := ⟨huI, hx, by
        have h1 : L u = coreLoop Q₁ (u 0) := by simp [L, PiLp.proj_apply]
        rw [← h1]
        exact heq⟩
      have h : LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) (u 0)).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) x).toLinearMap = ⊤ :=
        hTrans (u 0, x) hq
      have hconv : LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap
          = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) (u 0)).toLinearMap := by
        have hh := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) (fun a => ⟨mk1 a, by simp [mk1]⟩) u
        have h2 : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) u = u 0 := rfl
        rw [h2] at hh
        exact hh
      rw [← hconv] at h
      exact h
    have hfin1 := finite_loopChainMeet_of_transverse L (sgSweep0 Q c w) hLsm hchainsm htrans
    have himg : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        (p.1 0, p.2)) '' {p | p.1 ∈ Submission.Drive.unitBox 0 ∧
          p.2 ∈ Submission.Drive.unitBox 2 ∧ L p.1 = sgSweep0 Q c w p.2} =
        coreMeet Q₁ c (diskPlane Q₂) := by
      ext q
      constructor
      · rintro ⟨p, ⟨hp1, hp2, hpm⟩, rfl⟩
        exact ⟨by simpa [Submission.Drive.unitBox] using hp1, hp2, hpm⟩
      · rintro ⟨hq1, hq2, hqm⟩
        refine ⟨(mk1 q.1, q.2), ⟨?_, hq2, ?_⟩, ?_⟩
        · have hp1 : (mk1 q.1 : EuclideanSpace ℝ (Fin 1)) ∈ Submission.Drive.unitBox 0 := by
            simpa [Submission.Drive.unitBox, mk1] using hq1
          exact hp1
        · have h1 : L (mk1 q.1) = coreLoop Q₁ q.1 := by simp [L, mk1]
          rw [h1]
          exact hqm
        · simp [mk1]
    rw [← himg]
    exact hfin1.image _
  -- ### 5d. the interiority
  have hInt : ∀ q ∈ coreMeet Q₁ c (diskPlane Q₂),
      q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ j : Fin 3, q.2 j ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro q ⟨hq1, hq2, hmeet⟩
    obtain ⟨i, hiC0, hzK, hc1, hcz, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
    have hzbox : ∀ k : Fin 5, k ≠ 1 → meetPt q k ∈ Set.Icc (0 : ℝ) 1 :=
      fun k _ => meetPt_mem_unitBox_of hq1 hq2 k
    have hcontra : ∀ (k : Fin 4) (t : Fin 2), (t : ℝ) = meetPt q (boxIdx k) → False := by
      intro k t ht
      have hybox : gatherCLM k (meetPt q) ∈ Submission.Drive.unitBox 2 :=
        gatherCLM_mem_unitBox (k := k) hzbox
      have hyK : gatherCLM k (meetPt q) ∈ Kzero i (k, t) := by
        refine ⟨hybox, ?_, ?_⟩
        · rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht]; exact hc1
        · rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht]; exact hcz
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
  -- ## 6. the `GoodPair`
  exact ⟨pst, lt_trans hpst hbr₀, hQ₁sm, hQ₂sm, hFin, hInt, hTrans⟩

end

end Work.Drive
