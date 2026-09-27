import Mathlib
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.finite_loopChainMeet_of_transverse
import Submission.Work.Drive.range_mfderiv_comp_surjective_linear
import Submission.Work.Drive.gatherCLM_mem_unitBox
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi

/-!
# The Sard existence of the germ route at **two** truncation levels simultaneously

`Work.Drive.sideGerm_good_exists` proves that for every angle `w` and every truncation level `c > 0`
the good configurations accumulate at `0`:

`∃ᶠ t, GoodAt Ξ Q c w t`.

`Work.Drive.sideGerm_eq_of_level_lt` (the level-independence of the germ value, in
`Submission/Work/Drive/germLevelBridge.lean`) needs the *joint* statement: good configurations for the
two levels `c`, `c'` accumulate **at the same parameters**, i.e.

`∃ᶠ t, GoodAt Ξ Q c w t ∧ GoodAt Ξ Q c' w t`.

This module proves that (`sideGerm_good_exists_two_levels`, the requested lemma) by running the
parametric-Sard / avoidance machinery of `sgAssembly.lean` over the *doubled* finite index
`Fin 2 × Fin r` (level, chart of the cover of the union of the two sweeps' images), and then reading
off the two `GoodPair` conclusions at the single parameter produced.  The only new ingredient on top
of `sgAssembly.lean` is the index-type generalisation of the merged Sard brick
(`exists_forall_good_and_notMem_family_multi_ι`), obtained from
`Work.Drive.exists_forall_good_and_notMem_family_multi` by reindexing along `Fintype.equivFin`.
-/

namespace Work.Drive

open Manifold Filter Set Metric
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000

noncomputable section

/-! ## The merged Sard brick with an arbitrary finite index type

This is `Work.Drive.exists_forall_good_and_notMem_family_multi` with the index type `Fin r` replaced by
an arbitrary finite type `ι` (and the avoidance index type and the boundary parametrisations constant
along `ι`).  It is obtained from the original by reindexing along `Fintype.equivFin ι`. -/

theorem exists_forall_good_and_notMem_family_multi_ι {m n : ℕ} {ι ρ : Type*}
    [Fintype ι] [Fintype ρ]
    (K : ι → Set (Work.Drive.Amb n)) (hK : ∀ i, IsCompact (K i))
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (hX : Module.finrank ℝ X < n)
    (B : ρ → X → Work.Drive.Amb n) (hB : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B j))
    (K₀ : ι → ρ → Set X) (hK₀ : ∀ i j, IsCompact (K₀ i j))
    (Φ : ι → EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ i))
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (i : ι) (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n), ‖p‖ < ε →
      (z ∈ K i ∨ ∃ j : ρ, z ∈ B j '' K₀ i j) → Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ (i : ι) (z : Work.Drive.Amb n), z ∈ K i → Φ i (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z)) ∧
      (∀ (i : ι) (j : ρ), ∀ y ∈ K₀ i j, Φ i (p, B j y) ≠ 0) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨p, hp, h1, h2⟩ :=
    exists_forall_good_and_notMem_family_multi (m := m) (n := n) (r := Fintype.card ι)
      (K := fun i => K (e.symm i)) (hK := fun i => hK _)
      (ι := fun _ : Fin (Fintype.card ι) => ρ) (X := fun _ _ => X)
      (hX := fun _ _ => hX)
      (B := fun _ (j : ρ) => B j) (hB := fun _ j => hB j)
      (K₀ := fun i j => K₀ (e.symm i) j) (hK₀ := fun i j => hK₀ _ _)
      (Φ := fun i => Φ (e.symm i)) (hΦ := fun i => hΦ _)
      (ε := ε) (hε := hε)
      (hsurj := fun i p z hp hz h0 => hsurj (e.symm i) p z hp hz h0)
  refine ⟨p, hp, ?_, ?_⟩
  · intro i z hz h0
    have h := h1 (e i)
    simp only [e.symm_apply_apply] at h
    exact h z hz h0
  · intro i j y hy
    have h := h2 (e i) j
    simp only [e.symm_apply_apply] at h
    exact h y hy

/-! ## The one-dimensional parametrisation of the loop -/

/-- The constant map `ℝ → ℝ¹`. -/
private def ln1 (a : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => a)

@[simp] private lemma ln1_apply (a : ℝ) (i : Fin 1) : ln1 a i = a := rfl

/-- The point `(a, b)` of `ℝ²`. -/
private def sq2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]

@[simp] private lemma sq2_apply_zero (a b : ℝ) : sq2 a b 0 = a := rfl

/-! ## The two-level Sard existence -/

/-- **The two-level version of `Work.Drive.sgGoodPair_of_small`**: for every `ε₀ > 0` there is a single
perturbation parameter `p` of norm `< ε₀` at which *both* levels `c` and `c'` give a `GoodPair`.

The proof is the assembly of `sgAssembly.lean` run over the doubled index `Fin 2 × Fin r` of levels and
charts of a certified compact chart cover of the union of the two sweeps' images. -/
theorem sgGoodPair_of_small_two_levels {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c c' : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (w : UnitAddCircle) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε₀ ∧
      GoodPair (pertChart Ξ Q p) (fun z : ℂ => rotCapping w (Q z)) c ∧
      GoodPair (pertChart Ξ Q p) (fun z : ℂ => rotCapping w (Q z)) c' := by
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
  have hcontΞ : Continuous (fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2) :=
    hΞ.2.1.continuous
  have hloopsm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (coreLoop Q) :=
    contMDiff_coreLoop hQsm
  -- ## 0bis. the two levels
  let lv : Fin 2 → ℝ := Fin.cases c (fun _ : Fin 1 => c')
  have hlv0 : lv 0 = c := rfl
  have hlv1 : lv 1 = c' := rfl
  have hchainsm : ∀ k : Fin 2, ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (sgSweep0 Q (lv k) w) := fun k => contMDiff_sgSweep0 Q (lv k) w hQ
  -- ## 1. the compact sets and the chart cover (of the union of the two sweeps' images)
  let S : Set CappingSpace := coreLoop Q '' Set.Icc (0 : ℝ) 1
  have hScomp : IsCompact S := isCompact_Icc.image hloopsm.continuous
  let AbU : Set CappingSpace := ⋃ k : Fin 2, sgSweep0 Q (lv k) w '' Submission.Drive.unitBox 2
  have hAbUcomp : IsCompact AbU :=
    isCompact_iUnion fun k => (isCompact_unitBox 2).image (hchainsm k).continuous
  have hmemAbU : ∀ (k : Fin 2) (x : EuclideanSpace ℝ (Fin 3)),
      x ∈ Submission.Drive.unitBox 2 → sgSweep0 Q (lv k) w x ∈ AbU :=
    fun k x hx => Set.mem_iUnion.mpr ⟨k, x, hx, rfl⟩
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover AbU hAbUcomp
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
  let KsetOf : Fin 2 → Fin r → Set (Amb 4) := fun k i => {z : Amb 4 |
    z ∈ Submission.Drive.unitBox 4 ∧ coreLoop Q (z 0) ∈ C1 i ∧
      sgSweep0 Q (lv k) w (cbPart z) ∈ C1 i}
  have hKsetOf_compact : ∀ (k : Fin 2) (i : Fin r), IsCompact (KsetOf k i) := by
    intro k i
    refine IsCompact.of_isClosed_subset (isCompact_unitBox 4) ?_ (fun z hz => hz.1)
    refine IsClosed.inter (isClosed_unitBox 4) (IsClosed.inter ?_ ?_)
    · exact (hC1c i).isClosed.preimage (hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous))
    · exact (hC1c i).isClosed.preimage ((hchainsm k).continuous.comp continuous_cbPart)
  let KzeroOf : Fin 2 → Fin r → (Fin 4 × Fin 2) → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun k i j => {y | y ∈ Submission.Drive.unitBox 2 ∧
      coreLoop Q ((sgFace j.1 j.2 y) 0) ∈ C1 i ∧
      sgSweep0 Q (lv k) w (cbPart (sgFace j.1 j.2 y)) ∈ C1 i}
  have hKzeroOf_compact : ∀ (k : Fin 2) (i : Fin r) (j : Fin 4 × Fin 2),
      IsCompact (KzeroOf k i j) := by
    intro k i j
    refine IsCompact.of_isClosed_subset (isCompact_unitBox 2) ?_ (fun y hy => hy.1)
    refine IsClosed.inter (isClosed_unitBox 2) (IsClosed.inter ?_ ?_)
    · exact (hC1c i).isClosed.preimage ((hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous)).comp
          (continuous_sgFace j.1 j.2))
    · exact (hC1c i).isClosed.preimage (((hchainsm k).continuous.comp
        continuous_cbPart).comp (continuous_sgFace j.1 j.2))
  let KtildeOf : Fin 2 → Fin r → Set (Amb 4) := fun k i =>
    KsetOf k i ∪ ⋃ j : Fin 4 × Fin 2, sgFace j.1 j.2 '' KzeroOf k i j
  have hKtildeOf_compact : ∀ (k : Fin 2) (i : Fin r), IsCompact (KtildeOf k i) := fun k i =>
    (hKsetOf_compact k i).union (isCompact_iUnion fun j =>
      (hKzeroOf_compact k i j).image (continuous_sgFace j.1 j.2))
  let VsetOf : Fin 2 → Fin r → Set (Amb 4) := fun k i => {z : Amb 4 |
    coreLoop Q (z 0) ∈ O1 i ∧ sgSweep0 Q (lv k) w (cbPart z) ∈ (chr (pch i)).source}
  have hVsetOf_open : ∀ (k : Fin 2) (i : Fin r), IsOpen (VsetOf k i) := by
    intro k i
    exact ((hO1open i).preimage (hloopsm.continuous.comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous))).inter
      ((chr (pch i)).open_source.preimage ((hchainsm k).continuous.comp continuous_cbPart))
  have hKtildeOf_sub : ∀ (k : Fin 2) (i : Fin r), KtildeOf k i ⊆ VsetOf k i := by
    rintro k i z (hz | hz)
    · exact ⟨hC1O1 i hz.2.1, hC1sub i hz.2.2⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, hy, rfl⟩ := hj
      exact ⟨hC1O1 i hy.2.1, hC1sub i hy.2.2⟩
  have hβ : ∀ (k : Fin 2) (i : Fin r), ∃ β : Amb 4 → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      (∀ z ∈ KtildeOf k i, β z = 1) ∧ tsupport β ⊆ VsetOf k i := fun k i =>
    exists_cutoff_one_on_of_subset (hKtildeOf_compact k i) (hVsetOf_open k i) (hKtildeOf_sub k i)
  choose βi hβism hβione hβisupp using hβ
  have hUV : ∀ (k : Fin 2) (i : Fin r),
      Metric.ball (0 : EuclideanSpace ℝ (Fin m)) εtwo ×ˢ VsetOf k i ⊆
      {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr (pch i)).source ∧
        sgSweep0 Q (lv k) w (cbPart q.2) ∈ (chr (pch i)).source} := by
    rintro k i ⟨p', z⟩ ⟨hp', hz⟩
    rw [Metric.mem_ball, dist_zero_right] at hp'
    refine ⟨?_, hz.2⟩
    have hO1' : ∀ p' : EuclideanSpace ℝ (Fin m),
        ‖p'‖ ≤ εtwo → Ξ p' (coreLoop Q (z 0)) ∈ (chr (pch i)).source := by
      have h := hz.1
      rw [hO1def] at h
      exact h
    have := hO1' p' (le_of_lt hp')
    simpa [sgLoop, coreLoop] using this
  let Phi : Fin 2 → Fin r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun k i q =>
    (γi i q.1 * βi k i q.2) • chartDiff (pch i) (sgLoop Ξ Q q.1) (sgSweep0 Q (lv k) w) q.2
  have hΦsm : ∀ (k : Fin 2) (i : Fin r), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Phi k i) :=
    fun k i => contDiff_sgCutoff_chartDiff Ξ Q (lv k) w hΞ hQ (pch i) (hγism i) (hβism k i)
      (hUV k i) (hγisupp i) (hβisupp k i)
  have hsurjB : ∀ (k : Fin 2) (i : Fin r) (p' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      ‖p'‖ < εbr → (z ∈ KsetOf k i ∨ ∃ j : Fin 4 × Fin 2,
        z ∈ sgFace j.1 j.2 '' KzeroOf k i j) →
      Phi k i (p', z) = 0 →
      Function.Surjective (fderiv ℝ (fun p'' : EuclideanSpace ℝ (Fin m) => Phi k i (p'', z)) p') := by
    intro k i p' z hp' hz h0
    have hγ1 : γi i p' = 1 := hγione i p'
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (lt_trans hp' hbr_one))
    have hzKt : z ∈ KtildeOf k i := by
      rcases hz with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_iUnion.mpr h)
    have hβ1 : βi k i z = 1 := hβione k i z hzKt
    have hp'ts : p' ∈ tsupport (γi i) := subset_tsupport _ (by
      show γi i p' ≠ 0
      rw [hγ1]
      norm_num)
    have hzts : z ∈ tsupport (βi k i) := subset_tsupport _ (by
      show βi k i z ≠ 0
      rw [hβ1]
      norm_num)
    exact hsurj_sgCutoff Ξ Q (lv k) w hΞ hQ (pch i) (hγism i) (hβism k i) (hUV k i)
      (hγisupp i) (hβisupp k i) hp'ts hzts hγ1 hβ1 h0
  -- ## 4bis. the parametric-Sard / avoidance machinery over the doubled index
  have hfin3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) < 4 := by
    rw [finrank_euclideanSpace]
    norm_num
  obtain ⟨p, hpst, hreg, havoid⟩ :=
    exists_forall_good_and_notMem_family_multi_ι (m := m) (n := 4)
      (ι := Fin 2 × Fin r) (ρ := Fin 4 × Fin 2)
      (K := fun q : Fin 2 × Fin r => KsetOf q.1 q.2)
      (hK := fun q => hKsetOf_compact q.1 q.2)
      (X := EuclideanSpace ℝ (Fin 3)) (hX := hfin3)
      (B := fun j : Fin 4 × Fin 2 => sgFace j.1 j.2)
      (hB := fun j => contDiff_sgFace j.1 j.2)
      (K₀ := fun q j => KzeroOf q.1 q.2 j)
      (hK₀ := fun q j => hKzeroOf_compact q.1 q.2 j)
      (Φ := fun q : Fin 2 × Fin r => Phi q.1 q.2)
      (hΦ := fun q => hΦsm q.1 q.2)
      (ε := εbr) (hε := hεbrpos)
      (hsurj := fun q p' z hp' hz h0 => hsurjB q.1 q.2 p' z hp' hz h0)
  -- ## 5. the conversion, at each level
  have conv : ∀ k : Fin 2, GoodPair (pertChart Ξ Q p)
      (fun z : ℂ => rotCapping w (Q z)) (lv k) := by
    intro k
    have hpsta : ‖p‖ ≤ εa := le_trans (le_of_lt hpst) hbr_a
    have hpstb : ‖p‖ ≤ εb := le_trans (le_of_lt hpst) hbr_b
    have hchainsmk : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (sgSweep0 Q (lv k) w) := hchainsm k
    let Q₁ : ℂ → CappingSpace := fun z => Ξ p (Q z)
    let Q₂ : ℂ → CappingSpace := fun z => rotCapping w (Q z)
    have hQ₁sm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q₁ :=
      hΞ.2.1.comp (contMDiff_const.prodMk hQsm)
    have hloop₁sm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (coreLoop Q₁) :=
      contMDiff_coreLoop hQ₁sm
    -- ### 5a. the data of a meet
    have hmeetdata : ∀ q ∈ coreMeet Q₁ (lv k) (diskPlane Q₂), ∃ i : Fin r,
        sgSweep0 Q (lv k) w q.2 ∈ C0 i ∧ meetPt q ∈ KsetOf k i ∧
          coreLoop Q (q.1) ∈ C1 i ∧ sgSweep0 Q (lv k) w (cbPart (meetPt q)) ∈ C1 i ∧
          Phi k i (p, meetPt q) = 0 := by
      rintro q ⟨hq1, hq2, hmeet⟩
      have hv : sgSweep0 Q (lv k) w q.2 ∈ AbU := hmemAbU k q.2 hq2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
      have hzw : sgLoop Ξ Q p (sqPart (meetPt q)) = sgSweep0 Q (lv k) w q.2 := by
        have h1 : sgLoop Ξ Q p (sqPart (meetPt q)) = coreLoop Q₁ q.1 := by
          simp [sgLoop, coreLoop, Q₁, meetPt_apply_zero]
        rw [h1]
        exact hmeet
      have hc1 : coreLoop Q (q.1) ∈ C1 i := by
        refine hεa i p (coreLoop Q q.1) hpsta ⟨q.1, hq1, rfl⟩ ?_
        have h2 : Ξ p (coreLoop Q q.1) = sgSweep0 Q (lv k) w q.2 := by
          have h3 : Ξ p (coreLoop Q q.1) = coreLoop Q₁ q.1 := rfl
          rw [h3]
          exact hmeet
        rw [h2]
        exact hi
      have hz : meetPt q ∈ KsetOf k i := by
        refine ⟨meetPt_mem_unitBox_of hq1 hq2, ?_, ?_⟩
        · show coreLoop Q ((meetPt q) 0) ∈ C1 i
          rwa [meetPt_apply_zero]
        · show sgSweep0 Q (lv k) w (cbPart (meetPt q)) ∈ C1 i
          rw [cbPart_meetPt]
          exact interior_subset (hC0int i hi)
      have hsrc1 : sgLoop Ξ Q p (sqPart (meetPt q)) ∈ (chr (pch i)).source := by
        have h := hεb i p hpstb ⟨coreLoop Q (q.1), hc1, rfl⟩
        simpa [sgLoop, coreLoop, meetPt_apply_zero] using h
      have hsrc2 : sgSweep0 Q (lv k) w (cbPart (meetPt q)) ∈ (chr (pch i)).source :=
        hC1sub i (by rw [cbPart_meetPt]; exact interior_subset (hC0int i hi))
      have heq : sgLoop Ξ Q p (sqPart (meetPt q)) = sgSweep0 Q (lv k) w (cbPart (meetPt q)) := by
        rw [cbPart_meetPt]
        exact hzw
      have hcd0 : chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) (meetPt q) = 0 :=
        (chartDiff_eq_zero_iff ⟨hsrc1, hsrc2⟩).mpr heq
      have hγ1 : γi i p = 1 := hγione i p (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt (lt_trans hpst hbr_one))
      have hβ1 : βi k i (meetPt q) = 1 := hβione k i (meetPt q) (Or.inl hz)
      exact ⟨i, hi, hz, hc1, by simpa [cbPart_meetPt] using interior_subset (hC0int i hi),
        by show (γi i p * βi k i (meetPt q)) • chartDiff (pch i) (sgLoop Ξ Q p)
              (sgSweep0 Q (lv k) w) (meetPt q) = 0
           rw [hγ1, hβ1, mul_one, hcd0, smul_zero]⟩
    -- ### 5b. the cut-off does not change the `z`-derivative at a zero
    have cutDeriv : ∀ (i : Fin r) (z : Amb 4), βi k i z = 1 →
        (sgLoop Ξ Q p (sqPart z) ∈ (chr (pch i)).source ∧
          sgSweep0 Q (lv k) w (cbPart z) ∈ (chr (pch i)).source) →
        chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Amb 4 => Phi k i (p, z')) z) →
        Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
          chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z) := by
      intro i z hβ1 hreg' hcd0 hsurj
      have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z := by
        have h1 := contDiffAt_sgChartDiff Ξ Q (lv k) w hΞ hQ (pch i) (q₀ := (p, z)) hreg'
        have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z' : Amb 4 => (p, z')) z := contDiffAt_const.prodMk contDiffAt_id
        have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z' : Amb 4 => chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z :=
          h1.comp z h2
        exact hcomp
      have hγ1 : γi i p = 1 := hγione i p (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt (lt_trans hpst hbr_one))
      have hcdp : HasFDerivAt (fun z' : Amb 4 =>
          chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z')
          (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z) z :=
        (hcd.differentiableAt top_ne_zero_asm).hasFDerivAt
      have hbp : HasFDerivAt (fun z' : Amb 4 => γi i p * βi k i z')
          (fderiv ℝ (fun z' : Amb 4 => γi i p * βi k i z') z) z :=
        ((contDiffAt_const.mul (hβism k i).contDiffAt).differentiableAt top_ne_zero_asm).hasFDerivAt
      have hsmul := hbp.smul hcdp
      have h1 : (γi i p * βi k i z) •
            (fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z)
          + (fderiv ℝ (fun z' : Amb 4 => γi i p * βi k i z') z).smulRight
              (chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z)
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z := by
        rw [hγ1, hβ1, mul_one, hcd0]
        simp
      rw [h1] at hsmul
      have hfd : fderiv ℝ (fun z' : Amb 4 => (γi i p * βi k i z') •
            chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z := hsmul.fderiv
      change Function.Surjective (fderiv ℝ (fun z' : Amb 4 => (γi i p * βi k i z') •
        chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') z) at hsurj
      rw [hfd] at hsurj
      exact hsurj
    -- ### 5c. the transversality
    have hTrans : ∀ q ∈ coreMeet Q₁ (lv k) (diskPlane Q₂),
        LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep (lv k) (fun t => 1 - t) (diskPlane Q₂)) q.2).toLinearMap = ⊤ := by
      rintro q hq
      obtain ⟨hq1, hq2, hmeet⟩ := hq
      obtain ⟨i, hiC0, hzK, hc1, hcz, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
      have hsrc1 : sgLoop Ξ Q p (sqPart (meetPt q)) ∈ (chr (pch i)).source := by
        have h := hεb i p hpstb ⟨coreLoop Q (q.1), hc1, rfl⟩
        simpa [sgLoop, coreLoop, meetPt_apply_zero] using h
      have hsrc2 : sgSweep0 Q (lv k) w (cbPart (meetPt q)) ∈ (chr (pch i)).source := hC1sub i hcz
      have heq : sgLoop Ξ Q p (sqPart (meetPt q)) = sgSweep0 Q (lv k) w (cbPart (meetPt q)) := by
        rw [cbPart_meetPt]
        have h1 : sgLoop Ξ Q p (sqPart (meetPt q)) = coreLoop Q₁ q.1 := by
          simp [sgLoop, coreLoop, Q₁, meetPt_apply_zero]
        rw [h1]
        exact hmeet
      have hcd0 : chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) (meetPt q) = 0 :=
        (chartDiff_eq_zero_iff ⟨hsrc1, hsrc2⟩).mpr heq
      have hzderiv : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
          chartDiff (pch i) (sgLoop Ξ Q p) (sgSweep0 Q (lv k) w) z') (meetPt q)) :=
        cutDeriv i (meetPt q) (hβione k i (meetPt q) (Or.inl hzK)) ⟨hsrc1, hsrc2⟩
          hcd0 (hreg (k, i) (meetPt q) hzK hPhi0)
      have hbridge := range_sup_eq_top_of_chartDiff_surjective (pch i) (sgLoop Ξ Q p)
        (sgSweep0 Q (lv k) w) (contMDiff_sgLoop_fixed Ξ Q hΞ hQ p) hchainsmk ⟨hsrc1, hsrc2⟩
        heq hzderiv
      have hconv : LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (sgLoop Ξ Q p)
          (sqPart (meetPt q))).toLinearMap
          = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap := by
        have h := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)
          (fun a => ⟨sq2 a 0, by simp [PiLp.proj_apply]⟩) (sqPart (meetPt q))
        have h3 : (fun x : EuclideanSpace ℝ (Fin 2) =>
              coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) x)) = sgLoop Ξ Q p := by
          funext x
          simp [sgLoop, coreLoop, Q₁, PiLp.proj_apply]
        rw [h3] at h
        have h2 : (sqPart (meetPt q)) 0 = q.1 := by rw [sqPart_meetPt]; rfl
        rw [PiLp.proj_apply, h2] at h
        exact h
      rw [hconv, cbPart_meetPt] at hbridge
      rw [show (clampedSweep (lv k) (fun t => 1 - t) (diskPlane Q₂)) = sgSweep0 Q (lv k) w
        from rfl]
      exact hbridge
    -- ### 5d. the finiteness
    have hFin : (coreMeet Q₁ (lv k) (diskPlane Q₂)).Finite := by
      let L : EuclideanSpace ℝ (Fin 1) → CappingSpace :=
        fun x => coreLoop Q₁ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) x)
      have hLsm : ContMDiff (𝓡 1) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L :=
        hloop₁sm.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contMDiff
      have htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
          u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 →
          L u = sgSweep0 Q (lv k) w x →
          LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap ⊔
            LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (sgSweep0 Q (lv k) w) x).toLinearMap = ⊤ := by
        intro u x hu hx heq
        have huI : (u 0) ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Submission.Drive.unitBox] using hu
        have hq : (u 0, x) ∈ coreMeet Q₁ (lv k) (diskPlane Q₂) := ⟨huI, hx, by
          have h1 : L u = coreLoop Q₁ (u 0) := by simp [L, PiLp.proj_apply]
          rw [← h1]
          exact heq⟩
        have h : LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) (u 0)).toLinearMap ⊔
            LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
              (clampedSweep (lv k) (fun t => 1 - t) (diskPlane Q₂)) x).toLinearMap = ⊤ :=
          hTrans (u 0, x) hq
        have hconv : LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap
            = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q₁) (u 0)).toLinearMap := by
          have hh := range_mfderiv_comp_surjective_linear (coreLoop Q₁) hloop₁sm
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) (fun a => ⟨ln1 a, by simp [ln1]⟩) u
          have h2 : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) u = u 0 := rfl
          rw [h2] at hh
          exact hh
        rw [← hconv] at h
        exact h
      have hfin1 := finite_loopChainMeet_of_transverse L (sgSweep0 Q (lv k) w) hLsm hchainsmk
        htrans
      have himg : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
          (p.1 0, p.2)) '' {p | p.1 ∈ Submission.Drive.unitBox 0 ∧
            p.2 ∈ Submission.Drive.unitBox 2 ∧ L p.1 = sgSweep0 Q (lv k) w p.2} =
          coreMeet Q₁ (lv k) (diskPlane Q₂) := by
        ext q
        constructor
        · rintro ⟨p, ⟨hp1, hp2, hpm⟩, rfl⟩
          exact ⟨by simpa [Submission.Drive.unitBox] using hp1, hp2, hpm⟩
        · rintro ⟨hq1, hq2, hqm⟩
          refine ⟨(ln1 q.1, q.2), ⟨?_, hq2, ?_⟩, ?_⟩
          · have hp1 : (ln1 q.1 : EuclideanSpace ℝ (Fin 1)) ∈ Submission.Drive.unitBox 0 := by
              simpa [Submission.Drive.unitBox, ln1] using hq1
            exact hp1
          · have h1 : L (ln1 q.1) = coreLoop Q₁ q.1 := by simp [L, ln1]
            rw [h1]
            exact hqm
          · simp [ln1]
      rw [← himg]
      exact hfin1.image _
    -- ### 5e. the interiority
    have hInt : ∀ q ∈ coreMeet Q₁ (lv k) (diskPlane Q₂),
        q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ j : Fin 3, q.2 j ∈ Set.Ioo (0 : ℝ) 1 := by
      rintro q ⟨hq1, hq2, hmeet⟩
      obtain ⟨i, hiC0, hzK, hc1, hcz, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
      have hzbox : ∀ k' : Fin 5, k' ≠ 1 → meetPt q k' ∈ Set.Icc (0 : ℝ) 1 :=
        fun k' _ => meetPt_mem_unitBox_of hq1 hq2 k'
      have hcontra : ∀ (k' : Fin 4) (t : Fin 2), (t : ℝ) = meetPt q (boxIdx k') → False := by
        intro k' t ht
        have hybox : gatherCLM k' (meetPt q) ∈ Submission.Drive.unitBox 2 :=
          gatherCLM_mem_unitBox (k := k') hzbox
        have hyK : gatherCLM k' (meetPt q) ∈ KzeroOf k i (k', t) := by
          refine ⟨hybox, ?_, ?_⟩
          · rw [sgFace_gatherCLM k' t (meetPt_apply_one q) ht]; exact hc1
          · rw [sgFace_gatherCLM k' t (meetPt_apply_one q) ht]; exact hcz
        have hne := havoid (k, i) (k', t) (gatherCLM k' (meetPt q)) hyK
        rw [sgFace_gatherCLM k' t (meetPt_apply_one q) ht] at hne
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
    -- ### 5f. the `GoodPair`
    exact ⟨hQ₁sm, hQ₂sm, hFin, hInt, hTrans⟩
  exact ⟨p, lt_trans hpst hbr₀, conv 0, conv 1⟩

/-! ## The requested lemma -/

theorem sideGerm_good_exists_two_levels {m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.CappingSpace]
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c c' : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsSmoothChart Q)
    (hc : 0 < c) (hc' : 0 < c') (w : UnitAddCircle) :
    Filter.Frequently (fun t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      Work.Drive.GoodAt Ξ Q c w t ∧ Work.Drive.GoodAt Ξ Q c' w t) (nhds 0) := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε₀, hε₀, hsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨p, hpε, hgood, hgood'⟩ := sgGoodPair_of_small_two_levels Ξ Q c c' hΞ hQ w ε₀ hε₀
  refine ⟨(p, 0), hsub ?_, ?_⟩
  · have h1 : dist (p, (0 : EuclideanSpace ℝ (Fin m))) 0 = ‖p‖ := by
      simp [dist_eq_norm, Prod.norm_def]
    rw [Metric.mem_ball, h1]
    exact hpε
  · refine ⟨?_, ?_⟩
    · simpa [Work.Drive.GoodAt, Work.Drive.pertChart, hΞ.1] using hgood
    · simpa [Work.Drive.GoodAt, Work.Drive.pertChart, hΞ.1] using hgood'

end

end Work.Drive
