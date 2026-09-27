import Mathlib
import Submission.Work.Drive.N2.windowDatum

/-!
# A rename-copy of `windowDatumSmooth`

This module is a verbatim copy of `Submission.Work.Drive.N2.windowDatumSmooth` in which **every**
declaration is renamed with the `wdsN_` prefix.  It exists only to break an import clash: the original
declares `Work.Drive.N2.isOpen_modelBall`, and so does `Submission.Work.Drive.N2.hmono_of_chartODE`
(an identical lemma).  Lean refuses to load two modules declaring the same name, and the saddle-window
lane needs both cones at once.  Statements, proofs and hypotheses are unchanged.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The model ball of a chart is open. -/
lemma wdsN_isOpen_modelBall (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (modelBall φ r) := by
  rw [show modelBall φ r = φ.source ∩ φ ⁻¹' {v : EuclideanSpace ℝ (Fin 2) | ‖v‖ < r} from rfl]
  exact φ.continuousOn.isOpen_inter_preimage φ.open_source
    (isOpen_lt continuous_norm continuous_const)

/-- The chart-coordinate quadratic form of the window datum is smooth on the chart source. -/
lemma wdsN_contMDiffAt_chartQ' {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N) {y : M}
    (hy : y ∈ (D.φ i).source) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z) y := by
  have hφ : ContMDiffAt (𝓡 2) (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞ (fun z => D.φ i z) y :=
    (D.hφ i).contMDiffAt ((D.φ i).open_source.mem_nhds hy)
  have h0 : ContMDiffAt (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun z => (D.φ i z) 0) y :=
    (coordProj (0 : Fin 2)).contMDiff.contMDiffAt.comp y hφ
  have h1 : ContMDiffAt (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun z => (D.φ i z) 1) y :=
    (coordProj (1 : Fin 2)).contMDiff.contMDiffAt.comp y hφ
  have hfun : (fun z => chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z)
      = fun z => D.s₁ i * ((D.φ i z) 0) ^ 2 + D.s₂ i * ((D.φ i z) 1) ^ 2 := rfl
  rw [hfun]
  exact (contMDiffAt_const.mul (h0.pow 2)).add (contMDiffAt_const.mul (h1.pow 2))

/-- `f` is smooth at every point of the chart sources of the window datum. -/
lemma wdsN_contMDiffAt_of_mem_source {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {i : Fin D.N} {y : M} (hy : y ∈ (D.φ i).source) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f y := by
  have hev : f =ᶠ[𝓝 y] fun z => f (D.x i) + chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z := by
    filter_upwards [(D.φ i).open_source.mem_nhds hy] with z hz
    exact D.hval i z hz
  have hsmooth : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => f (D.x i) + chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z) y := by
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M => f (D.x i)) y :=
      contMDiffAt_const
    exact h1.add (wdsN_contMDiffAt_chartQ' D i hy)
  exact hsmooth.congr_of_eventuallyEq hev

/-- `f` is differentiable everywhere. -/
lemma wdsN_mdifferentiableAt_of_windowDatum {f : M → ℝ} {p : M} (D : WindowDatum f p) (y : M) :
    MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) f y := by
  by_contra h
  have hcrit : Work.Drive.Morse.IsCritical f y := by
    show mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) f y = 0
    rw [mfderiv]
    exact if_neg h
  obtain ⟨i, hi⟩ := D.hcover y hcrit
  have hsrc : y ∈ (D.φ i).source := hi ▸ D.hsrc i
  exact h ((wdsN_contMDiffAt_of_mem_source D hsrc).mdifferentiableAt (by simp))

/-- `f` is continuous. -/
lemma wdsN_continuous_of_windowDatum {f : M → ℝ} {p : M} (D : WindowDatum f p) : Continuous f :=
  continuous_iff_continuousAt.mpr fun y => (wdsN_mdifferentiableAt_of_windowDatum D y).continuousAt

/-- `f` is bounded. -/
lemma wdsN_bounded_of_windowDatum {f : M → ℝ} {p : M} (D : WindowDatum f p) :
    ∃ C : ℝ, ∀ y : M, ‖f y‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (isCompact_range (wdsN_continuous_of_windowDatum D)).isBounded
  exact ⟨C, fun y => hC (f y) ⟨y, rfl⟩⟩

/-- Every orbit of the model-adapted flow meets a model ball. -/
lemma wdsN_exists_ball_of_windowDatum {f : M → ℝ} {p : M} (D : WindowDatum f p) (y : M) :
    ∃ τ ∈ Set.Ici (0 : ℝ), ∃ i : Fin D.N, D.Φ (τ, y) ∈ modelBall (D.φ i) (D.ρ i / 8) := by
  obtain ⟨C, hC⟩ := wdsN_bounded_of_windowDatum D
  by_contra h
  have hlev : ∀ τ : ℝ, 0 ≤ τ → f (D.Φ (τ, y)) = f y + τ := by
    intro τ hτ
    refine D.hlevel y τ ?_
    intro u hu i
    have hu0 : 0 ≤ u := by
      have hmin : min (0 : ℝ) τ = 0 := min_eq_left hτ
      rw [hmin] at hu
      exact hu.1
    exact fun hmem => h ⟨u, hu0, i, hmem⟩
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (f y)) (hC y)
  have hτ : 0 ≤ C + |f y| + 1 := by
    have h1 := abs_nonneg (f y)
    linarith
  have h1 := hlev (C + |f y| + 1) hτ
  have h2 : ‖f (D.Φ (C + |f y| + 1, y))‖ ≤ C := hC _
  rw [h1, Real.norm_eq_abs] at h2
  have h4 : |f y + (C + |f y| + 1)| = f y + (C + |f y| + 1) := by
    rw [abs_of_nonneg]
    linarith [neg_le_abs (f y), abs_nonneg (f y), hC0]
  rw [h4] at h2
  linarith [neg_le_abs (f y), abs_nonneg (f y)]

/-! ## The closed model balls, the propagation of smoothness, and the conclusion -/

/-- The union of the closed model balls of a window datum. -/
def wdsN_closedBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) : Set M :=
  ⋃ i, closure (modelBall (D.φ i) (D.ρ i / 8))

lemma wdsN_isClosed_closedBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) :
    IsClosed (wdsN_closedBalls D) :=
  isClosed_iUnion_of_finite fun i => isClosed_closure

lemma wdsN_closure_modelBall_subset_source {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (i : Fin D.N) :
    closure (modelBall (D.φ i) (D.ρ i / 8)) ⊆ (D.φ i).source :=
  (closure_mono (D.hCball i)).trans (D.hCcl i).2

lemma wdsN_modelBall_subset_closedBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) {i : Fin D.N} :
    modelBall (D.φ i) (D.ρ i / 8) ⊆ wdsN_closedBalls D :=
  fun z hz => Set.mem_iUnion.mpr ⟨i, subset_closure hz⟩

/-- `f` is smooth at every point of a closed model ball. -/
lemma wdsN_contMDiffAt_of_mem_closedBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) {z : M}
    (hz : z ∈ wdsN_closedBalls D) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f z := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact wdsN_contMDiffAt_of_mem_source D (wdsN_closure_modelBall_subset_source D i hi)

/-- The slice `w ↦ Φ (τ, w)` of the flow is smooth. -/
lemma wdsN_contMDiffAt_slice {f : M → ℝ} {p : M} (D : WindowDatum f p) (τ : ℝ) (y : M) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => D.Φ (τ, w)) y :=
  (D.hΦsm.contMDiffAt).comp y (contMDiffAt_const.prodMk contMDiffAt_id)

/-- The orbit `τ ↦ Φ (τ, y)` is continuous. -/
lemma wdsN_continuous_orbit {f : M → ℝ} {p : M} (D : WindowDatum f p) (y : M) :
    Continuous fun τ : ℝ => D.Φ (τ, y) :=
  D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)

/-- **The tube step.**  If the orbit segment of `y` avoids the closed model balls, then so do the
segments of all points of a neighbourhood of `y`. -/
lemma wdsN_exists_nhds_segment_avoids {f : M → ℝ} {p : M} (D : WindowDatum f p) {y : M} {τ : ℝ}
    (hav : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, y) ∉ wdsN_closedBalls D) :
    ∃ U ∈ 𝓝 y, ∀ w ∈ U, ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, w) ∉ wdsN_closedBalls D := by
  have hn : IsOpen {q : ℝ × M | D.Φ q ∉ wdsN_closedBalls D} :=
    (wdsN_isClosed_closedBalls D).isOpen_compl.preimage D.hΦsm.continuous
  have hsub : Set.Icc (min 0 τ) (max 0 τ) ×ˢ ({y} : Set M)
      ⊆ {q : ℝ × M | D.Φ q ∉ wdsN_closedBalls D} := by
    rintro ⟨u, w⟩ ⟨hu, rfl⟩
    exact hav u hu
  obtain ⟨u₀, v₀, -, hv₀, hsu, hyv, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hn hsub
  exact ⟨v₀, hv₀.mem_nhds (hyv (by simp)), fun w hw u hu => huv ⟨hsu hu, hw⟩⟩

/-- **Propagation of smoothness backwards**, at any smoothness level.  If the orbit segment of `y`
avoids the closed model balls and `f` is `C^n` at its endpoint `Φ (τ, y)`, then `f` is `C^n` at
`y`. -/
lemma wdsN_contMDiffAt_of_flow_backward {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (n : WithTop ℕ∞) {y : M} {τ : ℝ}
    (hn : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    (hav : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, y) ∉ wdsN_closedBalls D)
    (hz : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n f (D.Φ (τ, y))) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n f y := by
  obtain ⟨U, hU, hUseg⟩ := wdsN_exists_nhds_segment_avoids D hav
  have hfun : f =ᶠ[𝓝 y] fun w => f (D.Φ (τ, w)) - τ := by
    filter_upwards [hU] with w hw
    have h := D.hlevel w τ (fun u hu i hmem =>
      hUseg w hw u hu (wdsN_modelBall_subset_closedBalls D hmem))
    linarith
  have hcomp : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n (fun w => f (D.Φ (τ, w))) y :=
    hz.comp y ((wdsN_contMDiffAt_slice D τ y).of_le hn)
  exact (hcomp.sub (contMDiffAt_const (c := τ))).congr_of_eventuallyEq hfun

/-- **Propagation of smoothness forwards**, at any smoothness level: if the orbit segment of `y`
avoids the closed model balls and `f` is `C^n` at `y`, then `f` is `C^n` at `Φ (τ, y)`. -/
lemma wdsN_contMDiffAt_of_flow_forward {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (n : WithTop ℕ∞) {y : M} {τ : ℝ}
    (hn : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    (hav : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, y) ∉ wdsN_closedBalls D)
    (hy : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n f y) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n f (D.Φ (τ, y)) := by
  have hav' : ∀ u ∈ Set.Icc (min 0 (-τ)) (max 0 (-τ)),
      D.Φ (u, D.Φ (τ, y)) ∉ wdsN_closedBalls D := by
    intro u hu
    have h1 : D.Φ (u, D.Φ (τ, y)) = D.Φ (u + τ, y) := D.hΦcomp u τ y
    rw [h1]
    refine hav (u + τ) ?_
    have hmin : u ∈ Set.Icc (min 0 (-τ)) (max 0 (-τ)) := hu
    rcases le_total 0 τ with hτ | hτ
    · have h1 : -τ ≤ 0 := by linarith
      rw [min_eq_right h1, max_eq_left h1] at hmin
      rw [min_eq_left hτ, max_eq_right hτ]
      exact ⟨by linarith [hmin.1], by linarith [hmin.2]⟩
    · have h1 : 0 ≤ -τ := by linarith
      rw [min_eq_left h1, max_eq_right h1] at hmin
      rw [min_eq_right hτ, max_eq_left hτ]
      exact ⟨by linarith [hmin.1], by linarith [hmin.2]⟩
  have hpt : D.Φ (-τ, D.Φ (τ, y)) = y := by
    rw [D.hΦcomp, neg_add_cancel, D.hΦ0]
  obtain ⟨U, hU, hUseg⟩ := wdsN_exists_nhds_segment_avoids D hav'
  have hfun : f =ᶠ[𝓝 (D.Φ (τ, y))] fun w => f (D.Φ (-τ, w)) + τ := by
    filter_upwards [hU] with w hw
    have h := D.hlevel w (-τ) (fun u hu i hmem =>
      hUseg w hw u hu (wdsN_modelBall_subset_closedBalls D hmem))
    linarith
  have hbase : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n f (D.Φ (-τ, D.Φ (τ, y))) := by
    rw [hpt]
    exact hy
  have hcomp : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) n (fun w => f (D.Φ (-τ, w))) (D.Φ (τ, y)) :=
    hbase.comp (D.Φ (τ, y)) ((wdsN_contMDiffAt_slice D (-τ) (D.Φ (τ, y))).of_le hn)
  exact (hcomp.add (contMDiffAt_const (c := τ))).congr_of_eventuallyEq hfun

/-- **`f` is smooth wherever it carries a `WindowDatum`.** -/
theorem wdsN_contMDiff_of_windowDatum {f : M → ℝ} {p : M} (D : WindowDatum f p) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  intro y
  rw [contMDiffAt_infty]
  intro m
  -- smoothness at level `m`; the set where `f` is `C^m` is open
  have hmne : ((m : ℕ∞) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hSopen : IsOpen {z : M | ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((m : ℕ∞) : WithTop ℕ∞) f z} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (contMDiffAt_iff_contMDiffAt_nhds hmne).mp hz
  have hle : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  by_cases hy : y ∈ wdsN_closedBalls D
  · exact (wdsN_contMDiffAt_of_mem_closedBalls D hy).of_le hle
  -- the set of hitting times of the closed balls is nonempty
  set A : Set ℝ := {τ | 0 ≤ τ ∧ D.Φ (τ, y) ∈ wdsN_closedBalls D} with hA
  have hAne : A.Nonempty := by
    obtain ⟨τ, hτ, i, hmem⟩ := wdsN_exists_ball_of_windowDatum D y
    exact ⟨τ, hτ, wdsN_modelBall_subset_closedBalls D hmem⟩
  have hAbdd : BddBelow A := ⟨0, fun a ha => ha.1⟩
  set t₁ : ℝ := sInf A with ht₁
  have ht₁0 : 0 ≤ t₁ := le_csInf hAne (fun a ha => ha.1)
  have hmem_cl : t₁ ∈ closure A := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h2 : ∃ a ∈ A, a < t₁ + ε := by
      by_contra h
      push_neg at h
      have : t₁ + ε ≤ sInf A := le_csInf hAne (fun a ha => h a ha)
      rw [ht₁] at this
      linarith
    obtain ⟨a, haA, ha⟩ := h2
    refine ⟨a, haA, ?_⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [csInf_le hAbdd haA], by linarith [csInf_le hAbdd haA, hε]⟩
  have htend : Tendsto (fun τ : ℝ => D.Φ (τ, y)) (𝓝[A] t₁) (𝓝 (D.Φ (t₁, y))) :=
    ((wdsN_continuous_orbit D y).continuousAt).mono_left nhdsWithin_le_nhds
  haveI : (𝓝[A] t₁).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem_cl
  have hzmem : D.Φ (t₁, y) ∈ wdsN_closedBalls D :=
    (wdsN_isClosed_closedBalls D).mem_of_tendsto htend
      (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun τ hτ => hτ.2))
  have hzsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((m : ℕ∞) : WithTop ℕ∞) f (D.Φ (t₁, y)) :=
    (wdsN_contMDiffAt_of_mem_closedBalls D hzmem).of_le hle
  rcases eq_or_lt_of_le ht₁0 with hzero | hpos
  · rw [← hzero, D.hΦ0 y] at hzsm
    exact hzsm
  · -- a nearby point of the orbit is `C^m`, and smoothness propagates back
    have hev : ∀ᶠ τ in 𝓝 t₁, ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((m : ℕ∞) : WithTop ℕ∞) f (D.Φ (τ, y)) :=
      ((wdsN_continuous_orbit D y).continuousAt).preimage_mem_nhds (hSopen.mem_nhds hzsm)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
    set e : ℝ := min δ t₁ / 2 with he
    have hepos : 0 < e := by
      rw [he]
      exact half_pos (lt_min hδpos hpos)
    have heδ : e < δ := by
      have h4 : min δ t₁ ≤ δ := min_le_left _ _
      rw [he]
      linarith
    have het : e < t₁ := by
      have h4 : min δ t₁ ≤ t₁ := min_le_right _ _
      rw [he]
      linarith
    have hτ₀0 : 0 ≤ t₁ - e := by linarith
    have hdist : dist (t₁ - e) t₁ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hτ₀sm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((m : ℕ∞) : WithTop ℕ∞) f (D.Φ (t₁ - e, y)) := hδ hdist
    refine wdsN_contMDiffAt_of_flow_backward D _ hle (τ := t₁ - e) ?_ hτ₀sm
    intro u hu hmem
    have hu0 : 0 ≤ u := by
      have h2 : min (0 : ℝ) (t₁ - e) = 0 := min_eq_left hτ₀0
      rw [h2] at hu
      exact hu.1
    have hut : u < t₁ := by
      have h2 : max (0 : ℝ) (t₁ - e) = t₁ - e := max_eq_right hτ₀0
      rw [h2] at hu
      linarith [hu.2]
    have hmemA : u ∈ A := ⟨hu0, hmem⟩
    have := csInf_le hAbdd hmemA
    rw [← ht₁] at this
    linarith

end Work.Drive.N2
