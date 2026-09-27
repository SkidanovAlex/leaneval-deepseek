import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.exists_tangential_field

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The same-box parity engine: local theory

Two smooth maps `F G : ℝ⁵ → M` into a smooth `4`-manifold `M` which meet transversally on the box
`[0,1]⁵` (the derivative of the *difference* `F - G` is surjective at every meet).  This is the
"self-intersection modulo the diagonal" shape: both maps live on the same five-box, so the local
model is the zero set of the charted difference map `chr p ∘ F - chr p ∘ G : ℝ⁵ → ℝ⁴`.

This file builds the local theory:

* `boxMeet`, `boxBMeet` — the meet set and its boundary part;
* `chartReg`, `chartDif`, `Lf` — the chart region, the charted difference map and the
  chart-independent difference `mfderiv F - mfderiv G` of the two derivatives;
* the derivative formula `fderiv_chartDif_apply`, its specialisation `fderiv_chartDif_eq_Lf` at a
  meet, and the surjectivity transfer `chartDif_surjective_of_Lf`;
* the face criterion `chartDif_face_of_kernel` (a common tangent direction with a non-zero `i`-th
  coordinate makes the derivative surjective on the coordinate hyperplane `{v | v i = 0}`);
* the local graph structure `exists_local_graph_box` (implicit function theorem in a chart);
* the local curve data `exists_curve_data_box`;
* the existence of a smooth compactly supported field tangent to the meet set
  (`exists_tangential_field_box`).

Everything here is a verbatim adaptation of the `(2,3)`-split theory in
`Submission/Work/Drive/ChartBridge.lean`, `.../ManifoldParity/exists_local_graph.lean`,
`.../ManifoldParity/exists_curve_data.lean` and `.../ManifoldParity/exists_tangential_field.lean`,
with the two block projections replaced by the identity.
-/

namespace Work.Drive.FamBox

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The meet set and its boundary part -/

/-- The meet set of two maps `F G : ℝ⁵ → M` inside the five-box. -/
def boxMeet (F G : Amb 4 → M) : Set (Amb 4) :=
  {x | x ∈ Submission.Drive.unitBox 4 ∧ F x = G x}

/-- The boundary part of the meet set. -/
def boxBMeet (F G : Amb 4 → M) : Set (Amb 4) :=
  {x | x ∈ Submission.Drive.unitBox 4 ∧ F x = G x ∧ x ∈ Submission.Drive.unitBoxBdry 4}

@[simp] theorem mem_boxMeet {F G : Amb 4 → M} {x : Amb 4} :
    x ∈ boxMeet F G ↔ x ∈ Submission.Drive.unitBox 4 ∧ F x = G x := Iff.rfl

@[simp] theorem mem_boxBMeet {F G : Amb 4 → M} {x : Amb 4} :
    x ∈ boxBMeet F G ↔ x ∈ Submission.Drive.unitBox 4 ∧ F x = G x ∧
      x ∈ Submission.Drive.unitBoxBdry 4 := Iff.rfl

theorem boxBMeet_subset_boxMeet (F G : Amb 4 → M) : boxBMeet F G ⊆ boxMeet F G :=
  fun _ hx => ⟨hx.1, hx.2.1⟩

theorem isClosed_boxMeet (F G : Amb 4 → M) (hF : Continuous F) (hG : Continuous G) :
    IsClosed (boxMeet F G) := by
  have h1 : IsClosed {x : Amb 4 | F x = G x} := isClosed_eq hF hG
  have h2 : IsClosed (Submission.Drive.unitBox 4 ∩ {x : Amb 4 | F x = G x}) :=
    (isClosed_unitBox 4).inter h1
  convert h2 using 1
  ext x
  simp [boxMeet]

theorem isCompact_boxMeet (F G : Amb 4 → M) (hF : Continuous F) (hG : Continuous G) :
    IsCompact (boxMeet F G) :=
  (isCompact_unitBox 4).of_isClosed_subset (isClosed_boxMeet F G hF hG) fun _ hx => hx.1

theorem isClosed_boxBMeet (F G : Amb 4 → M) (hF : Continuous F) (hG : Continuous G) :
    IsClosed (boxBMeet F G) := by
  have h1 : IsClosed {x : Amb 4 | F x = G x} := isClosed_eq hF hG
  have h2 : boxBMeet F G = Submission.Drive.unitBoxBdry 4 ∩ {x : Amb 4 | F x = G x} := by
    ext x
    constructor
    · intro h
      obtain ⟨hbox, heq, hbdry⟩ := h
      exact ⟨hbdry, heq⟩
    · intro h
      exact ⟨h.1.1, h.2, h.1⟩
  rw [h2]
  exact (isClosed_unitBoxBdry 4).inter h1

/-! ## The charted difference map -/

/-- The chart region: the points of `ℝ⁵` where both `F` and `G` take their values in the source of
the chart at `p`. -/
def chartReg (p : M) (F G : Amb 4 → M) : Set (Amb 4) :=
  {x | F x ∈ (chr p).source ∧ G x ∈ (chr p).source}

/-- The **charted difference map** of the two maps in the chart at `p`. -/
def chartDif (p : M) (F G : Amb 4 → M) : Amb 4 → Tgt 4 :=
  fun x => chr p (F x) - chr p (G x)

/-- The **chart-independent difference of the two derivatives** at `x`. -/
def Lf (F G : Amb 4 → M) (x : Amb 4) : Amb 4 →L[ℝ] Tgt 4 :=
  (show Amb 4 →L[ℝ] Tgt 4 from mfderiv (𝓡 5) (𝓡 4) F x) -
    (show Amb 4 →L[ℝ] Tgt 4 from mfderiv (𝓡 5) (𝓡 4) G x)

theorem Lf_apply (F G : Amb 4 → M) (x v : Amb 4) :
    Lf F G x v = (show Tgt 4 from mfderiv (𝓡 5) (𝓡 4) F x v) -
      (show Tgt 4 from mfderiv (𝓡 5) (𝓡 4) G x v) := rfl

@[simp] theorem mem_chartReg {p : M} {F G : Amb 4 → M} {x : Amb 4} :
    x ∈ chartReg p F G ↔ F x ∈ (chr p).source ∧ G x ∈ (chr p).source := Iff.rfl

/-- The chart at the common image point contains both images. -/
theorem mem_chartReg_self (F G : Amb 4 → M) {x : Amb 4} (heq : F x = G x) :
    x ∈ chartReg (F x) F G :=
  ⟨mem_chart_source _ _, by rw [← heq]; exact mem_chart_source _ _⟩

theorem chartReg_extChartAt_source {p : M} {F G : Amb 4 → M} {x : Amb 4}
    (hx : x ∈ chartReg p F G) : F x ∈ (extChartAt (𝓡 4) p).source := by
  have h := hx.1
  rwa [chr, ← extChartAt_source (I := 𝓡 4) p] at h

theorem isOpen_chartReg (p : M) (F G : Amb 4 → M) (hF : Continuous F) (hG : Continuous G) :
    IsOpen (chartReg p F G) :=
  (hF.isOpen_preimage _ (chr p).open_source).inter (hG.isOpen_preimage _ (chr p).open_source)

/-- The charted difference map vanishes exactly where the two maps meet (inside the chart region). -/
theorem chartDif_eq_zero_iff {p : M} {F G : Amb 4 → M} {x : Amb 4} (hx : x ∈ chartReg p F G) :
    chartDif p F G x = 0 ↔ F x = G x := by
  rw [chartDif, sub_eq_zero, mem_chartReg] at *
  constructor
  · intro h
    exact (chr p).injOn hx.1 hx.2 h
  · intro h
    rw [h]

theorem chartDif_eq (p : M) (F G : Amb 4 → M) :
    chartDif p F G = fun x => chr p (F x) - chr p (G x) := rfl

/-- Smoothness of the charted difference map on the chart region. -/
theorem contDiffOn_chartDif (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G) :
    ContDiffOn ℝ Ctop (chartDif p F G) (chartReg p F G) := by
  have h1 := contMDiffOn_chart_comp F hF p
  have h2 := contMDiffOn_chart_comp G hG p
  have hF3 : ContDiffOn ℝ Ctop (fun x : Amb 4 => chr p (F x)) (chartReg p F G) := by
    have := h1.mono (fun x (hx : x ∈ chartReg p F G) => hx.1)
    intro x hx
    have h1x : ContMDiffWithinAt (𝓡 5) (𝓡 4) Ctop
        (fun x : Amb 4 => chr p (F x)) (chartReg p F G) x := this x hx
    simpa [writtenInExtChartAt] using (contMDiffWithinAt_iff.mp h1x).2
  have hG3 : ContDiffOn ℝ Ctop (fun x : Amb 4 => chr p (G x)) (chartReg p F G) := by
    have := h2.mono (fun x (hx : x ∈ chartReg p F G) => hx.2)
    intro x hx
    have h1x : ContMDiffWithinAt (𝓡 5) (𝓡 4) Ctop
        (fun x : Amb 4 => chr p (G x)) (chartReg p F G) x := this x hx
    simpa [writtenInExtChartAt] using (contMDiffWithinAt_iff.mp h1x).2
  have hsub := hF3.sub hG3
  rw [show chartDif p F G = fun x : Amb 4 => chr p (F x) - chr p (G x) from rfl]
  exact hsub

/-- The derivative of the charted difference map. -/
theorem fderiv_chartDif_apply (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (v : Amb 4) :
    fderiv ℝ (chartDif p F G) x v =
      tangentCoordChange (𝓡 4) (F x) p (F x) (mfderiv (𝓡 5) (𝓡 4) F x v)
        - tangentCoordChange (𝓡 4) (G x) p (G x) (mfderiv (𝓡 5) (𝓡 4) G x v) := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := fderiv_chart_comp_hasFDerivAt F hF p hx1
  have h2 := fderiv_chart_comp_hasFDerivAt G hG p hx2
  have h3 : HasFDerivAt (chartDif p F G)
      ((tangentCoordChange (𝓡 4) (F x) p (F x)).comp (mfderiv (𝓡 5) (𝓡 4) F x)
        - (tangentCoordChange (𝓡 4) (G x) p (G x)).comp (mfderiv (𝓡 5) (𝓡 4) G x)) x := by
    rw [chartDif_eq]
    exact h1.sub h2
  rw [h3.fderiv]
  rfl

/-- **The derivative of the charted difference map through `Lf`.**  At a meet the two
change-of-coordinates maps coincide, so the derivative is the (invertible) change of coordinates
applied to the chart-independent difference `Lf`. -/
theorem fderiv_chartDif_eq_Lf (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (heq : F x = G x) (v : Amb 4) :
    fderiv ℝ (chartDif p F G) x v =
      tangentCoordChange (𝓡 4) (F x) p (F x) (Lf F G x v) := by
  rw [fderiv_chartDif_apply p F G hF hG hx v]
  have htc : tangentCoordChange (𝓡 4) (F x) p (F x) =
      tangentCoordChange (𝓡 4) (G x) p (G x) := by rw [heq]
  rw [htc, ← map_sub]
  rfl

/-- A common direction of the two derivatives is a kernel direction of the charted difference map. -/
theorem chartDif_fderiv_eq_zero_of_Lf_eq_zero (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (heq : F x = G x) {σ : Amb 4}
    (hσ : Lf F G x σ = 0) :
    fderiv ℝ (chartDif p F G) x σ = 0 := by
  rw [fderiv_chartDif_eq_Lf p F G hF hG hx heq σ, hσ, map_zero]

/-- **The charted difference map is a submersion at a meet where the difference of the derivatives
is surjective.** -/
theorem chartDif_surjective_of_Lf (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (heq : F x = G x)
    (hsurj : Function.Surjective (Lf F G x)) :
    Function.Surjective (fderiv ℝ (chartDif p F G) x) := by
  have hsrc1 : F x ∈ (extChartAt (𝓡 4) (F x)).source := mem_extChartAt_source (I := 𝓡 4) (F x)
  have hsrc2 : F x ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]; exact hx.1
  have hleft : Function.LeftInverse (tangentCoordChange (𝓡 4) (F x) p (F x))
      (tangentCoordChange (𝓡 4) p (F x) (F x)) :=
    fun v => tangentCoordChange_comp_inv ⟨hsrc2, hsrc1⟩ v
  have hsurjT : Function.Surjective (tangentCoordChange (𝓡 4) (F x) p (F x)) := hleft.surjective
  intro w
  obtain ⟨w', hw'⟩ := hsurjT w
  obtain ⟨v, hv⟩ := hsurj w'
  exact ⟨v, by rw [fderiv_chartDif_eq_Lf p F G hF hG hx heq v, hv, hw']⟩

/-- **The face criterion for the charted difference map.**  If the derivative of the charted
difference map is surjective at a meet and the difference of the two derivatives has a kernel vector
`σ` with `σ i ≠ 0`, then the restriction of the derivative to the coordinate hyperplane
`{v | v i = 0}` is surjective. -/
theorem chartDif_face_of_kernel (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (heq : F x = G x)
    (hsurj : Function.Surjective (fderiv ℝ (chartDif p F G) x))
    {i : Fin 5} {σ : Amb 4} (hσ : Lf F G x σ = 0) (hi : σ i ≠ 0) :
    Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDif p F G) x v.1) := by
  rw [surjective_domRestrict_iff_cofactorVec_ne_zero _ hsurj i]
  have hk : fderiv ℝ (chartDif p F G) x σ = 0 :=
    chartDif_fderiv_eq_zero_of_Lf_eq_zero p F G hF hG hx heq hσ
  have hne : σ ≠ 0 := fun h => hi (by rw [h]; rfl)
  exact (cofactorVec_apply_ne_zero_iff _ hsurj hk hne i).mpr hi

/-! ## Globalization and the local graph structure -/

/-- **Globalization of the charted difference map.**  At a point of the chart region the charted
difference map agrees on a neighbourhood of the point with a *globally* smooth map
`ℝ⁵ → ℝ⁴`. -/
theorem exists_chartDif_extension_box (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) :
    ∃ (F' : Amb 4 → Tgt 4) (U : Set (Amb 4)), IsOpen U ∧ x ∈ U ∧ U ⊆ chartReg p F G ∧
      ContDiff ℝ Ctop F' ∧ Set.EqOn F' (chartDif p F G) U := by
  have hregion : IsOpen (chartReg p F G) :=
    isOpen_chartReg p F G hF.continuous hG.continuous
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hregion x hx
  set χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hχ
  have hχ1 : ∀ y ∈ Metric.ball x (r / 4), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχ0 : ∀ y, r / 2 ≤ dist y x → χ y = 0 := by
    intro y hy
    refine χ.zero_of_le_dist ?_
    rw [hχ]
    show r / 2 ≤ dist y x
    exact hy
  have hsupp : ∀ y, ¬ (dist y x ≤ r / 2) → ∀ᶠ z in 𝓝 y, χ z = 0 := by
    intro y hy
    have hy' : r / 2 < dist y x := not_le.mp hy
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y (sub_pos.mpr hy')) ?_
    intro z hz
    refine hχ0 z (le_of_lt ?_)
    have hz' : dist z y < dist y x - r / 2 := Metric.mem_ball.mp hz
    have h1 : dist y x ≤ dist z y + dist z x := by
      simpa [dist_comm] using dist_triangle y z x
    linarith
  refine ⟨fun y => χ y • chartDif p F G y, Metric.ball x (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), ?_, ?_, ?_⟩
  · intro y hy
    exact hsub (Metric.ball_subset_ball (by linarith) hy)
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ chartReg p F G
    · have h1 : ContDiffAt ℝ Ctop (fun y : Amb 4 => χ y) y := χ.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ Ctop (chartDif p F G) y :=
        (contDiffOn_chartDif p F G hF hG).contDiffAt (hregion.mem_nhds hy)
      exact h1.smul h2
    · have hdist : ¬ (dist y x ≤ r / 2) := by
        intro hcon
        refine hy (hsub (Metric.mem_ball.mpr ?_))
        linarith
      refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [hsupp y hdist] with z hz
      simp [hz]
  · intro y hy
    change χ y • chartDif p F G y = chartDif p F G y
    rw [hχ1 y hy, one_smul]

/-- **The local graph structure of the meet set.**  Near a point `x` at which the two maps meet and
at which the charted difference map is transverse to the coordinate hyperplane `{v | v i = 0}`, the
meet set is the graph of a smooth map `η` over the `i`-th coordinate. -/
theorem exists_local_graph_box (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {x : Amb 4} (hx : x ∈ chartReg p F G) (heq : F x = G x) (i : Fin 5)
    (hsurj_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDif p F G) x v.1)) :
    ∃ (δ ρ : ℝ) (η : ℝ → Amb 4), 0 < δ ∧ 0 < ρ ∧ ContDiff ℝ Ctop η ∧
      (∀ u, η u i = 0) ∧ η (x i) = x - (x i) • EuclideanSpace.single i 1 ∧
      (∀ y, |y i - x i| < δ →
        ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ρ →
        y ∈ chartReg p F G ∧
        (F y = G y ↔ y = (y i) • EuclideanSpace.single i 1 + η (y i))) := by
  obtain ⟨F', U, hUopen, hxU, hUsub, hF'smooth, hF'eq⟩ :=
    exists_chartDif_extension_box p F G hF hG hx
  have hF'x : F' x = 0 := by
    rw [hF'eq hxU]
    exact (chartDif_eq_zero_iff hx).mpr heq
  have hderiv : fderiv ℝ F' x = fderiv ℝ (chartDif p F G) x := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact hF'eq hy
  have hface' : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ F' x v.1) := by
    rw [hderiv]
    exact hsurj_i
  obtain ⟨δ₀, ρ₀, η, hδ₀, hρ₀, hηsmooth, hηi, hηx, -, hchar⟩ :=
    exists_local_normalForm hF'smooth hF'x i hface'
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  have hε3 : (0:ℝ) < ε / 3 := by linarith
  have hηcont : ContinuousAt η (x i) := hηsmooth.continuous.continuousAt
  obtain ⟨δ₁, hδ₁, hηnear⟩ : ∃ δ₁ > 0, ∀ u, |u - x i| < δ₁ → ‖η u - η (x i)‖ < ε / 3 := by
    have hball : Metric.ball (η (x i)) (ε / 3) ∈ 𝓝 (η (x i)) :=
      Metric.ball_mem_nhds _ hε3
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.mem_nhds_iff.mp (hηcont.eventually hball)
    exact ⟨δ₁, hδ₁, fun u hu => hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hu)⟩
  refine ⟨min (min δ₀ δ₁) (ε / 3), min ρ₀ (ε / 3), η,
    lt_min (lt_min hδ₀ hδ₁) hε3, lt_min hρ₀ hε3, hηsmooth, hηi, hηx, ?_⟩
  intro y h1 h2
  have h1₀ : |y i - x i| < δ₀ :=
    lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have h1₁ : |y i - x i| < δ₁ :=
    lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have h1ε : |y i - x i| < ε / 3 := lt_of_lt_of_le h1 (min_le_right _ _)
  have h2₀ : ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ρ₀ :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have h2ε : ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ε / 3 :=
    lt_of_lt_of_le h2 (min_le_right _ _)
  have hynorm : ‖y - x‖ < ε := by
    have hsplit : y - x = (y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1) := by
      rw [hηx]
      module
    rw [hsplit]
    have hnorm : ‖(y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1)‖
        ≤ ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖
          + ‖η (y i) - η (x i)‖ + |y i - x i| := by
      have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ)‖ = |y i - x i| := by
        rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
        simp
      have h1 := norm_add_le ((y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i))) ((y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ))
      have h2 := norm_add_le (y - (y i) • EuclideanSpace.single i 1 - η (y i))
        (η (y i) - η (x i))
      rw [hsingle] at h1
      linarith
    have hη' := hηnear (y i) h1₁
    linarith
  have hyU : y ∈ U := hεsub hynorm
  have hyreg : y ∈ chartReg p F G := hUsub hyU
  exact ⟨hyreg, by rw [← chartDif_eq_zero_iff hyreg, ← hF'eq hyU, hchar y h1₀ h2₀]⟩

/-! ## The local curve data -/

/-- **The local graph data of the meet set at a point of the meet set**, in the form in which the
tangent-field construction consumes it: the meet set is near `x` the graph of a smooth curve `γ`
over some coordinate `i`, and the difference of the two derivatives kills the tangent of `γ`. -/
theorem exists_curve_data_box (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x))
    {x : Amb 4} (hx : x ∈ boxMeet F G) :
    ∃ (i : Fin 5) (γ : ℝ → Amb 4) (R : Set (Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, (F y = G y ↔ y = γ (y i))) ∧
      (∀ y ∈ R, F y = G y → Lf F G y (fderiv ℝ γ (y i) 1) = 0) := by
  obtain ⟨hbox, heq⟩ := hx
  have hxreg : x ∈ chartReg (F x) F G := mem_chartReg_self F G heq
  have hsurj : Function.Surjective (fderiv ℝ (chartDif (F x) F G) x) :=
    chartDif_surjective_of_Lf (F x) F G hF hG hxreg heq (htrans x hbox heq)
  obtain ⟨i, hi⟩ := exists_domRestrict_surjective hsurj
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph_box (F x) F G hF hG hxreg heq i hi
  let γ : ℝ → Amb 4 := fun t => t • EuclideanSpace.single i 1 + η t
  have hγ : γ = fun t : ℝ => t • EuclideanSpace.single i 1 + η t := rfl
  let R : Set (Amb 4) :=
    {y | |y i - x i| < δ ∧ ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ < ρ}
  have hR : R = {y : Amb 4 |
      |y i - x i| < δ ∧ ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ < ρ} := rfl
  refine ⟨i, γ, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (((PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) i).sub
        continuous_const).abs) continuous_const
    · have hηcont : Continuous η := hηcd.continuous
      have hcont : Continuous fun y : Amb 4 =>
          ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ := by
        fun_prop
      exact isOpen_lt hcont continuous_const
  · rw [hR]
    refine ⟨?_, ?_⟩
    · rw [sub_self, abs_zero]; exact hδ
    · have h0 : x - x i • EuclideanSpace.single i 1 - η (x i) = 0 := by
        rw [hηx, sub_self]
      rw [h0, norm_zero]; exact hρ
  · rw [hγ]
    exact (contDiff_id.smul contDiff_const).add hηcd
  · intro t
    rw [hγ]
    simp [hηi]
  · rw [hγ]
    show x i • EuclideanSpace.single i 1 + η (x i) = x
    rw [hηx]
    abel
  · intro y hy
    rw [hR] at hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨-, hiff⟩ := hchar y hy1 hy2
    rw [hγ]
    exact hiff
  · intro y hy hyeq
    rw [hR] at hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hyreg, hiff⟩ := hchar y hy1 hy2
    have hyγ : y = y i • EuclideanSpace.single i 1 + η (y i) := hiff.mp hyeq
    have hγy : γ (y i) = y := by rw [hγ]; exact hyγ.symm
    have hε : 0 < δ - |y i - x i| := by linarith [hy1]
    have hev : (fun t : ℝ => chartDif (F x) F G (γ t))
        =ᶠ[𝓝 (y i)] (fun _ : ℝ => (0 : Tgt 4)) := by
      show ∀ᶠ t in 𝓝 (y i), chartDif (F x) F G (γ t) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨δ - |y i - x i|, hε, ?_⟩
      intro t ht
      rw [Real.dist_eq] at ht
      have htδ : |t - x i| < δ := by
        have h1 : |t - x i| ≤ |t - y i| + |y i - x i| := by
          have h2 := abs_add_le (t - y i) (y i - x i)
          rwa [show t - y i + (y i - x i) = t - x i by ring] at h2
        linarith
      have hc : (γ t) i = t := by rw [hγ]; simp [hηi]
      have hz : ‖γ t - γ t i • EuclideanSpace.single i 1 - η (γ t i)‖ < ρ := by
        rw [hc]
        have h0 : γ t - t • EuclideanSpace.single i 1 - η t = 0 := by
          have hγt : γ t = t • EuclideanSpace.single i 1 + η t := rfl
          rw [hγt, add_sub_cancel_left, sub_self]
        rw [h0, norm_zero]; exact hρ
      obtain ⟨hreg, hiff'⟩ := hchar (γ t) (by rw [hc]; exact htδ) hz
      have hcoord : γ t = γ t i • EuclideanSpace.single i 1 + η (γ t i) := by
        rw [hc, hγ]
      exact (chartDif_eq_zero_iff hreg).mpr (hiff'.mpr hcoord)
    have hfd : fderiv ℝ (fun t : ℝ => chartDif (F x) F G (γ t)) (y i) = 0 := by
      have h0 : fderiv ℝ (fun _ : ℝ => (0 : Tgt 4)) (y i) = 0 := by simp
      exact (Filter.EventuallyEq.fderiv_eq hev).trans h0
    have hγcd : ContDiff ℝ Ctop γ := by
      rw [hγ]; exact (contDiff_id.smul contDiff_const).add hηcd
    have hγdiff : DifferentiableAt ℝ γ (y i) := (hγcd.differentiable (by simp)).differentiableAt
    have hcda : DifferentiableAt ℝ (chartDif (F x) F G) y := by
      have hopen : IsOpen (chartReg (F x) F G) :=
        isOpen_chartReg _ F G hF.continuous hG.continuous
      have hcd : ContDiffOn ℝ Ctop (chartDif (F x) F G) (chartReg (F x) F G) :=
        contDiffOn_chartDif _ F G hF hG
      exact (hcd.contDiffAt (hopen.mem_nhds hyreg)).differentiableAt (by simp)
    have hcda' : DifferentiableAt ℝ (chartDif (F x) F G) (γ (y i)) := hγy.symm ▸ hcda
    have hcomp : fderiv ℝ (fun t : ℝ => chartDif (F x) F G (γ t)) (y i)
        = (fderiv ℝ (chartDif (F x) F G) (γ (y i))).comp (fderiv ℝ γ (y i)) := by
      have h := fderiv_comp (𝕜 := ℝ) (f := γ) (x := y i)
        (g := chartDif (F x) F G) hcda' hγdiff
      simpa only [Function.comp_def] using h
    have h2 : (fderiv ℝ (chartDif (F x) F G) (γ (y i))) (fderiv ℝ γ (y i) 1) = 0 := by
      have h1 : (fderiv ℝ (chartDif (F x) F G) (γ (y i))).comp (fderiv ℝ γ (y i)) = 0 := by
        rw [← hcomp]; exact hfd
      have hh := congrArg (fun L : ℝ →L[ℝ] Tgt 4 => L 1) h1
      simpa using hh
    have hfdEq : fderiv ℝ (chartDif (F x) F G) (γ (y i)) = fderiv ℝ (chartDif (F x) F G) y := by
      rw [hγy]
    have hzero' : fderiv ℝ (chartDif (F x) F G) y (fderiv ℝ γ (y i) 1) = 0 := by
      rw [← hfdEq]; exact h2
    have hTeq := fderiv_chartDif_eq_Lf (F x) F G hF hG hyreg hyeq (fderiv ℝ γ (y i) 1)
    rw [hzero'] at hTeq
    have hsrc : F y ∈ (extChartAt (𝓡 4) (F x)).source := chartReg_extChartAt_source hyreg
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (F y) (F x) (F y)) :=
      tangentCoordChange_injective ⟨mem_extChartAt_source (I := 𝓡 4) (F y), hsrc⟩
    exact hinj (by rw [hTeq.symm, map_zero])

/-! ## The tangential field -/

/-- The kernel of `Lf` at a meet in the box is one dimensional. -/
theorem finrank_ker_Lf (F G : Amb 4 → M)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x))
    {x : Amb 4} (hx : x ∈ boxMeet F G) :
    Module.finrank ℝ (LinearMap.ker (Lf F G x : Amb 4 →ₗ[ℝ] Tgt 4)) = 1 := by
  have hsurj : Function.Surjective (Lf F G x) := htrans x hx.1 hx.2
  have hrange : LinearMap.range (Lf F G x : Amb 4 →ₗ[ℝ] Tgt 4) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (Lf F G x : Amb 4 →ₗ[ℝ] Tgt 4)
  rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
  omega

open Work.Drive.ManifoldParity in
/-- **A smooth compactly supported field tangent to the meet set.** -/
theorem exists_tangential_field_box (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Lf F G x)) :
    ∃ V : Amb 4 → Amb 4, ContDiff ℝ Ctop V ∧ HasCompactSupport V ∧
      (∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → V x ≠ 0) ∧
      (∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 → F x = G x → ∀ p : M,
        x ∈ chartReg p F G → fderiv ℝ (chartDif p F G) x (V x) = 0) := by
  classical
  set Z : Set (Amb 4) := {y | F y = G y} with hZdef
  have hZcl : IsClosed Z := by
    rw [hZdef]
    exact isClosed_eq hF.continuous hG.continuous
  have hKcomp : IsCompact (boxMeet F G) := isCompact_boxMeet F G hF.continuous hG.continuous
  have hKZ : boxMeet F G ⊆ Z := fun y hy => hy.2
  have hdata : ∀ x ∈ boxMeet F G, ∃ (i : Fin 5) (γ : ℝ → Amb 4) (R : Set (Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, (F y = G y ↔ y = γ (y i))) ∧
      (∀ y ∈ R, F y = G y → Lf F G y (fderiv ℝ γ (y i) 1) = 0) :=
    fun x hx => exists_curve_data_box F G hF hG htrans hx
  have hdataZ : ∀ x ∈ boxMeet F G, ∃ (i : Fin 5) (γ : ℝ → Amb 4) (R : Set (Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, y ∈ Z ↔ y = γ (y i)) := by
    intro x hx
    obtain ⟨i, γ, R, h1, h2, h3, h4, h5, h6, -⟩ := hdata x hx
    exact ⟨i, γ, R, h1, h2, h3, h4, h5, fun y hy => by rw [hZdef]; exact h6 y hy⟩
  obtain ⟨U, hUcont, hUne, hUpar⟩ :=
    Work.ManifoldParity.exists_continuous_tangent_field_of_local_data (m := 4)
      (boxMeet F G) Z hKcomp hZcl hKZ hdataZ
  have hUtan : ∀ x ∈ boxMeet F G, Lf F G x (U x) = 0 := by
    intro x hx
    obtain ⟨i, γ, R, hRopen, hxR, hγ, hi, hxi, hsym, htang⟩ := hdata x hx
    obtain ⟨c, hc, hcU⟩ := hUpar x hx i γ R hRopen hxR hγ hi hxi
      (fun y hy => by rw [hZdef]; exact hsym y hy)
    rw [hcU, map_smul, htang x hxR hx.2, smul_zero]
  have hloc : ∀ x ∈ boxMeet F G, ∃ (W : Amb 4 → Amb 4) (UU : Set (Amb 4)),
      IsOpen UU ∧ x ∈ UU ∧ ContDiff ℝ Ctop W ∧
      ∀ y ∈ boxMeet F G ∩ UU, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U y := by
    intro x hx
    obtain ⟨i, γ, R, hRopen, hxR, hγ, hi, hxi, hsym, htang⟩ := hdata x hx
    refine ⟨fun y => fderiv ℝ γ (y i) 1, R, hRopen, hxR, contDiff_frame hγ i, ?_⟩
    intro y hy
    obtain ⟨hyK, hyR⟩ := hy
    have hWy : Lf F G y (fderiv ℝ γ (y i) 1) = 0 := htang y hyR hyK.2
    have hUy : Lf F G y (U y) = 0 := hUtan y hyK
    have hWne : fderiv ℝ γ (y i) 1 ≠ 0 := by
      intro h0
      have hcoord : (fderiv ℝ γ (y i) 1) i = 1 := by
        set ℓ : ℝ → ℝ := fun t => (γ t) i with hℓ
        have hproj_eq : (fun v : Amb 4 => v i)
            = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i) := by
          funext v; rw [PiLp.proj_apply]
        have h2 : fderiv ℝ ℓ (y i)
            = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).comp (fderiv ℝ γ (y i)) := by
          rw [hℓ, show (fun t : ℝ => (γ t) i) = (fun v : Amb 4 => v i) ∘ γ from rfl, hproj_eq]
          exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).hasFDerivAt.comp (y i)
            (hγ.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
        have h3 : fderiv ℝ ℓ (y i) 1 = deriv ℓ (y i) :=
          (fderiv_apply_one_eq_deriv (f := ℓ) (x := y i)).symm
        have hℓid : ℓ = fun t : ℝ => t := by funext t; exact hi t
        have h4 : deriv ℓ (y i) = 1 := by rw [hℓid]; simp
        have h5 : (fderiv ℝ γ (y i) 1) i = fderiv ℝ ℓ (y i) 1 := by
          rw [h2, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
        rw [h5, h3, h4]
      rw [h0] at hcoord
      simp at hcoord
    have hUne' : U y ≠ 0 := hUne y hyK
    have hdim := finrank_ker_Lf F G htrans hyK
    exact exists_smul_of_finrank_eq_one hdim hUy hWy hUne' hWne
  obtain ⟨V, hVsmooth, hVsupp, hVne, hVpar⟩ :=
    Work.ManifoldParity.exists_parallel_smooth_field (n := 5) (boxMeet F G) hKcomp U hUcont hUne hloc
  refine ⟨V, hVsmooth, hVsupp, ?_, ?_⟩
  · intro x hxbox heq
    exact hVne x ⟨hxbox, heq⟩
  · intro x hxbox heq p hxreg
    obtain ⟨c, hc, hcV⟩ := hVpar x ⟨hxbox, heq⟩
    rw [hcV, map_smul, fderiv_chartDif_eq_Lf p F G hF hG hxreg heq, hUtan x ⟨hxbox, heq⟩,
      map_zero, smul_zero]

end

end Work.Drive.FamBox
