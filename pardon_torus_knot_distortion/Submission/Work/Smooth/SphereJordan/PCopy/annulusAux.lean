import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.plainAnnulusSetup
import Submission.Work.Smooth.SphereJordan.PCopy.annulusClosureCore
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetCurves
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp

/-!
# Auxiliary lemmas for the normalisation of the pcannulus

This module contains the general (Schoenflies-free and Schoenflies-using) facts about
`PlaneSeparation` data and about the four `4`-arc curves `pctgtUpB`, `pctgtDnB` of the two-pccuts
construction that were originally proved inside `annulusNormalise.lean`.  They live here so that
modules which need them (`pctgtCurvesTraceDiff`, `tilingOfPairing`, ...) do not have to import
`annulusNormalise` — which would create an import cycle, since the proof of the target
`Work.SphereJordan.annulusNormalise` uses the tiling of the pcannulus.

The content is:

* `pcboundedSide_subset_ball`, `pcV_subset_ball_diff`: the bounded side of a curve inside the open unit
  disc lies in the open disc and off any subset of the trace;
* `pcside_eq_component`: a component of `int 𝔻 \ T` is the bounded side of the lens curve `T ∪ Q`,
  the key structural fact (no Schoenflies input);
* `pcmem_boundedSide_of_local_arc`: the test point near the outer arc `Q` does lie in the bounded side;
* `pccomponent_disjoint_of_cover` / `pccomponent_disjoint_of_ne`: among two distinct components covering
  `int 𝔻 \ T` at most one meets `S.V`;
* `pcclosure_union_inter_of_pieces`: the abstract tiling lemma;
* the trace bookkeeping for `pctgtUpB`/`pctgtDnB`.
-/

namespace Work.SphereJordan

open Set

noncomputable section

/-- **The bounded side of a simple closed plane curve inside the open unit disc lies in the open
unit disc.** -/
theorem pcboundedSide_subset_ball {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1) :
    S.V ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : ‖z‖ ≤ 1 :=
    Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S hball z hz
  refine lt_of_le_of_ne h1 (fun h2 => ?_)
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds hz)
  set w : ℂ := ((1 + ε / 2 : ℝ) : ℂ) * z with hw
  have hwball : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w - z = ((ε / 2 : ℝ) : ℂ) * z := by rw [hw]; push_cast; ring
    rw [hsub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2), h2, mul_one]
    linarith
  have hwnorm : 1 < ‖w‖ := by
    rw [hw, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε / 2), h2, mul_one]
    linarith
  have := Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S hball w (hε' hwball)
  linarith

/-- **A component of `int 𝔻 \ T` is the bounded side of the lens curve `T ∪ Q`.**

Let `c` be a simple closed plane curve whose trace lies in the open unit disc and splits as
`c.trace = T ∪ Q` with `Q` on the boundary circle (`c.trace \ T ⊆ ∂𝔻`).  Then for any point `q`
of the bounded side `S.V` lying off `T`, the bounded side of `c` is exactly the connected component
of `int 𝔻 \ T` containing `q`. -/
theorem pcside_eq_component {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1)
    {T : Set ℂ} (hT : T ⊆ c.trace) (hOuter : c.trace \ T ⊆ Metric.sphere (0 : ℂ) 1)
    {q : ℂ} (hq : q ∈ S.V) (hqT : q ∉ T) :
    S.V = connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q := by
  have hVtr : S.V ⊆ c.traceᶜ := by
    intro x hx hxtr
    have : x ∈ S.U ∪ S.V := Or.inr hx
    rw [S.union_eq] at this
    exact this hxtr
  have hVsub : S.V ⊆ Metric.ball (0 : ℂ) 1 \ T := by
    intro z hz
    refine ⟨pcboundedSide_subset_ball S hball hz, fun hzT => hVtr hz (hT hzT)⟩
  refine Set.Subset.antisymm (S.preconn_V.subset_connectedComponentIn hq hVsub) ?_
  intro z hz
  have hPdisj : Disjoint (connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q) c.trace := by
    rw [Set.disjoint_left]
    intro y hy hytrace
    have hyT : y ∉ T := (connectedComponentIn_subset _ _ hy).2
    have hysphere : ‖y‖ = 1 := by
      have h := hOuter ⟨hytrace, hyT⟩
      rw [Metric.mem_sphere] at h
      rwa [dist_zero_right] at h
    have hyball : ‖y‖ < 1 := by
      have h := (connectedComponentIn_subset _ _ hy).1
      rw [Metric.mem_ball] at h
      rwa [dist_zero_right] at h
    rw [hysphere] at hyball
    exact lt_irrefl 1 hyball
  have hsub : connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ⊆ S.U ∪ S.V := by
    rw [S.union_eq]
    exact fun y hy => (Set.disjoint_left.mp hPdisj) hy
  have hqP : q ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q :=
    S.preconn_V.subset_connectedComponentIn hq hVsub hq
  rcases (isPreconnected_connectedComponentIn (F := Metric.ball (0 : ℂ) 1 \ T) (x := q)).subset_or_subset
      S.isOpen_U S.isOpen_V S.disjoint_UV hsub with hU | hV
  · exact absurd hq ((Set.disjoint_left.mp S.disjoint_UV) (hU hqP))
  · exact hV hz

/-- **A point of `int 𝔻` near an interior point of the outer arc lies in the bounded side.**

Let `c` be a simple closed plane curve whose trace lies in the open unit disc, with bounded side
`S.V`, whose trace coincides *locally* with the unit circle around a point `w` of its trace
(`c.trace ∩ ball w r = ∂𝔻 ∩ ball w r`).  Then every point of `ball w r` of norm `< 1` lies in
`S.V`:  the lens `ball w r ∩ int 𝔻` is preconnected and avoids the trace, and the bounded side
meets `ball w r` (its closure contains `w`); the unbounded side cannot contain the whole lens
because the bounded side lies in the closed unit disc. -/
theorem pcmem_boundedSide_of_local_arc {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1)
    (hcl : closure S.V = S.V ∪ c.trace)
    {w : ℂ} (hw : w ∈ c.trace) {r : ℝ} (hr : 0 < r)
    (hloc : c.trace ∩ Metric.ball w r = Metric.sphere (0 : ℂ) 1 ∩ Metric.ball w r)
    {q : ℂ} (hqw : q ∈ Metric.ball w r) (hq : ‖q‖ < 1) :
    q ∈ S.V := by
  have hinner_trace : Metric.ball w r ∩ Metric.ball (0 : ℂ) 1 ⊆ c.traceᶜ := by
    intro z hz hzt
    have hzmem : z ∈ c.trace ∩ Metric.ball w r := ⟨hzt, hz.1⟩
    rw [hloc] at hzmem
    have hzsp : z ∈ Metric.sphere (0 : ℂ) 1 := hzmem.1
    have hzball : ‖z‖ < 1 := by
      have h := hz.2; rw [Metric.mem_ball] at h; rwa [dist_zero_right] at h
    rw [Metric.mem_sphere] at hzsp
    rw [dist_zero_right] at hzsp
    exact absurd hzsp (ne_of_lt hzball)
  have hinner_conn : IsPreconnected (Metric.ball w r ∩ Metric.ball (0 : ℂ) 1) :=
    ((convex_ball w r).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  have hsub : Metric.ball w r ∩ Metric.ball (0 : ℂ) 1 ⊆ S.V ∪ S.U := by
    rw [Set.union_comm S.V S.U, S.union_eq]
    exact fun z hz => hinner_trace hz
  rcases hinner_conn.subset_or_subset S.isOpen_V S.isOpen_U (disjoint_comm.mpr S.disjoint_UV) hsub
    with hV | hU
  · refine hV ⟨hqw, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]; exact hq
  · exfalso
    have hwcl : w ∈ closure S.V := by rw [hcl]; exact Or.inr hw
    obtain ⟨y, hyV, hyball⟩ := Metric.mem_closure_iff.mp hwcl r hr
    have hyin : y ∈ Metric.ball w r ∩ Metric.ball (0 : ℂ) 1 :=
      ⟨Metric.mem_ball.mpr (by rwa [dist_comm]), pcboundedSide_subset_ball S hball hyV⟩
    exact (Set.disjoint_left.mp S.disjoint_UV.symm hyV) (hU hyin)

/-- **The bounded side avoids a closed set `T` contained in the trace and lies in the open disc.** -/
theorem pcV_subset_ball_diff {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1)
    {T : Set ℂ} (hT : T ⊆ c.trace) :
    S.V ⊆ Metric.ball (0 : ℂ) 1 \ T := by
  intro z hz
  refine ⟨pcboundedSide_subset_ball S hball hz, fun hzT => ?_⟩
  have : z ∈ S.U ∪ S.V := Or.inr hz
  rw [S.union_eq] at this
  exact this (hT hzT)

/-- **At most one of two distinct components of `int 𝔻 \ T` meets the bounded side.**

If the two components `C`, `C'` cover `int 𝔻 \ T` (so they are all of its components) and are
distinct, then the bounded side `S.V` (preconnected, contained in `int 𝔻 \ T`, non-empty) lies in
one of them, so the other is disjoint from `S.V`. -/
theorem pccomponent_disjoint_of_cover
    {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1)
    {T : Set ℂ} (hT : T ⊆ c.trace)
    {q q' p : ℂ} (hp : p ∈ S.V)
    (hne : connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ≠
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q')
    (hcover : connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ∪
        connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q' = Metric.ball (0 : ℂ) 1 \ T) :
    connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ⊆ S.Vᶜ ∨
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q' ⊆ S.Vᶜ := by
  have hpT : p ∈ Metric.ball (0 : ℂ) 1 \ T := pcV_subset_ball_diff S hball hT hp
  have hmem : p ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ∪
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q' := by rw [hcover]; exact hpT
  have hq_sub : S.V ⊆ Metric.ball (0 : ℂ) 1 \ T := pcV_subset_ball_diff S hball hT
  rcases hmem with hpq | hpq
  · right
    have hSsub : S.V ⊆ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q := by
      rw [connectedComponentIn_eq hpq]
      exact S.preconn_V.subset_connectedComponentIn hp hq_sub
    intro z hz hzV
    exact hne ((connectedComponentIn_eq (hSsub hzV)).trans (connectedComponentIn_eq hz).symm)
  · left
    have hSsub : S.V ⊆ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q' := by
      rw [connectedComponentIn_eq hpq]
      exact S.preconn_V.subset_connectedComponentIn hp hq_sub
    intro z hz hzV
    exact hne ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq (hSsub hzV)).symm)

/-- **Covering and intersection of the closures of the two pieces of a slit region.**

Let `A` be a closed subset of the plane decomposed as `A ⊆ P₁ ∪ P₂ ∪ pccuts`, where `P₁`, `P₂` are
disjoint and avoid `pccuts`, each is open in `A \ pccuts`, and each closure contains `pccuts`.  Then
`closure P₁ ∪ closure P₂ = A` and `closure P₁ ∩ closure P₂ = pccuts`.

This is the abstract form of the statement that the two pieces of the pcannulus `A = 𝔻 \ S.V` cut
along the two crosscuts `pccuts` have closures covering `A` and meeting exactly in `pccuts`; the
geometric inputs are exactly that the pieces are open in `A \ pccuts` (they are its connected
components, which is what the components of `int 𝔻 \ T` give) and that every point of a crosscut is
a limit point of both pieces. -/
theorem pcclosure_union_inter_of_pieces
    {A pccuts P₁ P₂ : Set ℂ} (hA : IsClosed A)
    (hP₁A : P₁ ⊆ A) (hP₂A : P₂ ⊆ A)
    (hP₁c : P₁ ∩ pccuts = ∅) (hP₂c : P₂ ∩ pccuts = ∅)
    (hdisj : Disjoint P₁ P₂)
    (hdecomp : A ⊆ P₁ ∪ P₂ ∪ pccuts)
    (hcl₁ : ∀ x ∈ P₁, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ U ∩ (A \ pccuts) ⊆ P₁)
    (hcl₂ : ∀ x ∈ P₂, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ U ∩ (A \ pccuts) ⊆ P₂)
    (hcuts₁ : pccuts ⊆ closure P₁) (hcuts₂ : pccuts ⊆ closure P₂) :
    closure P₁ ∪ closure P₂ = A ∧ closure P₁ ∩ closure P₂ = pccuts := by
  have hP₁cl : closure P₁ ⊆ A := closure_minimal hP₁A hA
  have hP₂cl : closure P₂ ⊆ A := closure_minimal hP₂A hA
  constructor
  · refine Set.Subset.antisymm (Set.union_subset hP₁cl hP₂cl) ?_
    intro x hx
    have hx' : x ∈ P₁ ∪ P₂ ∪ pccuts := hdecomp hx
    simp only [Set.mem_union] at hx'
    rcases hx' with (h | h) | h
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure h)
    · exact Or.inl (hcuts₁ h)
  · refine Set.Subset.antisymm ?_ (Set.subset_inter hcuts₁ hcuts₂)
    intro x hx
    by_contra hxc
    have hxA : x ∈ A := hP₁cl hx.1
    have hxA' : x ∈ P₁ ∪ P₂ ∪ pccuts := hdecomp hxA
    simp only [Set.mem_union] at hxA'
    rcases hxA' with (h | h) | h
    · obtain ⟨U, hUo, hxU, hUsub⟩ := hcl₁ x h
      have hne : (U ∩ P₂).Nonempty := mem_closure_iff_nhds.mp hx.2 U (hUo.mem_nhds hxU)
      obtain ⟨y, hyU, hyP₂⟩ := hne
      have hyAc : y ∈ A \ pccuts :=
        ⟨hP₂A hyP₂, fun hyc => (Set.eq_empty_iff_forall_notMem.mp hP₂c) y ⟨hyP₂, hyc⟩⟩
      exact Set.disjoint_left.mp hdisj (hUsub ⟨hyU, hyAc⟩) hyP₂
    · obtain ⟨U, hUo, hxU, hUsub⟩ := hcl₂ x h
      have hne : (U ∩ P₁).Nonempty := mem_closure_iff_nhds.mp hx.1 U (hUo.mem_nhds hxU)
      obtain ⟨y, hyU, hyP₁⟩ := hne
      have hyAc : y ∈ A \ pccuts :=
        ⟨hP₁A hyP₁, fun hyc => (Set.eq_empty_iff_forall_notMem.mp hP₁c) y ⟨hyP₁, hyc⟩⟩
      exact (Set.disjoint_left.mp hdisj.symm (hUsub ⟨hyU, hyAc⟩)) hyP₁
    · exact hxc h

/-! ## The traces of the four `4`-arc curves

The two `4`-arc curves `pctgtUpB`, `pctgtDnB` have traces made of the two crosscuts `pccut₁`, `pccut₂`, one
arc of `γ`, and one semicircle of `∂𝔻`.  The semicircle lies on the unit circle, so
`K.trace ∖ ∂𝔻` is the two crosscuts together with the inner `γ`-arc used by `K`.  This is what
lets two different curves of the four be compared as bounded sides of components of the *same*
set `int 𝔻 ∖ T`. -/

open Work.Smooth.SphereJordan (pctgtUpB pctgtDnB pctgtCut₁ pctgtCut₂ pcsrcOuterUp pccut₁ pccut₂ pcperPt)

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The upper outer semicircle lies on the unit circle. -/
theorem pcsrcOuterUp_mem_sphere (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    pcsrcOuterUp S x ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, pcsrcOuterUp, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Work.Smooth.SphereJordan.pcnorm_cutDir]

/-- `pctgtCut₁ S t₁ s₁` maps `[0,1]` into the first crosscut. -/
theorem pctgtCut₁_mem_cut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ y : ℝ}
    (ht : t₁ ≤ s₁) (hy : y ∈ Set.Icc (0 : ℝ) 1) : pctgtCut₁ S t₁ s₁ y ∈ pccut₁ S t₁ s₁ := by
  refine ⟨s₁ + y * (t₁ - s₁), ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hy.1, hy.2, ht]
  · nlinarith [hy.1, hy.2, ht]
  · rw [pctgtCut₁]

/-- `pctgtCut₂ S t₂ s₂` maps `[0,1]` into the second crosscut. -/
theorem pctgtCut₂_mem_cut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₂ s₂ y : ℝ}
    (ht : t₂ ≤ s₂) (hy : y ∈ Set.Icc (0 : ℝ) 1) : pctgtCut₂ S t₂ s₂ y ∈ pccut₂ S t₂ s₂ := by
  refine ⟨s₂ + y * (t₂ - s₂), ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hy.1, hy.2, ht]
  · nlinarith [hy.1, hy.2, ht]
  · rw [pctgtCut₂]

/-- The parameter of the second arc of `pctgtUpB`/`pctgtDnB`, on `[π/2, π]`. -/
theorem pchalfParam_mem {σ : ℝ} (h1 : Real.pi / 2 ≤ σ) (h2 : σ ≤ Real.pi) :
    (σ - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  rw [div_le_one (by positivity)]; linarith

/-- The parameter of the middle arc of `pctgtUpB`/`pctgtDnB`, on `[π, 3π/2]`. -/
theorem pcmidParam_mem {σ : ℝ} (h1 : Real.pi ≤ σ) (h2 : σ ≤ 3 * Real.pi / 2) :
    (σ - Real.pi) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  rw [div_le_one (by positivity)]; linarith

/-- The parameter of the fourth arc of `pctgtUpB`/`pctgtDnB`, on `[3π/2, 2π]`. -/
theorem pclastParam_mem {σ : ℝ} (h1 : 3 * Real.pi / 2 ≤ σ) (h2 : σ ≤ 2 * Real.pi) :
    1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [sub_nonneg, div_le_one (by positivity)]; linarith
  · have h0 : (0:ℝ) ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith

/-- **The trace of `pctgtUpB` with `b = true` lies in `∂𝔻 ∪ pccut₁ ∪ pccut₂ ∪ γ '' Icc θ₂ θ₁`.** -/
theorem pctgtUpB_true_mem_trace (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ ≤ s₁) (ht₂ : t₂ ≤ s₂) {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁) (τ : ℝ) :
    pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂ τ ∈ Metric.sphere (0 : ℂ) 1 ∪
      (pccut₁ S t₁ s₁ ∪ pccut₂ S t₂ s₂ ∪ γ '' Set.Icc θ₂ θ₁) := by
  set σ := pcperPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2 * Real.pi) := Work.SphereJordan.pcperPt_mem τ
  rw [Work.Smooth.SphereJordan.pctgtUpB, ← hσdef]
  rw [if_pos rfl]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    have hmem : pcsrcOuterUp S (σ / (Real.pi / 2)) ∈ Metric.sphere (0 : ℂ) 1 :=
      pcsrcOuterUp_mem_sphere S _
    simp only [Set.mem_union]; tauto
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : pctgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2)) ∈ pccut₂ S t₂ s₂ :=
        pctgtCut₂_mem_cut₂ S ht₂ (pchalfParam_mem (le_of_lt (not_le.mp h1)) h2)
      simp only [Set.mem_union]; tauto
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        obtain ⟨hs0, hs1⟩ := pcmidParam_mem (le_of_lt (not_le.mp h2)) h3
        have hmem : γ.γ (θ₂ + (σ - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂)) ∈ γ '' Set.Icc θ₂ θ₁ :=
          ⟨_, ⟨by linarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ θ₁ - θ₂)],
                 by linarith [mul_le_mul_of_nonneg_right hs1 (by linarith : (0:ℝ) ≤ θ₁ - θ₂)]⟩, rfl⟩
        simp only [Set.mem_union]; tauto
      · rw [if_neg h3]
        have hmem : pctgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) ∈ pccut₁ S t₁ s₁ :=
          pctgtCut₁_mem_cut₁ S ht₁ (pclastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        simp only [Set.mem_union]; tauto

/-- **The trace of `pctgtUpB` with `b = false` lies in `∂𝔻 ∪ pccut₁ ∪ pccut₂ ∪ γ '' Icc (θ₁-2π) θ₂`.** -/
theorem pctgtUpB_false_mem_trace (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ ≤ s₁) (ht₂ : t₂ ≤ s₂) {θ₁ θ₂ : ℝ} (hθ' : θ₁ < θ₂ + 2 * Real.pi) (τ : ℝ) :
    pctgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂ τ ∈ Metric.sphere (0 : ℂ) 1 ∪
      (pccut₁ S t₁ s₁ ∪ pccut₂ S t₂ s₂ ∪ γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) := by
  set σ := pcperPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2 * Real.pi) := Work.SphereJordan.pcperPt_mem τ
  rw [Work.Smooth.SphereJordan.pctgtUpB, ← hσdef]
  rw [if_neg Bool.false_ne_true]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    have hmem : pcsrcOuterUp S (σ / (Real.pi / 2)) ∈ Metric.sphere (0 : ℂ) 1 :=
      pcsrcOuterUp_mem_sphere S _
    simp only [Set.mem_union]; tauto
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : pctgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2)) ∈ pccut₂ S t₂ s₂ :=
        pctgtCut₂_mem_cut₂ S ht₂ (pchalfParam_mem (le_of_lt (not_le.mp h1)) h2)
      simp only [Set.mem_union]; tauto
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        obtain ⟨hs0, hs1⟩ := pcmidParam_mem (le_of_lt (not_le.mp h2)) h3
        have hc : θ₁ - θ₂ - 2 * Real.pi ≤ 0 := by linarith
        have hle : (θ₁ - θ₂ - 2 * Real.pi) ≤
            (σ - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂ - 2 * Real.pi) := by
          simpa using mul_le_mul_of_nonpos_right hs1 hc
        have hge : (σ - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂ - 2 * Real.pi) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hs0 hc
        have hmem : γ.γ (θ₂ + (σ - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂ - 2 * Real.pi)) ∈
            γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂ :=
          ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
        simp only [Set.mem_union]; tauto
      · rw [if_neg h3]
        have hmem : pctgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) ∈ pccut₁ S t₁ s₁ :=
          pctgtCut₁_mem_cut₁ S ht₁ (pclastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        simp only [Set.mem_union]; tauto

/-- **The first crosscut is contained in the range of `pctgtUpB` (with `b = true`).**

The three pieces of the crosscut are reached by three different arcs of `pctgtUpB`: the outer endpoint
`u` by the outer semicircle (`τ = 0`), the inner endpoint `a₁ = γ θ₁` by the middle (`γ`-)arc
(`τ = 3π/2`, where the middle parameter is `1`), and the intermediate points by the fourth (radial)
arc. -/
theorem pccut₁_subset_range_true (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht : t₁ < s₁)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    {θ₁ θ₂ : ℝ} (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pccut₁ S t₁ s₁ ⊆ Set.range (pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₁ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₁ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · -- `σ = t₁`: the inner endpoint, reached by the middle `γ`-arc
      refine ⟨3 * Real.pi / 2, ?_⟩
      have hmem : 3 * Real.pi / 2 ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith, by linarith⟩
      rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem, heq',
        if_neg (by linarith : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith : ¬ (3 * Real.pi / 2 ≤ Real.pi)),
        if_pos (le_refl (3 * Real.pi / 2)), if_pos rfl,
        show θ₂ + (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂) = θ₁ by
          rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by
            rw [div_eq_one_iff_eq (by positivity)]; ring]
          ring,
        hγ₁]
    · -- `t₁ < σ < s₁`: an intermediate point, reached by the fourth (radial) arc
      have hst : (0:ℝ) < s₁ - t₁ := by linarith
      set y : ℝ := (s₁ - σ) / (s₁ - t₁) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by
        rw [hydef, div_lt_one hst]; linarith
      have hys : s₁ + y * (t₁ - s₁) = σ := by
        rw [hydef]; field_simp; ring
      refine ⟨3 * Real.pi / 2 + (1 - y) * (Real.pi / 2), ?_⟩
      have hpos : (0:ℝ) < (1 - y) * (Real.pi / 2) := by nlinarith [hy1, hpi]
      have hmem : 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith, by nlinarith [hy0, hpi]⟩
      rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem,
        if_neg (by linarith : ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi / 2)),
        if_neg (by linarith : ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi)),
        if_neg (by linarith : ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ 3 * Real.pi / 2))]
      rw [Work.Smooth.SphereJordan.pctgtCut₁,
        show 1 - (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2) / (Real.pi / 2) = y by
          rw [show (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2) = (1 - y) * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
          ring,
        hys]
  · -- `σ = s₁`: the outer endpoint `u`, reached by the outer semicircle at `τ = 0`
    refine ⟨0, ?_⟩
    have hmem : (0:ℝ) ∈ Set.Ico (0:ℝ) (2 * Real.pi) := ⟨le_refl 0, by positivity⟩
    rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem, heq,
      if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2),
      show (0:ℝ) / (Real.pi / 2) = 0 by simp, pcsrcOuterUp_zero, hout₁]
  · exact absurd hσ2 (not_le.mpr hgt)

/-- **The second crosscut is contained in the range of `pctgtUpB` (with `b = true`).**

Mirror of `pccut₁_subset_range_true`: the outer endpoint `-u` is reached by the outer semicircle
(`τ = π/2`, where `pcsrcOuterUp S 1 = -pccutDir S`), the inner endpoint `pcbase - t₂·pccutDir` by the second
(radial) arc at `τ = π` (where its parameter is `1`), and the intermediate points by the second arc
with parameter `y := (s₂-σ)/(s₂-t₂) ∈ (0,1)`. -/
theorem pccut₂_subset_range_true (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht : t₂ < s₂)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    {θ₁ θ₂ : ℝ} :
    pccut₂ S t₂ s₂ ⊆ Set.range (pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₂ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₂ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · -- `σ = t₂`: the inner endpoint, reached by the second (radial) arc at `τ = π`
      refine ⟨Real.pi, ?_⟩
      have hmem : Real.pi ∈ Set.Ico (0:ℝ) (2 * Real.pi) := ⟨hpi.le, by linarith⟩
      rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem, heq',
        if_neg (by linarith : ¬ (Real.pi ≤ Real.pi / 2)),
        if_pos le_rfl]
      rw [Work.Smooth.SphereJordan.pctgtCut₂,
        show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by
          rw [div_eq_one_iff_eq (by positivity)]; ring]
      push_cast; ring
    · -- `t₂ < σ < s₂`: an intermediate point of the second arc
      have hst : (0:ℝ) < s₂ - t₂ := by linarith
      set y : ℝ := (s₂ - σ) / (s₂ - t₂) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₂ + y * (t₂ - s₂) = σ := by rw [hydef]; field_simp; ring
      refine ⟨Real.pi / 2 + y * (Real.pi / 2), ?_⟩
      have hpos : (0:ℝ) < y * (Real.pi / 2) := by nlinarith [hy0, hpi]
      have hmem : Real.pi / 2 + y * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith, by nlinarith [hy0, hpi]⟩
      rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem,
        if_neg (by nlinarith [hy0, hpi] : ¬ (Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi / 2)),
        if_pos (by nlinarith [hy1, hpi] : Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi)]
      rw [Work.Smooth.SphereJordan.pctgtCut₂,
        show (Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2) / (Real.pi / 2) = y by
          rw [show Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2 = y * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)],
        hys]
  · -- `σ = s₂`: the outer endpoint `-u`, reached by the outer semicircle at `τ = π/2`
    refine ⟨Real.pi / 2, ?_⟩
    have hmem : Real.pi / 2 ∈ Set.Ico (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
    rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem, heq,
      if_pos le_rfl,
      show Real.pi / 2 / (Real.pi / 2) = 1 by rw [div_self (by positivity : (Real.pi / 2) ≠ 0)],
      Work.SphereJordan.pcsrcOuterUp_one, hout₂]
  · exact absurd hσ2 (not_le.mpr hgt)

/-- **The inner `γ`-arc of `pctgtUpB` (with `b = true`) is contained in its range.**

The interior points are the middle `γ`-arc at `τ = π + s·(π/2)` (`s ∈ (0,1]`), whose parameter
`(τ-π)/(π/2)` is `s`; the initial point `γ θ₂` is the second (radial) arc's endpoint `pctgtCut₂ 1`,
already reached at `τ = π` in `pccut₂_subset_range_true`. -/
theorem pcarcA_subset_range_true (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    γ '' Set.Icc θ₂ θ₁ ⊆ Set.range (pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rintro z ⟨θ, ⟨hθ1, hθ2⟩, rfl⟩
  have hθdiff : (0:ℝ) < θ₁ - θ₂ := by linarith
  set s : ℝ := (θ - θ₂) / (θ₁ - θ₂) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (by linarith) hθdiff.le
  have hs1 : s ≤ 1 := by rw [hsdef, div_le_one hθdiff]; linarith
  have hval : θ₂ + s * (θ₁ - θ₂) = θ := by rw [hsdef]; field_simp; ring
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · -- `s = 0`: the point `γ θ₂`, reached by the second (radial) arc at `τ = π`
    rw [← hs_eq] at hval
    simp only [zero_mul, add_zero] at hval
    refine ⟨Real.pi, ?_⟩
    have hmem : Real.pi ∈ Set.Ico (0:ℝ) (2 * Real.pi) := ⟨hpi.le, by linarith⟩
    rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem,
      if_neg (by linarith : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl,
      Work.Smooth.SphereJordan.pctgtCut₂,
      show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by
        rw [div_eq_one_iff_eq (by positivity)]; ring,
      show s₂ + 1 * (t₂ - s₂) = t₂ from by ring]
    rw [← hval, hγ₂]
  · -- `s > 0`: the middle `γ`-arc at `τ = π + s·(π/2)`
    refine ⟨Real.pi + s * (Real.pi / 2), ?_⟩
    have hpos : (0:ℝ) < s * (Real.pi / 2) := by nlinarith [hs_pos, hpi]
    have hle : s * (Real.pi / 2) ≤ Real.pi / 2 := by nlinarith [hs1, hpi]
    have hmem : Real.pi + s * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
      ⟨by linarith, by linarith [hle]⟩
    rw [Work.Smooth.SphereJordan.pctgtUpB, Work.SphereJordan.pcperPt_self hmem,
      if_neg (by linarith [hpos] : ¬ (Real.pi + s * (Real.pi / 2) ≤ Real.pi / 2)),
      if_neg (by linarith [hpos] : ¬ (Real.pi + s * (Real.pi / 2) ≤ Real.pi)),
      if_pos (by linarith [hle] : Real.pi + s * (Real.pi / 2) ≤ 3 * Real.pi / 2),
      if_pos rfl,
      show θ₂ + (Real.pi + s * (Real.pi / 2) - Real.pi) / (Real.pi / 2) * (θ₁ - θ₂) =
          θ₂ + s * (θ₁ - θ₂) by
        rw [show Real.pi + s * (Real.pi / 2) - Real.pi = s * (Real.pi / 2) from by ring,
          mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)],
      hval]

/-- **`T_up(true) = pccut₁ ∪ pccut₂ ∪ γ '' Icc θ₂ θ₁` is contained in the range of `pctgtUpB` with
`b = true`.** -/
theorem pccuts_arc_subset_range_true (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pccut₁ S t₁ s₁ ∪ pccut₂ S t₂ s₂ ∪ γ '' Set.Icc θ₂ θ₁ ⊆
      Set.range (pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂) :=
  Set.union_subset (Set.union_subset
    (pccut₁_subset_range_true S ht₁ hout₁ hγ₁)
    (pccut₂_subset_range_true S ht₂ hout₂))
    (pcarcA_subset_range_true S hθ hγ₂)

/-- **The trace of `pctgtUpB` with `b = true`, with the unit circle removed.**

Removing `∂𝔻` from the trace leaves exactly the two crosscuts together with the inner arc
`γ '' Icc θ₂ θ₁`.  (The branch endpoints at `σ = π` and `σ = 3π/2` are supplied by the neighbouring
branch, via `2π`-periodicity of `γ` and `hγ₂`.) -/
theorem pctgtUpB_true_trace_diff (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Set.range (pctgtUpB S t₁ s₁ t₂ s₂ true θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (pccut₁ S t₁ s₁ ∪ pccut₂ S t₂ s₂ ∪ γ '' Set.Icc θ₂ θ₁) \ Metric.sphere (0 : ℂ) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hzsp⟩
    obtain ⟨w, hw⟩ := hz
    have h := pctgtUpB_true_mem_trace S ht₁.le ht₂.le hθ w
    rw [hw] at h
    rcases h with h1 | h1
    · exact absurd h1 hzsp
    · exact ⟨h1, hzsp⟩
  · rintro z ⟨hz, hzsp⟩
    exact ⟨pccuts_arc_subset_range_true S ht₁ ht₂ hθ hout₁ hγ₁ hout₂ hγ₂ hz, hzsp⟩

/-- **At most one of two *distinct* components of `int 𝔻 ∖ T` meets the bounded side.**

This is `pccomponent_disjoint_of_cover` without the hypothesis that the two components cover
`int 𝔻 ∖ T`:  distinctness of the two components already suffices, because the bounded side
`S.V` is preconnected and contained in `int 𝔻 ∖ T`, so if it meets one component it is contained in
it, and hence cannot meet the other. -/
theorem pccomponent_disjoint_of_ne {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (hball : ∀ θ : ℝ, ‖c.γ θ‖ < 1)
    {T : Set ℂ} (hT : T ⊆ c.trace)
    {q q' p : ℂ} (hp : p ∈ S.V)
    (hne : connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ≠
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q') :
    connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q ⊆ S.Vᶜ ∨
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q' ⊆ S.Vᶜ := by
  have hq_sub : S.V ⊆ Metric.ball (0 : ℂ) 1 \ T := pcV_subset_ball_diff S hball hT
  -- a point lying in `S.V` and in a component forces `S.V` into that component
  have key : ∀ {x : ℂ}, x ∈ S.V → x ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q →
      S.V ⊆ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q := by
    intro x hx hxq
    rw [connectedComponentIn_eq hxq]
    exact S.preconn_V.subset_connectedComponentIn hx hq_sub
  by_cases hpq : p ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q
  · right
    intro z hz hzV
    have hsz : z ∈ connectedComponentIn (Metric.ball (0 : ℂ) 1 \ T) q := key hp hpq hzV
    exact hne ((connectedComponentIn_eq hsz).trans (connectedComponentIn_eq hz).symm)
  · left
    intro z hz hzV
    exact hpq (key hzV hz hp)

end

end Work.SphereJordan
