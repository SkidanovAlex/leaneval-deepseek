import Mathlib
import Submission.Work.Smooth.SphereJordan.exists_half_spans_defs
import Submission.Work.Smooth.Jordan.All

/-!
# The plane picture of the slit annulus

This file sets up the planar vocabulary in which `Work.Smooth.SphereJordan.half_spans_plane` is
stated.  Let `c : ℝ → ℂ ∪ {∞}` be a simple closed curve, `T : TwoDiscs c` a two-disc datum for it
and `hball : ∀ z, InOpenDisc (T.e z)` the hypothesis that the *inner* disc `range T.e` lies in the
open unit disc.  Then the unit circle `Ω` and the inner curve `Γ` bound an annulus

`A = {‖z‖ < 1} ∖ range T.e`

in the plane, and the two crosscuts `cutSet T w` (the images of the radial arcs of the outer disc
`T.e'` beyond their last exit from the open unit disc) cut it into two halves.

The planar vocabulary is

* `hsCurve T hball` — the plane curve `γ` traced by the inner boundary circle of the annulus
  (so that the inner curve of the annulus is `γ.trace`);
* `hsInner T hball = range (ep T hball)` — the inner closed disc `K`;
* `hsAnnulus T hball = {z | ↑z ∈ openAnnulus T} = {‖z‖ < 1} ∖ K` — the open annulus `A`;
* `hsCut T hball w = {z | ↑z ∈ cutSet T w}` — the cut through `w`;
* `hsSlit T hball w₁ w₂ = {z | ↑z ∈ slitAnnulus T w₁ w₂}` — the annulus with the two cuts removed.

The final theorem `hsSlit_eq` identifies `hsSlit T hball w₁ w₂` with the set appearing in the
statement of `half_spans_plane`, so that the two halves of `hsSlit` are exactly the sets `P₁`, `P₂`
the target asks for.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Metric
open LeanEval.KnotTheory.PardonDistortion

variable {c : ℝ → RiemannSphere}

/-! ## The boundary circle of the model disc -/

/-- The parametrisation `θ ↦ e^{iθ}` of the boundary circle is continuous. -/
theorem continuous_circlePoint_aux : Continuous (circlePoint : ℝ → Disc) := by
  apply Continuous.subtype_mk
  exact (by fun_prop : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I))

/-- The parametrisation `θ ↦ e^{iθ}` of the boundary circle is `2π`-periodic. -/
theorem circlePoint_periodic_aux : Function.Periodic (circlePoint : ℝ → Disc) (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (2 * (Real.pi : ℂ)) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- A point of the Riemann sphere lies in the open unit disc exactly when it is the coercion of a
complex number of norm `< 1`. -/
theorem inOpenDisc_coe_aux (w : ℂ) : InOpenDisc ((w : ℂ) : RiemannSphere) ↔ ‖w‖ < 1 := by
  constructor
  · rintro ⟨u, hu, hu'⟩
    rw [← OnePoint.coe_injective hu']
    exact hu
  · intro hw
    exact ⟨w, hw, rfl⟩

/-! ## The inner boundary curve of the annulus -/

/-- The plane curve traced by the inner boundary circle of the annulus of a two-disc datum whose
inner disc lies in the open unit disc. -/
def hsCurve (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := cpl T hball
  cont := by
    have h : cpl T hball = fun θ => ep T hball (circlePoint θ) :=
      funext (fun θ => cpl_eq_ep_of_circlePoint T hball θ)
    rw [h]
    exact (ep T hball).continuous.comp continuous_circlePoint_aux
  periodic := by
    intro θ
    show cpl T hball (θ + 2 * Real.pi) = cpl T hball θ
    rw [cpl_eq_ep_of_circlePoint T hball (θ + 2 * Real.pi),
      cpl_eq_ep_of_circlePoint T hball θ, circlePoint_periodic_aux θ]

@[simp] theorem hsCurve_apply (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (θ : ℝ) : (hsCurve T hball).γ θ = cpl T hball θ := rfl

/-- **The inner boundary circle of the annulus is a simple closed plane curve.** -/
theorem hsCurve_isSimple (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    (hsCurve T hball).IsSimple := by
  intro a ha b hb hab
  apply T.simple.injOn ha hb
  have h : ((cpl T hball a : ℂ) : RiemannSphere) = ((cpl T hball b : ℂ) : RiemannSphere) :=
    congrArg (fun z : ℂ => ((z : ℂ) : RiemannSphere)) hab
  rwa [cpl_coe, cpl_coe] at h

/-- The trace of the inner boundary curve is the image of the boundary circle under `ep`. -/
theorem hsCurve_trace (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    (hsCurve T hball).trace = ep T hball '' Set.range (circlePoint : ℝ → Disc) := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨circlePoint θ, ⟨θ, rfl⟩, (cpl_eq_ep_of_circlePoint T hball θ).symm⟩
  · rintro ⟨z, ⟨θ, rfl⟩, rfl⟩
    exact ⟨θ, cpl_eq_ep_of_circlePoint T hball θ⟩

/-! ## The plane sets -/

/-- **The inner closed disc** of the annulus, as a set of complex numbers. -/
def hsInner (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) : Set ℂ :=
  Set.range (ep T hball)

/-- The plane annulus between the inner curve and the unit circle. -/
def hsAnnulus (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) : Set ℂ :=
  {z : ℂ | ((z : ℂ) : RiemannSphere) ∈ openAnnulus T}

/-- The cut through `w`, as a set of complex numbers. -/
def hsCut (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) : Set ℂ :=
  {z : ℂ | ((z : ℂ) : RiemannSphere) ∈ cutSet T w}

/-- **The slit annulus**: the plane annulus with the two cuts removed. -/
def hsSlit (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1) : Set ℂ :=
  {z : ℂ | ((z : ℂ) : RiemannSphere) ∈ slitAnnulus T w₁ w₂}

theorem mem_hsCut_iff (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (z : ℂ) :
    z ∈ hsCut T hball w ↔ ((z : ℂ) : RiemannSphere) ∈ cutSet T w := Iff.rfl

/-- The cut is the image of the radial arc of the outer disc beyond its last exit. -/
theorem mem_hsCut_iff' (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (z : ℂ) :
    z ∈ hsCut T hball w ↔
      ∃ t ∈ Set.Ioo (crosscutTime T w) 1,
        T.e' (arcPt w t) = ((z : ℂ) : RiemannSphere) := by
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, hx⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, ht'⟩
    exact ⟨arcPt w t, ⟨t, ht, rfl⟩, ht'⟩

/-- The slit annulus is the annulus with the two cuts removed. -/
theorem hsSlit_def (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1) :
    hsSlit T hball w₁ w₂ = hsAnnulus T hball \ (hsCut T hball w₁ ∪ hsCut T hball w₂) := by
  ext z
  simp only [hsSlit, hsAnnulus, hsCut, slitAnnulus, mem_setOf_eq, mem_sdiff, mem_union]

/-- A point of the plane lies in the inner disc `K` exactly when its image in the sphere lies in the
inner disc `range T.e`. -/
theorem mem_range_T_e_iff (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) (z : ℂ) :
    ((z : ℂ) : RiemannSphere) ∈ Set.range T.e ↔ z ∈ Set.range (ep T hball) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by
      apply OnePoint.coe_injective
      rw [ep_coe T hball w]
      exact hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by rw [← ep_coe T hball w, hw]⟩

/-- **The plane annulus is the open unit disc minus the inner closed disc.** -/
theorem hsAnnulus_eq (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    hsAnnulus T hball = Metric.ball (0 : ℂ) 1 \ hsInner T hball := by
  ext z
  simp only [hsAnnulus, hsInner, mem_openAnnulus, mem_setOf_eq, mem_sdiff, mem_ball,
    dist_zero_right, Set.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(inOpenDisc_coe_aux z).mp h1, fun h => h2 ((mem_range_T_e_iff T hball z).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(inOpenDisc_coe_aux z).mpr h1, fun h => h2 ((mem_range_T_e_iff T hball z).mp h)⟩

/-- The inner closed disc is compact. -/
theorem isCompact_hsInner (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    IsCompact (hsInner T hball) :=
  isCompact_range (ep T hball).continuous

/-- The plane annulus is open. -/
theorem isOpen_hsAnnulus (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    IsOpen (hsAnnulus T hball) := by
  rw [hsAnnulus_eq]
  exact isOpen_ball.sdiff (isCompact_hsInner T hball).isClosed

/-- The crosscut time is non-negative; no nonemptiness hypothesis is needed. -/
theorem crosscutTime_nonneg_aux (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) :
    0 ≤ crosscutTime T w := by
  rcases (arcOutSet T w).eq_empty_or_nonempty with he | hne
  · rw [crosscutTime, he, Real.sSup_empty]
  · obtain ⟨x, hx⟩ := hne
    exact le_trans hx.1.le (le_csSup (arcOutSet_bddAbove T w) hx)

/-- **Beyond the last exit the radial arc of the outer disc is in the open unit disc.**  The "last
exit" is read off the definition of `crosscutTime` as a supremum, so no nonemptiness hypothesis is
needed. -/
theorem hsOut_mem_openDisc (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) {t : ℝ}
    (h1 : crosscutTime T w < t) (h2 : t ≤ 1) : InOpenDisc (T.e' (arcPt w t)) := by
  by_contra hcon
  have ht0 : 0 < t := lt_of_le_of_lt (crosscutTime_nonneg_aux T w) h1
  have hmem : t ∈ arcOutSet T w := ⟨ht0, h2, hcon⟩
  have hle : t ≤ crosscutTime T w := le_csSup (arcOutSet_bddAbove T w) hmem
  linarith

/-- Every point of a cut lies in the open unit disc. -/
theorem hsCut_subset_ball (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) : hsCut T hball w ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  obtain ⟨t, ht, ht'⟩ := (mem_hsCut_iff' T hball w z).mp hz
  rw [Metric.mem_ball, dist_zero_right]
  exact (inOpenDisc_coe_aux z).mp (by rw [← ht']; exact hsOut_mem_openDisc T w ht.1 ht.2.le)

/-- The two cuts are disjoint. -/
theorem disjoint_hsCut (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    {w₁ w₂ : Metric.sphere (0 : ℂ) 1} (hw : w₁ ≠ w₂)
    (hne₁ : (arcOutSet T w₁).Nonempty) (hne₂ : (arcOutSet T w₂).Nonempty) :
    Disjoint (hsCut T hball w₁) (hsCut T hball w₂) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  exact Set.disjoint_left.mp (cutSet_disjoint T hw hne₁ hne₂) h1 h2

/-! ## The inner disc is a closed disc whose boundary is the inner curve -/

/-- The values of `ep T hball` lie in the open unit disc. -/
theorem norm_ep_lt_one (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) (z : Disc) :
    ‖ep T hball z‖ < 1 := by
  obtain ⟨u, hu, hu'⟩ := hball z
  have h : ep T hball z = u := by
    apply OnePoint.coe_injective
    rw [ep_coe T hball z, hu']
  rwa [h]

/-- The map `z ↦ ep T hball z` as a map into the model disc (its values lie in the open unit disc
by `hball`). -/
def epDisc (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) : C(Disc, Disc) where
  toFun z := ⟨ep T hball z, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact (norm_ep_lt_one T hball z).le⟩
  continuous_toFun := Continuous.subtype_mk (ep T hball).continuous (fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact (norm_ep_lt_one T hball z).le)

theorem epDisc_coe (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) (z : Disc) :
    ((epDisc T hball z : Disc) : ℂ) = ep T hball z := rfl

theorem epDisc_injective (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z)) :
    Function.Injective (epDisc T hball) := by
  intro a b hab
  apply ep_injective T hball
  have h : ((epDisc T hball a : Disc) : ℂ) = ((epDisc T hball b : Disc) : ℂ) := congrArg _ hab
  rwa [epDisc_coe, epDisc_coe] at h

/-- **The inner closed disc of the annulus is the closure of the bounded side of its boundary
curve.** -/
theorem hsInner_eq_closure_V (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (S : Work.Smooth.Jordan.PlaneSchoenflies (hsCurve T hball)) :
    hsInner T hball = closure S.V := by
  obtain ⟨h1, -⟩ := disc_spans_schoenflies_clean (γ := hsCurve T hball)
    (fun θ => cpl_norm_lt_one T hball θ) S (epDisc_injective T hball) (fun θ => by
      rw [epDisc_coe, hsCurve_apply]
      exact (cpl_eq_ep_of_circlePoint T hball θ).symm)
  rw [hsInner, ← h1]
  rfl

/-! ## The slit annulus is the set of the statement of `half_spans_plane` -/

/-- **The slit annulus is the set appearing in the statement of `half_spans_plane`.** -/
theorem hsSlit_eq (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1) :
    hsSlit T hball w₁ w₂ =
      {z : ℂ | ‖z‖ < 1 ∧ z ∉ Set.range (ep T hball) ∧
        ((z : ℂ) : RiemannSphere) ∈ openAnnulus T ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₁ ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₂} := by
  ext z
  simp only [hsSlit, slitAnnulus, mem_openAnnulus, mem_setOf_eq, mem_sdiff, mem_union, not_or]
  constructor
  · rintro ⟨⟨h1a, h1b⟩, h2a, h2b⟩
    exact ⟨(inOpenDisc_coe_aux z).mp h1a,
      fun h => h1b ((mem_range_T_e_iff T hball z).mpr h), ⟨h1a, h1b⟩, h2a, h2b⟩
  · rintro ⟨hz1, hzK, ⟨h1a, h1b⟩, h2a, h2b⟩
    exact ⟨⟨h1a, h1b⟩, h2a, h2b⟩

/-!
## Road map for the two halves of the slit annulus

The two target lemmas

* `Work.Smooth.SphereJordan.hsSlit_two_components` — `hsSlit T hball w₁ w₂` is the union of two
  non-empty disjoint open preconnected sets, and
* `Work.Smooth.SphereJordan.hsSlit_closure_spans` — the closures of such sets are the images of
  injective continuous maps of the model disc

are the classical "cut an annulus along two crosscuts" statement for the annulus

`A = hsAnnulus T hball = {‖z‖ < 1} ∖ hsInner T hball`

bounded by the inner curve `Γ = (hsCurve T hball).trace` and the unit circle `Ω`, cut along the two
crosscuts `hsCut T hball wᵢ` (arcs joining `Γ` to `Ω`, with interiors in `A`).

The classical route, which the planar Jordan–Schoenflies theorem (`PlaneHypothesis`, applied to
`hsCurve T hball` to get the Schoenflies disc `K = hsInner T hball` of `Γ`) makes available:

1. form the two four-arc Jordan curves `J₁`, `J₂` whose traces are

   `hsCut w₁ ∪ (arc of Ω) ∪ hsCut w₂ ∪ (arc of Γ)`

   one for each of the two ways of pairing the arc of `Ω` between the outer feet with the arc of
   `Γ` between the inner feet.  The pairing matters: it must be chosen so that the *bounded* side of
   `Jᵢ` is the corresponding half of the annulus (the other pairing gives the union of the two halves
   with the inner disc);
2. each `Vᵢ` (bounded side of `Jᵢ`, obtained from `PlaneHypothesis` as
   `Work.Smooth.Jordan.PlaneSchoenflies.V`) has closure the image of an injective continuous map of
   the disc, because `PlaneSchoenflies.range_e` is exactly that;
3. it therefore suffices to prove `V₁ ⊔ V₂ = hsSlit T hball w₁ w₂`.  Useful ingredients:

   * `Vᵢ ⊆ Metric.ball 0 1` (the far region `{1 < ‖z‖}` is preconnected and avoids `trace Jᵢ`, while
     `Vᵢ` is bounded);
   * a point just inside `Ω` near the interior of the `Ω`-arc of `Jᵢ` lies in `Vᵢ` (locally `Jᵢ`
     agrees with `Ω` there, so the two local sides are the inside and the outside of the ball, and
     the outside contains the far region, hence is the unbounded side);
   * `Vᵢ` is preconnected and avoids `trace Jᵢ`, so connectedness arguments (`PlaneSeparation`) and
     `Work.Smooth.Jordan.plane_separation_preconnected_subset` decide the side of any connected set.
-/

/-!
## Notes towards `hsSlit_two_components` and `hsSlit_closure_spans`

*Two components.*  Both the sphere-level statement (`slitAnnulusTwoHalves`) and the plane
`theta`-graph statement (`planeAnnulusTwoComponents`) are being proved by the team; the plane
statement applies to `hsSlit` after the configuration is moved so that the two boundary discs are
bounded: pick `p` in the slit annulus, use `exists_homeomorph_infty_eq` to get a Möbius map `Φ` of
the sphere with `Φ p = ∞`; both `Φ (hsInner T hball)` and the image of the closed exterior are then
compact subsets of `ℂ`, and the two cuts stay disjoint arcs joining them with interiors outside, so
`planeAnnulusTwoComponents` gives the two components of `Φ '' hsSlit`; pull back along `Φ`.

*Each half is a disc.*  Let `J` be the four-arc Jordan curve made from the two closed cuts and the
two boundary arcs (`discCurve`/`discArc` of `DiscCurve.lean` build the arcs from an embedding of
the disc), let `(U, V, e)` be the `PlaneSchoenflies` datum for `J` that `h : PlaneHypothesis`
provides, so that `Set.range e = closure V`.  If `P` is one of the two halves, then `P` is
preconnected and avoids `trace J`, so `P ⊆ U` or `P ⊆ V`; a point of `P` just inside the unit
circle near the interior of the corresponding arc of `Ω` lies in `V` (locally the trace of `J`
agrees with `Ω`, and the outside local piece is connected to the far region `{1 < ‖z‖}`, which lies
in the unbounded side), so `P ⊆ V`; and `V ⊆ hsSlit` because `V` is preconnected, `V ∩ hsCut = ∅`
(the cuts lie on `trace J`) and `V ∩ hsSlit` is nonempty, open and closed in `V` — it is `V ∖ K`
with `K = hsInner T hball` closed.  Hence `V = P` and `closure P = Set.range e`.
-/


/-! ## The far region lies in the unbounded side of a curve inside the unit disc -/

/-- **The exterior of the unit disc lies in the unbounded side** of a simple closed plane curve
whose trace lies in the closed unit disc.  This is the first step of the side determination: it
shows in particular that the *bounded* side of such a curve is contained in the open unit disc. -/
theorem exterior_subset_sideU {J : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation J)
    (htrace : J.trace ⊆ Metric.closedBall (0 : ℂ) 1) :
    {z : ℂ | 1 < ‖z‖} ⊆ h.U := by
  have hpre : IsPreconnected {z : ℂ | 1 < ‖z‖} :=
    Work.Smooth.Jordan.isPreconnected_exterior_unitBall
  have hsub : {z : ℂ | 1 < ‖z‖} ⊆ J.traceᶜ := by
    rintro z hz ⟨θ, hθ⟩
    have hz' : 1 < ‖z‖ := hz
    have h1 : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, ← hθ] using htrace ⟨θ, hθ⟩
    linarith
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset h hpre hsub with hU | hV
  · exact hU
  · exfalso
    obtain ⟨C, hC⟩ := h.bounded_V.exists_norm_le
    set t : ℝ := max (C + 1) 2 with ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two (le_max_right _ _)
    have hCt : C < t := lt_of_lt_of_le (lt_add_one C) (le_max_left _ _)
    have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht1.le
    have hmem : (t : ℂ) ∈ {z : ℂ | 1 < ‖z‖} := by
      simp only [mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact ht1
    have := hC (t : ℂ) (hV hmem)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at this
    linarith

/-- **The bounded side of a curve inside the closed unit disc is contained in the open unit disc.**
It cannot meet the exterior (which lies in the unbounded side) nor the unit circle (by openness and
the disjointness of the two sides). -/
theorem sideV_subset_ball {J : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation J)
    (htrace : J.trace ⊆ Metric.closedBall (0 : ℂ) 1) :
    h.V ⊆ Metric.ball (0 : ℂ) 1 := by
  have hU := exterior_subset_sideU h htrace
  intro z hzV
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · exact Set.disjoint_left.mp h.disjoint_UV (hU hlt) hzV
  · obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (h.isOpen_V.mem_nhds hzV)
    have hnorm : ‖((1 + ε / 2) • z : ℂ)‖ = 1 + ε / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 + ε / 2), ← heq]
      ring
    have hdist : dist ((1 + ε / 2) • z) z < ε := by
      rw [dist_eq_norm]
      have heq' : (1 + ε / 2) • z - z = (ε / 2) • z := by
        rw [add_smul, one_smul]; ring
      rw [heq', norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2), ← heq]
      linarith
    have hVmem : ((1 + ε / 2) • z : ℂ) ∈ h.V := hε' (by simpa [Metric.mem_ball] using hdist)
    have hexterior : 1 < ‖((1 + ε / 2) • z : ℂ)‖ := by rw [hnorm]; linarith
    exact Set.disjoint_left.mp h.disjoint_UV (hU hexterior) hVmem


/-- **The bounded side of a four-arc curve lies in the slit annulus**, provided it misses the inner
disc.  The hypotheses are exactly the incidence facts of the configuration: the trace of the curve
lies in the closed unit disc, it contains the two cuts, and the bounded side misses the two cuts
(automatic, as the cuts lie on the trace) — so the only non-trivial input is `S.V ∩ hsInner = ∅`,
i.e. that the bounded side does not contain a point of the inner disc. -/
theorem sideV_subset_hsSlit {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w₁ w₂ : Metric.sphere (0 : ℂ) 1)
    {J : Work.Smooth.Jordan.PlaneCurve} (S : Work.Smooth.Jordan.PlaneSchoenflies J)
    (htrace : J.trace ⊆ Metric.closedBall (0 : ℂ) 1)
    (hcuts : hsCut T hball w₁ ∪ hsCut T hball w₂ ⊆ J.trace)
    (hinner : S.V ∩ hsInner T hball = ∅) :
    S.V ⊆ hsSlit T hball w₁ w₂ := by
  intro z hzV
  have hzball : ‖z‖ < 1 := by
    have h := sideV_subset_ball S.toPlaneSeparation htrace hzV
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hVsub : S.V ⊆ J.traceᶜ := by rw [← S.union_eq]; exact Set.subset_union_right
  have hztrace : z ∉ J.trace := fun h => hVsub hzV h
  have hzinner : z ∉ hsInner T hball :=
    fun h => (Set.eq_empty_iff_forall_notMem.mp hinner z) ⟨hzV, h⟩
  have hzcut₁ : z ∉ hsCut T hball w₁ := fun h => hztrace (hcuts (Or.inl h))
  have hzcut₂ : z ∉ hsCut T hball w₂ := fun h => hztrace (hcuts (Or.inr h))
  rw [hsSlit_def, mem_sdiff, mem_union, not_or]
  refine ⟨?_, hzcut₁, hzcut₂⟩
  show ((z : ℂ) : RiemannSphere) ∈ openAnnulus T
  rw [openAnnulus, mem_setOf_eq]
  exact ⟨(inOpenDisc_coe_aux z).mpr hzball, fun h => hzinner ((mem_range_T_e_iff T hball z).mp h)⟩

/-! ## Two components of the plane slit annulus -/

theorem isOpen_pullback_coe {Q : Set RiemannSphere} (hQ : IsOpen Q) :
    IsOpen ((↑) ⁻¹' Q : Set ℂ) :=
  hQ.preimage OnePoint.continuous_coe



/-- **The preimage of a non-empty preconnected set of the sphere under the coercion is
preconnected**, provided the set lies in the finite part.  The coercion is an open embedding, hence
a homeomorphism onto its range, and it identifies the subtype over the pullback with the subtype
over the set itself. -/
theorem isPreconnected_preimage_coe {Q : Set RiemannSphere} (hQ : IsPreconnected Q)
    (hQne : Q.Nonempty) (hsub : Q ⊆ Set.range ((↑) : ℂ → RiemannSphere)) :
    IsPreconnected ((↑) ⁻¹' Q : Set ℂ) := by
  have hEmb : Topology.IsEmbedding ((↑) : ℂ → RiemannSphere) :=
    OnePoint.isOpenEmbedding_coe.toIsEmbedding
  -- the homeomorphism from the subtype over `Q` to the subtype over the pullback
  let g : ↥Q → ↥(Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) :=
    fun y => ⟨⟨y.1, hsub y.2⟩, y.2⟩
  let f : ↥(Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) → ↥Q :=
    fun x => ⟨Subtype.val x.1, x.2⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp continuous_subtype_val
  let ψ : ↥Q ≃ₜ ↥(Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) :=
    { toFun := g, invFun := f
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      continuous_toFun := hg, continuous_invFun := hf }
  -- `Q` is connected, so its homeomorphic copy is
  have hcc : ConnectedSpace ↥Q := isConnected_iff_connectedSpace.mp ⟨hQne, hQ⟩
  have hcc' : ConnectedSpace ↥(Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) :=
    (Homeomorph.connectedSpace_iff ψ).mp hcc
  have hpre : IsPreconnected (Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) :=
    (isConnected_iff_connectedSpace.mpr hcc').isPreconnected
  have hEq : ((↑) ⁻¹' Q : Set ℂ)
      = ⇑hEmb.toHomeomorph ⁻¹' (Subtype.val ⁻¹' Q : Set (Set.range ((↑) : ℂ → RiemannSphere))) := by
    ext z
    rfl
  rw [hEq]
  exact (Homeomorph.isPreconnected_preimage hEmb.toHomeomorph).mpr hpre

/-! ## An explicit point of the bounded side, and the connectedness criterion for the side -/

/-- **The centre of the spanning disc lies in the bounded side.** -/
theorem e_zero_mem_V {J : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies J) :
    S.e 0 ∈ S.V := by
  rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
  exact ⟨0, by simp, rfl⟩

/-- **A preconnected set avoiding the trace and meeting the centre of the spanning disc lies in the
bounded side.**  This is the criterion used to determine on which side of a four-arc curve a half of
the slit annulus lies: it suffices to connect a point of the half to the explicit point `S.e 0` by a
connected set avoiding the trace. -/
theorem subset_sideV_of_preconnected {J : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies J) {W : Set ℂ}
    (hW : IsPreconnected W) (hWsub : W ⊆ J.traceᶜ) (hWe : (S.e 0 : ℂ) ∈ W) :
    W ⊆ S.V := by
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S.toPlaneSeparation hW hWsub with
    hU | hV
  · exfalso
    exact Set.disjoint_left.mp S.disjoint_UV (hU hWe) (e_zero_mem_V S)
  · exact hV

/-- The same criterion for a point reached by a continuous path from the centre. -/
theorem mem_sideV_of_path {J : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies J) {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hsub : Set.range γ ⊆ J.traceᶜ) (hγ0 : γ ⟨0, by norm_num⟩ = (S.e 0 : ℂ)) {t : Set.Icc (0 : ℝ) 1} :
    γ t ∈ S.V := by
  have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hmem : (S.e 0 : ℂ) ∈ Set.range γ := ⟨⟨0, by norm_num⟩, hγ0⟩
  exact subset_sideV_of_preconnected S hpre hsub hmem ⟨t, rfl⟩

end

end Work.Smooth.SphereJordan
