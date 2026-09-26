import Mathlib
import Submission.Work.BoxShrink.PinchOff.PlaneCover
import Submission.Work.BoxShrink.PinchOff.IB.Pieces
import Submission.Work.BoxShrink.PinchOff.side_of_compact_sheet
import Submission.Work.BoxShrink.PinchOff.exists_lift_discRegion
import Submission.Work.SurgeryInvariance.All
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.OpenImageAux

/-!
# The lifted translates of a disc of the surface are the filled lifted Jordan domains

This file proves `Work.BoxShrink.PinchOff.lifted_boundary_structure`: the preimage in the parameter
plane of an embedded disc `D` of the surface is the disjoint union of the lattice translates of the
closed bounded side of the lift of its boundary circle.

The parameter plane of the torus is the complex plane `ℂ` (`Work.BoxShrink.PinchOff.planePsi`), and
the parametrisation is a covering map of `ℂ` onto the surface with deck group the period lattice
`2π(ℤ + iℤ)` (`Submission/Work/BoxShrink/PinchOff/PlaneCover.lean`).

Let `D` be an embedded disc of the surface — so `𝔻 ≅ D.carrier` — and `γ` its boundary circle,
lifted to a `2π`-periodic simple closed plane curve `c : t ↦ liftMap L t` through `planePsi P`.
Since `𝔻` is simply connected, every point `z` of the preimage of `D.carrier` lies on a *sheet*: a
continuous injective map `s : 𝔻 → ℂ` with `planePsi P (s w) = D.e w` and `s w₀ = z`.  The boundary
circle of that sheet is a translate `c.trace + ν` of the lift of `γ` (any two lifts of `γ` differ by
a period), and the sheet is a compact subset of `ℂ` whose `c.trace + ν`-complement is the image of
the open disc, which is open in `ℂ` and preconnected; `side_of_compact_sheet` then identifies the
sheet with the closure of one of the two sides of the translate of `c`, and only the bounded side is
compact.  This gives the equality; the disjointness of the translates follows because the projection
is injective on each sheet.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

set_option linter.unusedVariables false

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Elementary facts about the plane picture -/

theorem continuous_circlePoint' :
    Continuous (fun θ : ℝ => Work.Smooth.Jordan.circlePoint θ) := by
  have h1 : Continuous fun θ : ℝ => (⟨Complex.exp ((θ : ℂ) * Complex.I),
      by rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I]⟩ :
      Work.Smooth.Jordan.Disc) := by
    refine Continuous.subtype_mk ?_ (fun θ => by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I])
    fun_prop
  convert h1 using 1
  funext θ
  exact Subtype.ext (Work.Smooth.Jordan.circlePoint_coe θ)

theorem norm_circlePoint' (θ : ℝ) :
    ‖(Work.Smooth.Jordan.circlePoint θ : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The trace of a closed plane curve is compact. -/
theorem isCompact_trace' (c : Work.Smooth.Jordan.PlaneCurve) : IsCompact c.trace := by
  rw [Work.Smooth.Jordan.PlaneCurve.trace_eq_image_Icc]
  exact isCompact_Icc.image_of_continuousOn c.cont.continuousOn

/-- **The unbounded side of a Jordan separation of a plane curve is unbounded.** -/
theorem not_isBounded_planeSeparation_U {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation c) : ¬ Bornology.IsBounded h.U := by
  intro hU
  have htr : Bornology.IsBounded c.trace := (isCompact_trace' c).isBounded
  have huniv : Bornology.IsBounded (Set.univ : Set ℂ) := by
    rw [← Set.union_compl_self c.trace, ← h.union_eq]
    exact htr.union (hU.union h.bounded_V)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp huniv
  have hmem := hr (Set.mem_univ ((r + 1 : ℝ) : ℂ))
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hmem
  have h1 : r + 1 ≤ |r + 1| := le_abs_self _
  linarith [abs_nonneg (r + 1)]

/-! ## Lifts of the boundary circle of a disc -/

/-- A continuous map of the closed disc to the plane which *projects* to the parametrisation of
the disc `D`: a sheet of the preimage of the carrier of `D`. -/
def ProjectsToDisc {P : Work.CoreTopology.ParamTorus} (D : Work.SurgeryInvariance.DiscRegion P)
    (s : Work.Smooth.Jordan.Disc → ℂ) : Prop :=
  ∀ w : Work.Smooth.Jordan.Disc, planePsi P (s w) = D.e w

theorem injective_of_projects {D : Work.SurgeryInvariance.DiscRegion P}
    {s : Work.Smooth.Jordan.Disc → ℂ} (hproj : ProjectsToDisc D s) : Function.Injective s := by
  intro w w' hww
  refine D.inj ?_
  rw [← hproj w, hww, hproj w']

/-- **A sheet of the disc has the same boundary circle as the given lift `c`**, up to a period: the
curve `t ↦ s (circlePoint t)` is a lift of `γ` through the covering, and any two lifts of a curve
through a covering differ by a constant, which is a period lattice element. -/
theorem lift_boundary_eq {D : Work.SurgeryInvariance.DiscRegion P}
    {γ : Work.CoreTopology.ClosedCurve P}
    (hγ : ∀ t : ℝ, γ.γ t = D.e (Work.Smooth.Jordan.circlePoint t))
    {L : Work.CoreTopology.LiftOf P γ}
    {s : Work.Smooth.Jordan.Disc → ℂ} (hs : Continuous s) (hproj : ProjectsToDisc D s) :
    ∃ ν ∈ periodLattice, ∀ t : ℝ, s (Work.Smooth.Jordan.circlePoint t) = liftMap L t + ν := by
  set ν : ℂ := s (Work.Smooth.Jordan.circlePoint 0) - liftMap L 0 with hν
  have hνmem : ν ∈ periodLattice := by
    refine sub_mem_periodLattice_of_planePsi_eq (P := P) ?_
    show planePsi P (liftMap L 0) = planePsi P (s (Work.Smooth.Jordan.circlePoint 0))
    rw [planePsi_liftMap, hproj (Work.Smooth.Jordan.circlePoint 0), hγ 0]
  have h1c : Continuous (fun t : ℝ => s (Work.Smooth.Jordan.circlePoint t)) :=
    hs.comp continuous_circlePoint'
  have h2c : Continuous (fun t : ℝ => liftMap L t + ν) :=
    (continuous_liftMap L).add continuous_const
  have hcomp : planeCover P ∘ (fun t : ℝ => s (Work.Smooth.Jordan.circlePoint t)) =
      planeCover P ∘ (fun t : ℝ => liftMap L t + ν) := by
    funext t
    apply Subtype.ext
    simp only [Function.comp_apply, planeCover_coe]
    rw [hproj (Work.Smooth.Jordan.circlePoint t),
      planePsi_add_periodLattice P (liftMap L t) ν hνmem, planePsi_liftMap, hγ t]
  have hfun := (isCoveringMap_planeCover P).eq_of_comp_eq h1c h2c hcomp 0 (by rw [hν]; ring)
  exact ⟨ν, hνmem, fun t => congrFun hfun t⟩

/-! ## Sheets are the closures of the bounded sides -/

/-- **A sheet of the disc is the closure of a translate of the bounded side of the lifted boundary
circle.**  The sheet `s '' 𝔻` is compact and the complement of the boundary circle inside it is the
image of the open disc, which is open in the plane and preconnected; the Jordan separation of the
translate `c.trace + ν` of the lifted boundary curve then forces it to be one of the two sides, and
only the bounded one can be compact. -/
theorem sheet_eq_closure (s : Work.Smooth.Jordan.Disc → ℂ) (hs : Continuous s)
    (hinj : Function.Injective s)
    {D : Work.SurgeryInvariance.DiscRegion P} (hproj : ProjectsToDisc D s)
    {γ : Work.CoreTopology.ClosedCurve P}
    (hγ : ∀ t : ℝ, γ.γ t = D.e (Work.Smooth.Jordan.circlePoint t))
    {L : Work.CoreTopology.LiftOf P γ} {c : Work.Smooth.Jordan.PlaneCurve}
    (hc : ∀ t : ℝ, c.γ t = liftMap L t) (h : Work.Smooth.Jordan.PlaneSeparation c) :
    ∃ ν ∈ periodLattice, Set.range s = {z : ℂ | z - ν ∈ closure h.V} := by
  obtain ⟨ν, hνmem, hbdy⟩ := lift_boundary_eq (L := L) hγ hs hproj
  refine ⟨ν, hνmem, ?_⟩
  -- the curve `J = c.trace + ν` of the Jordan separation of the translate
  have hJc : IsCompact {z : ℂ | z - ν ∈ c.trace} := by
    have h1 : IsCompact ((fun z : ℂ => z + ν) '' c.trace) :=
      (isCompact_trace' c).image (continuous_id.add continuous_const)
    have hset : {z : ℂ | z - ν ∈ c.trace} = (fun z : ℂ => z + ν) '' c.trace := by
      ext z
      constructor
      · intro h
        exact ⟨z - ν, h, by ring⟩
      · rintro ⟨y, hy, hyz⟩
        rw [← hyz]
        show (y + ν) - ν ∈ c.trace
        rwa [show (y + ν) - ν = y from by ring]
    rwa [hset]
  have hUo : IsOpen {z : ℂ | z - ν ∈ h.U} :=
    h.isOpen_U.preimage (continuous_id.sub continuous_const)
  have hVo : IsOpen {z : ℂ | z - ν ∈ h.V} :=
    h.isOpen_V.preimage (continuous_id.sub continuous_const)
  have htrans : ∀ S : Set ℂ, {z : ℂ | z - ν ∈ S} = (fun z : ℂ => z + ν) '' S := by
    intro S
    ext z
    constructor
    · intro h
      exact ⟨z - ν, h, by ring⟩
    · rintro ⟨y, hy, hyz⟩
      rw [← hyz]
      show (y + ν) - ν ∈ S
      rwa [show (y + ν) - ν = y from by ring]
  have hUpc : IsPreconnected {z : ℂ | z - ν ∈ h.U} := by
    rw [htrans h.U]
    exact h.preconn_U.image _ (continuous_id.add continuous_const).continuousOn
  have hVpc : IsPreconnected {z : ℂ | z - ν ∈ h.V} := by
    rw [htrans h.V]
    exact h.preconn_V.image _ (continuous_id.add continuous_const).continuousOn
  have hUne : ({z : ℂ | z - ν ∈ h.U}).Nonempty := by
    obtain ⟨y, hy⟩ := h.nonempty_U
    exact ⟨y + ν, by simpa using hy⟩
  have hVne : ({z : ℂ | z - ν ∈ h.V}).Nonempty := by
    obtain ⟨y, hy⟩ := h.nonempty_V
    exact ⟨y + ν, by simpa using hy⟩
  have hdisj : Disjoint {z : ℂ | z - ν ∈ h.U} {z : ℂ | z - ν ∈ h.V} := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    exact Set.disjoint_left.mp h.disjoint_UV hzU hzV
  have hunion : {z : ℂ | z - ν ∈ h.U} ∪ {z : ℂ | z - ν ∈ h.V} =
      {z : ℂ | z - ν ∈ c.trace}ᶜ := by
    ext z
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro (hU | hV) htr
      · have h1 : z - ν ∈ c.traceᶜ := by rw [← h.union_eq]; exact Or.inl hU
        exact h1 htr
      · have h1 : z - ν ∈ c.traceᶜ := by rw [← h.union_eq]; exact Or.inr hV
        exact h1 htr
    · intro hneg
      by_contra hcon
      have h1 : z - ν ∈ h.U ∪ h.V := by rw [h.union_eq]; exact hneg
      exact hcon h1
  -- the sheet, with the boundary circle removed, is the image of the open disc
  have hAJ : Set.range s \ {z : ℂ | z - ν ∈ c.trace} =
      s '' {w : Work.Smooth.Jordan.Disc | ‖(w : ℂ)‖ < 1} := by
    ext z
    constructor
    · rintro ⟨⟨w, rfl⟩, hzJ⟩
      refine ⟨w, ?_, rfl⟩
      by_contra hw
      have hwle : ‖(w : ℂ)‖ ≤ 1 := by
        have h := w.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hw1 : ‖(w : ℂ)‖ = 1 := le_antisymm hwle (not_lt.mp hw)
      obtain ⟨t, ht⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w hw1
      exact hzJ ⟨t, by rw [hc t, ← ht, hbdy t]; ring⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, ?_⟩
      rintro ⟨t, ht⟩
      have hsw : s w = s (Work.Smooth.Jordan.circlePoint t) := by
        rw [hbdy t, ← hc t, ht]
        ring
      have hwt : w = Work.Smooth.Jordan.circlePoint t := hinj hsw
      have hw1 : ‖(Work.Smooth.Jordan.circlePoint t : ℂ)‖ < 1 := by rw [← hwt]; exact hw
      rw [norm_circlePoint'] at hw1
      exact lt_irrefl 1 hw1
  have hAopen : Set.range s \ {z : ℂ | z - ν ∈ c.trace} ⊆ interior (Set.range s) := by
    rw [hAJ]
    rintro z ⟨w, hw, rfl⟩
    exact interior_mono (Set.image_subset_range _ _)
      (Work.Smooth.SphereJordan.mem_interior_image_of_norm_lt_one ⟨s, hs⟩ hinj w hw)
  have hAdense : Set.range s ⊆ closure (Set.range s \ {z : ℂ | z - ν ∈ c.trace}) := by
    rw [hAJ]
    rintro z ⟨w, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp (hs.continuousAt (x := w)) ε hε
    have hwle : ‖(w : ℂ)‖ ≤ 1 := by
      have h := w.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    set η : ℝ := min (δ / (2 * (1 + ‖(w : ℂ)‖))) (1 / 2) with hη
    have hηpos : 0 < η := by
      rw [hη]
      exact lt_min (by positivity) (by norm_num)
    have hηle : η ≤ δ / (2 * (1 + ‖(w : ℂ)‖)) := by
      rw [hη]; exact min_le_left _ _
    have hηlt : η < 1 := by
      have h2 : η ≤ 1 / 2 := by rw [hη]; exact min_le_right _ _
      linarith
    have hvnorm : ‖((1 - η : ℝ) : ℂ) * (w : ℂ)‖ < 1 := by
      have h2 : (0 : ℝ) ≤ 1 - η := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
      have h4 : (1 - η) * ‖(w : ℂ)‖ ≤ (1 - η) * 1 := mul_le_mul_of_nonneg_left hwle h2
      linarith
    have hvm : ((1 - η : ℝ) : ℂ) * (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hvnorm.le
    have hvd : dist (⟨((1 - η : ℝ) : ℂ) * (w : ℂ), hvm⟩ : Work.Smooth.Jordan.Disc) w < δ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      have hvsub : ((1 - η : ℝ) : ℂ) * (w : ℂ) - (w : ℂ) = ((-η : ℝ) : ℂ) * (w : ℂ) := by
        push_cast
        ring
      rw [hvsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hηpos]
      have hden : (0 : ℝ) < 2 * (1 + ‖(w : ℂ)‖) := by positivity
      have hfrac : ‖(w : ℂ)‖ / (2 * (1 + ‖(w : ℂ)‖)) < 1 := by
        rw [div_lt_one hden]
        linarith
      calc η * ‖(w : ℂ)‖
          ≤ (δ / (2 * (1 + ‖(w : ℂ)‖))) * ‖(w : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hηle (norm_nonneg _)
        _ = δ * (‖(w : ℂ)‖ / (2 * (1 + ‖(w : ℂ)‖))) := by ring
        _ < δ * 1 := mul_lt_mul_of_pos_left hfrac hδpos
        _ = δ := by ring
    refine ⟨s (⟨((1 - η : ℝ) : ℂ) * (w : ℂ), hvm⟩ : Work.Smooth.Jordan.Disc), ?_, ?_⟩
    · refine ⟨(⟨((1 - η : ℝ) : ℂ) * (w : ℂ), hvm⟩ : Work.Smooth.Jordan.Disc), ?_, rfl⟩
      simpa using hvnorm
    · rw [dist_comm]
      exact hδ hvd
  have hAc : IsCompact (Set.range s) := isCompact_range hs
  have hAne : (Set.range s \ {z : ℂ | z - ν ∈ c.trace}).Nonempty := by
    refine ⟨s (⟨0, by simp⟩ : Work.Smooth.Jordan.Disc), ?_⟩
    rw [hAJ]
    exact ⟨⟨0, by simp⟩, by simp, rfl⟩
  have hApc : IsPreconnected (Set.range s \ {z : ℂ | z - ν ∈ c.trace}) := by
    rw [hAJ]
    refine IsPreconnected.image ?_ s hs.continuousOn
    have hW : IsPathConnected
        (Subtype.val ⁻¹' (Metric.ball (0 : ℂ) 1 ∩ Metric.closedBall (0 : ℂ) 1) :
          Set Work.Smooth.Jordan.Disc) :=
      ((convex_ball (0 : ℂ) 1).inter (convex_closedBall (0 : ℂ) 1)).isPathConnected
        ⟨0, by simp [Metric.mem_ball]⟩ |>.preimage_coe (fun y hy => hy.2)
    have hset : {w : Work.Smooth.Jordan.Disc | ‖(w : ℂ)‖ < 1} =
        Subtype.val ⁻¹' (Metric.ball (0 : ℂ) 1 ∩ Metric.closedBall (0 : ℂ) 1) := by
      ext w
      have hw2 : ‖(w : ℂ)‖ ≤ 1 := by
        have h := w.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      constructor
      · intro hw
        exact ⟨by rwa [Metric.mem_ball, dist_zero_right], by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hw2⟩
      · rintro ⟨h1, -⟩
        have h := h1
        rwa [Metric.mem_ball, dist_zero_right] at h
    rw [hset]
    exact hW.isConnected.2
  have hside := side_of_compact_sheet hUo hVo hUpc hVpc hUne hVne hdisj hunion hJc.isClosed
    hAc hAne hApc hAopen hAdense
  -- the closure of a translate of a side is the translate of its closure
  have hclU : closure {z : ℂ | z - ν ∈ h.U} = {z : ℂ | z - ν ∈ closure h.U} := by
    rw [htrans h.U, htrans (closure h.U)]
    simpa using ((Homeomorph.addRight ν).image_closure h.U).symm
  have hclV : closure {z : ℂ | z - ν ∈ h.V} = {z : ℂ | z - ν ∈ closure h.V} := by
    rw [htrans h.V, htrans (closure h.V)]
    simpa using ((Homeomorph.addRight ν).image_closure h.V).symm
  rcases hside with hV | hU
  · rw [hV, hclV]
  · exfalso
    have hUnb : ¬ Bornology.IsBounded ((fun z : ℂ => z + ν) '' h.U) := by
      intro hb
      refine not_isBounded_planeSeparation_U h ?_
      obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
      refine (Metric.isBounded_iff_subset_closedBall (-ν)).mpr ⟨r, fun y hy => ?_⟩
      have h1 : y + ν ∈ (fun z : ℂ => z + ν) '' h.U := ⟨y, hy, rfl⟩
      have h2 := hr h1
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa only [sub_neg_eq_add] using h2
    have hUnb2 : ¬ Bornology.IsBounded (closure ((fun z : ℂ => z + ν) '' h.U)) :=
      fun hb => hUnb (hb.subset subset_closure)
    refine hUnb2 ?_
    rw [← htrans h.U, ← hU]
    exact hAc.isBounded

/-! ## The main theorem -/

/-- **The lifted translates of a disc of the surface are the filled Jordan domains of the lifts of
its boundary circle.**

`D` is an embedded disc of the parametrised torus `P`, `γ` its boundary circle read as a closed
curve of `P` (`γ.γ t = D.e (circlePoint t)`), `L` a lift of `γ` to the parameter plane whose winding
vanishes (it exists since `γ` bounds `D`, so `γ` is inessential), `c` the resulting `2π`-periodic
plane curve (`c.γ t = liftMap L t`, a simple closed plane curve), and `h` a Jordan separation datum
for `c` (`h.V` the bounded side).

Then the preimage in the plane of the closed disc `D.carrier` is the disjoint union of the lattice
translates of the closed bounded side of `c`:

  `Xtilde P D.carrier = ⋃ ν ∈ periodLattice, {z | z - ν ∈ closure h.V}`,

and distinct translates are disjoint.

This is the statement that the lift of the disc is the *filled* lifted curve: the bounded side of
the lifted boundary circle is exactly the lifted disc.  The ingredients are `inj_mod` (so
`planePsi` is the covering with deck group `periodLattice`, hence `Xtilde` is `periodLattice`
invariant), the fact that `D.carrier ≅ 𝔻` is compact and simply connected (so each component of the
preimage is a compact disc bounded by a translate of `c.trace`, hence the bounded side), and the
disjointness of the translates (a translate meeting the bounded side `h.V` would put two points
differing by a nonzero lattice vector in one sheet, impossible since `h.V` is bounded). -/
theorem lifted_boundary_structure
    {P : Work.CoreTopology.ParamTorus} (D : Work.SurgeryInvariance.DiscRegion P)
    (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ.γ t = D.e (Work.Smooth.Jordan.circlePoint t))
    (L : Work.CoreTopology.LiftOf P γ) (hL : L.winding = (0, 0))
    (c : Work.Smooth.Jordan.PlaneCurve)
    (hc : ∀ t : ℝ, c.γ t = Work.BoxShrink.PinchOff.liftMap L t)
    (h : Work.Smooth.Jordan.PlaneSeparation c) :
    Work.BoxShrink.PinchOff.Xtilde P D.carrier =
      ⋃ ν ∈ Work.BoxShrink.PinchOff.periodLattice, {z : ℂ | z - ν ∈ closure h.V} ∧
    (∀ ν μ : ℂ, ν ∈ Work.BoxShrink.PinchOff.periodLattice →
      μ ∈ Work.BoxShrink.PinchOff.periodLattice → ν ≠ μ →
      Disjoint {z : ℂ | z - ν ∈ closure h.V} {z : ℂ | z - μ ∈ closure h.V}) := by
  -- a base point of the disc and a lift of it
  obtain ⟨z₀, hz₀⟩ : ∃ z : ℂ, planePsi P z = D.e (⟨0, by simp⟩ : Work.Smooth.Jordan.Disc) :=
    (mem_range_planePsi_iff P).mpr (D.mem _)
  obtain ⟨s₀, hs₀c, -, hs₀proj⟩ := exists_lift_discRegion P D z₀ ⟨0, by simp⟩ hz₀
  have hs₀inj : Function.Injective s₀ := injective_of_projects hs₀proj
  obtain ⟨ν₀, hν₀mem, hsheet₀⟩ := sheet_eq_closure s₀ hs₀c hs₀inj hs₀proj hγ hc h
  -- the projection is injective on the closed bounded side
  have hinjV : ∀ {a a' : ℂ}, a ∈ closure h.V → a' ∈ closure h.V →
      planePsi P a = planePsi P a' → a = a' := by
    intro a a' ha ha' heq
    have h1 : a + ν₀ ∈ Set.range s₀ := by
      rw [hsheet₀]
      simpa using ha
    have h2 : a' + ν₀ ∈ Set.range s₀ := by
      rw [hsheet₀]
      simpa using ha'
    obtain ⟨w, hw⟩ := h1
    obtain ⟨w', hw'⟩ := h2
    have hDw : D.e w = D.e w' := by
      calc D.e w = planePsi P (s₀ w) := (hs₀proj w).symm
        _ = planePsi P (a + ν₀) := by rw [hw]
        _ = planePsi P a := planePsi_add_periodLattice P a ν₀ hν₀mem
        _ = planePsi P a' := heq
        _ = planePsi P (a' + ν₀) := (planePsi_add_periodLattice P a' ν₀ hν₀mem).symm
        _ = planePsi P (s₀ w') := by rw [hw']
        _ = D.e w' := hs₀proj w'
    have hww : w = w' := D.inj hDw
    rw [show a = s₀ w - ν₀ from by rw [hw]; ring,
      show a' = s₀ w' - ν₀ from by rw [hw']; ring, hww]
  refine ⟨?_, ?_⟩
  · -- every point of the preimage of the disc lies in a translate of the closed bounded side
    ext z
    constructor
    · intro hz
      rw [mem_Xtilde] at hz
      obtain ⟨w, hw⟩ := hz
      obtain ⟨s, hsc, hsbase, hsproj⟩ := exists_lift_discRegion P D z w hw.symm
      have hsinj : Function.Injective s := injective_of_projects hsproj
      obtain ⟨ν, hνmem, hsheet⟩ := sheet_eq_closure s hsc hsinj hsproj hγ hc h
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      refine ⟨ν, hνmem, ?_⟩
      have hzA : z ∈ Set.range s := ⟨w, hsbase⟩
      rwa [hsheet] at hzA
    · rintro hz
      obtain ⟨ν, hνmem, hzV⟩ :
          ∃ ν ∈ Work.BoxShrink.PinchOff.periodLattice, z - ν ∈ closure h.V := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hz
      rw [mem_Xtilde]
      have hmem : z - ν + ν₀ ∈ Set.range s₀ := by
        rw [hsheet₀]
        simpa using hzV
      obtain ⟨w, hw⟩ := hmem
      have hkey : planePsi P (z - ν) = D.e w := by
        calc planePsi P (z - ν) = planePsi P ((z - ν) + ν₀) :=
              (planePsi_add_periodLattice P (z - ν) ν₀ hν₀mem).symm
          _ = planePsi P (s₀ w) := by rw [hw]
          _ = D.e w := hs₀proj w
      have hper : planePsi P (z - ν) = planePsi P z := by
        have h := planePsi_add_periodLattice P (z - ν) ν hνmem
        rw [show (z - ν) + ν = z from by ring] at h
        exact h.symm
      rw [← hper]
      exact ⟨w, hkey.symm⟩
  · -- distinct translates are disjoint
    intro ν μ hν hμ hne
    rw [Set.disjoint_left]
    intro z hz hz'
    refine hne ?_
    have hEq : z - ν = z - μ :=
      hinjV (by simpa using hz) (by simpa using hz') (by
        have hdiff : (z - μ) - (z - ν) ∈ periodLattice := by
          have h : (z - μ) - (z - ν) = ν - μ := by ring
          rw [h]
          exact periodLattice_sub_mem hν hμ
        exact planePsi_eq_of_sub_mem_periodLattice hdiff)
    have h2 : z - (z - ν) = z - (z - μ) := congrArg (fun t : ℂ => z - t) hEq
    rw [sub_sub_cancel, sub_sub_cancel] at h2
    exact h2

end

end Work.BoxShrink.PinchOff
