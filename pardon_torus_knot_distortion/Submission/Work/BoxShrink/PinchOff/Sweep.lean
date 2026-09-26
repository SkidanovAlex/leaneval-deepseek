import Submission.Work.BoxShrink.PinchOff.Drop
import Submission.Work.BoxShrink.PinchOff.upperRegion_rank_zero_or_two

/-!
# The one-parameter sweep of the pinch, and `DropCase` from a single jump-level analysis

`Drop.lean` isolates the whole remaining content of the area as `DropCase`: at a transverse,
closed-tame configuration whose box sphere (`hS`) and slice (`hZ`) carry no essential loop, if the
two half-regions together carry no essential loop then the box region is at most one-dimensional.

This module runs **Pardon's sweep** in the parameter of the pinch.  Instead of the two endpoint
regions only, one keeps the whole one-parameter family of *truncations*

  `OmegaCut ψ s c σ u t = Omega ψ s c σ ∩ {planeCoord c σ u < t}`,

so that `OmegaCut _ _ _ _ _ 0 = HalfDown` (the lower half-region), `OmegaCut … t = Omega` for `t`
large, and `t ↦ OmegaCut … t` interpolates from the lower half-region to the whole box region.  For
each `t` the boundary of the truncation in the surface is the level set of the level function

  `capLevel s c σ u t = max (boxNorm c σ - s) (planeCoord c σ u - t)`,

which is the trace of the *truncated convex box* `PBox s c σ ∩ {planeCoord < t}` on the surface.

Two facts about the sweep are established here.

* **`sweep_dichotomy`** — at every level `t` whose trace is nice and carries no essential loop
  (`SweepNice`), the winding span of the truncation is `⊥` or `⊤`.  This is Pardon's equation (1)
  at the truncated box: it is the chapter's dichotomy engine
  (`windingSpan_bot_or_top_of_inessential_boundary`) and needs no new input.

* **`dropCase_of_sweep`** — `DropCase` follows from `SweepNice` *at every level* together with the
  one-step statement that the sweep does not jump: the span of the truncation is locally constant
  in `t`.  The proof is the connectivity of `ℝ`: the two sets
  `{t | W(OmegaCut … t) = ⊥}` and `{t | W(OmegaCut … t) = ⊤}` are open (local constancy), disjoint
  and cover `ℝ` (the dichotomy), and the first one contains `0` (the truncation at level `0` is the
  lower half-region, whose span is `⊥` by hypothesis); so the second is empty and the span vanishes
  at *every* level, in particular at the levels beyond the range of the cutting-plane coordinate,
  where the truncation is the whole box region.

So the residue of the area is now exactly the pair

* `∀ t, SweepNice ψ s c σ u t` — Pardon's *cleanliness of every intermediate sphere* (his Lemma 2,
  `mustbeinessential`, which his counting supplies: every intermediate trace is inessential); and
* the local constancy of the sweep — Pardon's "a single `2`-surgery changes the invariant by at most
  one dimension" (his Lemma `spherefamily`'s key step);

which are precisely the two inputs of Pardon's own proof of Lemma 3.  The first is *not* implied by
the endpoint hypotheses `hS`, `hZ` alone (the union of two inessential curve families can be
essential); this is recorded in `README.md` §36.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## 1. The truncation of the box region by the cutting plane -/

/-- **The level function of the truncation**: `max (boxNorm c σ - s) (planeCoord c σ u - t)`.  Its
sublevel region is `Ω ∩ {planeCoord < t}` and its level set is the trace on the surface of the
truncated convex box `PBox s c σ ∩ {planeCoord < t}`. -/
noncomputable def capLevel (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) : R3 → ℝ :=
  fun y => max (Work.BoxShrink.Pinch.boxLevel s c σ y)
    (Work.BoxShrink.Bubble.planeCoord c σ u y - t)

theorem capLevel_continuous (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Continuous (capLevel s c σ u t) :=
  (Work.BoxShrink.Pinch.boxLevel_continuous s c σ).max
    ((Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.sub continuous_const)

/-- **The truncation `Ω_t = Ω ∩ {planeCoord < t}`** of the box region below the level `t` of the
cutting-plane coordinate. -/
def OmegaCut (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Set R3 :=
  Omega ψ s c σ ∩ {x : R3 | Work.BoxShrink.Bubble.planeCoord c σ u x < t}

@[simp] theorem mem_OmegaCut {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u t : ℝ} {x : R3} :
    x ∈ OmegaCut ψ s c σ u t ↔ x ∈ Omega ψ s c σ ∧
      Work.BoxShrink.Bubble.planeCoord c σ u x < t := Iff.rfl

theorem OmegaCut_subset_Omega (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u t : ℝ) : OmegaCut ψ s c σ u t ⊆ Omega ψ s c σ := inter_subset_left

theorem OmegaCut_mono {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {t t' : ℝ} (h : t ≤ t') : OmegaCut ψ s c σ u t ⊆ OmegaCut ψ s c σ u t' := by
  intro x hx
  rw [mem_OmegaCut] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- **The truncation at level `0` is the lower half-region.** -/
theorem OmegaCut_zero (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : OmegaCut ψ s c σ u 0 = HalfDown ψ s c σ u := by
  ext x
  rw [mem_OmegaCut, HalfDown, Work.BoxShrink.Core.mem_lowerRegion,
    Work.BoxShrink.Bubble.planeCoord_apply]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hx3⟩
    exact ⟨hx1, hx2, by linarith⟩
  · rintro ⟨hx1, hx2, hx3⟩
    exact ⟨⟨hx1, hx2⟩, by linarith⟩

theorem isOpenInCarrier_planeCoord_lt (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier (surface ψ)
      {x : R3 | Work.BoxShrink.Bubble.planeCoord c σ u x < t} :=
  (isOpen_lt (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous
    continuous_const).preimage continuous_subtype_val

theorem isOpenInCarrier_OmegaCut (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (OmegaCut ψ s c σ u t) :=
  Work.SurgeryInvariance.isOpenInCarrier_inter (surface ψ)
    (Work.BoxShrink.Core.isOpenInCarrier_boxRegion (surface ψ) s c σ)
    (isOpenInCarrier_planeCoord_lt ψ c σ u t)

/-- **The sublevel region of the cap level function is the truncation.** -/
theorem region_capLevel (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u t : ℝ) :
    Work.Smooth.Morse.region ψ (capLevel s c σ u t) 0 = OmegaCut ψ s c σ u t := by
  ext x
  rw [Work.Smooth.Morse.mem_region, mem_OmegaCut, Omega, Work.BoxShrink.Core.mem_boxRegion,
    Submission.mem_PBox_iff, capLevel, Work.BoxShrink.Pinch.boxLevel,
    Work.BoxShrink.Bubble.planeCoord_apply, max_lt_iff]
  constructor
  · rintro ⟨hcar, h1, h2⟩
    exact ⟨⟨hcar, by linarith⟩, by linarith⟩
  · rintro ⟨⟨hcar, h1⟩, h2⟩
    exact ⟨hcar, by linarith, by linarith⟩

/-! ## 2. The sweep hypothesis: every truncated trace is nice and inessential -/

/-- **The trace of the truncated box at level `t`**: the level set of the cap level function.  It
is the boundary, in the surface, of the truncation `OmegaCut ψ s c σ u t`. -/
def CapTrace (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Set R3 :=
  Work.Smooth.Morse.levelSet ψ (capLevel s c σ u t) 0

/-- **The sweep hypothesis at the level `t`**: the trace of the truncated box is a nice finite
disjoint union of simple closed curves and carries no essential loop of the surface.

This is the level-`t` instance of Pardon's *cleanliness of the intermediate spheres*: in his proof
of Lemma 3 the counting hypothesis (`mustbeinessential`) supplies it at every intermediate time.
It is the hypothesis under which the truncation satisfies Pardon's dichotomy. -/
def SweepNice (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    Prop :=
  Work.Smooth.Morse.NiceLevel ψ (capLevel s c σ u t) 0 ∧
  ¬ (surface ψ).ContainsEssentialLoop (CapTrace ψ s c σ u t)

/-! ## 3. Pardon's dichotomy at every level of the sweep -/

/-- **Pardon's equation (1) at the truncated box.**  If the trace of the truncation is a nice
finite disjoint union of simple closed curves carrying no essential loop, then the winding span of
the truncation is `⊥` or `⊤`.

This is the chapter's dichotomy engine at the two sides of the trace: the truncation is the
sublevel region of the cap level function, the open superlevel region is its complement in the
surface minus the trace, and every circle of the trace is inessential. -/
theorem sweep_dichotomy {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u t : ℝ} (hn : SweepNice ψ s c σ u t) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (OmegaCut ψ s c σ u t) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (OmegaCut ψ s c σ u t) = ⊤ := by
  obtain ⟨n, γ, hsimple, hdisj, hZeq⟩ := hn.1.circleUnion
  have hess : ∀ i, ¬ Work.CoreTopology.IsEssential (surface ψ) (γ i) := by
    intro i hi
    exact hn.2 ⟨γ i, hi, fun t' => by
      rw [CapTrace, hZeq]
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t'⟩⟩
  have hX : Work.SurgeryInvariance.IsOpenInCarrier (surface ψ)
      (Work.Smooth.Morse.region ψ (capLevel s c σ u t) 0) :=
    Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := surface ψ)
      (b := {x : R3 | capLevel s c σ u t x < 0})
      (isOpen_lt (capLevel_continuous s c σ u t) continuous_const)
  have hY : Work.SurgeryInvariance.IsOpenInCarrier (surface ψ)
      ((surface ψ).carrier ∩ {x : R3 | 0 < capLevel s c σ u t x}) :=
    Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := surface ψ)
      (b := {x : R3 | 0 < capLevel s c σ u t x})
      (isOpen_lt continuous_const (capLevel_continuous s c σ u t))
  have hXY : Disjoint (Work.Smooth.Morse.region ψ (capLevel s c σ u t) 0)
      ((surface ψ).carrier ∩ {x : R3 | 0 < capLevel s c σ u t x}) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Work.Smooth.Morse.mem_region] at hx
    exact absurd hx.2 (not_lt.mpr hx'.2.le)
  have hcover : (surface ψ).carrier \ (⋃ i, Set.range (γ i).γ) =
      Work.Smooth.Morse.region ψ (capLevel s c σ u t) 0 ∪
        ((surface ψ).carrier ∩ {x : R3 | 0 < capLevel s c σ u t x}) := by
    rw [← hZeq, carrier_sdiff_levelSet_eq_region_union]
  have hdich := windingSpan_bot_or_top_of_inessential_boundary (P := surface ψ)
    hsimple hess hdisj hX hY hXY hcover
  rwa [region_capLevel] at hdich

/-! ## 4. `DropCase` from the sweep -/

/-- **The whole remaining content of the area, from the sweep.**  `DropCase` follows from

* the sweep hypothesis at *every* level (`hclean`: Pardon's cleanliness of every intermediate
  sphere — the content of his counting argument), and
* the one-step statement (`hstep`: Pardon's "a single `2`-surgery changes the invariant by at most
  one dimension", here in the form that the invariant of the truncation is locally constant in the
  level).

The proof is the connectivity of the line of levels: the sets of levels where the truncation is
`⊥` resp. `⊤` are open (by `hstep`), disjoint and cover `ℝ` (by the dichotomy), and the `⊥` set is
inhabited (level `0`, where the truncation is the lower half-region and the hypothesis says its span
vanishes); so the `⊤` set is empty, the span vanishes at every level, and at levels beyond the range
of the cutting-plane coordinate the truncation is the whole box region. -/
theorem dropCase_of_sweep
    (hclean : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      ∀ t : ℝ, SweepNice ψ s c σ u t)
    (hstep : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
        (t : ℝ), SweepNice ψ s c σ u t →
      ∃ ε > 0, ∀ t' : ℝ, |t' - t| < ε →
        Work.SurgeryInvariance.WindingSpan (surface ψ) (OmegaCut ψ s c σ u t') =
          Work.SurgeryInvariance.WindingSpan (surface ψ) (OmegaCut ψ s c σ u t)) :
    DropCase := by
  intro ψ s c σ u hT hTa hS hZ hbot
  have hn : ∀ t : ℝ, SweepNice ψ s c σ u t := hclean ψ s c σ u hT hTa hS hZ
  have hdich : ∀ t : ℝ, Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (OmegaCut ψ s c σ u t) = ⊤ :=
    fun t => sweep_dichotomy (hn t)
  -- the two sets of levels
  have hAopen : IsOpen {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε, hε, h⟩ := hstep ψ s c σ u t (hn t)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) ?_
    intro t' ht'
    have hlt : |t' - t| < ε := by
      rw [← Real.dist_eq]; exact Metric.mem_ball.mp ht'
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [h t' hlt, ht]
  have hBopen : IsOpen {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε, hε, h⟩ := hstep ψ s c σ u t (hn t)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) ?_
    intro t' ht'
    have hlt : |t' - t| < ε := by
      rw [← Real.dist_eq]; exact Metric.mem_ball.mp ht'
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [h t' hlt, ht]
  have hdisj : Disjoint {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥} {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊤} := by
    rw [Set.disjoint_left]
    intro t h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [h1] at h2
    exact bot_ne_top h2
  have hcover : {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
        (OmegaCut ψ s c σ u t) = ⊥} ∪ {t : ℝ | Work.SurgeryInvariance.WindingSpan
        (surface ψ) (OmegaCut ψ s c σ u t) = ⊤} = Set.univ := by
    ext t
    rcases hdich t with h | h <;> simp [h]
  have hAne : ({t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥}).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [OmegaCut_zero]
    have hmono : Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
      Work.SurgeryInvariance.WindingSpan_mono (surface ψ)
        (Set.subset_union_right : HalfDown ψ s c σ u ⊆ Halves ψ s c σ u)
    rw [hbot] at hmono
    exact le_bot_iff.mp hmono
  have hsub : (Set.univ : Set ℝ) ⊆ {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
        (OmegaCut ψ s c σ u t) = ⊥} ∪ {t : ℝ | Work.SurgeryInvariance.WindingSpan
        (surface ψ) (OmegaCut ψ s c σ u t) = ⊤} := by
    intro t _
    rcases hdich t with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- connectivity of `ℝ`
  have hAuniv : {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥} = Set.univ := by
    rcases isPreconnected_univ.subset_or_subset hAopen hBopen hdisj hsub with h | h
    · exact Set.eq_univ_of_univ_subset h
    · exfalso
      obtain ⟨t, ht⟩ := hAne
      exact (Set.disjoint_left.mp hdisj ht) (h (Set.mem_univ t))
  have hall : ∀ t : ℝ, Work.SurgeryInvariance.WindingSpan (surface ψ)
      (OmegaCut ψ s c σ u t) = ⊥ := by
    intro t
    have : t ∈ {t : ℝ | Work.SurgeryInvariance.WindingSpan (surface ψ)
        (OmegaCut ψ s c σ u t) = ⊥} := by rw [hAuniv]; exact Set.mem_univ t
    simpa using this
  -- the truncation is the whole box region at a level beyond the range of the coordinate
  have hbdd : ∃ M : ℝ, ∀ x ∈ Omega ψ s c σ,
      Work.BoxShrink.Bubble.planeCoord c σ u x ≤ M := by
    have hne : ((surface ψ).carrier).Nonempty :=
      ⟨(surface ψ).psi 0 0, (surface ψ).psi_mem_carrier 0 0⟩
    obtain ⟨x₀, _hx₀, hmax⟩ := (Work.Smooth.Morse.Surface.isCompact_torus ψ).exists_isMaxOn hne
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).continuous.continuousOn
    exact ⟨Work.BoxShrink.Bubble.planeCoord c σ u x₀, fun x hx => hmax hx.1⟩
  obtain ⟨M, hM⟩ := hbdd
  have hcut : OmegaCut ψ s c σ u (M + 1) = Omega ψ s c σ := by
    refine Subset.antisymm (OmegaCut_subset_Omega ψ s c σ u (M + 1)) ?_
    intro x hx
    rw [mem_OmegaCut]
    exact ⟨hx, lt_of_le_of_lt (hM x hx) (by linarith)⟩
  have hbot' : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
    rw [← hcut]
    exact hall (M + 1)
  rw [hbot', finrank_bot]
  omega

end

end Work.BoxShrink.PinchOff
