import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.existsUnique_top_of_partition
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.BoxShrink.Core.All

/-!
# The two sides of a wall of inessential curves: exactly one is essential

This module sharpens the fleet's tool `Work.BoxShrink.PinchOff.IB.existsUnique_top_of_partition` to
the case of **two** pieces, in the form in which the solid ε-form of Pardon's Lemma 3 consumes it.

`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_aux` says that a region of the torus whose boundary
is a finite disjoint union of *simple* *inessential* closed curves has winding span `⊥` or `⊤`.  The
tool `existsUnique_top_of_partition` upgrades this to *exactly one* piece of a partition of the
complement having span `⊤` — but it demands that the index set of the pieces be the index set of the
curves, which makes it inapplicable to a wall with, say, five components and two sides.

Here both statements are proved in the general form (*any* finite number of wall curves, two pieces):

* `Wall.windingSpan_eq_bot_of_eq_top` — **the one-sided (uniqueness) half**: if one side has full
  winding span, the other side has vanishing winding span.  This is the half which gives, at a
  box/plane configuration whose box-sphere trace is inessential, the *inessentiality of the outside*
  `F ∖ closure (PBox)` from the essentiality of the box region.
* `Wall.exists_top_of_two_pieces` — **the existence half**: some side has full winding span
  (peeling the wall out of the whole carrier does not change the span, and the span of a disjoint
  union of two carrier-open pieces is the supremum of the two spans).
* `Wall.existsUnique_top_of_two_pieces` — **the sharpened dichotomy**: exactly one side has full
  winding span.

The proof of the one-sided half is Pardon's argument in the parameter plane: the side of span `⊤`
carries an unbounded connected component of its lift (`exists_unbounded_component_of_windingSpan_eq_top`),
and this component is a component of the complement of the lifted wall; since the complement of a
closed set with compact components has at most one unbounded component
(`Work.BoxShrink.PinchOff.unbounded_component_unique`), the other side has no unbounded component and
hence vanishing span (`Work.BoxShrink.PinchOff.windingSpan_eq_bot_of_components_bounded`).

## The route this serves

At a configuration carrying the counting data of the crux, write `Ω = F ∩ PBox s c σ` for the region
inside the box, `Ω₊`, `Ω₋` for the two half-regions, `Γ = F ∩ ∂PBox s c σ` for the box-sphere trace
and `Σ` for the trace of the cutting plane.  Then:

* `Γ` is a finite disjoint union of simple inessential closed curves (general position plus the
  counting, `Work.Drive.not_exists_weakCompressingLoop_of_counts`); `W(Ω) = ⊤` by `HasEssBox` and
  the dichotomy; so `W(outside) = ⊥` by `Wall.windingSpan_eq_bot_of_eq_top`;
* if `Z` is a thin collar of `Σ` inside the box whose boundary curves are simple, inessential and
  pairwise disjoint, then the wall `Γ ∪ ∂Z` has two sides `X := (Ω₊ ∖ Z) ∪ Z` and
  `Y := Ω₋ ∪ outside`, and `Wall.existsUnique_top_of_two_pieces` says that exactly one of them spans
  `⊤`.  If it is `Y`, then `W(Ω₋) = ⊤` (the outside contributes nothing); if it is `X`, then
  `W(Ω₊) = ⊤` or `W(Z) = ⊤`, and in the latter case the essential loop lies in the `δ`-thin collar,
  hence within `δ` of *both* solid half-boxes.  In every case an essential loop of `F` lies within
  `ε` of one of the two solid half-boxes, which is the conclusion of `Work.Drive.CountingHalfEpsBody`.

The missing input is the existence of the thin collar `Z` (a regular-neighbourhood/tameness
statement for the trace of the cutting plane, supplied by Pardon's perturbation into general
position), not the pinch family: this route spends the counting at the *wall* rather than at the
intermediate spheres of a one-parameter family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

namespace Wall

variable {P : Work.CoreTopology.ParamTorus}

/-- **The components of a piece of a clopen partition are components of the whole complement.**
If `X ⊆ Cᶜ`, `X` is open in the carrier and the complement of `X` inside `C̃ᶜ` is open (which is the
case when it is the union of the other pieces of a clopen partition), then the component of `z ∈ X̃`
in `X̃` is its component in `C̃ᶜ`. -/
theorem connectedComponentIn_compl_eq {C X : Set R3} (hXc : X ⊆ P.carrier)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) (hXC : X ⊆ Cᶜ)
    (hopen : IsOpen ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
      Work.BoxShrink.PinchOff.Xtilde P X))
    {z : ℂ} (hz : z ∈ Work.BoxShrink.PinchOff.Xtilde P X) :
    connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P X) z =
      connectedComponentIn ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ) z :=
  (Work.BoxShrink.PinchOff.connectedComponentIn_of_clopen
    (fun _ hx => hXC hx) (Work.BoxShrink.PinchOff.isOpen_Xtilde hXc hX) hopen hz).symm

/-- **The one-sided half of the wall dichotomy.**  Let the complement of a finite disjoint union of
simple inessential closed curves of the torus be split into two carrier-open pieces `X`, `Y`.  If one
piece has full winding span then the other has vanishing winding span.

Pardon's parameter-plane argument: the piece of full span carries an unbounded component of its lift,
that component is a component of the complement of the lifted wall, and a closed set with compact
components has at most one unbounded complementary component. -/
theorem windingSpan_eq_bot_of_eq_top {n : ℕ} {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    {X Y : Set R3}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hXc : X ⊆ P.carrier) (hYc : Y ⊆ P.carrier)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y)
    (h : Work.SurgeryInvariance.WindingSpan P X = ⊤) :
    Work.SurgeryInvariance.WindingSpan P Y = ⊥ := by
  classical
  set C : Set R3 := ⋃ i, Set.range (γ i).γ with hCdef
  -- the wall is compact, hence closed
  have hC_closed : IsClosed C := by
    rw [hCdef]
    refine (isCompact_iUnion (fun i => ?_)).isClosed
    have h1 : Set.range (γ i).γ = (γ i).γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
      refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
      rw [Work.CoreTopology.ClosedCurve.range_eq_image P (γ i)]
      exact Set.image_mono Set.Ico_subset_Icc_self
    rw [h1]
    exact isCompact_Icc.image_of_continuousOn (γ i).cont.continuousOn
  have hCt_closed : IsClosed (Work.BoxShrink.PinchOff.Xtilde P C) :=
    hC_closed.preimage (Work.BoxShrink.PinchOff.continuous_planePsi P)
  have hcomp : ∀ z ∈ Work.BoxShrink.PinchOff.Xtilde P C,
      IsCompact (connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P C) z) := by
    rw [hCdef]
    exact Work.BoxShrink.PinchOff.components_compact hsimple hess hdisj
  -- the two pieces are the two sides of the lifted wall
  have hXt_u : (Work.BoxShrink.PinchOff.Xtilde P C)ᶜ =
      Work.BoxShrink.PinchOff.Xtilde P X ∪ Work.BoxShrink.PinchOff.Xtilde P Y := by
    have h1 : (Work.BoxShrink.PinchOff.Xtilde P C)ᶜ =
        Work.BoxShrink.PinchOff.Xtilde P Cᶜ := Set.preimage_compl.symm
    have h2 : Work.BoxShrink.PinchOff.Xtilde P Cᶜ =
        Work.BoxShrink.PinchOff.Xtilde P (P.carrier \ C) := by
      ext z
      exact ⟨fun hz => ⟨Work.BoxShrink.PinchOff.planePsi_mem_carrier P z, hz⟩,
        fun hz => hz.2⟩
    rw [h1, h2, hcover]
    show Work.BoxShrink.PinchOff.planePsi P ⁻¹' (X ∪ Y) =
      Work.BoxShrink.PinchOff.planePsi P ⁻¹' X ∪ Work.BoxShrink.PinchOff.planePsi P ⁻¹' Y
    exact Set.preimage_union
  have hXt_open : IsOpen ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
      Work.BoxShrink.PinchOff.Xtilde P X) := by
    have hset : (Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
        Work.BoxShrink.PinchOff.Xtilde P X = Work.BoxShrink.PinchOff.Xtilde P Y := by
      rw [hXt_u]
      ext z
      exact ⟨fun hz => hz.1.resolve_left hz.2, fun hz =>
        ⟨Set.mem_union_right _ hz, fun hzX => Set.disjoint_left.mp hXY hzX hz⟩⟩
    rw [hset]
    exact Work.BoxShrink.PinchOff.isOpen_Xtilde hYc hY
  have hYt_open : IsOpen ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
      Work.BoxShrink.PinchOff.Xtilde P X) := hXt_open
  -- `X` has an unbounded lifted component, which is a component of the complement of the wall
  obtain ⟨x, hxX, hxunb⟩ :=
    Work.BoxShrink.PinchOff.IB.exists_unbounded_component_of_windingSpan_eq_top hXc hX h
  have hXC : X ⊆ Cᶜ := by
    intro y hy
    have h1 : y ∈ P.carrier \ C := by rw [hCdef, hcover]; exact Set.subset_union_left hy
    exact h1.2
  have hxcomp := connectedComponentIn_compl_eq (P := P) (C := C) (X := X) hXc hX hXC hXt_open hxX
  have hxunb' : ∀ R : ℝ,
      ∃ w ∈ connectedComponentIn ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ) x, R ≤ ‖w‖ := by
    intro R
    obtain ⟨w, hw, hR⟩ := hxunb R
    exact ⟨w, hxcomp ▸ hw, hR⟩
  -- hence every lifted component of `Y` is bounded
  have hYsub : Y ⊆ Cᶜ := by
    intro y hy
    have h1 : y ∈ P.carrier \ C := by rw [hCdef, hcover]; exact Set.subset_union_right hy
    exact h1.2
  have hYt_u : (Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
      Work.BoxShrink.PinchOff.Xtilde P Y = Work.BoxShrink.PinchOff.Xtilde P X := by
    rw [hXt_u]
    ext z
    exact ⟨fun hz => hz.1.resolve_right hz.2, fun hz =>
      ⟨Set.mem_union_left _ hz, fun hzY => Set.disjoint_left.mp hXY hz hzY⟩⟩
  have hbdd : ∀ z : ℂ, Bornology.IsBounded
      (connectedComponentIn (Work.BoxShrink.PinchOff.Xtilde P Y) z) := by
    intro z
    by_cases hz : z ∈ Work.BoxShrink.PinchOff.Xtilde P Y
    · have hzC : z ∉ Work.BoxShrink.PinchOff.Xtilde P C := by
        intro hzc
        exact hYsub (Work.BoxShrink.PinchOff.mem_Xtilde P Y z |>.mp hz) hzc
      have hzopen : IsOpen ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ \
          Work.BoxShrink.PinchOff.Xtilde P Y) := by
        rw [hYt_u]; exact Work.BoxShrink.PinchOff.isOpen_Xtilde hXc hX
      have hzcomp := connectedComponentIn_compl_eq (P := P) (C := C) (X := Y) hYc hY hYsub
        hzopen hz
      -- if the component of `z` were unbounded, it would be the component of `x`
      have hxC : x ∉ Work.BoxShrink.PinchOff.Xtilde P C := fun h =>
        hXC ((Work.BoxShrink.PinchOff.mem_Xtilde P X x).mp hxX)
          ((Work.BoxShrink.PinchOff.mem_Xtilde P C x).mp h)
      have hnotunb : ¬ (∀ R : ℝ,
          ∃ w ∈ connectedComponentIn ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ) z, R ≤ ‖w‖) := by
        intro hzunb
        have heq := Work.BoxShrink.PinchOff.unbounded_component_unique hCt_closed hcomp hxC hzC
          hxunb' hzunb
        have : x ∈ connectedComponentIn ((Work.BoxShrink.PinchOff.Xtilde P C)ᶜ) z := by
          rw [← heq]; exact mem_connectedComponentIn hxC
        rw [← hzcomp] at this
        have hxY : x ∈ Work.BoxShrink.PinchOff.Xtilde P Y :=
          connectedComponentIn_subset (Work.BoxShrink.PinchOff.Xtilde P Y) z this
        have hxX' : Work.BoxShrink.PinchOff.planePsi P x ∈ X :=
          (Work.BoxShrink.PinchOff.mem_Xtilde P X x).mp hxX
        have hxY' : Work.BoxShrink.PinchOff.planePsi P x ∈ Y :=
          (Work.BoxShrink.PinchOff.mem_Xtilde P Y x).mp hxY
        exact (Set.disjoint_left.mp hXY hxX') hxY'
      rw [hzcomp]
      push_neg at hnotunb
      obtain ⟨R, hR⟩ := hnotunb
      exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun w hw => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt (hR w hw))
    · rw [connectedComponentIn_eq_empty hz]
      exact Bornology.isBounded_empty
  exact Work.BoxShrink.PinchOff.windingSpan_eq_bot_of_components_bounded hYc hY hbdd

/-- **The existence half of the wall dichotomy**: some side of the wall has full winding span.
Peeling the wall out of the whole carrier does not change the winding span, and each side has span
`⊥` or `⊤` (the dichotomy `windingSpan_bot_or_top_aux`), so the side of span `⊤` exists. -/
theorem exists_top_of_two_pieces {n : ℕ} {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    {X Y : Set R3}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y) :
    Work.SurgeryInvariance.WindingSpan P X = ⊤ ∨
      Work.SurgeryInvariance.WindingSpan P Y = ⊤ := by
  have hcarrier : Work.SurgeryInvariance.IsOpenInCarrier P P.carrier := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    have h : (Subtype.val ⁻¹' P.carrier : Set P.carrier) = Set.univ := by ext x; simp
    rw [h]; exact isOpen_univ
  have hpeel := Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
    (P := P) (X := P.carrier) (γ := γ) hcarrier hsimple hess hdisj
    (fun i t => (γ i).mem t)
  have htop : Work.SurgeryInvariance.WindingSpan P
      (P.carrier \ (⋃ i, Set.range (γ i).γ)) = ⊤ := by
    rw [← hpeel, Work.SurgeryInvariance.WindingSpan.carrier_eq_top P]
  have htop' : Work.SurgeryInvariance.WindingSpan P X ⊔
      Work.SurgeryInvariance.WindingSpan P Y = ⊤ := by
    rw [← Work.SurgeryInvariance.Span.union_eq_sup hX hY hXY, ← hcover]
    exact htop
  have hdX : Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P X = ⊤ :=
    Work.BoxShrink.PinchOff.windingSpan_bot_or_top_aux (P := P) (γ := γ) (X := X) (Y := Y)
      hsimple hess hdisj hX hY hXY hcover
  have hdY : Work.SurgeryInvariance.WindingSpan P Y = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P Y = ⊤ :=
    Work.BoxShrink.PinchOff.windingSpan_bot_or_top_aux (P := P) (γ := γ) (X := Y) (Y := X)
      hsimple hess hdisj hY hX hXY.symm (by rw [Set.union_comm]; exact hcover.symm ▸ rfl)
  rcases hdX with h | h
  · rcases hdY with h' | h'
    · rw [h, h'] at htop'
      simp only [bot_sup_eq] at htop'
      exact absurd htop' bot_ne_top
    · exact Or.inr h'
  · exact Or.inl h

/-- **The sharpened wall dichotomy**: for a wall of finitely many pairwise disjoint simple
inessential closed curves and two carrier-open sides, exactly one side has full winding span. -/
theorem existsUnique_top_of_two_pieces {n : ℕ} {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    {X Y : Set R3}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hXc : X ⊆ P.carrier) (hYc : Y ⊆ P.carrier)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y) :
    (Work.SurgeryInvariance.WindingSpan P X = ⊤ ∧
        Work.SurgeryInvariance.WindingSpan P Y = ⊥) ∨
      (Work.SurgeryInvariance.WindingSpan P X = ⊥ ∧
        Work.SurgeryInvariance.WindingSpan P Y = ⊤) := by
  rcases exists_top_of_two_pieces (P := P) (γ := γ) (X := X) (Y := Y)
    hsimple hess hdisj hX hY hXY hcover with h | h
  · exact Or.inl ⟨h, windingSpan_eq_bot_of_eq_top (P := P) (γ := γ) (X := X) (Y := Y)
      hsimple hess hdisj hXc hYc hX hY hXY hcover h⟩
  · refine Or.inr ⟨windingSpan_eq_bot_of_eq_top (P := P) (γ := γ) (X := Y) (Y := X)
      hsimple hess hdisj hYc hXc hY hX hXY.symm ?_ h, h⟩
    rw [Set.union_comm]; exact hcover.symm ▸ rfl

/-! ## The box-sphere trace as a wall, and the inessentiality of the outside

The concrete instantiation at the box of the abstract dichotomy above.  The crux supplies
`Work.BoxShrink.SlicedSphere` at the box sphere (a `SphereSlicing`) and the counting gives that the
trace carries no essential loop (`Work.Drive.sphereTrace_inessential_of_countsW`, in the weak-disc
vocabulary).  The slicing curves are then a wall of simple inessential curves whose complement
splits into the region inside the box and the region outside it — so the **outside** of the box has
vanishing winding span as soon as the region inside the box has full span.
-/

section Box

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}

/-- **The slicing curves cover the trace.**  For a `SphereSlicing` of a sphere `S`, the ranges of
the slicing curves cover `F ∩ S`: the inclusion `⊆` is the field `mem`, and `⊇` is the field
`covers` applied to the constant curve through a point of `F ∩ S`. -/
theorem iUnion_range_eq_of_sphereSlicing {S : Set R3}
    (Sl : Work.InnermostDisk.SphereSlicing P S) :
    (⋃ i, Set.range (Sl.c i).γ) = P.carrier ∩ S := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    rw [Set.mem_range] at hx
    obtain ⟨t, ht⟩ := hx
    exact ⟨ht ▸ (Sl.c i).mem t, ht ▸ Sl.mem i t⟩
  · intro x hx
    obtain ⟨hxc, hxS⟩ := hx
    let κ : Work.CoreTopology.ClosedCurve P :=
      { γ := fun _ : ℝ => x, cont := continuous_const, periodic := fun _ => rfl,
        mem := fun _ => hxc }
    obtain ⟨i, hi⟩ := Sl.covers κ (fun _ => hxS)
    obtain ⟨t, ht⟩ := Set.mem_range.mp (hi (Set.mem_range_self (f := κ.γ) (0 : ℝ)))
    rw [Set.mem_iUnion]
    exact ⟨i, Set.mem_range.mpr ⟨t, by rw [ht]⟩⟩

/-- **The wall at the box sphere.**  From a slicing of the box sphere and the inessentiality of
its trace (general position plus the counting), a finite family of pairwise disjoint simple
inessential closed curves covering `F ∩ ∂PBox`: the slicing curves, reindexed along
`Fintype.equivFin` so that the index set is a `Fin`. -/
theorem exists_wall_of_slicedSphere (_hs : 0 < s)
    (hsl : Work.BoxShrink.SlicedSphere P (Work.BoxShrink.Core.sphereSet c σ s))
    (hess : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s)) :
    ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve P),
      (∀ i, Work.CoreTopology.IsSimple P (γ i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential P (γ i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
      (⋃ i, Set.range (γ i).γ) = P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s := by
  obtain ⟨Sl⟩ := hsl
  letI := Sl.fintype
  let e : Sl.ι ≃ Fin (Fintype.card Sl.ι) := Fintype.equivFin Sl.ι
  refine ⟨Fintype.card Sl.ι, fun i => Sl.c (e.symm i), ?_, ?_, ?_, ?_⟩
  · intro i; exact Sl.simple _
  · intro i h
    exact hess ⟨Sl.c (e.symm i), h, Sl.mem _⟩
  · intro i j hij
    exact Sl.disjoint fun h => hij (e.symm.injective h)
  · refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := Set.mem_range.mp hx
      exact ⟨ht ▸ (Sl.c (e.symm i)).mem t, ht ▸ Sl.mem (e.symm i) t⟩
    · intro x hx
      obtain ⟨hxc, hxS⟩ := hx
      let κ : Work.CoreTopology.ClosedCurve P :=
        { γ := fun _ : ℝ => x, cont := continuous_const, periodic := fun _ => rfl,
          mem := fun _ => hxc }
      obtain ⟨i, hi⟩ := Sl.covers κ (fun _ => hxS)
      obtain ⟨t, ht⟩ := Set.mem_range.mp (hi (Set.mem_range_self (f := κ.γ) (0 : ℝ)))
      have hmem : x ∈ Set.range (Sl.c i).γ := Set.mem_range.mpr ⟨t, by rw [ht]⟩
      refine Set.mem_iUnion.mpr ⟨e i, ?_⟩
      simpa [Equiv.symm_apply_apply] using hmem

/-- **The outside of the box is inessential.**  If the box-sphere trace is a wall of simple
inessential curves (general position of the box sphere plus the counting) and the region inside the
box has full winding span, then the region outside the box has vanishing winding span.

This is the one-sided half `windingSpan_eq_bot_of_eq_top` at the box wall, and it is the first step
of the wall route to the solid ε-form recorded in `NOTES_wallDichotomy.md`. -/
theorem windingSpan_outside_eq_bot (hs : 0 < s)
    (hsl : Work.BoxShrink.SlicedSphere P (Work.BoxShrink.Core.sphereSet c σ s))
    (hess : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s))
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤) :
    (Work.SurgeryInvariance.WindingSpan P
      (P.carrier \ closure (Submission.PBox s c σ))) = ⊥ := by
  obtain ⟨n, γ, hsimple, hiness, hdisj, hcover⟩ :=
    exists_wall_of_slicedSphere (P := P) (s := s) (c := c) (σ := σ) hs hsl hess
  have hfront : Work.BoxShrink.Core.sphereSet c σ s = frontier (Submission.PBox s c σ) := by
    rw [Work.BoxShrink.Core.sphereSet_eq_BoxSphere,
      ← Work.Topology.SphereSlicing.frontier_PBox hs c σ]
  have hout : P.carrier \ closure (Submission.PBox s c σ) =
      P.carrier ∩ (closure (Submission.PBox s c σ))ᶜ := by
    ext x; simp
  refine windingSpan_eq_bot_of_eq_top (P := P) (γ := γ)
    (X := Work.BoxShrink.Core.boxRegion P s c σ)
    (Y := P.carrier \ closure (Submission.PBox s c σ))
    hsimple hiness hdisj (fun x hx => hx.1) (fun x hx => hx.1)
    (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ) ?_ ?_ ?_ h
  · -- the outside of the box is open in the carrier
    rw [hout]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter isClosed_closure.isOpen_compl
  · -- the two pieces are disjoint
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 (subset_closure hx.2)
  · -- their union is the complement of the wall
    have hW : ∀ x : R3, x ∈ (⋃ i, Set.range (γ i).γ) ↔
        x ∈ P.carrier ∧ x ∈ frontier (Submission.PBox s c σ) := by
      intro x
      rw [hcover]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rwa [hfront] at h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rwa [hfront]
    have hfr : ∀ x : R3, x ∈ frontier (Submission.PBox s c σ) ↔
        x ∈ closure (Submission.PBox s c σ) ∧ x ∉ Submission.PBox s c σ := by
      intro x
      rw [frontier_eq_closure_inter_closure, closure_compl,
        (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq, Set.mem_inter_iff,
        Set.mem_compl_iff]
    ext x
    constructor
    · rintro ⟨hxc, hxW⟩
      have hxfr : ¬ (x ∈ closure (Submission.PBox s c σ) ∧ x ∉ Submission.PBox s c σ) :=
        fun h' => hxW ((hW x).mpr ⟨hxc, (hfr x).mpr h'⟩)
      rcases not_and_or.mp hxfr with hcl | hbox
      · exact Or.inr ⟨hxc, hcl⟩
      · exact Or.inl ⟨hxc, not_not.mp hbox⟩
    · rintro (⟨hxc, hxbox⟩ | ⟨hxc, hxcl⟩)
      · exact ⟨hxc, fun hxW => ((hfr x).mp ((hW x).mp hxW).2).2 hxbox⟩
      · exact ⟨hxc, fun hxW => hxcl ((hfr x).mp ((hW x).mp hxW).2).1⟩

end Box


end Wall

end Work.Drive.EpsForm

