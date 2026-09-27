import Mathlib
import Submission.Work.Drive.clampedSweepImage
import Submission.Work.Drive.cutTransportStrict
import Submission.Work.Drive.projPlaneCut

/-!
# The cut of a clamped sweep is a chord or empty: removing the level inequality from `hVcut`

`Submission/Work/Drive/CHAIN_INTERFACE_CONSUMERS.md` §7 records the risk in the design's
`hVcut : diskCut Q V = SmoothArc.Zset h`: the cut of the swept plane by the *radially clamped* sweep
is the class-cut *intersected with a level bound* (`Work.Drive.diskCut_clampedSweep_eq`), so the
identification of `diskCut Q V` with the level set `Zset h = {φ ∘ V' = 0}` requires the pointwise
inequality

> `levelOf (Q x) ≤ levelOf (P y)`   for every disk point `x` whose class is attained by `P`.

This file proves that this pointwise condition is **rigid**: along the class-cut the function
`levelOf (Q ·) − (the plane's level at the class)` is continuous and (for `u ∈ Zc γ`, i.e. for the two
planes disjoint) *nowhere zero*; if the class-cut is preconnected, the sign is therefore *constant*.
Consequently

> `diskCut Q (clampedSweep c ψ P)` is **either the whole class-cut or empty**

(`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty`).  So the design's obligation is *not* a
pointwise inequality along the cut but a single global sign — equivalently, the *side* of the pair
`(P, P_u)`: the cut is a chord when the base plane lies below the swept one over their common class
line and is empty otherwise.

The second half of the file records the consequence for the transport: an **empty cut contributes
nothing** (`cutBaseBox = ∅`), so the multiplicative statement of Hugelmeyer's Lemma 2 holds in the
*disjunctive* form

> `Odd #(cutBaseBox) ↔` (the first cut is non-empty and its arc count is odd) `∧` (same for the second),

which replaces the strict hypotheses `hVcut`/`hWcut` of
`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity_of_strict` by the disjunction "chord or empty" that the
geometry actually provides (`Work.Drive.odd_ncard_cutBaseBox_iff_mul_of_dichotomy`, and its packaged
form `Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_mul_of_dichotomy`).

All declarations below are sorry-free and rest only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The class-cut of a disk-presented plane by a projective plane.**  The parameters of the disk
model whose plane point has projective class on the projective plane `projLine (ker φ)`.  This is the
set that the design's profile `φ ∘ V'` cuts out (`Work.Drive.exists_classCutProfile`) and that
`diskCut Q V` is contained in (`Work.Drive.diskCut_subset_classCut`). -/
def classCut (Q : ℂ → CappingSpace) (φ : Eucl 3 →L[ℝ] ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ‖cplxOf x‖ ≤ 1 ∧
    (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))}

theorem mem_classCut {Q : ℂ → CappingSpace} {φ : Eucl 3 →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ classCut Q φ ↔ ‖cplxOf x‖ ≤ 1 ∧
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) :=
  Iff.rfl

/-- **The sign of a continuous nowhere-zero function on a preconnected set is constant.**  Applied to
`levelOf (Q ·) − (the swept plane's level at the class)`, this is the rigidity that turns the
pointwise level condition into a single global sign. -/
theorem preconnected_forall_pos_or_neg {α : Type*} [TopologicalSpace α] {S : Set α}
    {f : α → ℝ} (hpre : IsPreconnected S) (hcont : ContinuousOn f S)
    (hne : ∀ x ∈ S, f x ≠ 0) : (∀ x ∈ S, 0 < f x) ∨ (∀ x ∈ S, f x < 0) := by
  have himg : IsPreconnected (f '' S) := hpre.image f hcont
  have hsub : f '' S ⊆ Set.Ioi (0 : ℝ) ∪ Set.Iio (0 : ℝ) := by
    rintro y ⟨x, hx, rfl⟩
    rcases lt_trichotomy (f x) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (hne x hx)
    · exact Or.inl h
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio (0 : ℝ)) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : (0 : ℝ) < x := hx.1
    have h2 : x < 0 := hx.2
    linarith
  rcases himg.subset_or_subset isOpen_Ioi isOpen_Iio hdisj hsub with h | h
  · left
    intro x hx
    exact h ⟨x, hx, rfl⟩
  · right
    intro x hx
    exact h ⟨x, hx, rfl⟩

/-- **The cut of a clamped sweep lies in the class-cut.**  The class of every point of the sweep is
the class of the plane at the corresponding box point (`Work.Drive.cls_clampedSweep`), and the
class-image of the plane's box lies in `projLine (ker φ)`. -/
theorem diskCut_clampedSweep_subset_classCut (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    diskCut Q (clampedSweep c ψ P) ⊆ classCut Q φ := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨y, hy, hxy⟩ := hx.2
  rw [show (cappingSpaceHomeoProj (Q (cplxOf x))).2
      = (cappingSpaceHomeoProj (clampedSweep c ψ P y)).2 from by rw [hxy],
    cls_clampedSweep]
  exact hPcls _ (mk2_mem_unitBox (hy 0) (hy 1))

/-- **THE RIGIDITY DICHOTOMY OF THE CUT.**  The cut of a clamped radial sweep is *either* the whole
class-cut *or* empty.

The hypotheses are exactly the design's:

* `hPcls` — the class-image of the swept plane's box lies in the projective plane `projLine (ker φ)`;
* `g` is the *level of the swept plane at the class* — the **profile** `ρ_u` of the swept plane over
  the class line: it is an upper bound for the levels of all its box points with that class (`hgmax`,
  true by definition of a supremum) and is *attained* there (`hgatt`, true because the fibre is compact
  and non-empty), and it is continuous along the class-cut (`hgcont`).

  Note `hgmax`/`hgatt` are **strictly weaker** than "the level is a function of the class" (the
  class-injectivity of the plane's presentation): the profile is well defined even when several chords
  share a class.  What class-injectivity would give is the equality of `g x` with the level of *every*
  witness, which is not what the argument needs.
* `hne` — the two planes are *disjoint* over the class line (`levelOf (Q x) ≠ g x`); this is the
  `u ∈ Zc γ` condition of the design, and it is what makes the sign nowhere zero;
(The class surjectivity — every class of the class-cut is attained by the swept plane's box — is
implied by the attainment clause `hgatt` and is therefore not a separate hypothesis.) -/
theorem diskCut_clampedSweep_eq_classCut_or_empty (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgmax : ∀ x y : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 →
      y ∈ Submission.Drive.unitBox 1 →
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ g x)
    (hgatt : ∀ x ∈ classCut Q φ, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        g x = levelOf (P y))
    (hcontL : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 2) => levelOf (Q (cplxOf x))) (classCut Q φ))
    (hgcont : ContinuousOn g (classCut Q φ))
    (hne : ∀ x ∈ classCut Q φ, levelOf (Q (cplxOf x)) ≠ g x)
    (hclow : ∀ x ∈ classCut Q φ, c ≤ levelOf (Q (cplxOf x)))
    (hpre : IsPreconnected (classCut Q φ)) :
    diskCut Q (clampedSweep c ψ P) = classCut Q φ ∨
      diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  have hcs : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 2) =>
      levelOf (Q (cplxOf x)) - g x) (classCut Q φ) := hcontL.sub hgcont
  rcases preconnected_forall_pos_or_neg hpre hcs
    (fun x hx => sub_ne_zero.mpr (hne x hx)) with hpos | hneg
  · -- the chart is *above* the swept plane on the class line: no point is below, so the cut is empty
    right
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hxS : x ∈ classCut Q φ := hsub hx
    obtain ⟨-, hx2⟩ := hx
    rw [himg] at hx2
    obtain ⟨y, hy, hcls, hcle, hle⟩ := hx2
    have hle' : levelOf (P y) ≤ g x := hgmax x y hxS.1 hy hcls
    have hlt : g x < levelOf (Q (cplxOf x)) := by
      have := hpos x hxS
      linarith
    linarith
  · -- the chart is *below* the swept plane: the level condition holds everywhere
    left
    refine Set.Subset.antisymm hsub ?_
    intro x hxS
    obtain ⟨y, hy, hcls, hgy⟩ := hgatt x hxS
    have hlt : levelOf (Q (cplxOf x)) < levelOf (P y) := by
      have hh := hneg x hxS
      rw [hgy] at hh
      linarith
    refine ⟨hxS.1, ?_⟩
    rw [himg]
    exact ⟨y, hy, hcls, hclow x hxS, hlt.le⟩

/-- **An empty cut contributes nothing to the base count.**  The plane parameters of the unit square
lift into the disk model (`Work.Drive.diskPtFun`), so if the cut is empty then no parameter can lie on
both cuts. -/
theorem cutBaseBox_eq_empty_of_diskCut_eq_empty_left {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace} (h : diskCut Q V = ∅) :
    cutBaseBox (diskPlane Q) V W = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨-, ⟨y, hy, huy⟩, -⟩ := hu
  have hmem : diskPtFun u ∈ diskCut Q V := by
    refine ⟨?_, ?_⟩
    · show ‖cplxOf (diskPtFun u)‖ ≤ 1
      rw [diskPtFun_apply, cplxOf_cplxOfInv]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
    · show Q (cplxOf (diskPtFun u)) ∈ V '' Submission.Drive.unitBox 2
      rw [← diskPlane_eq_Q_cplxOf_diskPtFun Q u, huy]
      exact ⟨y, hy, rfl⟩
  rw [h] at hmem
  exact hmem

/-- The same for the second cut. -/
theorem cutBaseBox_eq_empty_of_diskCut_eq_empty_right {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace} (h : diskCut Q W = ∅) :
    cutBaseBox (diskPlane Q) V W = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨-, -, ⟨z, hz, huz⟩⟩ := hu
  have hmem : diskPtFun u ∈ diskCut Q W := by
    refine ⟨?_, ?_⟩
    · show ‖cplxOf (diskPtFun u)‖ ≤ 1
      rw [diskPtFun_apply, cplxOf_cplxOfInv]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
    · show Q (cplxOf (diskPtFun u)) ∈ W '' Submission.Drive.unitBox 2
      rw [← diskPlane_eq_Q_cplxOf_diskPtFun Q u, huz]
      exact ⟨z, hz, rfl⟩
  rw [h] at hmem
  exact hmem

/-- An empty cut makes the base count *even*. -/
theorem not_odd_ncard_cutBaseBox_of_diskCut_eq_empty {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (h : diskCut Q V = ∅ ∨ diskCut Q W = ∅) :
    ¬ Odd (cutBaseBox (diskPlane Q) V W).ncard := by
  have h0 : cutBaseBox (diskPlane Q) V W = ∅ := by
    rcases h with h | h
    · exact cutBaseBox_eq_empty_of_diskCut_eq_empty_left h
    · exact cutBaseBox_eq_empty_of_diskCut_eq_empty_right h
  rw [h0, Set.ncard_empty]
  exact Nat.not_odd_zero

/-- **THE TRANSPORT WITH THE CUTS "CHORD OR EMPTY".**  This is
`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity_of_strict` with the identifications
`diskCut Q V = arcCycle A`, `diskCut Q W = arcCycle B` replaced by the disjunction that the geometry
provides (`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty`):

> each cut is *either* the chord system `A` / `B`, *or* empty,

and with the conclusion written so that the empty case is handled: the base count is odd if and only if
both cuts are non-empty and their arc counts are odd.

In the design the arc systems are single chords (`ι = κ = Fin 1`), so `#(chainMeetsLine A) = 1` and the
right-hand side reads "both cuts are non-empty" — which is the side function `b` of the pair of planes.
The empty alternative is genuine: the sign rigidity above shows that the cut of `P_0` by the rotation
`u·P_0` is the chord exactly when `P_0` lies radially *below* `u·P_0` over their common class line, and
that is precisely one of the two values of `b`. -/
theorem odd_ncard_cutBaseBox_iff_mul_of_dichotomy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q V = arcCycle A ∨ diskCut Q V = ∅)
    (hW : diskCut Q W = arcCycle B ∨ diskCut Q W = ∅)
    (hVne : arcCycle A ≠ ∅) (hWne : arcCycle B ≠ ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      ((diskCut Q V ≠ ∅ ∧ Odd (chainMeetsLine A).ncard) ∧
        (diskCut Q W ≠ ∅ ∧ Odd (chainMeetsLine B).ncard)) := by
  rcases hV with hV | hV <;> rcases hW with hW | hW
  · -- both cuts are chord systems
    have hstrict := odd_ncard_cutBaseBox_iff_arcParity_of_strict Q V W A B hV hW hchordA hchordB
      hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans
    rw [hstrict]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by rw [hV]; exact hVne, h1⟩, ⟨by rw [hW]; exact hWne, h2⟩⟩
    · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      exact ⟨h1, h2⟩
  · -- the first cut is a chord, the second is empty
    have h0 : cutBaseBox (diskPlane Q) V W = ∅ := cutBaseBox_eq_empty_of_diskCut_eq_empty_right hW
    rw [h0, Set.ncard_empty]
    constructor
    · intro hodd
      exact absurd hodd Nat.not_odd_zero
    · rintro ⟨⟨-, -⟩, ⟨hne, -⟩⟩
      exact absurd hW hne
  · -- the first cut is empty, the second is a chord
    have h0 : cutBaseBox (diskPlane Q) V W = ∅ := cutBaseBox_eq_empty_of_diskCut_eq_empty_left hV
    rw [h0, Set.ncard_empty]
    constructor
    · intro hodd
      exact absurd hodd Nat.not_odd_zero
    · rintro ⟨⟨hne, -⟩, ⟨-, -⟩⟩
      exact absurd hV hne
  · -- both cuts are empty
    have h0 : cutBaseBox (diskPlane Q) V W = ∅ := cutBaseBox_eq_empty_of_diskCut_eq_empty_left hV
    rw [h0, Set.ncard_empty]
    constructor
    · intro hodd
      exact absurd hodd Nat.not_odd_zero
    · rintro ⟨⟨hne, -⟩, _⟩
      exact absurd hV hne

/-- **THE RIGIDITY DICHOTOMY, ON THE CLASS LINE.**  The same conclusion as
`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty`, but with the sign computed on the *class line*
instead of on the class-cut of the disk.

This is the form the design should use: the class line is `L = projLine (U ⊓ ker φ)` for the
`3`-plane `U` of the chart's class image and the functional `φ` of the swept plane, and such a
projective line is **preconnected** (`Work.Drive.isPreconnected_projLine`), so the last hypothesis
below is *free*.  In exchange one gives the two level functions on `L` as data
(`FQ` the chart's level, `G` the swept plane's level, both functions of the class):
the *class-injectivity* of the two presentations is exactly what makes them well defined.

Then, since the sign of `FQ − G` is constant on `L`, it is constant on the class-cut (which maps into
`L`), and the cut is the whole class-cut or empty — no preconnectedness of the class-cut itself is
needed. -/
theorem diskCut_clampedSweep_eq_classCut_or_empty_of_classLine
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (L : Set (Projectivization ℝ (Eucl 3)))
    (hLmem : ∀ x ∈ classCut Q φ,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ L)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ x ∈ classCut Q φ,
      FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (Q (cplxOf x)))
    (hGmax : ∀ x ∈ classCut Q φ, ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2))
    (hGatt : ∀ x ∈ classCut Q φ, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) = levelOf (P y))
    (hcontFG : ContinuousOn (fun q : Projectivization ℝ (Eucl 3) => FQ q - G q) L)
    (hne : ∀ q ∈ L, FQ q ≠ G q)
    (hclow : ∀ x ∈ classCut Q φ, c ≤ levelOf (Q (cplxOf x)))
    (hLpre : IsPreconnected L) :
    diskCut Q (clampedSweep c ψ P) = classCut Q φ ∨
      diskCut Q (clampedSweep c ψ P) = ∅ := by
  have hsub := diskCut_clampedSweep_subset_classCut Q c ψ P φ hPcls
  have himg := image_clampedSweep c hc ψ hψ0 hψ1 hψ01 hcont P hr
  rcases preconnected_forall_pos_or_neg hLpre hcontFG (fun q hq => sub_ne_zero.mpr (hne q hq))
    with hpos | hneg
  · -- the chart is *above* the swept plane along the class line: the cut is empty
    right
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hxS : x ∈ classCut Q φ := hsub hx
    obtain ⟨-, hx2⟩ := hx
    rw [himg] at hx2
    obtain ⟨y, hy, hcls, hcle, hle⟩ := hx2
    have h1 : levelOf (P y) ≤ G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) :=
      hGmax x hxS y hy hcls
    have h2 : G ((cappingSpaceHomeoProj (Q (cplxOf x))).2) < levelOf (Q (cplxOf x)) := by
      have hh := hpos _ (hLmem x hxS)
      rw [hFQval x hxS] at hh
      linarith
    linarith
  · -- the chart is *below*: the level condition holds everywhere on the class-cut
    left
    refine Set.Subset.antisymm hsub ?_
    intro x hxS
    obtain ⟨y, hy, hcls, hgy⟩ := hGatt x hxS
    have h1 : FQ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) - G ((cappingSpaceHomeoProj (Q (cplxOf x))).2)
        = levelOf (Q (cplxOf x)) - levelOf (P y) := by
      rw [hFQval x hxS, hgy]
    have h2 := hneg _ (hLmem x hxS)
    have hlt : levelOf (Q (cplxOf x)) < levelOf (P y) := by linarith
    refine ⟨hxS.1, ?_⟩
    rw [himg]
    exact ⟨y, hy, hcls, hclow x hxS, hlt.le⟩

/-- **A common truncation level below both the chart's and the plane's levels.**  The design's two
lower-bound hypotheses (`hr` for the sweep and `hclow` for the chart) are discharged by a *single*
constant: on the compact disk and parameter square the level functions of two continuous presentations
have a positive lower bound.  (The strict form is what the design needs; the non-strict forms follow.) -/
theorem exists_common_truncationLevel (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hQ : Continuous Q) (hP : Continuous P) :
    ∃ c : ℝ, 0 < c ∧ (∀ y ∈ Submission.Drive.unitBox 1, c < levelOf (P y)) ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ≤ 1 → c < levelOf (Q (cplxOf x))) := by
  obtain ⟨cP, hcP, hPlow⟩ := exists_truncationLevel P hP
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 2) => levelOf (Q (cplxOf x)) :=
    continuous_levelOf.comp (hQ.comp continuous_cplxOf)
  obtain ⟨cQ, hcQ, hQlow⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_forall_le'
    hcont.continuousOn (a := 0) (fun b _ => levelOf_pos (Q (cplxOf b)))
  refine ⟨min cP cQ / 2, by positivity, fun y hy => ?_, fun x hx => ?_⟩
  · have h1 : min cP cQ / 2 < cP := by
      have := min_le_left cP cQ
      linarith
    exact lt_trans h1 (hPlow y hy)
  · have h1 : min cP cQ / 2 < cQ := by
      have := min_le_right cP cQ
      linarith
    refine lt_of_lt_of_le h1 (hQlow x ?_)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hx

/-- **The dichotomy in the design's own vocabulary.**  With the class dictionary
(`Work.Drive.exists_cutProfile_of_diskPlane`: the profile `φ ∘ V'` of the *lifted* class map vanishes
exactly on the class-cut), the rigidity dichotomy reads

> `diskCut Q (clampedSweep c ψ P)` is the profile's zero set `SmoothArc.Zset h`, or it is empty.

So the design's obligation `hVcut : diskCut Q V = SmoothArc.Zset h` is not lost: it holds *or* the cut
is empty, and the arc datum `A` of the transport always exists (it is the chord of `Zset h`, which is
the class-cut and hence always a chord of the disk model). -/
theorem diskCut_clampedSweep_eq_zset_or_empty (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (φ : Eucl 3 →L[ℝ] ℝ)
    (hPcls : ∀ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (P y)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hgmax : ∀ x y : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 →
      y ∈ Submission.Drive.unitBox 1 →
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 →
        levelOf (P y) ≤ g x)
    (hgatt : ∀ x ∈ classCut Q φ, ∃ y ∈ Submission.Drive.unitBox 1,
      (cappingSpaceHomeoProj (Q (cplxOf x))).2 = (cappingSpaceHomeoProj (P y)).2 ∧
        g x = levelOf (P y))
    (hcontL : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 2) => levelOf (Q (cplxOf x))) (classCut Q φ))
    (hgcont : ContinuousOn g (classCut Q φ))
    (hne : ∀ x ∈ classCut Q φ, levelOf (Q (cplxOf x)) ≠ g x)
    (hclow : ∀ x ∈ classCut Q φ, c ≤ levelOf (Q (cplxOf x)))
    (hpre : IsPreconnected (classCut Q φ))
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} (hclasscut : classCut Q φ = SmoothArc.Zset h) :
    diskCut Q (clampedSweep c ψ P) = SmoothArc.Zset h ∨
      diskCut Q (clampedSweep c ψ P) = ∅ := by
  rcases diskCut_clampedSweep_eq_classCut_or_empty Q c hc ψ hψ0 hψ1 hψ01 hcont P hr φ hPcls g
    hgmax hgatt hcontL hgcont hne hclow hpre with h' | h'
  · exact Or.inl (h'.trans hclasscut)
  · exact Or.inr h'

namespace Capping

/-- **The transport for the radial sweeps, with the cuts "chord or empty".**  The packaged form of
`Work.Drive.odd_ncard_cutBaseBox_iff_mul_of_dichotomy` for the engine's `top` count: this is
`Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres` with the strict
identifications replaced by the disjunction that the sign rigidity provides. -/
theorem odd_ncard_topBdryMeet_zero_iff_mul_of_dichotomy
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A ∨
      diskCut Q (clampedSweep (c 1) ψ (P 1)) = ∅)
    (hW : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B ∨
      diskCut Q (clampedSweep (c 2) ψ (P 2)) = ∅)
    (hVne : arcCycle A ≠ ∅) (hWne : arcCycle B ≠ ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      ((diskCut Q (clampedSweep (c 1) ψ (P 1)) ≠ ∅ ∧ Odd (chainMeetsLine A).ncard) ∧
        (diskCut Q (clampedSweep (c 2) ψ (P 2)) ≠ ∅ ∧ Odd (chainMeetsLine B).ncard)) := by
  rw [ncard_topBdryMeet_zero_eq_ncard_cutBaseBox P c ψ hψ hfibV hfibW, hQ]
  exact odd_ncard_cutBaseBox_iff_mul_of_dichotomy Q _ _ A B hV hW hVne hWne hchordA hchordB
    hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans

/-- **The design's form of the multiplicative transport: the cut of a single chord.**

With the arc systems reduced to the design's case of a *single* chord per cut
(`A : Fin 1 → ℝ → 𝔼²`, whose `chainMeetsLine` count is `1`), the packaged transport above reads

> `Odd n_P ↔` the first cut is non-empty `∧` the second cut is non-empty,

i.e. `n_P ≡ ε_Q · ε_R` with `ε` the *non-emptiness* of the cut of the plane by the sweep — the
side function `b` of Hugelmeyer's order.  The empty alternative is not an artefact: it is exactly the
other value of `b`, and the sign rigidity shows that it is the case in which the chart lies radially
*above* the swept plane over their common class line. -/
theorem odd_ncard_topBdryMeet_zero_iff_nonempty_of_dichotomy
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1)
    (A B : Fin 1 → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A ∨
      diskCut Q (clampedSweep (c 1) ψ (P 1)) = ∅)
    (hW : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B ∨
      diskCut Q (clampedSweep (c 2) ψ (P 2)) = ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : Fin 1, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : Fin 1, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : Fin 1, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : Fin 1, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      (diskCut Q (clampedSweep (c 1) ψ (P 1)) ≠ ∅ ∧
        diskCut Q (clampedSweep (c 2) ψ (P 2)) ≠ ∅) := by
  have hAne : arcCycle A ≠ ∅ := by
    intro h
    have hmem : A 0 0 ∈ arcCycle A :=
      mem_arcCycle_of_eq (i := 0) (t := 0) ⟨le_rfl, zero_le_one⟩ rfl
    rw [h] at hmem
    exact hmem
  have hBne : arcCycle B ≠ ∅ := by
    intro h
    have hmem : B 0 0 ∈ arcCycle B :=
      mem_arcCycle_of_eq (i := 0) (t := 0) ⟨le_rfl, zero_le_one⟩ rfl
    rw [h] at hmem
    exact hmem
  rw [odd_ncard_topBdryMeet_zero_iff_mul_of_dichotomy Q P hQ c ψ hψ hfibV hfibW A B hV hW
    hAne hBne hchordA hchordB hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans]
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
    · rw [ncard_chainMeetsLine A hendsA]
      exact ⟨0, by norm_num⟩
    · rw [ncard_chainMeetsLine B hendsB]
      exact ⟨0, by norm_num⟩

end Capping

end

end Work.Drive
