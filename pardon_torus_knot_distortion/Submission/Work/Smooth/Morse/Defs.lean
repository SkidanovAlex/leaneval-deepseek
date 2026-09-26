import Mathlib
import Submission.Smooth
import Submission.Work.Core.Torus
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.CoreTopology.All
import Submission.Work.SurgeryInvariance.API

/-!
# Smooth level sets on the torus of the challenge: vocabulary

This file is the vocabulary of the smooth level-set / Morse chapter of the Pardon project.

## The setting

`Submission.Diffeo` is a `C^∞` diffeomorphism of `ℝ³`; for `ψ : Submission.Diffeo` the surface

`F = ψ(standard torus of revolution)`

is a smoothly embedded torus, parametrised by `param ψ p = ψ (Work.Core.torusMap p.1 p.2)`, and
`torus ψ = Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph` is the corresponding
`ParamTorus` (so that `(torus ψ).carrier = Set.range (param ψ)` and all the topological API of
`Work.CoreTopology`/`Work.SurgeryInvariance` applies to it).

For a function `g : ℝ³ → ℝ` the *sweep* is `{x | g x = t}` and the regions are
`region ψ g t = F ∩ {x | g x < t}`.

## Main definitions

* `param`, `torus`, `pullback` — the parametrisation, its `ParamTorus` structure, and `g|_F` read in
  the parameter plane;
* `levelSet`, `region` — the level set `F ∩ {g = t}` and the sublevel region `F ∩ {g < t}`;
* `criticalParam`, `criticalValues`, `IsRegularValue` — the critical points of `g|_F` in the
  parameter plane, their values, and regular values;
* `IsImmersion` — `param ψ` is an immersion (item 1 of the chapter; proved in
  `Submission.Work.Smooth.Morse.Immersion`);
* `IsCircleUnion`, `NiceLevel` — a subset of the surface which is a finite disjoint union of simple
  closed curves of the torus, and the bundle "the level set is a nice level" (item 2);
* `SublevelTransport` — the analytic input of item 3: a homotopy of the surface, starting at the
  identity, pushing the larger sublevel region into the smaller one;
* `RegularEquivalent` — the conclusion of item 3: across a regular interval the two regions are
  related by `Work.SurgeryInvariance.RegionEquivalent`;
* `DiscModel` — the local Morse model of item 4: at a critical value, passing the level adds the
  interior of an embedded disc of the surface;
* `AERegularValues` — the Sard input "almost every level is a regular value".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

/-! ## The surface, its parametrisation, and the pull-back of `g` -/

/-- The parametrisation of the surface `F = ψ(standard torus)`. -/
def param (ψ : Submission.Diffeo) : ℝ × ℝ → R3 :=
  fun p => ψ (Work.Core.torusMap p.1 p.2)

theorem param_def (ψ : Submission.Diffeo) :
    param ψ = fun p : ℝ × ℝ => ψ (Work.Core.torusMap p.1 p.2) := rfl

theorem param_apply (ψ : Submission.Diffeo) (x y : ℝ) :
    param ψ (x, y) = ψ (Work.Core.torusMap x y) := rfl

/-- The surface of the challenge, as a `Work.CoreTopology.ParamTorus`. -/
def torus (ψ : Submission.Diffeo) : Work.CoreTopology.ParamTorus :=
  Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph

@[simp] theorem torus_psi (ψ : Submission.Diffeo) (x y : ℝ) :
    (torus ψ).psi x y = param ψ (x, y) := rfl

@[simp] theorem torus_carrier (ψ : Submission.Diffeo) :
    (torus ψ).carrier = Set.range (param ψ) := rfl

theorem param_contDiff (ψ : Submission.Diffeo) : ContDiff ℝ (⊤ : ℕ∞) (param ψ) :=
  Submission.contDiff_paramDiffeo ψ

theorem param_continuous (ψ : Submission.Diffeo) : Continuous (param ψ) :=
  (param_contDiff ψ).continuous

theorem param_mem (ψ : Submission.Diffeo) (p : ℝ × ℝ) : param ψ p ∈ (torus ψ).carrier :=
  ⟨p, rfl⟩

/-- `g` restricted to the surface, read in the parameter plane. -/
def pullback (ψ : Submission.Diffeo) (g : R3 → ℝ) : ℝ × ℝ → ℝ := fun p => g (param ψ p)

theorem pullback_apply (ψ : Submission.Diffeo) (g : R3 → ℝ) (x y : ℝ) :
    pullback ψ g (x, y) = g (ψ (Work.Core.torusMap x y)) := rfl

theorem pullback_contDiff (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (pullback ψ g) :=
  hg.comp (param_contDiff ψ)

theorem pullback_contDiff_one (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (pullback ψ g) :=
  ContDiff.comp hg ((param_contDiff ψ).of_le (by simp))

theorem pullback_continuous (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g) :
    Continuous (pullback ψ g) := hg.comp (param_continuous ψ)

/-! ## Level sets and sublevel regions -/

/-- The level set `F ∩ {g = t}`. -/
def levelSet (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Set R3 :=
  (torus ψ).carrier ∩ {x : R3 | g x = t}

/-- The sublevel region `F ∩ {g < t}`. -/
def region (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Set R3 :=
  (torus ψ).carrier ∩ {x : R3 | g x < t}

@[simp] theorem mem_levelSet {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ} {x : R3} :
    x ∈ levelSet ψ g t ↔ x ∈ (torus ψ).carrier ∧ g x = t := Iff.rfl

@[simp] theorem mem_region {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ} {x : R3} :
    x ∈ region ψ g t ↔ x ∈ (torus ψ).carrier ∧ g x < t := Iff.rfl

theorem levelSet_subset_carrier (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    levelSet ψ g t ⊆ (torus ψ).carrier := inter_subset_left

theorem region_subset_carrier (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    region ψ g t ⊆ (torus ψ).carrier := inter_subset_left

/-- The sublevel regions are monotone in the level. -/
theorem region_mono (ψ : Submission.Diffeo) (g : R3 → ℝ) {a b : ℝ} (h : a ≤ b) :
    region ψ g a ⊆ region ψ g b :=
  fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- The closed sublevel region `F ∩ {g ≤ t}` (the closure, in the surface, of the region
`region ψ g t = F ∩ {g < t}`). -/
def closedRegion (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Set R3 :=
  (torus ψ).carrier ∩ {x : R3 | g x ≤ t}

@[simp] theorem mem_closedRegion {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ} {x : R3} :
    x ∈ closedRegion ψ g t ↔ x ∈ (torus ψ).carrier ∧ g x ≤ t := Iff.rfl

theorem region_subset_closedRegion (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    region ψ g t ⊆ closedRegion ψ g t := by
  intro x hx
  rw [mem_region] at hx
  rw [mem_closedRegion]
  exact ⟨hx.1, le_of_lt hx.2⟩

theorem closedRegion_subset_carrier (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    closedRegion ψ g t ⊆ (torus ψ).carrier := fun _ hx => hx.1

theorem closedRegion_eq_region_union_levelSet (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    closedRegion ψ g t = region ψ g t ∪ levelSet ψ g t := by
  ext x
  constructor
  · intro hx
    rw [mem_closedRegion] at hx
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact Or.inl (by rw [mem_region]; exact ⟨hx.1, h⟩)
    · exact Or.inr (by rw [mem_levelSet]; exact ⟨hx.1, h⟩)
  · intro hx
    rw [mem_closedRegion]
    rcases hx with h | h
    · rw [mem_region] at h; exact ⟨h.1, le_of_lt h.2⟩
    · rw [mem_levelSet] at h; exact ⟨h.1, le_of_eq h.2⟩

/-- The region below `b` is the region below `a` together with the band `{a ≤ g < b}`. -/
theorem region_eq_union_band (ψ : Submission.Diffeo) (g : R3 → ℝ) {a b : ℝ} (hab : a ≤ b) :
    region ψ g b = region ψ g a ∪ ((torus ψ).carrier ∩ {x : R3 | a ≤ g x ∧ g x < b}) := by
  ext x
  simp only [mem_region, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hxb⟩
    rcases lt_or_ge (g x) a with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h, hxb⟩
  · rintro (h | h)
    · exact ⟨h.1, lt_of_lt_of_le h.2 hab⟩
    · exact ⟨h.1, h.2.2⟩

/-- The symmetric difference of two sublevel regions is the band between the two levels. -/
theorem region_symmDiff_eq (ψ : Submission.Diffeo) (g : R3 → ℝ) {a b : ℝ} (h : a ≤ b) :
    region ψ g b \ region ψ g a = (torus ψ).carrier ∩ {x : R3 | a ≤ g x ∧ g x < b} := by
  ext x
  constructor
  · rintro ⟨hxb, hxa⟩
    refine ⟨hxb.1, ?_, hxb.2⟩
    by_contra hc
    exact hxa ⟨hxb.1, lt_of_not_ge hc⟩
  · rintro ⟨hx, hax, hxb⟩
    refine ⟨⟨hx, hxb⟩, ?_⟩
    rintro ⟨-, hxa⟩
    exact absurd hxa (not_lt.mpr hax)

/-- The band `{a ≤ g < b}` on the surface is the difference of the two sublevel regions. -/
theorem band_eq_region_symmDiff (ψ : Submission.Diffeo) (g : R3 → ℝ) {a b : ℝ} (h : a ≤ b) :
    (torus ψ).carrier ∩ {x : R3 | a ≤ g x ∧ g x < b} = region ψ g b \ region ψ g a :=
  (region_symmDiff_eq ψ g h).symm

theorem levelSet_subset_region_succ (ψ : Submission.Diffeo) (g : R3 → ℝ) {s t : ℝ} (h : s < t) :
    levelSet ψ g s ⊆ region ψ g t :=
  fun x hx => by
    simp only [mem_levelSet] at hx
    simp only [mem_region]
    exact ⟨hx.1, by rw [hx.2]; exact h⟩

/-! ## Critical points and regular values -/

/-- The critical points of `g|_F`, read in the parameter plane: the points where the derivative of
the pull-back `pullback ψ g` vanishes. -/
def criticalParam (ψ : Submission.Diffeo) (g : R3 → ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | fderiv ℝ (pullback ψ g) p = 0}

/-- The critical values of `g|_F`. -/
def criticalValues (ψ : Submission.Diffeo) (g : R3 → ℝ) : Set ℝ :=
  pullback ψ g '' criticalParam ψ g

theorem mem_criticalValues {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ} :
    t ∈ criticalValues ψ g ↔ ∃ p : ℝ × ℝ, fderiv ℝ (pullback ψ g) p = 0 ∧ pullback ψ g p = t :=
  Iff.rfl

/-- `t` is a **regular value** of `g|_F`: the level `{g = t}` contains no critical point. -/
def IsRegularValue (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Prop :=
  t ∉ criticalValues ψ g

theorem isRegularValue_iff (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) :
    IsRegularValue ψ g t ↔ ∀ p : ℝ × ℝ, pullback ψ g p = t → fderiv ℝ (pullback ψ g) p ≠ 0 := by
  constructor
  · intro h p hp hd
    exact h ⟨p, hd, hp⟩
  · rintro h ⟨p, hd, hp⟩
    exact h p hp hd

/-- The **Sard input** for the level sets: almost every level of `g|_F` is a regular value. -/
def AERegularValues (ψ : Submission.Diffeo) (g : R3 → ℝ) : Prop :=
  ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), IsRegularValue ψ g t

/-- **The Morse/Sard input in the form used by the sweep**: every bounded interval contains only
finitely many critical values of `g|_F`.

For a `C∞` (or `C²`) function on the compact surface this follows from Sard's theorem; for a Morse
function it follows because nondegenerate critical points are isolated, so there are only finitely
many critical points on the compact surface.  Mathlib contains neither, so this is carried as a
hypothesis: it is exactly the input the sweep needs (finitely many exceptional parameters, and
almost every level regular, see `AERegularValues`). -/
def LocallyFiniteCriticalValues (ψ : Submission.Diffeo) (g : R3 → ℝ) : Prop :=
  ∀ a b : ℝ, (criticalValues ψ g ∩ Set.Icc a b).Finite

/-- A function whose critical values are locally finite has at most countably many of them. -/
theorem countable_criticalValues_of_locallyFinite (ψ : Submission.Diffeo) (g : R3 → ℝ)
    (h : LocallyFiniteCriticalValues ψ g) : (criticalValues ψ g).Countable := by
  have hcover : criticalValues ψ g ⊆
      ⋃ n : ℤ, (criticalValues ψ g ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⌊t⌋, ht, ?_⟩
    exact Set.mem_Icc.mpr ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
  refine Set.Countable.mono hcover ?_
  exact Set.countable_iUnion fun n => (h _ _).countable

/-! ## Circle unions and the shape of a nice level -/

/-- A subset of the surface which is a **finite disjoint union of simple closed curves** of the
torus: finitely many `C⁰` (in the application `C¹`) simple closed curves of `torus ψ`, pairwise
disjoint, whose union is the set. -/
def IsCircleUnion (ψ : Submission.Diffeo) (Z : Set R3) : Prop :=
  ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (torus ψ)),
    (∀ i : Fin n, Work.CoreTopology.IsSimple (torus ψ) (γ i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
      Z = ⋃ i, Set.range (γ i).γ

/-- **The list of properties that make a level "nice"** (item 2 of the chapter): the level set is a
compact finite disjoint union of simple closed curves of the surface, and the corresponding
sublevel region is a compact surface with boundary (compact, and with the level set as its
frontier in the surface).

The classification of compact `1`-manifolds (a compact topological `1`-manifold without boundary is
a finite disjoint union of circles) is the input which turns the local model of a regular level
(proved in `Submission.Work.Smooth.Morse.RegularLevel` from the implicit function theorem) into
`IsCircleUnion`; it is isolated in the structure `CompactOneManifoldCircleUnion` in
`Submission.Work.Smooth.Morse.RegularLevel`. -/
structure NiceLevel (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Prop where
  /-- the level set is compact (it is closed in the compact surface) -/
  isCompact_levelSet : IsCompact (levelSet ψ g t)
  /-- the level set is a finite disjoint union of simple closed curves -/
  circleUnion : IsCircleUnion ψ (levelSet ψ g t)
  /-- the closed sublevel region is compact: `F ∩ {g ≤ t}` is a compact surface with boundary
  the level set (`closedRegion_eq_region_union_levelSet`) -/
  isCompact_closedRegion : IsCompact (closedRegion ψ g t)

theorem IsCircleUnion.subset_carrier {ψ : Submission.Diffeo} {Z : Set R3}
    (h : IsCircleUnion ψ Z) : Z ⊆ (torus ψ).carrier := by
  obtain ⟨n, γ, -, -, rfl⟩ := h
  rintro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨i, t, rfl⟩ := hx
  exact (γ i).mem t

/-- **A subset of the surface is *locally an arc***: every one of its points has a neighbourhood
`U` which is open in the surface and meets the set exactly in the image of an injective continuous
arc.  This is the local model of a regular level set (a `1`-dimensional submanifold of the
surface), and the input of the classification of compact `1`-manifolds.

It is proved for a regular level of `g|_F` in
`Submission.Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue`, from the implicit
function theorem (in the parameter plane) and the local injectivity of the parametrisation. -/
def IsLocalArc (ψ : Submission.Diffeo) (Z : Set R3) : Prop :=
  ∀ x ∈ Z, ∃ U : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (torus ψ) U ∧ x ∈ U ∧
    ∃ (I : Set ℝ) (s₀ : ℝ) (ρ : ℝ → R3),
      IsOpen I ∧ s₀ ∈ I ∧ ContinuousOn ρ I ∧ ρ s₀ = x ∧ Set.InjOn ρ I ∧
      (∀ s ∈ I, ρ s ∈ Z) ∧ (∀ y ∈ Z, y ∈ U → ∃ s ∈ I, ρ s = y)

/-- **The classification of compact `1`-manifolds**, isolated as a clearly stated input of the
chapter: a compact subset of the surface which is locally an arc is a finite disjoint union of
simple closed curves of the torus.

Mathlib contains no classification of compact `1`-manifolds, so this is the one statement of the
"smooth level set" item which is not proved here; every other consumer of item 2 only needs it in
the form of a hypothesis of this type (see
`Submission.Work.Smooth.Morse.Regular.niceLevel_of_regularValue`). -/
def CompactOneManifoldInput (ψ : Submission.Diffeo) : Prop :=
  ∀ Z : Set R3, IsCompact Z → IsLocalArc ψ Z → IsCircleUnion ψ Z

/-! ## The transport of a sublevel region across a regular interval (item 3) -/

/-- **A transport of the sublevel region across a level interval.**  `H` is a homotopy of the
surface, starting at the identity and preserving `F` at all times, whose time-one map sends the
larger sublevel region `region ψ g b` into the smaller one `region ψ g a`.

This is the datum produced by the normalised gradient flow of `g|_F` when `[a,b]` contains no
critical value: the flow moves each point of the surface down to the level `a` in time one (or into
it, if the point was already below `a`). -/
structure SublevelTransport (ψ : Submission.Diffeo) (g : R3 → ℝ) (a b : ℝ) where
  /-- the time-one map of the transport -/
  φ : R3 → R3
  /-- the homotopy, from the identity to `φ` -/
  H : ℝ → R3 → R3
  /-- the homotopy is continuous -/
  cont : Continuous (Function.uncurry H)
  /-- it starts at the identity -/
  zero : ∀ x : R3, H 0 x = x
  /-- it ends at `φ` -/
  one : ∀ x : R3, H 1 x = φ x
  /-- it preserves the surface at all times -/
  mem : ∀ u : ℝ, ∀ x : R3, x ∈ (torus ψ).carrier → H u x ∈ (torus ψ).carrier
  /-- it pushes the larger sublevel region into the smaller one -/
  maps : ∀ x : R3, x ∈ region ψ g b → φ x ∈ region ψ g a

/-- **The analytic input of item 3**, isolated in the form in which the chapter consumes it:
across every level interval `[a,b]` free of critical values the sublevel region `F ∩ {g < b}` is
transported into `F ∩ {g < a}` by a homotopy of the surface starting at the identity.

This is what the normalised gradient flow of `g|_F` provides: on the band `{a ≤ g ≤ b}` the
gradient of `g|_F` does not vanish, so the flow of `∇g/|∇g|²` moves every point of the band down to
the level `a` in time `b - a` (the field is bounded above and below on the compact band, so the
solution exists for the whole time interval and stays in the level band).  The existence of the
flow from the ODE theory is *not* proved in this chapter; `regularEquivalent_of_transport` in
`Submission.Work.Smooth.Morse.Transport` shows that this input implies `RegularEquivalent`, and the
README of the chapter records how much of the flow construction is carried by Mathlib
(`Mathlib.Analysis.ODE`). -/
def HasRegularTransport (ψ : Submission.Diffeo) (g : R3 → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → (∀ t ∈ Set.Icc a b, IsRegularValue ψ g t) →
    Nonempty (SublevelTransport ψ g a b)

/-- **Item 3, loop-level form.**  Across a level interval `[a,b]` free of critical values the two
sublevel regions `region ψ g a` and `region ψ g b` are `RegionEquivalent`: every loop of one region
is transported to a loop of the other with the same winding vector.

The transport is `SublevelTransport`; the forward direction is monotonicity (`region_mono`), the
backward direction is the transported loop, whose winding vector is unchanged because it is
homotopic to the original through the loops `u ↦ H u (γ t)`
(`Work.SurgeryInvariance.windingOf_map_eq`). -/
def RegularEquivalent (ψ : Submission.Diffeo) (g : R3 → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → (∀ t ∈ Set.Icc a b, IsRegularValue ψ g t) →
    Work.SurgeryInvariance.RegionEquivalent (torus ψ) (region ψ g a) (region ψ g b)

/-! ## The normalised gradient field of `g|_F` in the parameter plane -/

/-- The two coordinate derivatives of `G = pullback ψ g` at a parameter: the derivatives of `G` in
the directions `(1,0)` and `(0,1)` of the parameter plane. -/
noncomputable def partialD₁ (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (pullback ψ g) p (1, 0)

/-- The second coordinate derivative of `G = pullback ψ g`. -/
noncomputable def partialD₂ (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (pullback ψ g) p (0, 1)

/-- **The normalised gradient field of `G = pullback ψ g`**, in the descent direction: at a
parameter `p` where the derivative of `G` does not vanish,

`normalisedGradField ψ g p = -((∂₁G)² + (∂₂G)²)⁻¹ • (∂₁G, ∂₂G)`

is the field which lowers the level of `G` at unit speed, `dG(V p) = -1`
(`Submission.Work.Smooth.Morse.Flow.fderiv_pullback_normalisedGradField`).

The flow of `V` is the normalised gradient flow of `g|_F` in the parameter plane: it is
`2π`-periodic (the derivatives of a periodic function are periodic), so it descends to the surface
`F` along the covering `ℝ² → F`, and it transports the sublevel region `F ∩ {g < b}` into
`F ∩ {g < a}` in time `b - a`
(`Submission.Work.Smooth.Morse.Flow.sublevelTransport_of_periodicFlow`).

The two coordinate derivatives are used rather than Mathlib's `gradient` because the parameter
plane `ℝ × ℝ` carries the product (sup) norm and not the Euclidean inner product. -/
noncomputable def normalisedGradField (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    ℝ × ℝ :=
  -(((partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2)⁻¹) • (partialD₁ ψ g p, partialD₂ ψ g p)

/-- **The descent field of `G = pullback ψ g`**: the globally defined, bounded field

`descentField ψ g p = -((1 + (∂₁G)² + (∂₂G)²)⁻¹) • (∂₁G, ∂₂G)`.

Unlike `normalisedGradField`, this field has no singularity at the critical points of `G`: it is
smooth (for `g` of class `C²`), bounded by `1`, Lipschitz and `2π`-periodic
(`Submission.Work.Smooth.Morse.Flow.lipschitzWith_descentField`).  Its flow decreases `G` at rate

`ρ = (∂₁G)² + (∂₂G)²) / (1 + (∂₁G)² + (∂₂G)²) ∈ [0, 1)`,

which is bounded below by a positive constant on any critical-free level band; this is the field
whose global flow gives the transport of item 3. -/
noncomputable def descentField (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  -((1 + (partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2)⁻¹) •
    (partialD₁ ψ g p, partialD₂ ψ g p)

/-- The rate at which the descent field decreases `pullback ψ g`. -/
noncomputable def descentRate (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) : ℝ :=
  ((partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2) /
    (1 + (partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2)

theorem descentRate_nonneg (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    0 ≤ descentRate ψ g p := by
  unfold descentRate
  exact div_nonneg (by positivity) (by positivity)

theorem descentRate_lt_one (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    descentRate ψ g p < 1 := by
  have h : (0:ℝ) < 1 + (partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2 := by positivity
  rw [descentRate, div_lt_one h]
  linarith [sq_nonneg (partialD₁ ψ g p), sq_nonneg (partialD₂ ψ g p)]

/-- **The descent field lowers the level of `G = pullback ψ g` at the rate `descentRate`.** -/
theorem fderiv_pullback_descentField (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (pullback ψ g) p (descentField ψ g p) = -descentRate ψ g p := by
  have hsplit : (partialD₁ ψ g p, partialD₂ ψ g p) =
      (partialD₁ ψ g p) • ((1, 0) : ℝ × ℝ) + (partialD₂ ψ g p) • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hlin : fderiv ℝ (pullback ψ g) p (partialD₁ ψ g p, partialD₂ ψ g p) =
      (partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2 := by
    rw [hsplit, map_add, map_smul, map_smul]
    simp [partialD₁, partialD₂, pow_two, mul_comm]
  have hW : descentField ψ g p =
      -((1 + (partialD₁ ψ g p) ^ 2 + (partialD₂ ψ g p) ^ 2)⁻¹) •
        (partialD₁ ψ g p, partialD₂ ψ g p) := rfl
  rw [hW, map_smul, hlin, descentRate, smul_eq_mul, neg_mul, inv_mul_eq_div]

/-! ## The local Morse model at a critical value (item 4) -/

/-- **The local model of a nondegenerate critical value of `g|_F`.**  For all small enough
`ε > 0` the passage from the sublevel region `{g < t₀ - ε}` to `{g < t₀ + ε}` adds the interior of
an embedded disc of the surface, disjointly.

This is what the Morse lemma gives at a nondegenerate critical point of `g|_F` — a local maximum, a
local minimum or a saddle — for a small disc around the critical point: the added piece is the
trace of a small ball, which is an embedded disc of `F` (or, at a saddle, the band between the two
branches of the level set, which is also a disc of `F`). -/
def DiscModel (ψ : Submission.Diffeo) (g : R3 → ℝ) (t₀ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ D : Work.SurgeryInvariance.DiscRegion (torus ψ),
      region ψ g (t₀ + ε) = region ψ g (t₀ - ε) ∪ D.interior ∧
        Disjoint (region ψ g (t₀ - ε)) D.interior

/-- **The local model at a *first* tangency of a growing body with the surface**, in a form which
*is* satisfied by the level family of a gauge: for small `ε > 0` the region below `t₀` is empty and
the region just above `t₀` is exactly the interior of an embedded disc of the surface.

This is what happens when a growing convex body first touches `F` (the bottom of the range of the
gauge): the trace of the body on `F` is a small disc near the tangency point.  It is the local model
in the form in which the sweep of Pardon's boxes actually uses it, and it implies
`Work.SurgeryInvariance.SurgeryStepZero` and the equality of the winding spans at `t₀`
(`Work.Smooth.Morse.DiscGrowth.toSurgeryStepZero`, `…DiscGrowth.windingSpan_eq`).

Note that the stronger-looking `DiscModel` (the region at `t₀+ε` is the region at `t₀-ε` together
with a disc interior) is *only* satisfiable at a critical value at the bottom of the range of `g|_F`:
its union identity forces `region (t₀-ε)` to be clopen in the connected surface and hence empty,
which for small `ε` says `t₀ ≤ min (g|_F)` (`Work.Smooth.Morse.MorseModel.not_discModel_of_lt`).
`DiscGrowth` is that same local model with the emptiness of the lower region built in, so that it is
a satisfiable hypothesis. -/
def DiscGrowth (ψ : Submission.Diffeo) (g : R3 → ℝ) (t₀ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ region ψ g (t₀ - ε) = ∅ ∧
    ∃ D : Work.SurgeryInvariance.DiscRegion (torus ψ), region ψ g (t₀ + ε) = D.interior

/-- The local model at a critical value states that the region *gains* the interior of a disc. -/
theorem DiscModel.adds (ψ : Submission.Diffeo) (g : R3 → ℝ) {t₀ : ℝ} (h : DiscModel ψ g t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ D : Work.SurgeryInvariance.DiscRegion (torus ψ),
        region ψ g (t₀ + ε) = region ψ g (t₀ - ε) ∪ D.interior ∧
          Disjoint (region ψ g (t₀ - ε)) D.interior := h

/-! ## The local models of a level family -/

/-- **A one-parameter family of regions whose local models are those of a level family.**

Away from the finite exceptional set the loop content of the region is transported
(`Work.SurgeryInvariance.RegionEquivalent`), and at an exceptional parameter the *winding span* is
locally constant.

This is the local model which the sublevel family of a smooth function actually satisfies: the
transport across regular intervals is item 3 (`SublevelTransport.toRegionEquivalent`) and the local
constancy at the critical values is item 4 (`DiscModel.windingSpan_eq`, proved using the
one-sided span bound `Work.Smooth.Morse.WindingSpan.le_of_subset_union`).

It differs from `Work.SurgeryInvariance.SweepLoops` in one respect: at an exceptional parameter the
region is *not* required to be exactly the union of the neighbouring region with an open piece of
zero winding span.  A sublevel family never satisfies that stronger condition: the difference of
two sublevel regions always contains the level set `F ∩ {g = t₀ - ε}`
(`Work.Smooth.Morse.region_eq_union_band`), which is not open in the surface, so no union of open
pieces can equal the larger region.  See `Submission.Work.Smooth.Morse.MorseModel` for the details;
`Work.SurgeryInvariance.SweepLoops` remains the right structure for a family of spheres which is
put in general position by hand. -/
structure LevelFamily (P : Work.CoreTopology.ParamTorus) where
  /-- the region `F ∩ int(S_t)` -/
  region : ℝ → Set R3
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- away from the exceptional parameters the loop content is transported -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.RegionEquivalent P (region t) (region s)
  /-- at an exceptional parameter the winding span is locally constant -/
  crossing : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧
    ∀ s : ℝ, |s - t| < ε → Work.SurgeryInvariance.WindingSpan P (region s) =
      Work.SurgeryInvariance.WindingSpan P (region t)

end

end Work.Smooth.Morse
