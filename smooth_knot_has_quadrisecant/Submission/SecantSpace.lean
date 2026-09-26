import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.ChordMap

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A3 (continued) — the Möbius band of secants

Kuperberg's secant space `M` is the space of *unordered* pairs of points of
the parameter circle `S¹ = AddCircle period`.  This module constructs it as
the quotient of the square by the endpoint-swap involution

    pairFlip (x, y) = (y, x)

exactly as the classical open Möbius band is obtained from the cylinder by a
half-twist: the swap is a free involution on the off-diagonal part, so

    OrderedPairs ↠ UnordCirclePairs

is a two-to-one covering of the *open* part, whose points are the secants of
the knot with distinct endpoints.  Diagonal classes `⟦(a, a)⟧` form the
boundary circle of the band (degenerate secants).

The module provides:
* the flip involution and the swap-orbit setoid / quotient `UnordCirclePairs`;
* class-level API: `class_eq_iff`, `classOf_pairFlip` (the half-twist
  identifies `(x,y)` with `(y,x)`), the diagonal-class characterisation, and
  the two-to-one fibre lemma over off-diagonal classes;
* the canonical map `unordOfOrdered : OrderedPairs → UnordCirclePairs`, its
  continuity, and its range (exactly the non-diagonal classes);
* descent machinery (`liftSwapInvariant`): any continuous function on the
  square that is invariant under `pairFlip` descends to a continuous map on
  `UnordCirclePairs`.  Secant directions are *odd* under the flip
  (`secantDir_swap`), so they descend only to *projective* directions; the
  invariant geometric functions that descend directly — and are given here —
  are the chord midpoint `unordMidpoint` and the chord length
  `unordChordLength`, both continuous, plus their restrictions to the open
  Möbius band (`mobiusMidpoint`, `mobiusChordLength`).
* The `ZMod 2`-swap action (`vaddSwap`, `AddSemigroupAction`/`AddAction`/
  `ContinuousConstVAdd`/`ProperlyDiscontinuousVAdd` instances,
  `LocallyCompactSpace OrderedPairs`), its orbit characterisation
  `mem_orbit_swap_iff` / `mobiusCover_eq_iff_orbit` (same unordered class
  iff same orbit), and freeness `stabilizer_eq_bot` /
  `free_part_eq_univ` — the exact hypotheses of
  `Topology.IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousVAdd`.
* THE DOUBLE COVER IS A COVERING MAP: `mobiusCover : OrderedPairs →
  OpenMobius` is an open quotient map (`isOpenMap_mobiusCover` — the open
  map `unordMap` restricted to the open off-diagonal square, with
  `isOpen_openMobiusSet`, `offdiag_eq_preimage`,
  `mobius_open_iff`) and hence a quotient map
  (`isQuotientMap_mobiusCover`), so the group-action covering theorem
  applies and yields **`isCoveringMap_mobiusCover : IsCoveringMap mobiusCover`**
  (a two-sheeted covering; the action is free so the covered part is all of
  `OpenMobius`).
* Hausdorffness of the secant space: `isOpenMap_unordClass` /
  `isOpenQuotientMap_unordClass` (the swap-quotient map is an open quotient
  map, since the saturation of an open set `U ∪ pairFlip '' U` is open),
  `isClosed_unordClass_kernel` (the kernel is the union of the diagonal and
  the graph of the flip, both closed), and the instance
  `T2Space UnordCirclePairs` (via `t2Space_iff_of_isOpenQuotientMap`).
  `OpenMobius` is therefore Hausdorff and `UnordCirclePairs` is compact
  Hausdorff; the parameter square is locally compact Hausdorff — the exact
  hypotheses needed for the double-cover certificate
  (`IsCoveringMap mobiusCover`) via Mathlib's
  `isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul`.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The endpoint-swap involution on pairs of parameters. -/
def pairFlip (p : AddCircle period × AddCircle period) : AddCircle period × AddCircle period :=
  (p.2, p.1)

/-- Swapping twice is the identity. -/
@[simp]
lemma pairFlip_pairFlip (p : AddCircle period × AddCircle period) : pairFlip (pairFlip p) = p := by
  rfl

/-- The flip is a homeomorphism of the parameter square. -/
lemma continuous_pairFlip : Continuous (pairFlip : AddCircle period × AddCircle period → _) := by
  unfold pairFlip
  exact continuous_snd.prodMk continuous_fst

/-- Two pairs of parameters are equivalent when they lie in the same
swap-orbit (i.e. are equal or are each other's flip). -/
def pairRel (p q : AddCircle period × AddCircle period) : Prop :=
  p = q ∨ pairFlip p = q

lemma pairRel_refl (p : AddCircle period × AddCircle period) : pairRel p p :=
  Or.inl rfl

lemma pairRel_symm {p q : AddCircle period × AddCircle period} (h : pairRel p q) : pairRel q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [← h]
    exact pairFlip_pairFlip p

lemma pairRel_trans {p q r : AddCircle period × AddCircle period}
    (hpq : pairRel p q) (hqr : pairRel q r) : pairRel p r := by
  rcases hpq with hpq | hpq
  · rcases hqr with hqr | hqr
    · exact Or.inl (hpq.trans hqr)
    · right
      rw [hpq]
      exact hqr
  · rcases hqr with hqr | hqr
    · right
      rw [← hqr]
      exact hpq
    · left
      rw [← hpq] at hqr
      exact (pairFlip_pairFlip p).symm.trans hqr

/-- The swap-orbit equivalence relation on pairs of parameters. -/
instance pairSetoid : Setoid (AddCircle period × AddCircle period) where
  r := pairRel
  iseqv := ⟨pairRel_refl, @pairRel_symm, @pairRel_trans⟩

/-- The space of unordered pairs of points of the parameter circle
(Kuperberg's secant space `M`, the open Möbius band together with its
boundary circle of degenerate secants). -/
abbrev UnordCirclePairs := Quotient pairSetoid

/-- Two ordered pairs are equal as unordered pairs iff they are equal or
swapped. -/
lemma class_eq_iff (p q : AddCircle period × AddCircle period) :
    ((⟦p⟧ : UnordCirclePairs) = ⟦q⟧) ↔ pairRel p q := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- The half-twist: an unordered pair does not see the order of its two
points. -/
@[simp]
lemma classOf_pairFlip (p : AddCircle period × AddCircle period) :
    (⟦pairFlip p⟧ : UnordCirclePairs) = ⟦p⟧ := by
  exact Quotient.sound (Or.inr (pairFlip_pairFlip p))

/-- The quotient map from the parameter square is continuous. -/
lemma continuous_classOf : Continuous (fun p : AddCircle period × AddCircle period =>
    (⟦p⟧ : UnordCirclePairs)) := by
  exact continuous_quot_mk

/-- The class of a diagonal pair `(a, a)` (a degenerate secant, on the
boundary circle of the Möbius band). -/
def diagClass (a : AddCircle period) : UnordCirclePairs := ⟦(a, a)⟧

/-- A class is the diagonal class of `a` iff both coordinates of the
representative equal `a`. -/
lemma classOf_eq_diag_iff (p : AddCircle period × AddCircle period) (a : AddCircle period) :
    ((⟦p⟧ : UnordCirclePairs) = diagClass a) ↔ p.1 = a ∧ p.2 = a := by
  constructor
  · intro h
    have h' : (⟦p⟧ : UnordCirclePairs) = ⟦(a, a)⟧ := by simpa [diagClass] using h
    have hr := (class_eq_iff p (a, a)).mp h'
    rcases hr with hr | hr
    · exact ⟨by simpa using congrArg Prod.fst hr, by simpa using congrArg Prod.snd hr⟩
    · exact ⟨by simpa [pairFlip] using congrArg Prod.snd hr,
        by simpa [pairFlip] using congrArg Prod.fst hr⟩
  · intro h
    apply Quotient.sound
    left
    exact Prod.ext h.1 h.2

/-- The fibre over an off-diagonal class has exactly the two ordered
representatives `(x, y)` and `(y, x)`. -/
lemma class_eq_of_offdiag {x y u v : AddCircle period} (_hxy : x ≠ y)
    (h : (⟦(u, v)⟧ : UnordCirclePairs) = ⟦(x, y)⟧) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hr := (class_eq_iff (u, v) (x, y)).mp h
  rcases hr with hr | hr
  · exact Or.inl ⟨by simpa using congrArg Prod.fst hr, by simpa using congrArg Prod.snd hr⟩
  · exact Or.inr ⟨by simpa [pairFlip] using congrArg Prod.snd hr,
      by simpa [pairFlip] using congrArg Prod.fst hr⟩

/-- Every class is either a diagonal class or the class of an ordered pair of
distinct parameters (i.e. is hit by `OrderedPairs`). -/
lemma exists_eq_diag_or_ordered (c : UnordCirclePairs) :
    (∃ a : AddCircle period, c = diagClass a) ∨
      ∃ p : OrderedPairs, c = (⟦(p.1.1, p.1.2)⟧ : UnordCirclePairs) := by
  refine Quotient.inductionOn c ?_
  intro p
  by_cases h : p.1 = p.2
  · left
    refine ⟨p.1, ?_⟩
    congr 1
    ext <;> simp [h]
  · right
    exact ⟨⟨p, h⟩, rfl⟩

/-- The map from ordered distinct pairs to the quotient. -/
def unordOfOrdered (p : OrderedPairs) : UnordCirclePairs := ⟦(p.1.1, p.1.2)⟧

/-- ... which is continuous. -/
lemma continuous_unordOfOrdered : Continuous unordOfOrdered := by
  unfold unordOfOrdered
  change Continuous (fun p : OrderedPairs =>
    (⟦(p.1.1, p.1.2)⟧ : UnordCirclePairs))
  have h1 : Continuous (fun p : OrderedPairs => (p : AddCircle period × AddCircle period).1) :=
    continuous_fst.comp continuous_subtype_val
  have h2 : Continuous (fun p : OrderedPairs => (p : AddCircle period × AddCircle period).2) :=
    continuous_snd.comp continuous_subtype_val
  exact continuous_classOf.comp (h1.prodMk h2)

/-- Two ordered pairs of distinct parameters give the same unordered pair iff
they are equal or swapped. -/
lemma unordOfOrdered_eq_iff (p q : OrderedPairs) :
    unordOfOrdered p = unordOfOrdered q ↔ p = q ∨ swapOrdered p = q := by
  unfold unordOfOrdered
  rw [class_eq_iff]
  constructor
  · intro h
    rcases h with h | h
    · left
      apply Subtype.ext
      exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
    · right
      apply Subtype.ext
      unfold swapOrdered
      exact Prod.ext (by simpa [pairFlip] using congrArg Prod.fst h)
        (by simpa [pairFlip] using congrArg Prod.snd h)
  · intro h
    rcases h with h | h
    · rw [h]
      exact pairRel_refl _
    · -- h : swapOrdered p = q; both ordered representatives have equal classes
      have hf : p.1.2 = q.1.1 := by
        have := congrArg (fun z : OrderedPairs =>
          (z : AddCircle period × AddCircle period).1) h
        simpa [swapOrdered] using this
      have hs : p.1.1 = q.1.2 := by
        have := congrArg (fun z : OrderedPairs =>
          (z : AddCircle period × AddCircle period).2) h
        simpa [swapOrdered] using this
      rw [← hf, ← hs]
      exact Or.inr rfl

/-- Well-definedness of a `pairFlip`-invariant function on the swap quotient. -/
lemma swapInvariant_resp {Y : Type*} {f : AddCircle period × AddCircle period → Y}
    (h : ∀ p : AddCircle period × AddCircle period, f (pairFlip p) = f p) :
    ∀ p q : AddCircle period × AddCircle period, p ≈ q → f p = f q := by
  intro p q hpq
  rcases hpq with hpq | hpq
  · exact congrArg f hpq
  · rw [← hpq]
    exact (h p).symm

/-- Descent of a `pairFlip`-invariant function to unordered pairs. -/
def liftSwapInvariant {Y : Type*} (f : AddCircle period × AddCircle period → Y)
    (h : ∀ p : AddCircle period × AddCircle period, f (pairFlip p) = f p) :
    UnordCirclePairs → Y :=
  Quotient.lift f (swapInvariant_resp h)

/-- An invariant continuous function on the square descends continuously to
the quotient. -/
lemma continuous_liftSwapInvariant {Y : Type*} [TopologicalSpace Y]
    {f : AddCircle period × AddCircle period → Y} (hf : Continuous f)
    (h : ∀ p : AddCircle period × AddCircle period, f (pairFlip p) = f p) :
    Continuous (liftSwapInvariant f h) := by
  simpa [liftSwapInvariant] using (Continuous.quotient_lift hf (swapInvariant_resp h))

/-- The value of the descended function on a class agrees with the value of
the original function on any representative. -/
@[simp]
lemma liftSwapInvariant_mk {Y : Type*} {f : AddCircle period × AddCircle period → Y}
    (h : ∀ p : AddCircle period × AddCircle period, f (pairFlip p) = f p)
    (p : AddCircle period × AddCircle period) :
    liftSwapInvariant f h ⟦p⟧ = f p := rfl

/-- The midpoint of the two endpoints of a (possibly degenerate) secant is
`pairFlip`-invariant, so it descends to unordered pairs. -/
def pairMidpoint (r : ℝ → Space) (p : AddCircle period × AddCircle period) : Space :=
  (2 : ℝ)⁻¹ • (knotMap r p.1 + knotMap r p.2)

lemma pairMidpoint_invariant (r : ℝ → Space) (p : AddCircle period × AddCircle period) :
    pairMidpoint r (pairFlip p) = pairMidpoint r p := by
  unfold pairMidpoint pairFlip
  simp [add_comm]

/-- The midpoint map on unordered pairs of parameters (i.e. on secants). -/
def unordMidpoint (r : ℝ → Space) : UnordCirclePairs → Space :=
  liftSwapInvariant (pairMidpoint r) (pairMidpoint_invariant r)

lemma unordMidpoint_mk (r : ℝ → Space) (p : AddCircle period × AddCircle period) :
    unordMidpoint r ⟦p⟧ = (2 : ℝ)⁻¹ • (knotMap r p.1 + knotMap r p.2) := rfl

/-- The midpoint depends continuously on the (unordered) pair. -/
lemma continuous_unordMidpoint (r : ℝ → Space) (h : IsSmoothKnot r) :
    Continuous (unordMidpoint r) := by
  apply continuous_liftSwapInvariant
  · -- (x,y) ↦ (1/2) • (knotMap x + knotMap y) is continuous
    change Continuous (fun p : AddCircle period × AddCircle period =>
      (2 : ℝ)⁻¹ • (knotMap r p.1 + knotMap r p.2))
    have hk : Continuous (knotMap r) := h.knotMap_continuous
    have hsum : Continuous (fun p : AddCircle period × AddCircle period =>
        knotMap r p.1 + knotMap r p.2) :=
      (hk.comp continuous_fst).add (hk.comp continuous_snd)
    exact (continuous_const_smul (γ := (2 : ℝ)⁻¹)).comp hsum

/-- The range of `unordOfOrdered` is exactly the set of non-diagonal classes
(the open Möbius band: secants with distinct endpoints). -/
lemma unordOfOrdered_range :
    Set.range unordOfOrdered = {c : UnordCirclePairs | ¬∃ a : AddCircle period, c = diagClass a} := by
  ext c
  constructor
  · rintro ⟨p, rfl⟩
    rintro ⟨a, ha⟩
    have hpair := (classOf_eq_diag_iff (p.1.1, p.1.2) a).mp ha
    exact p.2 (hpair.1.trans hpair.2.symm)
  · intro h
    rcases exists_eq_diag_or_ordered c with hd | ⟨p, hp⟩
    · exfalso
      exact h hd
    · exact ⟨p, hp.symm⟩

/-- Two diagonal classes agree iff their parameters agree (the boundary
circle is faithfully parametrized). -/
lemma diagClass_injective : Function.Injective diagClass := by
  intro a b h
  have hb : (⟦(a, a)⟧ : UnordCirclePairs) = diagClass b := by simpa [diagClass] using h
  exact (classOf_eq_diag_iff (a, a) b).mp hb |>.1

lemma swapOrdered_involutive (p : OrderedPairs) : swapOrdered (swapOrdered p) = p := by
  apply Subtype.ext
  unfold swapOrdered
  rfl

/-- The two ordered representatives of an unordered pair are distinct. -/
lemma ordered_ne_swapOrdered (p : OrderedPairs) : p ≠ swapOrdered p := by
  intro h
  have hp := congrArg (fun z : OrderedPairs => (z : AddCircle period × AddCircle period)) h
  have hfirst : p.1.1 = p.1.2 := by
    simpa [swapOrdered] using congrArg Prod.fst hp
  exact p.2 hfirst

/-- The fibre of the double cover over an unordered pair of distinct
parameters consists of exactly the two ordered representatives. -/
lemma unordOfOrdered_fiber (p : OrderedPairs) :
    {q : OrderedPairs | unordOfOrdered q = unordOfOrdered p} =
      ({p, swapOrdered p} : Set OrderedPairs) := by
  ext q
  constructor
  · intro hq
    rcases (unordOfOrdered_eq_iff q p).mp hq with h | h
    · exact Or.inl h
    · right
      exact (swapOrdered_involutive q).trans (congrArg swapOrdered h)
  · intro hq
    change unordOfOrdered q = unordOfOrdered p
    rw [unordOfOrdered_eq_iff]
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (by rw [hq]; exact swapOrdered_involutive p)

/-- The open Möbius band: unordered pairs of *distinct* parameters (the
interior of `UnordCirclePairs`, i.e. secants with distinct endpoints). -/
abbrev OpenMobius := {c : UnordCirclePairs // ¬ ∃ a : AddCircle period, c = diagClass a}

/-- Every point of the open Möbius band has an ordered representative. -/
lemma OpenMobius_representative (c : OpenMobius) :
    ∃ p : OrderedPairs, (⟦(p.1.1, p.1.2)⟧ : UnordCirclePairs) = c.1 := by
  rcases exists_eq_diag_or_ordered c.1 with hd | ⟨p, hp⟩
  · exfalso
    exact c.2 hd
  · exact ⟨p, hp.symm⟩

/-- The double cover of the open Möbius band by the ordered pairs of distinct
parameters. -/
def mobiusCover (p : OrderedPairs) : OpenMobius :=
  ⟨unordOfOrdered p, by
    rintro ⟨a, ha⟩
    have hpair := (classOf_eq_diag_iff (p.1.1, p.1.2) a).mp ha
    exact p.2 (hpair.1.trans hpair.2.symm)⟩

/-- The covering map is continuous. -/
lemma continuous_mobiusCover : Continuous mobiusCover := by
  unfold mobiusCover
  refine Continuous.subtype_mk continuous_unordOfOrdered _

/-- The double cover is surjective: every open (non-degenerate) class is the
class of some ordered pair of distinct parameters. -/
lemma mobiusCover_surjective : Function.Surjective mobiusCover := by
  intro c
  rcases OpenMobius_representative c with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  simpa [mobiusCover, unordOfOrdered] using hp

/-- The covering map is exactly two-to-one: over an ordered pair `p` the
fibre is the two-element set `{p, swapOrdered p}`. -/
lemma mobiusCover_fiber (p : OrderedPairs) :
    {q : OrderedPairs | mobiusCover q = mobiusCover p} = ({p, swapOrdered p} : Set OrderedPairs) := by
  ext q
  constructor
  · intro hq
    have hq' : unordOfOrdered q = unordOfOrdered p := by
      simpa [mobiusCover] using congrArg Subtype.val hq
    rcases (unordOfOrdered_eq_iff q p).mp hq' with hq1 | hq2
    · left
      exact hq1
    · right
      exact (swapOrdered_involutive q).trans (congrArg swapOrdered hq2)
  · intro hq
    have hcov : mobiusCover (swapOrdered p) = mobiusCover p := by
      apply Subtype.ext
      change unordOfOrdered (swapOrdered p) = unordOfOrdered p
      rw [unordOfOrdered_eq_iff]
      right
      exact swapOrdered_involutive p
    rcases hq with hq | hq
    · change mobiusCover q = mobiusCover p
      exact congrArg mobiusCover hq
    · change mobiusCover q = mobiusCover p
      exact (congrArg mobiusCover hq).trans hcov

/-- The parameter square is compact (both factors are compact circles), so the
space of unordered pairs is compact. -/
lemma isCompact_univ_unord : IsCompact (Set.univ : Set UnordCirclePairs) := by
  have hsurj : Function.Surjective (fun p : AddCircle period × AddCircle period =>
      (⟦p⟧ : UnordCirclePairs)) := by
    intro c
    refine Quotient.inductionOn c ?_
    intro p
    exact ⟨p, rfl⟩
  have hc : IsCompact (Set.range (fun p : AddCircle period × AddCircle period =>
      (⟦p⟧ : UnordCirclePairs))) := isCompact_range continuous_classOf
  simpa [hsurj.range_eq] using hc

/-- Length of the chord determined by an ordered pair of parameters
(flip-invariant, so it descends to unordered pairs). -/
def pairChordLength (r : ℝ → Space) (p : AddCircle period × AddCircle period) : ℝ :=
  ‖knotMap r p.1 - knotMap r p.2‖

lemma pairChordLength_invariant (r : ℝ → Space) (p : AddCircle period × AddCircle period) :
    pairChordLength r (pairFlip p) = pairChordLength r p := by
  unfold pairChordLength pairFlip
  exact norm_sub_rev _ _

/-- The chord length on unordered pairs of parameters (i.e. on secants). -/
def unordChordLength (r : ℝ → Space) : UnordCirclePairs → ℝ :=
  liftSwapInvariant (pairChordLength r) (pairChordLength_invariant r)

lemma unordChordLength_mk (r : ℝ → Space) (p : AddCircle period × AddCircle period) :
    unordChordLength r ⟦p⟧ = ‖knotMap r p.1 - knotMap r p.2‖ := rfl

/-- The chord length depends continuously on the (unordered) pair. -/
lemma continuous_unordChordLength (r : ℝ → Space) (h : IsSmoothKnot r) :
    Continuous (unordChordLength r) := by
  apply continuous_liftSwapInvariant
  · change Continuous (fun p : AddCircle period × AddCircle period =>
      ‖knotMap r p.1 - knotMap r p.2‖)
    have hk : Continuous (knotMap r) := h.knotMap_continuous
    exact continuous_norm.comp ((hk.comp continuous_fst).sub (hk.comp continuous_snd))

/-- The midpoint of the endpoints of a secant over the open Möbius band. -/
def mobiusMidpoint (r : ℝ → Space) : OpenMobius → Space :=
  fun c => unordMidpoint r c.1

/-- ... continuous. -/
lemma continuous_mobiusMidpoint (r : ℝ → Space) (h : IsSmoothKnot r) :
    Continuous (mobiusMidpoint r) :=
  (continuous_unordMidpoint r h).comp continuous_subtype_val

/-- The length of a secant over the open Möbius band. -/
def mobiusChordLength (r : ℝ → Space) : OpenMobius → ℝ :=
  fun c => unordChordLength r c.1

/-- ... continuous. -/
lemma continuous_mobiusChordLength (r : ℝ → Space) (h : IsSmoothKnot r) :
    Continuous (mobiusChordLength r) :=
  (continuous_unordChordLength r h).comp continuous_subtype_val

/-! ### The secant space is Hausdorff -------------------------------- -/

/-- The preimage of the image of a set under the swap-quotient map is its
swap-saturation. -/
lemma unordClass_preimage_image (U : Set (AddCircle period × AddCircle period)) :
    (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) ⁻¹'
      ((fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' U) =
      U ∪ pairFlip '' U := by
  ext x
  constructor
  · rintro ⟨u, hu, hxu⟩
    have hrel := (class_eq_iff x u).mp hxu.symm
    rcases hrel with hrel | hrel
    · left
      simpa [hrel] using hu
    · right
      refine ⟨u, hu, ?_⟩
      have h1 : pairFlip u = x := by simpa using congrArg pairFlip hrel.symm
      exact h1
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · rcases hx with ⟨u, hu, hxu⟩
      exact ⟨u, hu, by
        rw [← hxu]
        exact (classOf_pairFlip u).symm⟩

/-- The image of an open set under the swap is the preimage (the flip is an
involution). -/
lemma flip_image_eq_preimage (U : Set (AddCircle period × AddCircle period)) :
    pairFlip '' U = pairFlip ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨u, hu, hxu⟩
    have this : pairFlip x = u := by
      calc pairFlip x = pairFlip (pairFlip u) := by rw [hxu]
        _ = u := pairFlip_pairFlip u
    simpa [this] using hu
  · intro hx
    refine ⟨pairFlip x, ?_, ?_⟩
    · simpa using hx
    · simp

/-- The swap-quotient map onto `UnordCirclePairs` is an open map. -/
lemma isOpenMap_unordClass : IsOpenMap (fun p : AddCircle period × AddCircle period =>
    (⟦p⟧ : UnordCirclePairs)) := by
  intro U hU
  have hpre : IsOpen ((fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) ⁻¹'
      ((fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) '' U)) := by
    rw [unordClass_preimage_image]
    have hflip : IsOpen (pairFlip '' U) := by
      simpa [flip_image_eq_preimage] using (hU.preimage continuous_pairFlip)
    exact hU.union hflip
  change @IsOpen UnordCirclePairs
    (TopologicalSpace.coinduced (Quotient.mk' : AddCircle period × AddCircle period →
      UnordCirclePairs) inferInstance) ((fun p : AddCircle period × AddCircle period =>
      (⟦p⟧ : UnordCirclePairs)) '' U)
  exact hpre

/-- The swap-quotient map is an open quotient map (surjective, continuous,
open). -/
lemma isOpenQuotientMap_unordClass :
    IsOpenQuotientMap (fun p : AddCircle period × AddCircle period =>
      (⟦p⟧ : UnordCirclePairs)) where
  surjective := by
    intro c
    refine Quotient.inductionOn c ?_
    intro p
    exact ⟨p, rfl⟩
  continuous := continuous_classOf
  isOpenMap := isOpenMap_unordClass

/-- The kernel of the swap-quotient map is closed, so the quotient is
Hausdorff (it is the quotient of the compact Hausdorff square by the closed
swap-orbit relation). -/
lemma isClosed_unordClass_kernel :
    IsClosed {q : (AddCircle period × AddCircle period) × (AddCircle period × AddCircle period) |
        (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) q.1 =
          (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) q.2} := by
  -- the kernel is the union of the diagonal and the graph of the flip
  have hdiag : IsClosed ({q : (AddCircle period × AddCircle period) ×
      (AddCircle period × AddCircle period) | q.1 = q.2} : Set _) := by
    simpa [Set.diagonal] using (isClosed_diagonal :
      IsClosed (Set.diagonal (AddCircle period × AddCircle period)))
  have hflip : IsClosed ({q : (AddCircle period × AddCircle period) ×
      (AddCircle period × AddCircle period) | pairFlip q.1 = q.2} : Set _) := by
    -- preimage of the diagonal under (q ↦ (pairFlip q.1, q.2))
    have hF : Continuous (fun q : (AddCircle period × AddCircle period) ×
        (AddCircle period × AddCircle period) => (pairFlip q.1, q.2)) :=
      (continuous_pairFlip.comp continuous_fst).prodMk continuous_snd
    have hpre : (fun q : (AddCircle period × AddCircle period) ×
        (AddCircle period × AddCircle period) => (pairFlip q.1, q.2)) ⁻¹'
          (Set.diagonal (AddCircle period × AddCircle period)) =
        {q | pairFlip q.1 = q.2} := by
      ext q
      simp [Set.diagonal]
    rw [← hpre]
    exact (isClosed_diagonal : IsClosed (Set.diagonal (AddCircle period × AddCircle period))).preimage hF
  -- a class is determined by its swap-orbit, so the kernel is exactly this union
  have hcover : {q : (AddCircle period × AddCircle period) × (AddCircle period × AddCircle period) |
      (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) q.1 =
        (fun p : AddCircle period × AddCircle period => (⟦p⟧ : UnordCirclePairs)) q.2} =
    {q : (AddCircle period × AddCircle period) × (AddCircle period × AddCircle period) |
      q.1 = q.2} ∪
      {q : (AddCircle period × AddCircle period) × (AddCircle period × AddCircle period) |
        pairFlip q.1 = q.2} := by
    ext q
    constructor
    · intro hq
      have hrel := (class_eq_iff q.1 q.2).mp hq
      rcases hrel with hrel | hrel
      · left
        exact hrel
      · right
        exact hrel
    · intro hq
      rcases hq with hq | hq
      · change (⟦q.1⟧ : UnordCirclePairs) = ⟦q.2⟧
        rw [hq]
      · change (⟦q.1⟧ : UnordCirclePairs) = ⟦q.2⟧
        rw [class_eq_iff]
        right
        exact hq
  rw [hcover]
  exact hdiag.union hflip

/-- The space of unordered pairs of points of the circle (the secant space of
the knot, with its boundary circle of degenerate secants) is Hausdorff. -/
instance : T2Space UnordCirclePairs := by
  exact (t2Space_iff_of_isOpenQuotientMap (π := fun p : AddCircle period × AddCircle period =>
    (⟦p⟧ : UnordCirclePairs)) isOpenQuotientMap_unordClass).mpr isClosed_unordClass_kernel

/-- The open Möbius band (the interior: secants with distinct endpoints) is
Hausdorff, as a subspace of the Hausdorff secant space. -/
instance : T2Space OpenMobius := inferInstance

/-- The closed Möbius band (unordered pairs of parameters, including the
boundary circle of degenerate secants) is compact as well as Hausdorff. -/
instance : CompactSpace UnordCirclePairs := ⟨isCompact_univ_unord⟩

/-- Consequently the open Möbius band is a locally compact Hausdorff space
(an open subspace of a compact Hausdorff space), and the parameter square is
a locally compact Hausdorff space as well. -/
example : T2Space (AddCircle period × AddCircle period) := inferInstance
example : LocallyCompactSpace (AddCircle period × AddCircle period) := by
  infer_instance

/-! ### The double cover is a covering map --------------------------- -/

/-- The endpoint swap is continuous on ordered pairs of distinct parameters. -/
lemma continuous_swapOrdered : Continuous (swapOrdered : OrderedPairs → OrderedPairs) := by
  have hunder : Continuous (fun p : OrderedPairs => pairFlip (p : AddCircle period × AddCircle period)) :=
    continuous_pairFlip.comp continuous_subtype_val
  have hp : ∀ p : OrderedPairs,
      (pairFlip (p : AddCircle period × AddCircle period)).1 ≠
        (pairFlip (p : AddCircle period × AddCircle period)).2 := by
    intro p h
    exact p.2 h.symm
  exact Continuous.subtype_mk (f := fun p : OrderedPairs =>
    pairFlip (p : AddCircle period × AddCircle period))
    (p := fun q : AddCircle period × AddCircle period => q.1 ≠ q.2) hunder hp

/-- The two-element additive group `ZMod 2` acts on ordered pairs of distinct
parameters: the nontrivial element swaps the two parameters. -/
def vaddSwap (h : ZMod 2) (p : OrderedPairs) : OrderedPairs :=
  if h = 0 then p else swapOrdered p

instance : AddSemigroupAction (ZMod 2) OrderedPairs where
  vadd := vaddSwap
  add_vadd := by
    intro a b p
    change vaddSwap (a + b) p = vaddSwap a (vaddSwap b p)
    fin_cases a <;> fin_cases b <;> aesop

instance : AddAction (ZMod 2) OrderedPairs where
  zero_vadd := by
    intro p
    change vaddSwap 0 p = p
    simp [vaddSwap]

instance : ContinuousConstVAdd (ZMod 2) OrderedPairs := ContinuousConstVAdd.mk (by
  intro γ
  fin_cases γ
  · change Continuous (fun p : OrderedPairs => vaddSwap 0 p)
    simp [vaddSwap]
    exact continuous_id
  · change Continuous (fun p : OrderedPairs => vaddSwap 1 p)
    simp [vaddSwap]
    exact continuous_swapOrdered)

set_option linter.style.haveILetI false
/-- The space of ordered pairs of distinct parameters is locally compact (an
open subset of the compact square) and Hausdorff. -/
instance : LocallyCompactSpace OrderedPairs := by
  haveI : LocallyCompactSpace (AddCircle period × AddCircle period) := inferInstance
  have hd : IsClosed (Set.diagonal (AddCircle period)) :=
    (isClosed_diagonal : IsClosed (Set.diagonal (AddCircle period)))
  exact hd.isOpen_compl.locallyCompactSpace

/-- The (finite) swap action is properly discontinuous on ordered pairs. -/
instance : ProperlyDiscontinuousVAdd (ZMod 2) OrderedPairs := inferInstance

/-- The group action is exactly the swap: `h +ᵥ p = vaddSwap h p`. -/
@[simp] lemma vadd_eq_swap (h : ZMod 2) (p : OrderedPairs) : h +ᵥ p = vaddSwap h p := by
  change vaddSwap h p = vaddSwap h p
  rfl

/-- The zero element acts trivially. -/
@[simp] lemma vadd_zero_swap (p : OrderedPairs) : (0 : ZMod 2) +ᵥ p = p := by
  change vaddSwap 0 p = p
  simp [vaddSwap]

/-- The nontrivial element swaps the two parameters. -/
@[simp] lemma vadd_one_swap (p : OrderedPairs) : (1 : ZMod 2) +ᵥ p = swapOrdered p := by
  change vaddSwap 1 p = swapOrdered p
  simp [vaddSwap]

/-- The orbit of an ordered pair under the swap action is `{p, swapOrdered p}`. -/
lemma mem_orbit_swap_iff (p q : OrderedPairs) :
    p ∈ AddAction.orbit (ZMod 2) q ↔ p = q ∨ swapOrdered p = q := by
  constructor
  · rintro ⟨g, hg⟩
    by_cases hg0 : g = 0
    · left
      rw [hg0] at hg
      exact hg.symm.trans (vadd_zero_swap q)
    · right
      have hg1 : g = 1 := by
        fin_cases g
        · exfalso
          exact hg0 rfl
        · rfl
      rw [hg1] at hg
      have hp : p = swapOrdered q := hg.symm.trans (vadd_one_swap q)
      calc swapOrdered p = swapOrdered (swapOrdered q) := by rw [hp]
        _ = q := swapOrdered_involutive q
  · intro h
    rcases h with h | h
    · exact ⟨(0 : ZMod 2), (vadd_zero_swap q).trans h.symm⟩
    · have hsq : swapOrdered q = p := by
        calc swapOrdered q = swapOrdered (swapOrdered p) := by rw [h]
          _ = p := swapOrdered_involutive p
      exact ⟨(1 : ZMod 2), (vadd_one_swap q).trans hsq⟩

/-- Two ordered pairs of distinct parameters give the same unordered pair iff
they lie in the same `ZMod 2`-orbit (i.e. are equal or swapped). -/
lemma mobiusCover_eq_iff_orbit (p q : OrderedPairs) :
    mobiusCover p = mobiusCover q ↔ p ∈ AddAction.orbit (ZMod 2) q := by
  rw [mem_orbit_swap_iff]
  constructor
  · intro h
    -- mobiusCover p = mobiusCover q gives the same unordered class
    have huf : unordOfOrdered p = unordOfOrdered q := by
      simpa [mobiusCover] using congrArg Subtype.val h
    exact (unordOfOrdered_eq_iff p q).mp huf
  · intro h
    apply Subtype.ext
    change unordOfOrdered p = unordOfOrdered q
    exact (unordOfOrdered_eq_iff p q).mpr h

/-- The action is free: the stabilizer of every ordered pair of distinct
parameters is trivial. -/
lemma stabilizer_eq_bot (p : OrderedPairs) :
    AddAction.stabilizer (ZMod 2) p = ⊥ := by
  ext g
  rw [AddAction.mem_stabilizer_iff, AddSubgroup.mem_bot]
  constructor
  · intro hg
    by_cases hg0 : g = 0
    · exact hg0
    · exfalso
      have hg1 : g = 1 := by
        fin_cases g
        · exfalso
          exact hg0 rfl
        · rfl
      rw [hg1] at hg
      have : swapOrdered p = p := by rw [vadd_one_swap] at hg; exact hg
      exact ordered_ne_swapOrdered p this.symm
  · intro hg
    rw [hg]
    exact zero_vadd (ZMod 2) p

/-- All ordered pairs of distinct parameters have trivial stabilizer, so the
free part of the swap action is everything. -/
lemma free_part_eq_univ :
    ({e : OrderedPairs | AddAction.stabilizer (ZMod 2) e = ⊥} : Set OrderedPairs) = Set.univ := by
  ext e
  constructor
  · intro _
    trivial
  · intro _
    exact stabilizer_eq_bot e
/-- The carrier set of the open Möbius band inside the (closed) secant
space: the complement of the boundary circle of degenerate secants. -/
def openMobiusSet : Set UnordCirclePairs :=
  {c : UnordCirclePairs | ¬ ∃ a : AddCircle period, c = diagClass a}

/-- The swap-quotient map from the square to unordered pairs (synonym for
the quotient map `⟦·⟧`, kept for readability). -/
def unordMap (p : AddCircle period × AddCircle period) : UnordCirclePairs := ⟦p⟧

lemma unordMap_surj : Function.Surjective unordMap := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  exact ⟨p, rfl⟩

/-- The image of the off-diagonal part of the square is exactly the open
Möbius band (the non-degenerate secants). -/
lemma unordMap_image_offdiag :
    unordMap '' ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) = openMobiusSet := by
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    rintro ⟨a, ha⟩
    have := (classOf_eq_diag_iff p a).mp ha
    exact hp (this.1.trans this.2.symm)
  · intro hc
    rcases unordMap_surj c with ⟨p₀, hp₀⟩
    have hpD : p₀.1 ≠ p₀.2 := by
      intro hdiag
      apply hc
      refine ⟨p₀.1, ?_⟩
      rw [← hp₀]
      exact (classOf_eq_diag_iff p₀ p₀.1).mpr ⟨rfl, hdiag.symm⟩
    exact ⟨p₀, hpD, hp₀⟩

/-- The off-diagonal part of the parameter square is open (it is the
complement of the diagonal). -/
lemma isOpen_offdiag : IsOpen ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) := by
  have hd : IsClosed (Set.diagonal (AddCircle period)) :=
    (isClosed_diagonal : IsClosed (Set.diagonal (AddCircle period)))
  have hset : ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) =
      (Set.diagonal (AddCircle period))ᶜ := by
    ext q
    simp [Set.diagonal]
  rw [hset]
  exact hd.isOpen_compl

/-- The open Möbius band is open in the (closed) secant space: it is the
image of the open off-diagonal square under the open quotient map. -/
lemma isOpen_openMobiusSet : IsOpen openMobiusSet := by
  rw [← unordMap_image_offdiag]
  exact isOpenMap_unordClass ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _)
    isOpen_offdiag

/-- A set inside the open Möbius band is open iff its image under the
inclusion into the (closed) secant space is open (the inclusion of an open
subset is an open embedding). -/
lemma mobius_open_iff {s : Set OpenMobius} :
    IsOpen s ↔ IsOpen (Subtype.val '' s) := by
  constructor
  · intro hs
    exact isOpen_openMobiusSet.isOpenMap_subtype_val s hs
  · intro hs
    have hcont : Continuous (Subtype.val : OpenMobius → UnordCirclePairs) := continuous_subtype_val
    have hs' : IsOpen ((Subtype.val : OpenMobius → UnordCirclePairs) ⁻¹'
        (Subtype.val '' s)) := hs.preimage hcont
    simpa [Subtype.val_injective.preimage_image] using hs'

/-- The off-diagonal part of the square is precisely the preimage of the open
Möbius band under the quotient map. -/
lemma offdiag_eq_preimage :
    ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) =
      unordMap ⁻¹' openMobiusSet := by
  ext q
  constructor
  · intro hne
    rintro ⟨a, ha⟩
    have := (classOf_eq_diag_iff q a).mp ha
    exact hne (this.1.trans this.2.symm)
  · intro hq hdiag
    apply hq
    refine ⟨q.1, ?_⟩
    exact (classOf_eq_diag_iff q q.1).mpr ⟨rfl, hdiag.symm⟩

/-- The double cover `mobiusCover : OrderedPairs → OpenMobius` is an open
map (it is the restriction of the open quotient map `unordMap` to the open
off-diagonal part). -/
lemma isOpenMap_mobiusCover : IsOpenMap mobiusCover := by
  intro U hU
  rw [mobius_open_iff]
  have himg : (Subtype.val : OpenMobius → UnordCirclePairs) '' (mobiusCover '' U) =
      unordMap '' ((Subtype.val : OrderedPairs → AddCircle period × AddCircle period) '' U) := by
    ext x
    constructor
    · rintro ⟨c, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨(p : AddCircle period × AddCircle period), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨p, hp, hq⟩, rfl⟩
      refine ⟨mobiusCover p, ⟨p, hp, rfl⟩, ?_⟩
      rw [← hq]
      rfl
  rw [himg]
  have hUdec : ∃ V : Set (AddCircle period × AddCircle period), IsOpen V ∧
      U = (Subtype.val : OrderedPairs → AddCircle period × AddCircle period) ⁻¹' V := by
    rw [isOpen_induced_iff] at hU
    rcases hU with ⟨V, hV, hUeq⟩
    exact ⟨V, hV, hUeq.symm⟩
  rcases hUdec with ⟨V, hV, hUeq⟩
  have hvalU : (Subtype.val : OrderedPairs → AddCircle period × AddCircle period) '' U =
      V ∩ ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) := by
    rw [hUeq]
    rw [Set.image_preimage_eq_range_inter]
    have hrange : Set.range (Subtype.val : OrderedPairs → AddCircle period × AddCircle period) =
        ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _) := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        exact p.2
      · intro hq
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [hrange]
    rw [Set.inter_comm]
  rw [hvalU]
  have hsplit : unordMap '' (V ∩ ({q : AddCircle period × AddCircle period | q.1 ≠ q.2} : Set _)) =
      (unordMap '' V) ∩ openMobiusSet := by
    rw [offdiag_eq_preimage]
    exact Set.image_inter_preimage unordMap V openMobiusSet
  rw [hsplit]
  exact (isOpenMap_unordClass V hV).inter isOpen_openMobiusSet

/-- `mobiusCover` is an open, surjective, continuous map, hence a quotient
map: the topology of the open Möbius band is the quotient topology of the
ordered pairs of distinct parameters by the swap. -/
lemma isQuotientMap_mobiusCover : Topology.IsQuotientMap mobiusCover :=
  IsOpenMap.isQuotientMap isOpenMap_mobiusCover continuous_mobiusCover mobiusCover_surjective

/-- **The double cover is a covering map**: `mobiusCover : OrderedPairs →
OpenMobius` is a two-sheeted covering of the open Möbius band by the ordered
pairs of distinct parameters (the swap action of `ZMod 2` is properly
discontinuous and free, so Mathlib's group-action covering theorem applies
and the free part is everything). -/
lemma isCoveringMap_mobiusCover : IsCoveringMap mobiusCover := by
  have hcv : IsCoveringMapOn mobiusCover
      (mobiusCover '' {e : OrderedPairs | AddAction.stabilizer (ZMod 2) e = ⊥}) := by
    exact Topology.IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousVAdd
      (f := mobiusCover) (G := (ZMod 2)) isQuotientMap_mobiusCover
      (fun {e₁ e₂} => mobiusCover_eq_iff_orbit e₁ e₂)
  have hfree : (mobiusCover '' {e : OrderedPairs | AddAction.stabilizer (ZMod 2) e = ⊥} : Set OpenMobius) =
      Set.univ := by
    ext c
    constructor
    · intro _
      trivial
    · intro _
      rcases mobiusCover_surjective c with ⟨p, rfl⟩
      have : p ∈ {e : OrderedPairs | AddAction.stabilizer (ZMod 2) e = ⊥} := by
        rw [free_part_eq_univ]
        trivial
      exact ⟨p, this, rfl⟩
  have hcv' : IsCoveringMapOn mobiusCover Set.univ := by
    rw [← hfree]
    exact hcv
  exact (isCoveringMap_iff_isCoveringMapOn_univ).mpr hcv'

/-- Swapping the ordered representatives leaves the unordered pair unchanged. -/
lemma mobiusCover_swap (p : OrderedPairs) : mobiusCover (swapOrdered p) = mobiusCover p := by
  apply Subtype.ext
  change unordOfOrdered (swapOrdered p) = unordOfOrdered p
  rw [unordOfOrdered_eq_iff]
  right
  exact swapOrdered_involutive p
