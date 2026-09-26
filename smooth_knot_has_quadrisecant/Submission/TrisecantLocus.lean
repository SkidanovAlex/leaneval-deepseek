import Mathlib
import Submission.QuadrisecantChord
import Submission.SecantSpace

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The trisecant locus over the Möbius band of secants

Layer A (iii) of the road-map: the *trisecant vocabulary* on the secant
space.  For a smooth knot `r`, a (strict) trisecant is a chord of two
distinct parameters `a, b` of the knot together with a third parameter `m`
whose image lies strictly inside the chord — `IsMiddleOnChord r a b m`
(from `Submission/QuadrisecantChord.lean`; Kuperberg's *middle point*).  This
module records, for each unordered pair `c : OpenMobius`, whether some knot
point is a middle point of its chord (`HasMiddleOnClass r c`; the set
`trisecantSet r` is Kuperberg's `O`) and whether two distinct knot points are
middle points (`HasTwoMiddlePointsOnClass r c` — the *double points* of the
trisecant locus, i.e. quadrisecants).  The middle-point property is
order-invariant (`IsMiddleOnChord_swap`, `OOrdered_swap`) and therefore
independent of the representative of the unordered pair
(`HasMiddleOnClass_rep`); strict betweenness forces the middle parameter to
be distinct from both chord endpoints (`IsMiddleOnChord.ne_params` via the
generic `ne_left_right_of_mem_openSegment`), so a class with two middle
points supplies the four pairwise-distinct parameters of a quadrisecant
chord and vice versa (`quadrisecantChord_iff_exists_class`).
-/

section GenericAffine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point strictly between two distinct points is distinct from both
(middle points of a genuine secant are not its endpoints). -/
lemma ne_left_right_of_mem_openSegment {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) : z ≠ x ∧ z ≠ y := by
  rcases hz with ⟨a, b, ha, hb, hab, hz⟩
  constructor
  · intro hzx
    have hx : x = a • x + b • y := by
      exact (hz.trans hzx).symm
    have hzero' : (a • x + b • y) - x = 0 := by
      have hsub := congrArg (fun w : E => w - x) hx
      simpa using hsub.symm
    have h1 : a • x + b • y - x = b • (y - x) := by
      rw [smul_add_smul_eq_add_smul_sub (E := E) hab]
      abel
    have hmain : b • (y - x) = 0 := by
      rw [← h1]
      exact hzero'
    have hin : b * (inner ℝ (y - x) (y - x)) = 0 := by
      have hI : inner ℝ (b • (y - x)) (y - x) = 0 := by rw [hmain]; simp
      simpa [inner_smul_left] using hI
    have hb' : b ≠ 0 := ne_of_gt hb
    have hww : inner ℝ (y - x) (y - x) ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy.symm))
    exact hb' (mul_eq_zero.mp hin |>.resolve_right hww)
  · intro hzy
    have hzxy : a • x + b • y = y := hz.trans hzy
    have hzero' : (a • x + b • y) - y = 0 := by
      have hsub := congrArg (fun w : E => w - y) hzxy
      simpa using hsub
    have h1 : a • x + b • y - y = a • (x - y) := by
      have hstep := smul_add_smul_eq_add_smul_sub (E := E) (A := y) (B := x) (s := b) (t := a)
        (by simpa [add_comm] using hab)
      calc
        a • x + b • y - y = (b • y + a • x) - y := by rw [add_comm]
        _ = (y + a • (x - y)) - y := by rw [hstep]
        _ = a • (x - y) := by abel
    have hmain : a • (x - y) = 0 := by
      rw [← h1]
      exact hzero'
    have hin : a * (inner ℝ (x - y) (x - y)) = 0 := by
      have hI : inner ℝ (a • (x - y)) (x - y) = 0 := by rw [hmain]; simp
      simpa [inner_smul_left] using hI
    have ha' : a ≠ 0 := ne_of_gt ha
    have hww : inner ℝ (x - y) (x - y) ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    exact ha' (mul_eq_zero.mp hin |>.resolve_right hww)

end GenericAffine

/-- Swapping the endpoints of a chord does not change strict betweenness
(`openSegment` is symmetric). -/
lemma IsMiddleOnChord_swap (r : ℝ → Space) (p : OrderedPairs) (m : AddCircle period) :
    IsMiddleOnChord r p.1.2 p.1.1 m ↔ IsMiddleOnChord r p.1.1 p.1.2 m := by
  unfold IsMiddleOnChord
  constructor
  · intro hm
    simpa [openSegment_symm] using hm
  · intro hm
    simpa [openSegment_symm] using hm

/-- The middle-point property for a chord is invariant under endpoint swap:
`O` is a well-defined subset of the unordered secant space. -/
lemma OOrdered_swap (r : ℝ → Space) (p : OrderedPairs) :
    (∃ m : AddCircle period, IsMiddleOnChord r p.1.2 p.1.1 m) ↔
      (∃ m : AddCircle period, IsMiddleOnChord r p.1.1 p.1.2 m) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (IsMiddleOnChord_swap r p m).mp hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (IsMiddleOnChord_swap r p m).mpr hm⟩

/-- Strict betweenness forces the middle parameter to be neither chord
endpoint (for a smooth knot, whose `knotMap` is injective). -/
lemma IsMiddleOnChord.ne_params {r : ℝ → Space} (h : IsSmoothKnot r) {a b m : AddCircle period}
    (hab : a ≠ b) (hm : IsMiddleOnChord r a b m) : m ≠ a ∧ m ≠ b := by
  have hkm_ne : knotMap r a ≠ knotMap r b := by
    intro hk
    exact hab (knotMap_injective h hk)
  have himg := ne_left_right_of_mem_openSegment (E := Space) hkm_ne hm
  constructor
  · intro hma
    exact himg.1 (by rw [hma])
  · intro hmb
    exact himg.2 (by rw [hmb])

/-- A secant class (unordered pair of distinct parameters) is a *trisecant*
when some knot point lies strictly inside its chord (Kuperberg's set `O`). -/
def HasMiddleOnClass (r : ℝ → Space) (c : OpenMobius) : Prop :=
  ∃ m : AddCircle period, ∃ p : OrderedPairs, mobiusCover p = c ∧
    IsMiddleOnChord r p.1.1 p.1.2 m

/-- Kuperberg's `O`: the trisecant subset of the open Möbius band of secants. -/
def trisecantSet (r : ℝ → Space) : Set OpenMobius :=
  {c : OpenMobius | HasMiddleOnClass r c}

/-- Membership of `O` depends only on the unordered pair, not on the ordered
representative. -/
lemma HasMiddleOnClass_rep (r : ℝ → Space) (p q : OrderedPairs)
    (hpq : mobiusCover p = mobiusCover q) :
    (∃ m : AddCircle period, IsMiddleOnChord r p.1.1 p.1.2 m) ↔
      (∃ m : AddCircle period, IsMiddleOnChord r q.1.1 q.1.2 m) := by
  have hfib := mobiusCover_fiber p
  have hq : q ∈ ({p, swapOrdered p} : Set OrderedPairs) := by
    rw [← hfib]
    exact hpq.symm
  simp at hq
  rcases hq with rfl | hq
  · rfl
  · rw [hq]
    simpa [swapOrdered] using (OOrdered_swap r p).symm

/-- A secant class is a trisecant iff (any) one of its ordered representatives
is (with a middle point). -/
lemma HasMiddleOnClass_iff (r : ℝ → Space) (p : OrderedPairs) :
    HasMiddleOnClass r (mobiusCover p) ↔
      ∃ m : AddCircle period, IsMiddleOnChord r p.1.1 p.1.2 m := by
  constructor
  · rintro ⟨m, q, hq, hm⟩
    exact (HasMiddleOnClass_rep r p q hq.symm).mpr ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, p, rfl, hm⟩

/-- A secant class whose chord carries *two* distinct middle points — the
double point of the trisecant locus, i.e. a quadrisecant in the secant space
(Kuperberg: a quadrisecant is a pair of distinct trisecants with the same
underlying line segment). -/
def HasTwoMiddlePointsOnClass (r : ℝ → Space) (c : OpenMobius) : Prop :=
  ∃ z w : AddCircle period, z ≠ w ∧ ∃ p : OrderedPairs, mobiusCover p = c ∧
    IsMiddleOnChord r p.1.1 p.1.2 z ∧ IsMiddleOnChord r p.1.1 p.1.2 w

/-- A secant class with two middle points is exactly a quadrisecant chord
(four pairwise-distinct parameters with two strictly inside the chord of the
other two). -/
lemma quadrisecantChord_iff_exists_class {r : ℝ → Space} (h : IsSmoothKnot r) :
    QuadrisecantChord r ↔ ∃ c : OpenMobius, HasTwoMiddlePointsOnClass r c := by
  constructor
  · rintro ⟨a, b, z, w, hd, hz, hw⟩
    refine ⟨mobiusCover ⟨(a, b), hd.1⟩, z, w, ?_, ⟨(a, b), hd.1⟩, rfl, hz, hw⟩
    exact hd.2.2.2.2.2
  · rintro ⟨c, z, w, hzw, p, hp, hzp, hwp⟩
    let a : AddCircle period := p.1.1
    let b : AddCircle period := p.1.2
    have hab : a ≠ b := p.2
    have hzn : z ≠ a ∧ z ≠ b := IsMiddleOnChord.ne_params h hab hzp
    have hwn : w ≠ a ∧ w ≠ b := IsMiddleOnChord.ne_params h hab hwp
    refine ⟨a, b, z, w, ?_, ?_, ?_⟩
    · exact ⟨hab, hzn.1.symm, hwn.1.symm, hzn.2.symm, hwn.2.symm, hzw⟩
    · simpa [a, b] using hzp
    · simpa [a, b] using hwp

/-- A quadrisecant in the trusted sense exists iff some secant class of the
open Möbius band has two middle points (the double-point formulation of the
Kuperberg contradiction, at class level). -/
lemma hasQuadrisecant_iff_exists_class {r : ℝ → Space} (h : IsSmoothKnot r) :
    HasQuadrisecant r ↔ ∃ c : OpenMobius, HasTwoMiddlePointsOnClass r c := by
  rw [hasQuadrisecant_iff_quadrisecantChord h]
  exact quadrisecantChord_iff_exists_class h

end LeanEval.KnotTheory.Quadrisecant
