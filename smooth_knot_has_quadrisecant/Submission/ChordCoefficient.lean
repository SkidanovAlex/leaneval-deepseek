import Mathlib
import ChallengeDeps
import Submission.KnotMap
import Submission.TorusCollinearity
import Submission.QuadrisecantChord

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S276 — the chord-coefficient of the trapped middle: continuous affine
position along a chord (VERIFIED, sorry-free) — brick-(c) sub-problem 4,
first stone

The trapped-middle measurement (S253b sub-problem 4 / S260–S262: from the
real strict betweenness `r (m̂ u) ∈ openSegment ℝ (r (a u)) (r (b u))` of
the middle knot point on the moving chord plus the endpoint windings to a
statement about the middle's parameter advance) is an analysis of *how
far along the chord* the middle knot point lies.  This module supplies
that object and its elementary API:

1. **`segmentCoeff x y z`** — for points `x, y, z` of an inner-product
   space over `ℝ`, the unique `c : ℝ` with `z = (1 − c) • x + c • y`,
   given explicitly by the inner-product formula
   `c = ⟪z − x, y − x⟫ / ‖y − x‖²` (total: `0` when the denominator
   vanishes, i.e. `x = y`, where the coefficient is meaningless);
2. **`segmentCoeff_of_mem_openSegment`** — for distinct endpoints and
   `z` strictly inside the open segment, the coefficient is strict:
   `z = (1 − c) • x + c • y ∧ 0 < c ∧ c < 1`, and the representation is
   unique (`segmentCoeff_eq_of_affine`);
3. **`continuous_segmentCoeff`** — the coefficient is *continuous in the
   data*: for continuous families `A, B, M : C(α, E)` with distinct
   endpoints `A u ≠ B u` for all `u`, the map
   `u ↦ segmentCoeff (A u) (B u) (M u)` is continuous (the formula
   `⟪M−A, B−A⟫ / ‖B−A‖²` is a composition of continuous maps, with the
   denominator nonzero; no membership hypothesis is needed — when
   `M u` does lie strictly inside the segment the value is the strict
   coefficient of `segmentCoeff_of_mem_openSegment`);
4. **knot instances** — real parameters of a smooth knot that are
   distinct as circle classes have distinct knot values
   (`r_ne_of_class_ne`), so the real endpoint and middle parameter curves
   of a circular component (S258/S261, `(a u) ≠ (b u)` as classes) give a
   continuous chord coefficient
   `continuous_knot_segmentCoeff : u ↦ segmentCoeff (r (a u)) (r (b u))
   (r (m u))`; combined with the S260 trappedness
   `r (m u) ∈ openSegment ℝ (r (a u)) (r (b u))` this coefficient is the
   strict `(0,1)`-position of the middle on its chord
   (`segmentCoeff_of_mem_openSegment` instanced), and it is invariant
   under knot-period shifts of the real representatives
   (`segmentCoeff_congr` + the periodicity of `r`), so it depends only on
   the classes — ready to be consumed by the once/twice winding
   derivations.

This is the "chord-coefficient continuity" item of the S253b route-(i)
decomposition of the trapped-middle measurement; the measurement itself
(the comparison of the middle's parameter advance with the endpoint
windings) is the continuation, recorded as open content after this
module.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

section GenericAffine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving the point of an affine combination to the difference: if
`z = (1−c) • x + c • y` then `z − x = c • (y − x)`. -/
lemma sub_of_affine_combination {x y z : E} {c : ℝ} (hz : z = (1 - c) • x + c • y) :
    z - x = c • (y - x) := by
  rw [hz]
  have hab : (1 - c) + c = 1 := by ring
  rw [smul_add_smul_eq_add_smul_sub (A := x) (B := y) (s := 1 - c) (t := c) hab]
  abel

/-- **The chord coefficient (VERIFIED def)**: for points `x, y, z` of an
inner-product space over `ℝ`, the coefficient `c` of `z` on the affine
line through `x` and `y` (`z = (1−c) • x + c • y`), given by
`⟪z − x, y − x⟫ / ‖y − x‖²` (when the endpoints are distinct this is the
unique such coefficient; with `x = y` the expression is the total
`0`-division).  When `z` lies strictly in the open segment from `x` to
`y` this coefficient lies in `(0,1)` and measures *how far along the
chord* `z` sits. -/
def segmentCoeff (x y z : E) : ℝ :=
  inner ℝ (z - x) (y - x) / ‖y - x‖ ^ 2

/-- The coefficient of a point of the open segment is strict and realises
the point affinely: `z = (1−c) • x + c • y`, `0 < c < 1` for
`c = segmentCoeff x y z` (endpoints distinct). -/
lemma segmentCoeff_of_mem_openSegment {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) :
    z = (1 - segmentCoeff x y z) • x + segmentCoeff x y z • y ∧
      0 < segmentCoeff x y z ∧ segmentCoeff x y z < 1 := by
  rcases hz with ⟨a, b, ha, hb, hab, hzab⟩
  have hzsub : z - x = b • (y - x) := by
    calc z - x = (a • x + b • y) - x := by rw [hzab]
      _ = b • (y - x) := by
        rw [smul_add_smul_eq_add_smul_sub (A := x) (B := y) (s := a) (t := b) hab]
        abel
  have hden : ‖y - x‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy)))
  have hnum : inner ℝ (z - x) (y - x) = b * ‖y - x‖ ^ 2 := by
    rw [hzsub, inner_smul_left]
    congr 1
    exact real_inner_self_eq_norm_sq (y - x)
  have hc : segmentCoeff x y z = b := by
    unfold segmentCoeff
    rw [hnum]
    have hn0 : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    field_simp [hden, hn0]
  have ha' : a = 1 - b := by linarith
  constructor
  · have hz2 : z = (1 - b) • x + b • y := by
      simpa [ha'] using hzab.symm
    have hb' : (1 - b) • x + b • y =
        (1 - segmentCoeff x y z) • x + segmentCoeff x y z • y := by
      rw [hc]
    exact hz2.trans hb'
  · constructor
    · rw [hc]
      exact hb
    · rw [hc]
      linarith

/-- A point given affinely with strict coefficient `c ∈ (0,1)` has that
coefficient: `segmentCoeff x y ((1−c) • x + c • y) = c` (endpoints
distinct). -/
lemma segmentCoeff_eq_of_affine {x y z : E} {c : ℝ} (hxy : x ≠ y)
    (hc0 : 0 < c) (hc1 : c < 1) (hz : z = (1 - c) • x + c • y) :
    segmentCoeff x y z = c := by
  have hz' : z ∈ openSegment ℝ x y := by
    refine ⟨1 - c, c, ?_, hc0, ?_, ?_⟩
    · linarith
    · ring
    · exact hz.symm
  rcases segmentCoeff_of_mem_openSegment hxy hz' with ⟨hspec, hc0', hc1'⟩
  have hd : z - x = (segmentCoeff x y z) • (y - x) := sub_of_affine_combination hspec
  have hd' : z - x = c • (y - x) := sub_of_affine_combination hz
  have hv : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  exact (coeff_eq_of_smul_eq_smul hv (hd'.symm.trans hd)).symm

/-- The coefficient is invariant under changing all three points
(congruence of the data). -/
lemma segmentCoeff_congr {x y z x' y' z' : E} (hx : x = x') (hy : y = y')
    (hz : z = z') : segmentCoeff x y z = segmentCoeff x' y' z' := by
  subst x'
  subst y'
  subst z'
  rfl

/-- The coefficient of a point of the open segment is strictly positive. -/
lemma segmentCoeff_pos {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) : 0 < segmentCoeff x y z :=
  (segmentCoeff_of_mem_openSegment hxy hz).2.1

/-- The coefficient of a point of the open segment is strictly less than
one. -/
lemma segmentCoeff_lt_one {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) : segmentCoeff x y z < 1 :=
  (segmentCoeff_of_mem_openSegment hxy hz).2.2

/-- The affine-position identity of a point of the open segment. -/
lemma segmentCoeff_spec {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) :
    z = (1 - segmentCoeff x y z) • x + segmentCoeff x y z • y :=
  (segmentCoeff_of_mem_openSegment hxy hz).1

/-- **The swap law of the chord coefficient (VERIFIED)**: measuring the
point `z` of the open segment from the other endpoint turns the
coefficient around: `segmentCoeff y x z = 1 − segmentCoeff x y z` (if
`z = (1−c)•x + c•y` then `z = (1−(1−c))•y + (1−c)•x`).  This is the
coefficient-level expression of the odd-branch flip of a once-winding
component (S261: the ordered chord `(a(u+T), b(u+T))` is the swapped
pair `(b u, a u)` up to knot periods, so the middle's chord coefficient
is `1 − λ` on the next circuit). -/
lemma segmentCoeff_swap {x y z : E} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) :
    segmentCoeff y x z = 1 - segmentCoeff x y z := by
  have hc0 : 0 < segmentCoeff x y z := segmentCoeff_pos hxy hz
  have hc1 : segmentCoeff x y z < 1 := segmentCoeff_lt_one hxy hz
  have hspec := segmentCoeff_spec hxy hz
  -- z = c • y + (1 - c) • x  (swap the two summands of the affine identity)
  have hsw : z = (1 - (1 - segmentCoeff x y z)) • y +
      (1 - segmentCoeff x y z) • x := by
    -- (1 - c) • x + c • y = c • y + (1 - c) • x by commutativity of addition
    rw [add_comm]
    -- z = (1-c)•x + c•y  with c := segmentCoeff
    simpa [sub_sub_cancel] using hspec
  have h0 : 0 < 1 - segmentCoeff x y z := by linarith
  have h1 : 1 - segmentCoeff x y z < 1 := by linarith
  have hyx : y ≠ x := Ne.symm hxy
  exact segmentCoeff_eq_of_affine hyx h0 h1 hsw

/-- **Continuity of the chord coefficient (VERIFIED)**: for continuous
families `A, B, M : C(α, E)` with distinct endpoints `A u ≠ B u` for
every `u`, the coefficient `u ↦ segmentCoeff (A u) (B u) (M u)` is
continuous — the explicit formula `⟪M−A, B−A⟫ / ‖B−A‖²` is a composition
of continuous maps (inner product continuous, subtractions continuous,
division by the never-zero squared norm).  (No membership hypothesis is
needed for continuity; in the open-segment case
`segmentCoeff_of_mem_openSegment` supplies the strictness `0 < c < 1`.) -/
theorem continuous_segmentCoeff {α : Type*} [TopologicalSpace α]
    {A B M : C(α, E)} (hne : ∀ u : α, A u ≠ B u) :
    Continuous (fun u : α => segmentCoeff (A u) (B u) (M u)) := by
  have hfun : (fun u : α => segmentCoeff (A u) (B u) (M u)) =
      (fun u : α => inner ℝ (M u - A u) (B u - A u) / ‖B u - A u‖ ^ 2) := by
    funext u
    rfl
  rw [hfun]
  have hsubA : Continuous (fun u : α => M u - A u) := M.continuous.sub A.continuous
  have hsubB : Continuous (fun u : α => B u - A u) := B.continuous.sub A.continuous
  have hnum : Continuous (fun u : α => inner ℝ (M u - A u) (B u - A u)) :=
    continuous_inner.comp (hsubA.prodMk hsubB)
  have hden : Continuous (fun u : α => ‖B u - A u‖ ^ 2) :=
    (hsubB.norm).pow 2
  refine hnum.div hden ?_
  intro u
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hne u))))

end GenericAffine

/-! ## Knot instance: real parameter lifts of a chord and the coefficient
of the trapped middle -/

/-- Distinct circle classes of real parameters of a smooth knot have
distinct knot values (the knot map on the circle is injective). -/
lemma r_ne_of_class_ne {r : ℝ → Space} (h : IsSmoothKnot r) {x y : ℝ}
    (hxy : (x : AddCircle period) ≠ (y : AddCircle period)) : r x ≠ r y := by
  intro hr
  have hk : knotMap r (x : AddCircle period) = knotMap r (y : AddCircle period) := by
    rw [knotMap_eq_r h x, knotMap_eq_r h y]
    exact hr
  exact hxy (knotMap_injective h hk)

/-- **The knot-instance of the chord-coefficient continuity (VERIFIED)**:
with continuous real parameter curves `a b m : ℝ → ℝ` (the endpoint and
middle real lifts of a chord family of a circular component, S258/S261)
whose endpoint classes are distinct at every parameter
(`(a u) ≠ (b u)` in `AddCircle period`), the middle's chord coefficient
`u ↦ segmentCoeff (r (a u)) (r (b u)) (r (m u))` is continuous.  (When
the S260 trappedness `r (m u) ∈ openSegment ℝ (r (a u)) (r (b u))` also
holds, `segmentCoeff_of_mem_openSegment` (via
`r_ne_of_class_ne`) makes this coefficient the strict `(0,1)`-position of
the middle knot point on its moving chord.) -/
theorem continuous_knot_segmentCoeff {r : ℝ → Space} (h : IsSmoothKnot r)
    {a b m : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) (hm : Continuous m)
    (hab : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period)) :
    Continuous (fun u : ℝ => segmentCoeff (r (a u)) (r (b u)) (r (m u))) := by
  have hrc : Continuous (r : ℝ → Space) := h.continuous
  let A : C(ℝ, Space) := ⟨fun u => r (a u), hrc.comp ha⟩
  let B : C(ℝ, Space) := ⟨fun u => r (b u), hrc.comp hb⟩
  let M : C(ℝ, Space) := ⟨fun u => r (m u), hrc.comp hm⟩
  have hne : ∀ u : ℝ, A u ≠ B u := by
    intro u
    exact r_ne_of_class_ne h (hab u)
  have hcont := continuous_segmentCoeff (A := A) (B := B) (M := M) hne
  have hco : (fun u : ℝ => segmentCoeff ((A : C(ℝ, Space)) u) ((B : C(ℝ, Space)) u)
      ((M : C(ℝ, Space)) u)) = (fun u : ℝ => segmentCoeff (r (a u)) (r (b u)) (r (m u))) := by
    rfl
  simpa [hco] using hcont

end LeanEval.KnotTheory.Quadrisecant
