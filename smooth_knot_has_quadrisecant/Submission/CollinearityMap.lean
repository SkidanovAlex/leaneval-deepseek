import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.Commons.Analysis.Calculus.ContDiff.crossProduct
import Submission.Commons.Analysis.CrossProduct.hasDerivAt_cross3

open LeanEval.KnotTheory.Quadrisecant
open scoped Matrix

/-!
# Layer A (vi) — the collinearity map (real-parameter scaffold)

The transversality analysis behind Kuperberg's structure theorem for the
trisecant locus `O` (§3) is the smooth study of the *collinearity map* on
the real parameter cube:

    Φ (a, b, m) = (r a − r b) × (r a − r m) ∈ ℝ³ ,

whose zero set (away from the diagonals) is the set of strict-trisecant
parameter triples of the smooth knot `r` (a point of `O` with its middle
point attached, in real parameters).  This module is the scaffold on which
that analysis will be built.  `r : ℝ → Space` is smooth (`IsSmoothKnot`), so
everything here is done on the *real* parameterisation `r` (the circle
quotient is not yet a smooth manifold in Mathlib); the periodicity lemmas
record that `Φ` is `period`-periodic in each argument, i.e. really lives on
the torus `(S¹)³`.

Contents:
* `cross3` — the cross product on `Space = EuclideanSpace ℝ (Fin 3)`,
  transported from Mathlib's `⨯₃` on the function space `(Fin 3 → ℝ)` via the
  `WithLp` equivalence, with its elementary identities (antisymmetry,
  self-vanishing, vanishing on the zero vectors, bilinearity, and the
  collinearity criterion `cross3 u (t • u) = 0`).
* `collinearityMap r : ℝ × (ℝ × ℝ) → Space` — the map
  `(a, b, m) ↦ (r a − r b) × (r a − r m)` (with `collinearityValue r a b m`
  the flat three-argument form).
* **smoothness**: `contDiff_collinearityMap` (`ContDiff ℝ ⊤`, hence `C¹` by
  `contDiff_one_collinearityMap` / `contDiffOn_collinearityMap`) — the map is
  smooth on all of `ℝ³`, so in particular on any locus (off-diagonal, etc.).
  The proof feeds the two smooth difference maps into the fleet-proven
  commons lemma `Commons.Analysis.Calculus.ContDiff.crossProduct`.
* degeneracies: `Φ(a, a, m) = Φ(a, b, a) = Φ(a, b, b) = 0` (a zero vector
  argument) — the trivial triples live in the zero set.
* `periodic_collinearity_arg1/2/3` — `Φ` is `period`-periodic in each of its
  three arguments (it descends to the parameter torus).

The derivative / rank analysis of `Φ` on its zero set (the actual
transversality step: `0` as a regular value in the projective sense, giving
`O` the structure of a smooth 1-manifold image under a genericity
hypothesis) is the next layer, recorded in ROADMAP.md.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The cross product on `Space = EuclideanSpace ℝ (Fin 3)`, transported
from Mathlib's `⨯₃ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → Fin 3 → ℝ` through the
`WithLp` linear equivalence. -/
def cross3 (u v : Space) : Space :=
  WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v)

/-- The cross product is antisymmetric. -/
lemma cross3_anticomm (u v : Space) : cross3 v u = -cross3 u v := by
  rw [eq_neg_iff_add_eq_zero]
  unfold cross3
  rw [← WithLp.toLp_add]
  rw [cross_anticomm' (WithLp.ofLp v) (WithLp.ofLp u)]
  simp

/-- The cross product of a vector with itself vanishes. -/
lemma cross3_self (v : Space) : cross3 v v = 0 := by
  simp [cross3]

/-- The cross product is left-linear at zero. -/
lemma cross3_zero_left (w : Space) : cross3 0 w = 0 := by
  simp [cross3]

/-- The cross product is right-linear at zero. -/
lemma cross3_zero_right (u : Space) : cross3 u 0 = 0 := by
  simp [cross3]

/-- The cross product is additive in the first argument. -/
lemma cross3_add_left (u v w : Space) : cross3 (u + v) w = cross3 u w + cross3 v w := by
  simp [cross3, crossProduct.map_add]

/-- The cross product is ℝ-linear in the first argument. -/
lemma cross3_smul_left (c : ℝ) (u v : Space) : cross3 (c • u) v = c • cross3 u v := by
  simp [cross3]

/-- The cross product is ℝ-linear in the second argument. -/
lemma cross3_smul_right (c : ℝ) (u v : Space) : cross3 u (c • v) = c • cross3 u v := by
  simp [cross3, (crossProduct (WithLp.ofLp u)).map_smul]

/-- Parallel vectors have zero cross product (the collinearity criterion). -/
lemma cross3_collinear_zero (u : Space) (t : ℝ) : cross3 u (t • u) = 0 := by
  rw [cross3_smul_right, cross3_self]
  simp

/-- A triple of real parameters `(a, b, m)`, right-associated. -/
abbrev RealParamTriple := ℝ × (ℝ × ℝ)

/-- **The collinearity map** on the real parameter cube:
`(a, b, m) ↦ (r a − r b) × (r a − r m)`.  Its zero set (away from the
diagonal planes) is the strict-trisecant locus of the smooth knot `r`, with
the middle parameter attached. -/
def collinearityMap (r : ℝ → Space) (p : RealParamTriple) : Space :=
  cross3 (r p.1 - r p.2.1) (r p.1 - r p.2.2)

/-- The flat three-argument form of the collinearity map. -/
def collinearityValue (r : ℝ → Space) (a b m : ℝ) : Space :=
  collinearityMap r (a, (b, m))

/-- The flat form, unfolded to the two difference vectors. -/
@[simp]
lemma collinearityValue_eq (r : ℝ → Space) (a b m : ℝ) :
    collinearityValue r a b m = cross3 (r a - r b) (r a - r m) := rfl

/-- The first difference-vector argument of the collinearity map is smooth. -/
lemma contDiffOn_collinearity_body1 {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    ContDiffOn ℝ ⊤ (fun p : RealParamTriple => r p.1 - r p.2.1) Set.univ := by
  apply ContDiffOn.sub
  · exact (hr.comp contDiff_fst).contDiffOn
  · exact (hr.comp (contDiff_fst.comp contDiff_snd)).contDiffOn

/-- The second difference-vector argument of the collinearity map is smooth. -/
lemma contDiffOn_collinearity_body2 {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    ContDiffOn ℝ ⊤ (fun p : RealParamTriple => r p.1 - r p.2.2) Set.univ := by
  apply ContDiffOn.sub
  · exact (hr.comp contDiff_fst).contDiffOn
  · exact (hr.comp (contDiff_snd.comp contDiff_snd)).contDiffOn

/-- **The collinearity map is smooth** (`C^∞`, hence in particular `C¹`) on
the whole parameter cube.  Proof: `r` is smooth, differences of smooth maps
are smooth, and the cross product of two smooth `EuclideanSpace ℝ (Fin 3)`-
valued maps is smooth (commons lemma
`Commons.Analysis.Calculus.ContDiff.crossProduct`). -/
lemma contDiff_collinearityMap {r : ℝ → Space} (h : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : RealParamTriple => collinearityMap r p) := by
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ⊤
    (fun p : RealParamTriple => WithLp.toLp 2
      (WithLp.ofLp (r p.1 - r p.2.1) ⨯₃ WithLp.ofLp (r p.1 - r p.2.2))) Set.univ
  apply Commons.Analysis.Calculus.ContDiff.crossProduct
  · exact contDiffOn_collinearity_body1 h.smooth
  · exact contDiffOn_collinearity_body2 h.smooth

/-- The collinearity map is `C¹`. -/
lemma contDiff_one_collinearityMap {r : ℝ → Space} (h : IsSmoothKnot r) :
    ContDiff ℝ 1 (fun p : RealParamTriple => collinearityMap r p) :=
  ContDiff.of_le (contDiff_collinearityMap h) le_top

/-- The collinearity map is `C¹` on the whole cube (hence on any locus, in
particular on the complement of the diagonal planes where the strict
trisecants live). -/
lemma contDiffOn_collinearityMap {r : ℝ → Space} (h : IsSmoothKnot r) :
    ContDiffOn ℝ 1 (fun p : RealParamTriple => collinearityMap r p) Set.univ :=
  (contDiff_one_collinearityMap h).contDiffOn

/-- Degenerate triples with `a = b` lie in the zero set: the first chord
vector vanishes. -/
lemma collinearity_diag_ab (r : ℝ → Space) (a m : ℝ) :
    collinearityValue r a a m = 0 := by
  simp [collinearityValue_eq, cross3_zero_left]

/-- Degenerate triples with `a = m` lie in the zero set: the second chord
vector vanishes. -/
lemma collinearity_diag_am (r : ℝ → Space) (a b : ℝ) :
    collinearityValue r a b a = 0 := by
  simp [collinearityValue_eq, cross3_zero_right]

/-- Degenerate triples with `b = m` lie in the zero set: the two chord
vectors are equal, and the cross product of a vector with itself vanishes. -/
lemma collinearity_diag_bm (r : ℝ → Space) (a b : ℝ) :
    collinearityValue r a b b = 0 := by
  simp [collinearityValue_eq, cross3_self]

/-- The collinearity map is `period`-periodic in its first argument `a`
(`r` is `period`-periodic). -/
lemma periodic_collinearity_arg1 {r : ℝ → Space} (h : IsSmoothKnot r) (b m : ℝ) :
    Function.Periodic (fun a : ℝ => collinearityValue r a b m) period := by
  intro a
  simp [collinearityValue_eq, h.periodic a]

/-- The collinearity map is `period`-periodic in its second argument `b`. -/
lemma periodic_collinearity_arg2 {r : ℝ → Space} (h : IsSmoothKnot r) (a m : ℝ) :
    Function.Periodic (fun b : ℝ => collinearityValue r a b m) period := by
  intro b
  simp [collinearityValue_eq, h.periodic b]

/-- The collinearity map is `period`-periodic in its third argument `m`. -/
lemma periodic_collinearity_arg3 {r : ℝ → Space} (h : IsSmoothKnot r) (a b : ℝ) :
    Function.Periodic (fun m : ℝ => collinearityValue r a b m) period := by
  intro m
  simp [collinearityValue_eq, h.periodic m]

/-! ### Elementary cross-product identities for the derivative step

The partial-derivative computations for the collinearity map (below) use the
additive/negative identities of `cross3` and the basic fact that a smooth knot
is differentiable at every parameter with derivative `velocity`. -/

/-- The cross product is additive in the second argument. -/
lemma cross3_add_right (u v w : Space) : cross3 u (v + w) = cross3 u v + cross3 u w := by
  unfold cross3
  simp [WithLp.ofLp_add, (crossProduct (WithLp.ofLp u)).map_add]

/-- The cross product is antisymmetric under negation of the first argument. -/
lemma cross3_neg_left (u v : Space) : cross3 (-u) v = -cross3 u v := by
  rw [eq_neg_iff_add_eq_zero]
  rw [← cross3_add_left]
  rw [neg_add_cancel, cross3_zero_left]

/-- The cross product is antisymmetric under negation of the second argument. -/
lemma cross3_neg_right (u v : Space) : cross3 u (-v) = -cross3 u v := by
  rw [eq_neg_iff_add_eq_zero]
  rw [← cross3_add_right]
  rw [neg_add_cancel, cross3_zero_right]

/-- Exchanging the order and flipping the sign of one argument gives a swap of
the other two arguments: `(-u) × v = v × u`. -/
lemma cross3_neg_left_swap (u v : Space) : cross3 (-u) v = cross3 v u := by
  rw [cross3_neg_left, cross3_anticomm]
  simp

/-- A smooth knot is differentiable at every real parameter, with derivative
`velocity r t` (which is nonzero by regularity). -/
lemma hasDerivAt_velocity {r : ℝ → Space} (h : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt r (velocity r t) t := by
  have h1 : ContDiff ℝ 1 r := ContDiff.of_le h.smooth (by exact le_top)
  have hd : DifferentiableAt ℝ r t := h1.differentiable_one t
  simpa [velocity] using hd.hasDerivAt

/-! ### The partial derivatives of the collinearity map

With the (fleet-proven) Leibniz rule for the cross product along curves
(`Commons.Analysis.CrossProduct.hasDerivAt_cross3`) the three partial
derivatives of `Φ` are straightforward.  Writing `v t = velocity r t` for the
velocity of the knot:

    ∂/∂b Φ(a,b,m) = (r a − r m) × v b        (the middle-argument hinge)
    ∂/∂a Φ(a,b,m) = (v a) × (r a − r m) + (r a − r b) × (v a)
    ∂/∂m Φ(a,b,m) = (v m) × (r a − r b)

(The middle one is the hinge the rank/regular-value analysis rotates
around.)  Each is a `HasDerivAt` statement for the corresponding partial
map of the flat form `collinearityValue`. -/

/-- Leibniz rule for `cross3` along two differentiable curves (local wrapper
of the commons theorem, in terms of the local `cross3`). -/
lemma hasDerivAt_cross3_curves (u v : ℝ → Space) {du dv : Space} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun x : ℝ => cross3 (u x) (v x)) (cross3 du (v t) + cross3 (u t) dv) t := by
  simpa [cross3] using (Commons.Analysis.CrossProduct.hasDerivAt_cross3 u v hu hv)

/-- The curve `x ↦ r a − r x` has derivative `− velocity r b` at `b`. -/
lemma hasDerivAt_const_sub_curve {r : ℝ → Space} (h : IsSmoothKnot r) (a b : ℝ) :
    HasDerivAt (fun x : ℝ => r a - r x) (-velocity r b) b := by
  have hsub : HasDerivAt ((fun x : ℝ => r a) - r) (0 - velocity r b) b :=
    HasDerivAt.sub (hasDerivAt_const b (r a)) (hasDerivAt_velocity h b)
  have hcong : HasDerivAt (fun x : ℝ => r a - r x) (0 - velocity r b) b := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hsub
    · filter_upwards with x
      simp
  simpa using hcong

/-- The curve `x ↦ r x − r b` has derivative `velocity r a` at `a`. -/
lemma hasDerivAt_sub_const_curve {r : ℝ → Space} (h : IsSmoothKnot r) (a b : ℝ) :
    HasDerivAt (fun x : ℝ => r x - r b) (velocity r a) a := by
  have hsub : HasDerivAt (r - fun x : ℝ => r b) (velocity r a - 0) a :=
    HasDerivAt.sub (hasDerivAt_velocity h a) (hasDerivAt_const a (r b))
  have hcong : HasDerivAt (fun x : ℝ => r x - r b) (velocity r a - 0) a := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hsub
    · filter_upwards with x
      simp
  simpa using hcong

/-- **Hinge (middle argument `b`)**: `∂/∂b Φ(a,b,m) = (r a − r m) × v(b)`,
where `v(b) = velocity r b`.  The first chord vector `r a − r b` is the only
one that moves as `b` varies; its derivative is `−v(b)`, and the sign flip
(`cross3_neg_left_swap`) turns `(−v(b)) × (r a − r m)` into
`(r a − r m) × v(b)`. -/
lemma hasDerivAt_collinearity_middle {r : ℝ → Space} (h : IsSmoothKnot r) (a m b : ℝ) :
    HasDerivAt (fun x : ℝ => collinearityValue r a x m)
      (cross3 (r a - r m) (velocity r b)) b := by
  have hu : HasDerivAt (fun x : ℝ => r a - r x) (-velocity r b) b :=
    hasDerivAt_const_sub_curve h a b
  have hv : HasDerivAt (fun x : ℝ => r a - r m) (0 : Space) b :=
    hasDerivAt_const b (r a - r m)
  have hd := hasDerivAt_cross3_curves (u := fun x : ℝ => r a - r x)
    (v := fun x : ℝ => r a - r m) (du := -velocity r b) (dv := 0) hu hv
  have hd1 : HasDerivAt (fun x : ℝ => collinearityValue r a x m)
      (cross3 (-velocity r b) (r a - r m) + cross3 (r a - r b) 0) b := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with x
      simp [collinearityValue_eq]
  apply HasDerivAt.congr_deriv hd1
  rw [cross3_zero_right, add_zero, cross3_neg_left_swap]

/-- Derivative in the *first* argument `a`: both chord vectors move, giving
the two-term Leibniz sum `(v a) × (r a − r m) + (r a − r b) × (v a)`. -/
lemma hasDerivAt_collinearity_first {r : ℝ → Space} (h : IsSmoothKnot r) (b m a : ℝ) :
    HasDerivAt (fun x : ℝ => collinearityValue r x b m)
      (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) a := by
  have hu : HasDerivAt (fun x : ℝ => r x - r b) (velocity r a) a :=
    hasDerivAt_sub_const_curve h a b
  have hv : HasDerivAt (fun x : ℝ => r x - r m) (velocity r a) a :=
    hasDerivAt_sub_const_curve h a m
  have hd := hasDerivAt_cross3_curves (u := fun x : ℝ => r x - r b)
    (v := fun x : ℝ => r x - r m) (du := velocity r a) (dv := velocity r a) hu hv
  have hd1 : HasDerivAt (fun x : ℝ => collinearityValue r x b m)
      (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) a := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with x
      simp [collinearityValue_eq]
  exact hd1

/-- Derivative in the *third* argument `m`: only the second chord vector
moves; its derivative is `−v(m)` and the sign flips give
`(v m) × (r a − r b)`. -/
lemma hasDerivAt_collinearity_third {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun x : ℝ => collinearityValue r a b x)
      (cross3 (velocity r m) (r a - r b)) m := by
  have hu : HasDerivAt (fun x : ℝ => r a - r b) (0 : Space) m :=
    hasDerivAt_const m (r a - r b)
  have hv : HasDerivAt (fun x : ℝ => r a - r x) (-velocity r m) m :=
    hasDerivAt_const_sub_curve h a m
  have hd := hasDerivAt_cross3_curves (u := fun x : ℝ => r a - r b)
    (v := fun x : ℝ => r a - r x) (du := 0) (dv := -velocity r m) hu hv
  have hd1 : HasDerivAt (fun x : ℝ => collinearityValue r a b x)
      (cross3 (0 : Space) (r a - r m) + cross3 (r a - r b) (-velocity r m)) m := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with x
      simp [collinearityValue_eq]
  apply HasDerivAt.congr_deriv hd1
  rw [cross3_zero_left, zero_add, cross3_neg_right,
    ← cross3_anticomm (u := r a - r b) (v := velocity r m)]

/-! ### Assembly: the total (directional) derivative of `Φ`

The three hinges assemble into the derivative of `Φ` along any affine line
through the cube: for a direction `d = (da, db, dm)`, the curve
`s ↦ Φ(a + s·da, b + s·db, m + s·dm)` has derivative

    da • ∂_a + db • ∂_b + dm • ∂_m

with the three partials of the hinges.  The proof differentiates the two
chord-difference curves by the chain rule (`hasDerivAt_affine_reparam`) and
applies the Leibniz rule (`hasDerivAt_cross3_curves`); the coefficient
algebra (`deriv_algebra`) collects the terms into the three partials.  This
is the coordinate form of `HasFDerivAt Φ`: the derivative along the
direction `d` is a ℝ-linear combination of the three partial vectors, so the
directional derivative map is the linear map
`d ↦ da • ∂_a + db • ∂_b + dm • ∂_m` (range = the span of the three
partials). -/

/-- Derivative of the chord-vector curve `s ↦ r (c + s·k)` at `s = 0` is
`k • velocity r c` (chain rule along an affine reparametrisation). -/
lemma hasDerivAt_affine_reparam {r : ℝ → Space} (h : IsSmoothKnot r) (c k : ℝ) :
    HasDerivAt (fun s : ℝ => r (c + s * k)) (k • velocity r c) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * k) k 0 := by
    simpa using ((hasDerivAt_id 0).mul_const k)
  have hconst : HasDerivAt (fun s : ℝ => c) (0 : ℝ) 0 := hasDerivAt_const 0 c
  have hadd : HasDerivAt ((fun s : ℝ => s * k) + fun s : ℝ => c) (k + 0) 0 := h1.add hconst
  have hcong : HasDerivAt (fun s : ℝ => s * k + c) (k + 0) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hadd
    · filter_upwards with s
      simp [Pi.add_apply, add_comm]
  have hg0 : HasDerivAt (fun s : ℝ => c + s * k) (k + 0) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hcong
    · filter_upwards with s
      simp [add_comm]
  have hg : HasDerivAt (fun s : ℝ => c + s * k) k 0 :=
    HasDerivAt.congr_deriv hg0 (by simp)
  have houter : HasDerivAt r (velocity r c) (c + 0 * k) := by
    have hc : c + 0 * k = c := by ring
    rw [hc]
    exact hasDerivAt_velocity h c
  exact HasDerivAt.scomp (0 : ℝ) houter hg

/-- The cross product is additive-under-subtraction in the first argument. -/
lemma cross3_sub_left (u v w : Space) : cross3 (u - v) w = cross3 u w - cross3 v w := by
  rw [sub_eq_add_neg, cross3_add_left, cross3_neg_left]
  abel

/-- The cross product is additive-under-subtraction in the second argument. -/
lemma cross3_sub_right (u v w : Space) : cross3 u (v - w) = cross3 u v - cross3 u w := by
  rw [sub_eq_add_neg, cross3_add_right, cross3_neg_right]
  abel

/-- Bilinear expansion of the two-term derivative expression into the three
partial combinations: `(da·A − db·B) × W + Z × (da·A − dm·M)` splits as
`da · (A×W + Z×A) + db · (−(B×W)) + dm · (−(Z×M))`. -/
lemma deriv_algebra (A B M W Z : Space) (da db dm : ℝ) :
    cross3 (da • A - db • B) W + cross3 Z (da • A - dm • M) =
      da • (cross3 A W + cross3 Z A) + db • (-cross3 B W) + dm • (-cross3 Z M) := by
  rw [cross3_sub_left, cross3_sub_right]
  rw [cross3_smul_left, cross3_smul_left, cross3_smul_right, cross3_smul_right]
  have hstep :
      (da • cross3 A W - db • cross3 B W) + (da • cross3 Z A - dm • cross3 Z M) =
        da • (cross3 A W + cross3 Z A) + -(db • cross3 B W) + -(dm • cross3 Z M) := by
    rw [show (da • cross3 A W - db • cross3 B W) + (da • cross3 Z A - dm • cross3 Z M) =
          da • cross3 A W + da • cross3 Z A + -(db • cross3 B W) + -(dm • cross3 Z M) by abel]
    rw [← smul_add]
  rw [hstep]
  rw [← smul_neg, ← smul_neg]

/-- **The derivative assembly**: along the affine line through the cube in
direction `(da, db, dm)`, the derivative of `Φ` at the point `(a, b, m)` is
`da • ∂_a + db • ∂_b + dm • ∂_m`, where the three vectors are the hinge
partials:
`∂_a = v(a) × (r a − r m) + (r a − r b) × v(a)`,
`∂_b = (r a − r m) × v(b)`,
`∂_m = v(m) × (r a − r b)`.
This is the coordinate form of `HasFDerivAt`: the directional derivative
depends ℝ-linearly on the direction with exactly these coefficients. -/
lemma hasDerivAt_collinearity_directional {r : ℝ → Space} (h : IsSmoothKnot r)
    (a b m : ℝ) (da db dm : ℝ) :
    HasDerivAt
      (fun s : ℝ => collinearityValue r (a + s * da) (b + s * db) (m + s * dm))
      (da • (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) +
        db • cross3 (r a - r m) (velocity r b) +
        dm • cross3 (velocity r m) (r a - r b)) 0 := by
  have hU : HasDerivAt (fun s : ℝ => r (a + s * da) - r (b + s * db))
      (da • velocity r a - db • velocity r b) 0 := by
    have hsub := (hasDerivAt_affine_reparam h a da).sub (hasDerivAt_affine_reparam h b db)
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hsub
    · filter_upwards with s
      simp [Pi.sub_apply]
  have hV : HasDerivAt (fun s : ℝ => r (a + s * da) - r (m + s * dm))
      (da • velocity r a - dm • velocity r m) 0 := by
    have hsub := (hasDerivAt_affine_reparam h a da).sub (hasDerivAt_affine_reparam h m dm)
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hsub
    · filter_upwards with s
      simp [Pi.sub_apply]
  have hd := hasDerivAt_cross3_curves (u := fun s : ℝ => r (a + s * da) - r (b + s * db))
    (v := fun s : ℝ => r (a + s * da) - r (m + s * dm))
    (du := da • velocity r a - db • velocity r b)
    (dv := da • velocity r a - dm • velocity r m) hU hV
  -- reshape the function side to `collinearityValue`
  have hd1 : HasDerivAt
      (fun s : ℝ => collinearityValue r (a + s * da) (b + s * db) (m + s * dm))
      (cross3 (da • velocity r a - db • velocity r b) (r (a + 0 * da) - r (m + 0 * dm)) +
        cross3 (r (a + 0 * da) - r (b + 0 * db))
          (da • velocity r a - dm • velocity r m)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with s
      simp [collinearityValue_eq]
  -- simplify the endpoint evaluations `r (a + 0 * da)` etc.
  have hd2 : HasDerivAt
      (fun s : ℝ => collinearityValue r (a + s * da) (b + s * db) (m + s * dm))
      (cross3 (da • velocity r a - db • velocity r b) (r a - r m) +
        cross3 (r a - r b) (da • velocity r a - dm • velocity r m)) 0 := by
    apply HasDerivAt.congr_deriv hd1
    simp
  -- collect the coefficients into the three hinge partials
  apply HasDerivAt.congr_deriv hd2
  rw [deriv_algebra (A := velocity r a) (B := velocity r b) (M := velocity r m)
    (W := r a - r m) (Z := r a - r b)]
  rw [← cross3_anticomm (u := velocity r b) (v := r a - r m),
    ← cross3_anticomm (u := r a - r b) (v := velocity r m)]

end LeanEval.KnotTheory.Quadrisecant
