/-
# `Work.EL` — shared vocabulary of the equator-leak (EL) argument

This module fixes the language in which the EL areas (the plane topology of external rays in
the *dynamical* plane of the antiholomorphic quadratic family `T_c(z) = z̄² + c`) are phrased.
It is the dynamical-plane analogue of `Work.Top`, which was written abstractly in `(Mb, Φ)`.
Accordingly the whole API of `Work.Top` (`rayPt`, `paramRay`, `eqArc`, `rayPiece`, `potential`)
is reused verbatim at `Mb := K c` and `Φ := dynPhi c φ`, the Böttcher coordinate of the
dynamical plane extended by `0` on the filled Julia set.

The Böttcher homeomorphism is *not* constructed here; it enters every statement as the
explicit hypothesis `hN : DynB c φ` (Nakane's data for the dynamical plane), together, where
the dynamics is used, with `IsDynBottcher c φ`.

## Main definitions

* `Work.EL.K c` : the filled Julia set of `T_c`;
* `Work.EL.dynPhi c φ`, `Work.EL.DynB c φ`, `Work.EL.pot` : the Böttcher data of the
  dynamical plane and its potential;
* `Work.EL.T`, `Work.EL.arcLen`, `Work.EL.InArc`, `Work.EL.InClosedArc` : the angle doubling
  map `θ ↦ -2θ mod 1`, the length and the membership of (open, closed) cyclic arcs;
* `Work.EL.LandsN hN θ y` : the ray of angle `θ` lands at `y`, in `Work.Top`'s vocabulary;
* `Work.EL.CoPair hN` : a pair of rays that co-land;
* `Work.EL.pairCurve`, `Work.EL.pairSide`, `Work.EL.pairSideThroughArc`, `Work.EL.pairSideNear` :
  the curve `R(a) ∪ {y} ∪ R(b)` and its two sides;
* `Work.EL.PolyAdmissible`, `Work.EL.polyCurve`, `Work.EL.polyRegion` : ray polygons and the
  region they bound;
* `Work.EL.F c = (T_c)^{10} = (Tsq c)^[5]`, the holomorphic degree-1024 map used by the nests;
* `Work.EL.RootParabolic c` : a root-parabolic parameter of the period-5 component of `H`
  (the input bundle produced on the F side).
-/
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.ParamRays.Basic
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The dynamical plane and its Böttcher data -/

/-- The filled Julia set of `T_c`: the "dynamical plane" copy of the connectedness locus. -/
abbrev K (c : ℂ) : Set ℂ := Work.ParamRays.filledJulia c

/-- The dynamical Böttcher coordinate of `T_c`, extended by `0` on the filled Julia set. -/
def dynPhi (c : ℂ) (φ : ℂ → ℂ) : ℂ → ℂ := fun z => if z ∈ K c then 0 else φ z

theorem dynPhi_of_mem {c : ℂ} {φ : ℂ → ℂ} {z : ℂ} (hz : z ∈ K c) : dynPhi c φ z = 0 := by
  simp [dynPhi, hz]

theorem dynPhi_of_notMem {c : ℂ} {φ : ℂ → ℂ} {z : ℂ} (hz : z ∉ K c) : dynPhi c φ z = φ z := by
  simp [dynPhi, hz]

/-- **Dynamical Böttcher data**: `Work.Top`'s Nakane interface `NakaneData Mb Φ`, instantiated
at `Mb := K c` and `Φ := dynPhi c φ`.  This is the hypothesis `hN` under which the plane
topology of the rays of the dynamical plane is developed. -/
abbrev DynB (c : ℂ) (φ : ℂ → ℂ) : Type := Work.Top.NakaneData (K c) (dynPhi c φ)

/-- The potential of the dynamical plane: `log ‖φ z‖` off the filled Julia set, `0` on it. -/
def pot {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z : ℂ) : ℝ :=
  Work.Top.potential (K c) (dynPhi c φ) z

@[simp] theorem pot_apply {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z : ℂ) :
    pot hN z = Work.Top.potential (K c) (dynPhi c φ) z := rfl

theorem pot_of_mem {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) {z : ℂ} (hz : z ∈ K c) : pot hN z = 0 :=
  Work.Top.potential_of_mem hz

theorem pot_of_notMem {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) {z : ℂ} (hz : z ∉ K c) :
    pot hN z = Real.log ‖dynPhi c φ z‖ := Work.Top.potential_of_not_mem hz

theorem pot_eq_zero_iff {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z : ℂ) :
    pot hN z = 0 ↔ z ∈ K c := Work.Top.NakaneData.potential_eq_zero_iff hN z

theorem pot_nonneg {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z : ℂ) : 0 ≤ pot hN z :=
  Work.Top.NakaneData.potential_nonneg hN z

/-- The point of the ray of angle `θ` at level `t > 1`, in the dynamical plane. -/
abbrev rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (θ t : ℝ) : ℂ :=
  Work.Top.NakaneData.rayPt hN θ t

/-- The ray of angle `θ` in the dynamical plane. -/
abbrev paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (θ : ℝ) : Set ℂ :=
  Work.Top.NakaneData.paramRay hN θ

/-- The piece of the ray of angle `β` between the levels `t₀` and `R`. -/
abbrev rayPiece {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (β t₀ R : ℝ) : Set ℂ :=
  Work.Top.NakaneData.rayPiece hN β t₀ R

/-- The equipotential arc of level `R` between the angles `β₁` and `β₂`. -/
abbrev eqArc {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (β₁ β₂ R : ℝ) : Set ℂ :=
  Work.Top.NakaneData.eqArc hN β₁ β₂ R

theorem rayPt_notMem_K {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    rayPt hN θ t ∉ K c := Work.Top.NakaneData.rayPt_notMem hN ht

theorem pot_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    pot hN (rayPt hN θ t) = Real.log t := Work.Top.NakaneData.potential_rayPt hN ht

theorem paramRay_subset_compl {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (θ : ℝ) :
    paramRay hN θ ⊆ (K c)ᶜ := Work.Top.NakaneData.paramRay_subset_compl hN θ

theorem rayPt_mem_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    rayPt hN θ t ∈ paramRay hN θ :=
  ⟨rayPt_notMem_K hN ht, t, ht, Work.Top.NakaneData.Phi_rayPt hN ht⟩

theorem isCompact_le_pot {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (t : ℝ) :
    IsCompact {z : ℂ | pot hN z ≤ t} := Work.Top.NakaneData.isCompact_le_potential hN t

/-! ## Angles on the circle `ℝ/ℤ` -/

/-- The angle-doubling map of the antiholomorphic quadratic family: `θ ↦ -2θ mod 1`. -/
def T (θ : ℝ) : ℝ := Int.fract (-2 * θ)

/-- The (counterclockwise) length of the cyclic arc from `a` to `b`. -/
def arcLen (a b : ℝ) : ℝ := Int.fract (b - a)

/-- `x` lies in the open counterclockwise arc `(a, b)`. -/
def InArc (x a b : ℝ) : Prop := 0 < Int.fract (x - a) ∧ Int.fract (x - a) < arcLen a b

/-- `x` lies in the closed counterclockwise arc `[a, b]`. -/
def InClosedArc (x a b : ℝ) : Prop := 0 ≤ Int.fract (x - a) ∧ Int.fract (x - a) ≤ arcLen a b

theorem arcLen_nonneg (a b : ℝ) : 0 ≤ arcLen a b := Int.fract_nonneg _

theorem arcLen_lt_one (a b : ℝ) : arcLen a b < 1 := Int.fract_lt_one _

theorem InArc.fract_pos {x a b : ℝ} (h : InArc x a b) : 0 < Int.fract (x - a) := h.1

theorem InArc.fract_lt {x a b : ℝ} (h : InArc x a b) : Int.fract (x - a) < arcLen a b := h.2

theorem InArc.inClosedArc {x a b : ℝ} (h : InArc x a b) : InClosedArc x a b :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem InArc.fract_ne_zero {x a b : ℝ} (h : InArc x a b) : Int.fract (x - a) ≠ 0 :=
  ne_of_gt h.1

/-! ## Landing -/

/-- The ray of angle `θ` lands at `y`: the ray points of level `t → 1⁺` converge to `y`. -/
def LandsN {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (θ : ℝ) (y : ℂ) : Prop :=
  Filter.Tendsto (fun t : ℝ => rayPt hN θ t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y)

/-- A pair of rays which co-land at the common point `y`. -/
structure RawPair where
  /-- the first angle. -/
  a : ℝ
  /-- the second angle. -/
  b : ℝ
  /-- the common landing point. -/
  y : ℂ

/-- A pair of rays of the dynamical plane which co-land at `y`. -/
structure CoPair {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) extends RawPair where
  /-- the ray of angle `a` lands at `y`. -/
  lands_a : LandsN hN a y
  /-- the ray of angle `b` lands at `y`. -/
  lands_b : LandsN hN b y

namespace RawPair

/-- The curve `R(a) ∪ {y} ∪ R(b)` of a pair of rays. -/
def curve {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (P : RawPair) : Set ℂ :=
  paramRay hN P.a ∪ {P.y} ∪ paramRay hN P.b

/-- The side of the curve of `P` containing the points of the plane whose external angle lies
in the cyclic arc `(θ₁, θ₂)`; the reference point is the ray point of level `2` at the middle
of that arc. -/
def sideThrough {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (P : RawPair) (θ₁ θ₂ : ℝ) : Set ℂ :=
  connectedComponentIn (curve hN P)ᶜ (rayPt hN (θ₁ + arcLen θ₁ θ₂ / 2) 2)

/-- The **far side** of a pair: the side through the arc of its own two angles. -/
def side {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (P : RawPair) : Set ℂ :=
  sideThrough hN P P.a P.b

/-- The **near side** of a pair: the side through the complementary arc, i.e. the arc from `b`
to `a`. -/
def sideNear {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (P : RawPair) : Set ℂ :=
  sideThrough hN P P.b P.a

end RawPair

/-- The curve `R(a) ∪ {y} ∪ R(b)` of a co-landing pair. -/
def pairCurve {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) : Set ℂ :=
  RawPair.curve hN P.toRawPair

/-- The side of the curve of `P` containing the points of the plane whose external angle lies
in the cyclic arc `(θ₁, θ₂)`. -/
def pairSideThroughArc {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN)
    (θ₁ θ₂ : ℝ) : Set ℂ :=
  RawPair.sideThrough hN P.toRawPair θ₁ θ₂

/-- The **far side** of a co-landing pair: the side through the arc of its own angles. -/
def pairSide {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) : Set ℂ :=
  pairSideThroughArc P P.a P.b

/-- The **near side** of a co-landing pair: the side through the complementary arc. -/
def pairSideNear {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) : Set ℂ :=
  pairSideThroughArc P P.b P.a

@[simp] theorem pairSide_eq {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) :
    pairSide P = RawPair.side hN P.toRawPair := rfl

@[simp] theorem pairSideNear_eq {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) :
    pairSideNear P = RawPair.sideNear hN P.toRawPair := rfl

theorem mem_pairCurve_iff {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) (z : ℂ) :
    z ∈ pairCurve P ↔ z ∈ paramRay hN P.a ∨ z = P.y ∨ z ∈ paramRay hN P.b := by
  simp only [pairCurve, RawPair.curve, Set.mem_union, Set.mem_singleton_iff]
  tauto

/-! ## Ray polygons and the region they bound -/

/-- A list of reals is **strictly cyclically ordered**: it is strictly increasing (as a list)
and all of its entries lie in `[head, head + 1)`. -/
def CyclicStrict (l : List ℝ) : Prop :=
  l ≠ [] ∧ l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < l.headD 0 + 1

/-- The data of a **ray polygon**: a nonempty list of co-landing pairs whose `2m` angles are
strictly cyclically ordered and whose landing points are pairwise distinct. -/
structure PolyAdmissible {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (ps : List (CoPair hN)) : Prop
    where
  /-- the list of pairs is nonempty. -/
  ne : ps ≠ []
  /-- the angles `a₀ < b₀ < a₁ < b₁ < ⋯ < a_{m-1} < b_{m-1} < a₀ + 1` are cyclically ordered. -/
  cyc : CyclicStrict (ps.flatMap fun P => [P.a, P.b])
  /-- the landing points of the pairs are pairwise distinct. -/
  inj : ps.Pairwise fun P Q => P.y ≠ Q.y

/-- The **ray polygon** with boundary the ray pieces (below level `R`) at the `2m` angles, the
landing points, and the equipotential arcs at level `R` running through the *near* arcs (the
complementary arcs of the pairs). -/
def polyCurve {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (ps : List (CoPair hN)) (R : ℝ) : Set ℂ :=
  {z : ℂ | (∃ P ∈ ps, z = P.y ∨ z ∈ rayPiece hN P.a 0 R ∨ z ∈ rayPiece hN P.b 0 R) ∨
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, (∀ P ∈ ps, ¬ InArc θ P.a P.b) ∧ z = rayPt hN θ R}

/-- The middle of the **near arc** following the first pair of the list, used as the reference
point of the component of the complement of `polyCurve` which is the region. -/
def midNear {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} : List (CoPair hN) → ℝ
  | P :: Q :: _ => P.b + Int.fract (Q.a - P.b) / 2
  | [P] => P.b + Int.fract (P.a + 1 - P.b) / 2
  | [] => 0

/-- The **region** of a ray polygon: the component of the complement of `polyCurve` containing
the ray point of level `√R` in the first near arc.  For an admissible polygon and `1 < R` this
is the bounded side of the Jordan curve `polyCurve`. -/
def polyRegion {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (ps : List (CoPair hN)) (R : ℝ) : Set ℂ :=
  connectedComponentIn (polyCurve ps R)ᶜ (rayPt hN (midNear ps) (Real.sqrt R))

theorem polyRegion_subset_compl {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (ps : List (CoPair hN))
    (R : ℝ) : polyRegion ps R ⊆ (polyCurve ps R)ᶜ :=
  connectedComponentIn_subset _ _

theorem isPreconnected_polyRegion {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (ps : List (CoPair hN))
    (R : ℝ) : IsPreconnected (polyRegion ps R) :=
  isPreconnected_connectedComponentIn

/-- The **uniformization input** which the EL area consumes in the form in which it will be
supplied by the copied `Work.Analysis.Complex.simplyConnectedSpace_of_isBounded_isConnected_compl`:
a bounded, open, connected plane set with connected complement is simply connected. -/
def PlaneSimplyConnectedInput : Prop :=
  ∀ U : Set ℂ, Bornology.IsBounded U → IsOpen U → IsConnected U → IsPreconnected Uᶜ →
    SimplyConnectedSpace ↥U

/-! ## The tripod at the branch point `b₂` -/

/-- The three rays of the **tripod** at the branch point `b₂`: the rays of angles `22/63`,
`25/63`, `37/63` land at the common point `y` (the angle `22/63 + 1` is the same ray as
`22/63`, recorded separately because the third arm is naturally bounded by it). -/
structure Tripod {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) where
  /-- the branch point. -/
  y : ℂ
  /-- the ray of angle `22/63` lands at `y`. -/
  lands₁ : LandsN hN (22 / 63) y
  /-- the ray of angle `25/63` lands at `y`. -/
  lands₂ : LandsN hN (25 / 63) y
  /-- the ray of angle `37/63` lands at `y`. -/
  lands₃ : LandsN hN (37 / 63) y
  /-- the ray of angle `22/63 + 1` lands at `y`. -/
  lands₁' : LandsN hN (22 / 63 + 1) y

namespace Tripod

/-- The tripod curve: the three rays together with their common landing point. -/
def curve {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : Set ℂ :=
  paramRay hN (22 / 63) ∪ {T.y} ∪ paramRay hN (25 / 63) ∪ paramRay hN (37 / 63)

/-- The pair of rays bounding the arm `A` of the tripod (`22/63`, `25/63`). -/
def pairA {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : CoPair hN where
  toRawPair := ⟨22 / 63, 25 / 63, T.y⟩
  lands_a := T.lands₁
  lands_b := T.lands₂

/-- The pair of rays bounding the arm `B` of the tripod (`25/63`, `37/63`). -/
def pairB {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : CoPair hN where
  toRawPair := ⟨25 / 63, 37 / 63, T.y⟩
  lands_a := T.lands₂
  lands_b := T.lands₃

/-- The pair of rays bounding the arm `C` of the tripod (`37/63`, `85/63`). -/
def pairC {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : CoPair hN where
  toRawPair := ⟨37 / 63, 22 / 63 + 1, T.y⟩
  lands_a := T.lands₃
  lands_b := T.lands₁'

/-- The **arm `A`** of the tripod: the side of the pair `(22/63, 25/63)` through its own arc. -/
def armA {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : Set ℂ := pairSide (pairA T)

/-- The **arm `B`** of the tripod: the side of the pair `(25/63, 37/63)` through its own arc. -/
def armB {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : Set ℂ := pairSide (pairB T)

/-- The **arm `C`** of the tripod: the side of the pair `(37/63, 85/63)` through its own arc. -/
def armC {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (T : Tripod hN) : Set ℂ := pairSide (pairC T)

end Tripod

/-! ## The high iterate `F = (T_c)^{10}` -/

/-- The holomorphic map `F = (T_c)^{2·5} = (Tsq c)^[5]`, of degree `1024`. -/
def F (c : ℂ) : ℂ → ℂ := (Work.Landing.Tsq c)^[5]

theorem F_apply (c z : ℂ) : F c z = (Work.Landing.Tsq c)^[5] z := rfl

/-! ## The two angles of the root portrait and the wake sides -/

/-- The first angle of the root portrait: `371/1023`. -/
def alpha1 : ℝ := 371 / 1023

/-- The second angle of the root portrait: `404/1023`. -/
def alpha2 : ℝ := 404 / 1023

/-- The lower end of the wake arc `Wⱼ` of the root portrait, as an explicit rational
(the certificate `mb_EL_cert.py`; `W₀ = (371,404)/1023`, `W₁ = (215,281)/1023`,
`W₂ = (461,593)/1023`, `W₃ = (860,1124)/1023`, `W₄ = (821,1349)/1023`). -/
def wakeLo (j : ℕ) : ℝ :=
  match j % 5 with
  | 0 => 371 / 1023
  | 1 => 215 / 1023
  | 2 => 461 / 1023
  | 3 => 860 / 1023
  | _ => 821 / 1023

/-- The upper end of the wake arc `Wⱼ`. -/
def wakeHi (j : ℕ) : ℝ :=
  match j % 5 with
  | 0 => 404 / 1023
  | 1 => 281 / 1023
  | 2 => 593 / 1023
  | 3 => 1124 / 1023
  | _ => 1349 / 1023

/-- The pair `Pⱼ = {T^j α₁, T^j α₂}` of the root portrait, with landing point
`(Tantibar c)^[j] z₁` — the `j`-th iterate of the parabolic point `z₁` under `T_c`, which is
where the `j`-th root-portrait pair lands (`T` is the action of `T_c` on the external angles; the
portrait of the parabolic point propagates along the orbit).  (`0`-th iterate: `P₀` lands at `z₁`
itself.)  The landing point `(Tantibar c)^[j] z₁` was previously recorded as `z₁` for every `j`,
which made `wakeSide` — and hence the `wake` field of `RootParabolic` — almost vacuous for
`j ≠ 0`; the definition now takes the parameter `c` so that the correct landing point can be
formed. -/
def alphaPairRaw (c : ℂ) (z₁ : ℂ) (j : ℕ) : RawPair :=
  ⟨min (T^[j] alpha1) (T^[j] alpha2), max (T^[j] alpha1) (T^[j] alpha2),
    (Tantibar c)^[j] z₁⟩

/-- The **wake side** `Xⱼ`: the side of the pair `Pⱼ` through the wake arc `Wⱼ`. -/
def wakeSide {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z₁ : ℂ) (j : ℕ) : Set ℂ :=
  RawPair.sideThrough hN (alphaPairRaw c z₁ j) (wakeLo j) (wakeHi j)

/-! ## The input bundle produced on the `F` side -/

/-- A **root-parabolic parameter** of the period-5 component of `H`: the root point `c` together
with the characteristic parabolic point `z₁` of its period-5 cycle, its Böttcher data, and the
parabolic/orbit-portrait data used by the EL argument. -/
structure RootParabolic (c : ℂ) where
  /-- the Böttcher coordinate of the dynamical plane. -/
  φ : ℂ → ℂ
  /-- the Böttcher coordinate is a genuine (Böttcher) coordinate. -/
  bottcher : Work.ParamRays.IsDynBottcher c φ
  /-- the Böttcher data of the dynamical plane. -/
  hN : DynB c φ
  /-- the characteristic parabolic point. -/
  z₁ : ℂ
  /-- `z₁` is fixed by the second return map `(T_c)^[10] = (Tsq c)^[5]`. -/
  per_half : (Tantibar c)^[5] z₁ = z₁
  /-- `z₁` has exact period `5` for `T_c`. -/
  ne_per : ∀ j ∈ Finset.Ioo 0 5, (Tantibar c)^[j] z₁ ≠ z₁
  /-- the multiplier of the holomorphic second return map at `z₁` is `1`: simple parabolic. -/
  mult : Work.Landing.multiplier2 c 5 z₁ = 1
  /-- the parabolic point is simple: `F = (T_c)^{10}` has nonvanishing second derivative. -/
  simple : iteratedDeriv 2 (F c) z₁ ≠ 0
  /-- the two root-portrait rays land at `z₁`. -/
  rays : Work.Landing.landsAt c alpha1 z₁ ∧ Work.Landing.landsAt c alpha2 z₁
  /-- the critical orbit of `F` converges to `z₁` without attaining it. -/
  crit : Filter.Tendsto (fun n : ℕ => (F c)^[n] c) Filter.atTop (nhds z₁) ∧
    ∀ n : ℕ, (F c)^[n] c ≠ z₁
  /-- **L-wake**: the `k`-th point of the critical orbit lies in the wake side `X_{(k-1) % 5}`. -/
  wake : ∀ k : ℕ, 1 ≤ k → (Tantibar c)^[k] 0 ∈ wakeSide hN z₁ ((k - 1) % 5)

end Work.EL
