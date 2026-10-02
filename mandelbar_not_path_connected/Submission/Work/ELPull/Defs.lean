/-
# ELPull — definitions: angles, external-ray pairs, ray polygons

This module is the vocabulary of the `ELPull` area (EL, part 2 of the equator-leak
argument): pull-backs of co-landing pairs of external rays, region bijections and the
rational angle certificate.

Everything here is *plane topology + dynamics in the dynamical plane*, phrased on top of

* `Work.Top.NakaneData` (`Work.Top.Defs`) — the abstract Böttcher/Nakane interface
  (`rayPt`, `paramRay`, `eqArc`, `rayPiece`, `potential`), instantiated at a parameter `c`
  with `Mb := filledJulia c` and `Φ := Work.ParamRays.dynPhi c`;
* `Work.Top.JordanForm` (`Work.Top.Jordan.lean`) — the Jordan curve theorem, as a hypothesis;
* `Work.Landing` (`Tsq`, `angDouble`, `landsAt`, `multiplier2`).

## Main definitions

* `T`, `Tq` : the angle-doubling map `θ ↦ -2θ mod 1` on `ℝ` and on `ℚ`;
* `arcLen`, `InArc` : counterclockwise arcs and their length;
* `K`, `DynB` : the filled Julia set and the dynamical Böttcher interface at `c`;
* `LandsN` : landing of a ray in the Böttcher/Nakane vocabulary;
* `CoPair`, `pairCurve`, `arcSide`, `pairSide` : co-landing pairs of rays and the sides of
  their pair curves;
* `CyclicStrict`, `PolyAdmissible`, `polyCurve`, `polyRegion` : ray polygons (regions bounded
  by ray pieces, landing points and equipotential arcs) and their interior regions;
* `F` : the holomorphic `10`-th iterate `(Tsq c)^[5]` of `Tantibar c`;
* `preArc`, `IsPB1Step` : the two counterclockwise `T`-preimages of an arc, and the one-step
  pull-back relation between co-landing pairs;
* `RootParabolic` : the root-parabolic parameter bundle of the EL contract (§6).

## Convention

Angles are real numbers modulo `1`; `InArc x a b` means that `x` lies in the **open
counterclockwise arc** from `a` to `b`, of length `Int.fract (b - a) < 1`.  A co-landing pair
`P = (a, b, y)` stores its rays in the order in which they are used: the *far arc* of `P` is
the counterclockwise arc from `P.a` to `P.b` (`pairSide` is the side of `pairCurve P` met by
the rays with angles in that arc), and `arcSide hN P p q` is the side met by the angles in the
counterclockwise arc from `p` to `q` (which must be one of the two arcs of `P` for the
statement to be meaningful).

*Namespace note.*  The EL contract writes these definitions under `Work.EL`; in this
workspace the area lives in `Submission/Work/ELPull/`, and the definitions are collected here
under `Work.ELPull` so that no two areas of the fleet declare the same name.  The bodies are
the bodies prescribed by the contract (`NOTES_LEAD_mandelbar_EL_F_contracts.md` §1), so the
corresponding declarations of a future `Work/ELDefs.lean` are related to these by `rfl`.
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.Landing.Rays
import Submission.Work.ParamRays.DynBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. Angles, arcs and the doubling map -/

/-- The angle-doubling map of the tricorn on `ℝ`: `T θ = -2 θ mod 1`.  This is the action of
`Tantibar c` on external angles (`Work.Landing.angDouble`). -/
def T (θ : ℝ) : ℝ := Int.fract (-2 * θ)

theorem T_def (θ : ℝ) : T θ = Int.fract (-2 * θ) := rfl

theorem T_eq_angDouble (θ : ℝ) : T θ = Work.Landing.angDouble θ := rfl

/-- The angle-doubling map on `ℚ`: the arithmetic layer of the certificate (P5). -/
def Tq (q : ℚ) : ℚ := Int.fract (-2 * q)

theorem Tq_def (q : ℚ) : Tq q = Int.fract (-2 * q) := rfl

/-- The length of the open counterclockwise arc from `a` to `b` (in `(0,1]`, `0` iff `a ≡ b`). -/
def arcLen (a b : ℝ) : ℝ := Int.fract (b - a)

/-- The length of the counterclockwise arc on `ℚ`. -/
def arcLenQ (a b : ℚ) : ℚ := Int.fract (b - a)

/-- `x` lies in the open counterclockwise arc from `a` to `b`. -/
def InArc (x a b : ℝ) : Prop := 0 < Int.fract (x - a) ∧ Int.fract (x - a) < arcLen a b

/-- `x` lies in the open counterclockwise arc from `a` to `b`, on `ℚ`. -/
def InArcQ (x a b : ℚ) : Prop := 0 < Int.fract (x - a) ∧ Int.fract (x - a) < arcLenQ a b

/-- The smallest lift of the angle `a` above `b`: `b ≤ ccwLift b a < b + 1`.  It is the
endpoint of the counterclockwise arc from `b` to `a`, unwrapped. -/
def ccwLift (b a : ℝ) := a + (⌈b - a⌉ : ℝ)

/-- The action of the `m`-th iterate of `Tsq c` on external angles: `θ ↦ 4^m θ mod 1`. -/
def angMul (m : ℕ) (θ : ℝ) : ℝ := Int.fract ((4 : ℝ) ^ m * θ)

/-! ## 2. Strict cyclic order of a list of angles -/

/-- Walk the angles of a list counterclockwise, starting just above `a`, and return the lift of
the last angle: each angle is lifted to the representative in `(a, a + 1)` if necessary. -/
def cycLast (a : ℝ) : List ℝ → ℝ
  | [] => a
  | b :: t => cycLast (if a < b then b else b + 1) t

@[simp] theorem cycLast_nil (a : ℝ) : cycLast a [] = a := rfl

theorem cycLast_cons (a b : ℝ) (t : List ℝ) :
    cycLast a (b :: t) = cycLast (if a < b then b else b + 1) t := rfl

/-- The angles of `l` are in **strictly counterclockwise order**: walking from the first angle,
each next angle is (strictly) above the previous one, and the total span is `< 1`. -/
def CyclicStrict (l : List ℝ) : Prop :=
  match l with
  | [] => False
  | a :: t => cycLast a t < a + 1

theorem CyclicStrict.ne_nil {l : List ℝ} (h : CyclicStrict l) : l ≠ [] := by
  rintro rfl; exact h

/-- Two counterclockwise arcs whose endpoints interleave: `(a,b)` and `(c,d)` are *unlinked* if
each of `c`, `d` either lies in `(a,b)` or in the complementary arc. -/
def Unlinked (a b c d : ℝ) : Prop :=
  (InArc c a b ↔ InArc d a b) ∧ (InArc a c d ↔ InArc b c d)

/-! ## 3. The dynamical Böttcher interface and landing -/

/-- The filled Julia set of `Tantibar c`. -/
abbrev K (c : ℂ) : Set ℂ := Work.ParamRays.filledJulia c

/-- **The dynamical Böttcher (Nakane) data** at the parameter `c`: `Work.Top`'s abstract
interface with `Mb := filledJulia c` and `Φ := Work.ParamRays.dynPhi c`.  It is a *type*, and
it is the hypothesis `hN` of every statement of this area. -/
abbrev DynB (c : ℂ) : Type := Work.Top.NakaneData (K c) (Work.ParamRays.dynPhi c)

/-- The ray at angle `θ` **lands** at `y`: the points of the ray of `Φ`-modulus `t` converge to
`y` as `t → 1⁺`. -/
def LandsN {c : ℂ} (hN : DynB c) (θ : ℝ) (y : ℂ) : Prop :=
  Filter.Tendsto (fun t : ℝ => hN.rayPt θ t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y)

/-- A **co-landing pair**: two rays (at angles `a`, `b`) landing at the same point `y`. -/
structure CoPair {c : ℂ} (hN : DynB c) where
  /-- the first angle. -/
  a : ℝ
  /-- the second angle. -/
  b : ℝ
  /-- the common landing point. -/
  y : ℂ
  lands_a : LandsN hN a y
  lands_b : LandsN hN b y

/-- The **pair curve** of a co-landing pair: the two rays together with their landing point. -/
def pairCurve {c : ℂ} (hN : DynB c) (P : CoPair hN) : Set ℂ :=
  hN.paramRay P.a ∪ {P.y} ∪ hN.paramRay P.b

/-- The **side of a pair** met by the rays with angles in the counterclockwise arc from `p` to
`q` (`(p,q)` must be one of the two arcs of `P`). -/
def arcSide {c : ℂ} (hN : DynB c) (P : CoPair hN) (p q : ℝ) : Set ℂ :=
  connectedComponentIn (pairCurve hN P)ᶜ (hN.rayPt (p + arcLen p q / 2) 2)

/-- The side of `P` met by the rays with angles in the **far arc** `(P.a, P.b)`. -/
def pairSide {c : ℂ} (hN : DynB c) (P : CoPair hN) : Set ℂ := arcSide hN P P.a P.b

/-- **Local two-sidedness of a pair curve at its landing point.**  There is a disc `W` about the
landing point which `pairCurve hN P` cuts into exactly two connected halves (a "tame" landing in
the sense of the classical two-sidedness of an external ray at its landing point; it is what
`Work.Top.Sides.sides_of_halves` formalises locally). -/
def LocallyTwoSided {c : ℂ} (hN : DynB c) (P : CoPair hN) : Prop :=
  ∃ W H₁ H₂ : Set ℂ,
    IsOpen W ∧ P.y ∈ W ∧ H₁ ∪ H₂ = W \ pairCurve hN P ∧
    IsPreconnected H₁ ∧ IsPreconnected H₂ ∧ H₁.Nonempty ∧ H₂.Nonempty ∧
    Disjoint H₁ (pairCurve hN P) ∧ Disjoint H₂ (pairCurve hN P)

/-- The two arcs of a pair `P`, as `(lo, hi)` with `lo < hi`: the arcs `(a,b)` and `(b,a)`. -/
def arcOf {c : ℂ} {hN : DynB c} (P : CoPair hN) (k : Fin 2) : ℝ × ℝ :=
  if k = 0 then (P.a, P.b) else (P.b, P.a)

/-- `I` is one of the two counterclockwise arcs of the pair `P`. -/
def IsArcOf {c : ℂ} {hN : DynB c} (P : CoPair hN) (I : ℝ × ℝ) : Prop :=
  I = (P.a, P.b) ∨ I = (P.b, P.a)

/-- `I` is one of the two counterclockwise arcs of the pair `P`, in the **unwrapped**
representation: the second entry is the lifted endpoint, so that `arcLen I.1 I.2 = I.2 - I.1`.
This is the representation in which `preArc` computes the preimage arcs of `I`. -/
def IsUnwrappedArcOf {c : ℂ} {hN : DynB c} (P : CoPair hN) (I : ℝ × ℝ) : Prop :=
  (I.1 = P.a ∧ I.2 = P.a + arcLen P.a P.b) ∨ (I.1 = P.b ∧ I.2 = P.b + arcLen P.b P.a)

/-! ## 4. Ray polygons and their regions -/

/-- The cyclic list of angles `a₀, b₀, a₁, b₁, …` of a list of pairs. -/
def flatAngles {c : ℂ} {hN : DynB c} (ps : List (CoPair hN)) : List ℝ :=
  ps.flatMap fun P => [P.a, P.b]

/-- A **ray polygon** is a cyclic list of co-landing pairs whose angles are in strictly
counterclockwise order and whose landing points are pairwise distinct. -/
structure PolyAdmissible {c : ℂ} (hN : DynB c) (ps : List (CoPair hN)) : Prop where
  ne : ps ≠ []
  cyc : CyclicStrict (flatAngles ps)
  inj : ps.Pairwise fun P Q => P.y ≠ Q.y

/-- The index of the vertex following `i` in the cyclic list. -/
def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.1) i.2)⟩

/-- The counterclockwise arc of the polygon from the second angle of the `i`-th pair to the
first angle of the next pair (the `i`-th **near arc**), as an unwrapped pair. -/
def nearArc {c : ℂ} {hN : DynB c} (ps : List (CoPair hN)) (i : Fin ps.length) : ℝ × ℝ :=
  ((ps.get i).b, ccwLift (ps.get i).b (ps.get (nextIdx i)).a)

/-- The **boundary** of the ray polygon `ps` at level `R`: the ray pieces below level `R`, the
landing points, and the equipotential arcs through the near arcs. -/
def polyCurve {c : ℂ} (hN : DynB c) (ps : List (CoPair hN)) (R : ℝ) : Set ℂ :=
  (⋃ P ∈ ps, {P.y} ∪ hN.rayPiece P.a 0 R ∪ hN.rayPiece P.b 0 R) ∪
    ⋃ (i : Fin ps.length), hN.eqArc (nearArc ps i).1 (nearArc ps i).2 R

/-- The midpoint angle of the first near arc of the polygon (the base point of the region). -/
def firstNearMid {c : ℂ} {hN : DynB c} : List (CoPair hN) → ℝ
  | [] => 0
  | P :: [] => P.b + arcLen P.b P.a / 2
  | P :: Q :: t => P.b + arcLen P.b Q.a / 2

/-- The **region** bounded by the ray polygon `ps` at level `R`: the component of the complement
of `polyCurve hN ps R` containing the ray point of the first near arc at modulus `√R`. -/
def polyRegion {c : ℂ} (hN : DynB c) (ps : List (CoPair hN)) (R : ℝ) : Set ℂ :=
  connectedComponentIn (polyCurve hN ps R)ᶜ (hN.rayPt (firstNearMid ps) (Real.sqrt R))

/-- The combinatorial input of a region pull-back `polyPullback`: the angle map `θ ↦ 4^m θ`
carries the near arcs of the polygon `ps'` onto those of `ps`, in a way that matches the
boundary pairs as well.  (All of this is rational data, certified in `Cert.Check`.) -/
structure NearArcsCover {c : ℂ} (hN : DynB c) (ps ps' : List (CoPair hN)) (m : ℕ) : Prop where
  /-- the angle map matches boundary pairs (the target pair being stored in its unwrapped
  representation, the images are reduced modulo `1`). -/
  pair : ∀ P' ∈ ps', ∃ P ∈ ps,
    angMul m P'.a = Int.fract P.a ∧ angMul m P'.b = Int.fract P.b
  /-- the angle map carries the near arcs of `ps'` *into* the near arcs of `ps` (the forward
  implication; `angMul m` is `4^m`-to-one, so the converse is false whenever `4^m > 1`). -/
  arc : ∀ i : Fin ps'.length, ∃ j : Fin ps.length,
      ∀ x : ℝ, InArc x (nearArc ps' i).1 (nearArc ps' i).2 →
        InArc (angMul m x) (nearArc ps j).1 (nearArc ps j).2

/-! ## 4b. Periodicity of the rays in the angle -/

theorem rayPoint_periodic (θ t : ℝ) (m : ℤ) :
    Work.Top.NakaneData.rayPoint (θ + m) t = Work.Top.NakaneData.rayPoint θ t := by
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * ((θ + m : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) *
        Complex.exp ((m : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, h1, Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I, one_zpow, mul_one]

/-- The pair curve is periodic in the angle with period `1`. -/
theorem paramRay_periodic {c : ℂ} (hN : DynB c) (θ : ℝ) (m : ℤ) :
    hN.paramRay (θ + m) = hN.paramRay θ := by
  ext z
  rw [Work.Top.NakaneData.mem_paramRay_iff, Work.Top.NakaneData.mem_paramRay_iff]
  constructor
  · rintro ⟨hz, t, ht, h⟩
    refine ⟨hz, t, ht, ?_⟩
    rw [h, rayPoint_periodic θ t m]
  · rintro ⟨hz, t, ht, h⟩
    refine ⟨hz, t, ht, ?_⟩
    rw [h, rayPoint_periodic θ t m]

/-- The ray pieces are periodic in the angle with period `1`. -/
theorem rayPiece_periodic {c : ℂ} (hN : DynB c) (θ t R : ℝ) (m : ℤ) :
    hN.rayPiece (θ + m) t R = hN.rayPiece θ t R := by
  rw [Work.Top.NakaneData.rayPiece, Work.Top.NakaneData.rayPiece, paramRay_periodic hN θ m]

/-- The ray pieces only depend on the angle modulo `1`. -/
theorem rayPiece_fract_eq {c : ℂ} (hN : DynB c) (θ t R : ℝ) :
    hN.rayPiece (Int.fract θ) t R = hN.rayPiece θ t R := by
  conv_lhs => rw [Int.fract]
  rw [show θ - (⌊θ⌋ : ℝ) = θ + (-⌊θ⌋ : ℤ) by push_cast; ring]
  exact rayPiece_periodic hN θ t R (-⌊θ⌋)

/-- The ray points are periodic in the angle with period `1`. -/
theorem rayPt_periodic {c : ℂ} (hN : DynB c) (θ t : ℝ) (m : ℤ) (ht : 1 < t) :
    hN.rayPt (θ + m) t = hN.rayPt θ t := by
  refine hN.injOn_Phi (hN.rayPt_notMem ht) (hN.rayPt_notMem ht) ?_
  rw [hN.Phi_rayPt ht, hN.Phi_rayPt ht, rayPoint_periodic θ t m]

/-- The ray points only depend on the angle modulo `1`. -/
theorem rayPt_fract_eq {c : ℂ} (hN : DynB c) (θ t : ℝ) (ht : 1 < t) :
    hN.rayPt (Int.fract θ) t = hN.rayPt θ t := by
  conv_lhs => rw [Int.fract]
  rw [show θ - (⌊θ⌋ : ℝ) = θ + (-⌊θ⌋ : ℤ) by push_cast; ring]
  exact rayPt_periodic hN θ t (-⌊θ⌋) ht

/-! ## 4c. The topological input of the one-step pull-back (P1) -/

/-- **The topological input of `pb1`** (design of `NOTES_LEAD_mandelbar_EL_fix.md` §2).  The pair
curves are closed, the two sides of a pair curve are disjoint, and every ray whose angle lies in
one of the two arcs of a pair lies in the side met by that arc.  It is the part of `ELTop`'s pair
theory (T6) that the pull-back uses; nothing produces `LocallyTwoSided`. -/
structure PB1Top {c : ℂ} (hN : DynB c) : Prop where
  /-- pair curves are closed. -/
  closed : ∀ P : CoPair hN, IsClosed (pairCurve hN P)
  /-- the two sides of a pair curve are disjoint. -/
  sep : ∀ P : CoPair hN, arcLen P.a P.b ≠ 0 →
    Disjoint (arcSide hN P P.a P.b) (arcSide hN P P.b P.a)
  /-- a ray whose angle lies in an arc of the pair lies in the side met by that arc. -/
  angle : ∀ (P : CoPair hN) (p q θ : ℝ),
    ((p = P.a ∧ q = P.b) ∨ (p = P.b ∧ q = P.a)) → arcLen P.a P.b ≠ 0 → InArc θ p q →
    hN.paramRay θ ⊆ arcSide hN P p q

/-! ## 4d. The orbit-portrait count (the external input of the L-portrait) -/

/-- **The orbit-portrait count** for the dynamical plane (Goldberg–Milnor orbit portraits;
Mukherjee 2015, Thm 2.6; the dynamical counterpart of `Work.Landing.RotationNumberZero`): if exactly
two external rays land at `y` (at the angles `u ≠ v` of `[0,1)`), then at every preimage `y'` of `y`
the map `θ ↦ T θ` is injective on the angles of `[0,1)` whose rays land at `y'` — i.e. `y'` carries
at most one ray per ray of `y`, hence at most two rays.

This is a *classical input*, not a consequence of the data of `RootParabolic c`: it is the
pull-back count of the orbit portrait (each ray of a two-ray point is pulled back into the sector of
`y'`, at most once). -/
def PortraitCount {c : ℂ} (hN : DynB c) : Prop :=
  ∀ (y y' : ℂ), Tantibar c y' = y →
    (∃ u v : ℝ, u ∈ Set.Ico 0 1 ∧ v ∈ Set.Ico 0 1 ∧ u ≠ v ∧
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (LandsN hN θ y ↔ θ = u ∨ θ = v)) →
    ∀ θ' θ'' : ℝ, θ' ∈ Set.Ico 0 1 → θ'' ∈ Set.Ico 0 1 →
      LandsN hN θ' y' → LandsN hN θ'' y' → T θ' = T θ'' → θ' = θ''

/-! ## 5. The holomorphic iterate `F` and the pull-back arcs -/

/-- The holomorphic `10`-th iterate of `Tantibar c`: `F c = (Tsq c)^[5]`. -/
def F (c : ℂ) : ℂ → ℂ := (Work.Landing.Tsq c)^[5]

theorem F_def (c : ℂ) : F c = (Work.Landing.Tsq c)^[5] := rfl

/-- `Tsq c` is the second iterate of `Tantibar c`. -/
theorem Tsq_eq_iterate (c z : ℂ) : Work.Landing.Tsq c z = (Tantibar c)^[2] z := by
  simp [Work.Landing.Tsq, Tantibar, Function.iterate_succ]

/-- `F c` is the tenth iterate of `Tantibar c`. -/
theorem F_eq_iterate (c : ℂ) : F c = (Tantibar c)^[10] := by
  funext z
  simp only [F, Work.Landing.Tsq, Tantibar, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
  norm_num

/-- The two counterclockwise `T`-preimages of the arc `I = (p, q)`, each of half its length:
`J_k = (-q/2 + k/2, -p/2 + k/2)` reduced modulo `1` (the second entry of `I` is the *unwrapped*
endpoint `q ≥ p` of the arc).  This is the (P1) preimage arc: `T` maps `J_k` onto `I`. -/
def preArc (k : Fin 2) (I : ℝ × ℝ) : ℝ × ℝ :=
  (Int.fract (-(I.2) / 2 + (k : ℝ) / 2), Int.fract (-(I.1) / 2 + (k : ℝ) / 2))

/-- The pair of angles `Q` consists of the two endpoints of the `k`-th counterclockwise
`T`-preimage arc of `I` (in either order: the two rays are unordered). -/
def IsPreimageArcPair (k : Fin 2) (I Q : ℝ × ℝ) : Prop :=
  (Q.1 = (preArc k I).1 ∧ Q.2 = (preArc k I).2) ∨
    (Q.2 = (preArc k I).1 ∧ Q.1 = (preArc k I).2)

/-- The one-step pull-back relation between two co-landing pairs: the two angles of `Q` are the
endpoints of one of the two counterclockwise `T`-preimage arcs of the arc `I`. -/
def IsPB1Step (I Q : ℝ × ℝ) : Prop := IsPreimageArcPair 0 I Q ∨ IsPreimageArcPair 1 I Q

/-! ## 6. The named angles and the root-parabolic parameter bundle -/

/-- The first root angle `371/1023`. -/
def alpha1 : ℝ := 371 / 1023

/-- The second root angle `404/1023`. -/
def alpha2 : ℝ := 404 / 1023

/-- The angle `22/63` of the first ray of the tripod at the branch point `b₂`. -/
def tripod1 : ℝ := 22 / 63

/-- The angle `25/63` of the second ray of the tripod at `b₂`. -/
def tripod2 : ℝ := 25 / 63

/-- The angle `37/63` of the third ray of the tripod at `b₂`. -/
def tripod3 : ℝ := 37 / 63

/-- The upper angle of the `j`-th wake arc `W_j` (`j = 0,…,4`). -/
def wakeLo : Fin 5 → ℝ := ![371 / 1023, 215 / 1023, 461 / 1023, 860 / 1023, 821 / 1023]

/-- The lower angle of the `j`-th wake arc `W_j` (`j = 0,…,4`); `W₃` and `W₄` are unwrapped. -/
def wakeHi : Fin 5 → ℝ := ![404 / 1023, 281 / 1023, 593 / 1023, 1124 / 1023, 1349 / 1023]

/-- The **wake side** of the `j`-th α-pair: the side of `P j` met by the rays whose angles lie
in the wake arc `W_j` (the arc of `P j` that contains the critical value; `Landing`'s `L-wake`
export). -/
def wakeSide {c : ℂ} (hN : DynB c) (P : Fin 5 → CoPair hN) (j : Fin 5) : Set ℂ :=
  arcSide hN (P j) (wakeLo j) (wakeHi j)

/-- The **root-parabolic parameter bundle** of the EL contract (§6): a parameter `c` together
with the dynamical Böttcher data, a simple parabolic fixed point `z₁` of `F c = (Tsq c)^[5]`
whose two root rays co-land, the five α-pairs `P₀ … P₄`, the critical orbit and the wake
condition (each critical-orbit point lies in the wake side of its α-pair). -/
structure RootParabolic (c : ℂ) where
  /-- the parabolic point. -/
  z₁ : ℂ
  /-- the dynamical Böttcher data at `c`. -/
  hN : DynB c
  /-- `z₁` is fixed by `Tantibar c` and has exact period `5`. -/
  per : (Tantibar c)^[5] z₁ = z₁ ∧ ∀ j ∈ Finset.Ioo 0 5, (Tantibar c)^[j] z₁ ≠ z₁
  /-- the second-return multiplier is `1`. -/
  mult : Work.Landing.multiplier2 c 5 z₁ = 1
  /-- the parabolic point is simple. -/
  simple : iteratedDeriv 2 (F c) z₁ ≠ 0
  /-- the two root rays land at `z₁`. -/
  rays : Work.Landing.landsAt c alpha1 z₁ ∧ Work.Landing.landsAt c alpha2 z₁
  /-- the five α-pairs `P_j = (T^j α₁, T^j α₂)` landing at `f^j z₁`. -/
  P : Fin 5 → CoPair hN
  /-- `P_j` is the pair of the `j`-th iterate of the root rays. -/
  P_spec : ∀ j : Fin 5,
    (P j).y = (Tantibar c)^[j.1] z₁ ∧ (P j).a = T^[j.1] alpha1 ∧ (P j).b = T^[j.1] alpha2
  /-- the critical orbit converges to `z₁` and never hits it. -/
  crit : Filter.Tendsto (fun n : ℕ => (F c)^[n] c) Filter.atTop (nhds z₁) ∧
    ∀ n : ℕ, (F c)^[n] c ≠ z₁
  /-- the **wake** condition: every critical-orbit point of `Tantibar c` lies in the wake side of
  its α-pair. -/
  wake : ∀ k : ℕ, 1 ≤ k →
    (Tantibar c)^[k] 0 ∈ wakeSide hN P ⟨(k - 1) % 5, Nat.mod_lt _ (by norm_num)⟩

end Work.ELPull
