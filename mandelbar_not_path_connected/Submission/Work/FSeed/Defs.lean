/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# FSeed: a root-parabolic seed parameter — vocabulary

This file fixes the vocabulary of the `FSeed` area, the part of the `F` (height-zero root
parameter) contract which supplies **a root-parabolic parameter**: a parameter `c` of the tricorn
at which `T_c(z) = z̄² + c` has a *simple* parabolic cycle of exact period `5`, carrying the two
root rays `371/1023` and `404/1023`, with the critical orbit converging to it.  The structure
itself is `Work.EL.RootParabolic` (`Submission/Work/FSeed/RootParabolic.lean`); the present file
provides the notions its fields are phrased with.

## Contents

* angle arithmetic on the circle: `T`, `arcLen`, `InArc`, `midArc`, `InArcClosed`, and the
  rational level `Tq`, `arcLenQ`, `InArcQ` with the cast lemmas `Tq_cast`, `arcLenQ_cast`,
  `InArcQ_cast`;
* the `PB1` pull-back relation of angle pairs: `IsTpreimagePair`, `cfreeArc`, `IsPB1Step`;
* the numerical data of the orbit portrait: `α₁`, `α₂`, `β₀`, `β₀'`, `β₁`, `β₁'`, the tripod
  `b₂₁`, `b₂₂`, `b₂₃`, the arms `armA`, `armB`, `armC`, the portrait pairs `pairRay₁`,
  `pairRay₂` and the wake arcs `wakeLo`, `wakeHi`, `wakeMid`;
* the holomorphic fifth iterate `F c = (Tsq c)^[5] = T_c^[10]` of the second return map, with
  `Tantibar_iterate_two` and `Tantibar_iterate_ten`;
* the dynamical external ray `dynRayF`, the pair curve `pairCurve`, the pair side `pairSide`,
  the **wake side** `wakeSide`, and the grand orbit `grandOrbit`;
* the local ray portrait `LocalRayPortrait c z` of the root point, **modulo `1`** (at most two ray
  angles land at `z`), classical at the seed (root-arc interior) and *not* a general principle;
  consumed as a hypothesis by `Classify.lean`.

## Conventions

* Angles live in `ℝ/ℤ` and are normalised with `Int.fract` to `[0,1)`.  `InArc x a b` is the
  *open counterclockwise* arc from `a` to `b`; the arms of the tripod are written with a lifted
  upper end (`armC` uses `b₂₁ + 1`).
* All numerical certificates are stated with the explicit rationals of
  `Submission/Work/lead_mb/mb_EL_cert.py` and proved by `norm_num [T, Int.fract, ...]`.
-/
import Submission.Work.Landing.Land
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Angle arithmetic on the circle `ℝ/ℤ` -/

/-- The angle map of the tricorn: `T θ = -2θ mod 1`, in the normalisation `[0,1)`.  This is
`Work.Landing.angDouble`; the external ray at angle `θ` is mapped by `T_c` to the ray at angle
`T θ`. -/
abbrev T (θ : ℝ) : ℝ := Work.Landing.angDouble θ

theorem T_apply (θ : ℝ) : T θ = Int.fract (-2 * θ) := rfl

/-- The counterclockwise length of the arc from `a` to `b`. -/
def arcLen (a b : ℝ) : ℝ := Int.fract (b - a)

/-- `x` lies in the open counterclockwise arc `(a,b)`. -/
def InArc (x a b : ℝ) : Prop := 0 < Int.fract (x - a) ∧ Int.fract (x - a) < arcLen a b

/-- `x` lies in the closed counterclockwise arc from `a` to `b`. -/
def InArcClosed (x a b : ℝ) : Prop := 0 ≤ Int.fract (x - a) ∧ Int.fract (x - a) ≤ arcLen a b

/-- The midpoint of the counterclockwise arc from `a` to `b`. -/
def midArc (a b : ℝ) : ℝ := a + arcLen a b / 2

/-! ### The rational level of the same angle arithmetic

The numerical certificates of the area are checked with explicit rationals; the rational level
below is the form in which the certificate of `Submission/Work/lead_mb/mb_EL_cert.py` is written,
and `Tq_cast` transfers it to `ℝ`.  Beware: `decide` does *not* reduce rational comparisons here;
the certificates are proved with `norm_num [T, Int.fract, ...]`. -/

/-- The angle map `T` at the level of `ℚ`. -/
def Tq (q : ℚ) : ℚ := Int.fract (-2 * q)

/-- The rational counterclockwise arc length. -/
def arcLenQ (a b : ℚ) : ℚ := Int.fract (b - a)

/-- The rational `InArc`. -/
def InArcQ (x a b : ℚ) : Prop := 0 < Int.fract (x - a) ∧ Int.fract (x - a) < arcLenQ a b

/-- The rational `Int.fract` casts to the real `Int.fract`. -/
theorem frac_cast (a : ℚ) : ((Int.fract a : ℚ) : ℝ) = Int.fract ((a : ℚ) : ℝ) := by
  refine ((Int.fract_eq_iff (a := ((a : ℚ) : ℝ))
    (b := ((Int.fract a : ℚ) : ℝ))).mpr ⟨?_, ?_, ?_⟩).symm
  · exact_mod_cast Int.fract_nonneg a
  · exact_mod_cast Int.fract_lt_one a
  · refine ⟨⌊a⌋, ?_⟩
    rw [← Int.self_sub_floor a]
    push_cast
    ring

/-- The rational angle map casts to the real angle map. -/
theorem Tq_cast (q : ℚ) : ((Tq q : ℚ) : ℝ) = T (q : ℝ) := by
  have h := frac_cast ((-2 : ℚ) * q)
  simp only [Tq, T, Work.Landing.angDouble] at h ⊢
  rw [h]
  push_cast
  ring

/-- The iterated rational angle map casts to the iterated real angle map. -/
theorem Tq_iterate_cast (q : ℚ) (n : ℕ) :
    ((((Tq : ℚ → ℚ)^[n]) q : ℚ) : ℝ) = ((T : ℝ → ℝ)^[n]) (q : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Tq_cast, ih]

/-- The rational arc length casts to the real arc length. -/
theorem arcLenQ_cast (a b : ℚ) : ((arcLenQ a b : ℚ) : ℝ) = arcLen (a : ℝ) (b : ℝ) := by
  have h := frac_cast (b - a)
  simp only [arcLenQ, arcLen] at h ⊢
  rw [h]
  push_cast
  ring

/-- The rational `InArc` casts to the real `InArc`. -/
theorem InArcQ_cast {x a b : ℚ} (h : InArcQ x a b) : InArc (x : ℝ) (a : ℝ) (b : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have h3 : ((Int.fract (x - a) : ℚ) : ℝ) = Int.fract ((x : ℝ) - (a : ℝ)) := by
    have h := frac_cast (x - a)
    rw [show (((x - a : ℚ)) : ℝ) = ((x : ℝ) - (a : ℝ)) by push_cast; ring] at h
    exact h
  have h4 : ((arcLenQ a b : ℚ) : ℝ) = arcLen (a : ℝ) (b : ℝ) := arcLenQ_cast a b
  constructor
  · rw [← h3]; exact_mod_cast h1
  · rw [← h3, ← h4]; exact_mod_cast h2

/-- The first root angle `371/1023` (the same number as `Work.Landing.rootAngle1`). -/
def α₁ : ℝ := 371 / 1023

/-- The second root angle `404/1023` (the same number as `Work.Landing.rootAngle2`). -/
def α₂ : ℝ := 404 / 1023

/-- The first root angle at the rational level. -/
def α₁q : ℚ := 371 / 1023

/-- The second root angle at the rational level. -/
def α₂q : ℚ := 404 / 1023

/-! ### The `PB1` pull-back relation for angle pairs -/

/-- `(a',b')` is one of the two `T`-preimage pairs of the unwrapped arc from `p` to `q` (whose
length is `q - p`): the pairs `{fract (-q/2), fract (-p/2)}` and
`{fract (1/2 - q/2), fract (1/2 - p/2)}`, normalised to `[0,1)` by `Int.fract` — this is exactly
the relation `T_preimage_pairs` of the certificate `Submission/Work/lead_mb/mb_EL_cert.py`. -/
def IsTpreimagePair (p q a' b' : ℝ) : Prop :=
  (a' = Int.fract (-q / 2) ∧ b' = Int.fract (-p / 2)) ∨
    (a' = Int.fract (-p / 2) ∧ b' = Int.fract (-q / 2)) ∨
    (a' = Int.fract (1 / 2 - q / 2) ∧ b' = Int.fract (1 / 2 - p / 2)) ∨
    (a' = Int.fract (1 / 2 - p / 2) ∧ b' = Int.fract (1 / 2 - q / 2))

/-- An unwrapped representative `(p, q)` (with `q = p + |arc|`) of the **c-free arc** of the
pair `{a, b}`, in the convention of the certificate `Submission/Work/lead_mb/mb_EL_cert.py`: for
the root pair `{α₁,α₂}` it is the *far* arc from `α₂` counterclockwise to `α₁` (the complement of
the wake arc `W₀ = (α₁,α₂)`), and for any other pair it is the arc which does not contain the
wake direction `α₁`. -/
def cfreeArc (a b : ℝ) : ℝ × ℝ :=
  if a = α₁ ∧ b = α₂ then (α₂, α₂ + arcLen α₂ α₁)
  else if InArc α₁ a b then (b, b + arcLen b a)
  else (a, a + arcLen a b)

/-- One step of the `PB1` pull-back relation: the pair `{a',b'}` is one of the two
`T`-preimage pairs of the c-free arc of the pair `{a,b}`. -/
def IsPB1Step (a b a' b' : ℝ) : Prop :=
  IsTpreimagePair (cfreeArc a b).1 (cfreeArc a b).2 a' b'

/-! ## The numerical data of the orbit portrait

The angles are those of the certificate `Submission/Work/lead_mb/mb_EL_cert.py`; the tables of
`NOTES_LEAD_mandelbar_EL_F_contracts.md` §5 record the same numbers. -/

/-- The angle `β₀ = 379859/1047552` of the first ray of the level-`11` preimage `u` of the
parabolic point `z₁`. -/
def β₀ : ℝ := 379859 / 1047552

/-- The angle `β₀' = 414113/1047552` of the second ray of the `u`-pair. -/
def β₀' : ℝ := 414113 / 1047552

/-- The first angle of the `u`-pair at the rational level. -/
def β₀q : ℚ := 379859 / 1047552

/-- The second angle of the `u`-pair at the rational level. -/
def β₀q' : ℚ := 414113 / 1047552

/-- The first angle `β₁` of the level-`1` `u`-pair: `α₁ - (α₁ - β₀)/1024`. -/
def β₁ : ℝ := 389021651 / 1072693248

/-- The second angle `β₁'` of the level-`1` `u`-pair: `α₂ + (β₀' - α₂)/1024`. -/
def β₁' : ℝ := 423625121 / 1072693248

/-- The first angle of the level-`1` `u`-pair at the rational level. -/
def β₁q : ℚ := 389021651 / 1072693248

/-- The second angle of the level-`1` `u`-pair at the rational level. -/
def β₁q' : ℚ := 423625121 / 1072693248

/-- The first ray `22/63` of the branch point `b₂`. -/
def b₂₁ : ℝ := 22 / 63

/-- The second ray `25/63` of the branch point `b₂`. -/
def b₂₂ : ℝ := 25 / 63

/-- The third ray `37/63` of the branch point `b₂`. -/
def b₂₃ : ℝ := 37 / 63

/-- The three rays of the branch point `b₂ = {22,25,37}/63` as a `Fin 3`-indexed family. -/
def b₂rays : Fin 3 → ℚ := ![22 / 63, 25 / 63, 37 / 63]

/-- The three rays `13/63`, `19/63`, `52/63` of the branch point `b₁ = T_c(b₂)`. -/
def b₁rays : Fin 3 → ℚ := ![13 / 63, 19 / 63, 52 / 63]

/-- The arm `A` of the tripod at `b₂`, between the rays `22/63` and `25/63`; it contains the
α-pair. -/
def armA : Set ℝ := {x : ℝ | InArc x b₂₁ b₂₂}

/-- The arm `B` of the tripod at `b₂`, between the rays `25/63` and `37/63`. -/
def armB : Set ℝ := {x : ℝ | InArc x b₂₂ b₂₃}

/-- The arm `C` of the tripod at `b₂`, between the rays `37/63` and `22/63` (with the upper end
lifted by `1`). -/
def armC : Set ℝ := {x : ℝ | InArc x b₂₃ (b₂₁ + 1)}

/-- The angle of the first ray of the level-`j` portrait pair: the `j`-th image of `α₁`. -/
def pairRay₁ (j : ℕ) : ℝ := (T^[j]) α₁

/-- The angle of the second ray of the level-`j` portrait pair: the `j`-th image of `α₂`. -/
def pairRay₂ (j : ℕ) : ℝ := (T^[j]) α₂

/-- The two angles of the level-`j` portrait pair, as a set. -/
def pairAngleSet (j : ℕ) : Set ℝ := {pairRay₁ j, pairRay₂ j}

/-- The lower end of the wake arc of the level-`j` pair: the image of the wake arc `(α₁,α₂)`
under `T^j`.  The angle map `T` reverses the orientation of the circle, so for odd `j` the image
arc is traversed from `T^j α₂` to `T^j α₁`. -/
def wakeLo (j : ℕ) : ℝ := if j % 2 = 0 then pairRay₁ j else pairRay₂ j

/-- The upper end of the wake arc of the level-`j` pair (see `wakeLo`). -/
def wakeHi (j : ℕ) : ℝ := if j % 2 = 0 then pairRay₂ j else pairRay₁ j

/-- The midpoint of the wake arc of the level-`j` pair. -/
def wakeMid (j : ℕ) : ℝ := midArc (wakeLo j) (wakeHi j)

/-- The length of the wake arc of the level-`j` pair (`33·2^j/1023` for `j ≤ 4`). -/
def wakeLen (j : ℕ) : ℝ := arcLen (wakeLo j) (wakeHi j)

/-! ## The dynamics -/

/-- The holomorphic **fifth iterate of the second return map**,
`F c = (T_c ∘ T_c)^[5] = T_c^[10]`; holomorphic of degree `1024`.  This is the map `Work.EL.F`
of the contracts. -/
def F (c : ℂ) : ℂ → ℂ := (Work.Landing.Tsq c)^[5]

@[simp] theorem F_apply (c : ℂ) : F c = (Work.Landing.Tsq c)^[5] := rfl

theorem Tantibar_iterate_two_apply (c z : ℂ) :
    (Tantibar c)^[2] z = Work.Landing.Tsq c z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  simp only [Work.Landing.Tsq, Tantibar]
  simp

/-- `T_c^[2] = Tsq c`. -/
theorem Tantibar_iterate_two (c : ℂ) : (Tantibar c)^[2] = Work.Landing.Tsq c :=
  funext (Tantibar_iterate_two_apply c)

/-- `T_c^[10] = F c`: the fifth iterate of the second return map is the tenth iterate of `T_c`. -/
theorem Tantibar_iterate_ten (c : ℂ) (z : ℂ) : (Tantibar c)^[10] z = F c z := by
  rw [show (10 : ℕ) = 2 * 5 from rfl, Function.iterate_mul, Tantibar_iterate_two]
  rfl

/-- The **grand orbit** of `z` under `F c = T_c^[10]`. -/
def grandOrbit (c : ℂ) (z : ℂ) : Set ℂ := {w : ℂ | ∃ n : ℕ, (F c)^[n] z = w}

/-! ## Dynamical rays, pair curves and sides -/

/-- The dynamical Böttcher data of `T_c`: Top's abstract interface `NakaneData`, instantiated in
the dynamical plane with the filled Julia set `K_c` and the canonical Böttcher coordinate
`Work.ParamRays.dynPhi c`.  This is the `DynB c` of the contract. -/
abbrev DynData (c : ℂ) :=
  Work.Top.NakaneData (Work.ParamRays.filledJulia c) (Work.ParamRays.dynPhi c)

/-- The dynamical Böttcher homeomorphism input: `dynPhi c` is a homeomorphism of the complement
of the filled Julia set onto the exterior of the unit disc (`Work.ParamRays.DynBottcherHomeo`).
This is the hypothesis under which the external rays of `T_c` behave as curves from the filled
Julia set to infinity. -/
abbrev DynHomeo (c : ℂ) : Prop := Work.ParamRays.DynBottcherHomeo c

/-- The dynamical external ray of `T_c` at angle `θ`: the points of the escaping set whose
Böttcher coordinate has angle `θ` (this is `Work.Landing.dynRay` for the canonical choice
`dynPhi c` of Böttcher coordinate). -/
def dynRayF (c : ℂ) (θ : ℝ) : Set ℂ := Work.Landing.dynRay c (Work.ParamRays.dynPhi c) θ

/-- The point of the ray of angle `θ` and modulus `t > 1` is independent of the chosen Nakane
data: it is the unique point at which `Φ` takes the value `rayPoint θ t`.  Consequently the pair
curves and sides below do not depend on the choice of Böttcher homeomorphism. -/
theorem NakaneData.rayPt_eq {Mb : Set ℂ} {Φ : ℂ → ℂ} (d d' : Work.Top.NakaneData Mb Φ)
    {θ t : ℝ} (ht : 1 < t) : d.rayPt θ t = d'.rayPt θ t := by
  have h3 : Φ (d.rayPt θ t) = Φ (d'.rayPt θ t) := by
    rw [d.Phi_rayPt ht, d'.Phi_rayPt ht]
  exact d.injOn_Phi (d.rayPt_notMem ht) (d'.rayPt_notMem ht) h3

/-- The **pair curve** of the rays at angles `θ` and `θ'`: the two rays together with their
accumulation (landing) points, i.e. the closure of their union. -/
def pairCurve (c : ℂ) (θ θ' : ℝ) : Set ℂ := closure (dynRayF c θ ∪ dynRayF c θ')

/-- The **side** of the pair curve of `(θ,θ')` containing the ray at the intermediate angle
`mid`, computed from given dynamical Böttcher data `d`: the connected component of the
complement of the pair curve which contains the point of the `mid`-ray of modulus `2`. -/
def pairSideD (c : ℂ) (d : DynData c) (θ θ' mid : ℝ) : Set ℂ :=
  connectedComponentIn (pairCurve c θ θ')ᶜ (d.rayPt mid 2)

/-- The **side** of the pair curve of `(θ,θ')` containing the ray at the intermediate angle
`mid`; the empty set when `T_c` has no dynamical Böttcher data. -/
def pairSide (c : ℂ) (θ θ' mid : ℝ) : Set ℂ :=
  if h : Nonempty (DynData c) then pairSideD c (Classical.choice h) θ θ' mid else ∅

/-- The **wake side** of the level-`j` portrait pair: the side of the pair curve
`R(T^j α₁) ∪ R(T^j α₂)` through the wake arc `W_j = T^j(α₁,α₂)`.  This is the set occurring in
the `wake` field of `Work.EL.RootParabolic`. -/
def wakeSide (c : ℂ) (j : ℕ) : Set ℂ := pairSide c (pairRay₁ j) (pairRay₂ j) (wakeMid j)

/-! ## The local ray portrait of the root point (modulo `1`)

The clause below is the classical ray count at the **root point of the non-real period-`5`
component** `H` — the point where the two root rays `α₁ = 371/1023` and `α₂ = 404/1023` land.  It
is consumed as a hypothesis (`RootParabolicInput.portrait`) by
`Submission/Work/FSeed/Classify.lean`, which derives from it the co-landing of `α₂`, the exactness
of the period, and the structure `Work.EL.RootParabolic`.

Two warnings, both of which are the content of
`Submission/Work/NOTES_LEAD_mandelbar_seedsimple.md` (§1, §4.1):

* it is classical **at the seed** — at the interior points of the root arc of the period-`5`
  component — and is *not* a general principle about parabolic points.  At the two *cusps* ending
  the root arc, three rays land at the double parabolic point: the two root rays and a co-root ray
  (Hubbard–Schleicher, arXiv:1209.1753 §5, the Remark before Def. 5.2 and Fig. 6; Mukherjee,
  arXiv:1404.7193, Lemma 2.10).  The earlier clause `one_ray_of_cusp` ("at a cusp at most one ray
  lands") had exactly this false justification and has been deleted; the non-cusp condition of the
  seed is now the direct field `RootParabolicInput.simple` (`Inputs.lean`);
* since `Work.Landing.landsAt` depends on the angle only modulo `1`
  (`Work.FSeed.landsAt_add_int_iff`, `Work.FSeed.landsAt_fract_iff`, in
  `Submission/Work/FSeed/Rays/landsAt_periodic.lean`), the count must be stated **modulo `1`**,
  with `Int.fract`.  The earlier real-valued form `θ = θ'` quantified over *real* angles and was
  refuted by the three angles `α₁, α₁+1, α₁+2`, which are pairwise distinct and all land at the
  same point: the bundle carrying it was false for every `c`.
-/

/-- **The exact local portrait at the root point**, modulo 1: at most two ray angles (mod 1) land
at `z`.  Classical at the seed: for `c` in the interior of the root arc of the period-5 component,
the rays landing at the characteristic parabolic point are exactly those at angles `α₁, α₂`
(mod 1) (MNS 1404.5031 Lemma 4.4(2) + Cor. 4.7/4.9; Mukherjee 1404.7193 Lemma 2.5/2.10;
HS 1209.1753 §5, Fig. 6).  NOT a general principle: at the cusps ending the root arc three rays
land (HS §5, Remark before Def. 5.2).

It is deliberately a statement about a *single* point `z` (not about every parabolic point): the
counts for satellite parabolic points (rotation number `p/q` with `q ≥ 3`) are larger, and only the
root of the period-`5` component is relevant here. -/
structure LocalRayPortrait (c : ℂ) (z : ℂ) : Prop where
  /-- at most two ray angles, modulo `1`, land at `z`. -/
  two_rays : ∀ θ θ' θ'' : ℝ, Work.Landing.landsAt c θ z → Work.Landing.landsAt c θ' z →
    Work.Landing.landsAt c θ'' z →
    Int.fract θ = Int.fract θ' ∨ Int.fract θ = Int.fract θ'' ∨ Int.fract θ' = Int.fract θ''

end Work.FSeed

end
