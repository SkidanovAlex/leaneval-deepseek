/-
# ELRig — vocabulary of the equator-curve rigidity (EL, part 4)

Area `Submission/Work/ELRig/` of the mandelbar project: the **equator-curve rigidity**, i.e. the
proof of the main theorem `equatorLeak` (EL part 4 of
`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6).

This file adds the vocabulary that only ELRig needs, on top of the shared vocabulary `Work.EL`
of the area `ELTop` (`Submission/Work/ELTop/Defs.lean`):

* the tripod of the branch point `b₂` (rays `22/63`, `25/63`, `37/63`) and its three arms;
* the **equator** `E = Ψ '' ℝ` of the repelling coordinate of the parabolic point `z₁`;
* the **flower** `ParabolicFlower`, i.e. §4 of the contract (`Work.FatouCoord.ParabolicFlower`)
  together with the differentiability of the repelling coordinate, which `ELNest`'s
  `FlowerData` records without it;
* the input bundles `Portrait` (ELPull: the rational certificate and the portrait), `Nests`
  (ELNest: the two shrinking nests, the side preservation `SP`) and `PairTop` (ELTop: the
  plane topology of the ray polygons), which are the *explicit hypotheses* under which ELRig
  proves its theorems until the sibling areas land.

Nothing in this file is proved: it fixes language.  The theorems of the area are in
`Submission/Work/ELRig/Rigidity.lean`, `Reach.lean`, `Equator.lean`, `Ray.lean` and
`EquatorLeak.lean`.
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.FatouCoord.Flower
import Submission.Work.Top.Jordan
import Submission.Work.ELTop.Defs
import Submission.Work.Landing.Core
import Submission.Work.Landing.Rays
import Submission.Work.ParamRays.DynBottcher

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

/-! ## The tripod at `b₂` and its three arms -/

/-- The first ray of the tripod at the branch point `b₂`: `22/63`. -/
def b2a : ℝ := 22 / 63

/-- The second ray of the tripod at `b₂`: `25/63`. -/
def b2b : ℝ := 25 / 63

/-- The third ray of the tripod at `b₂`: `37/63`. -/
def b2c : ℝ := 37 / 63

/-- The tripod curve at the point `y`: the three rays of angles `22/63`, `25/63`, `37/63`
together with their common landing point `y`. -/
def tripodCurve {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) : Set ℂ :=
  paramRay hN b2a ∪ paramRay hN b2b ∪ paramRay hN b2c ∪ {y}

/-- The pair of rays bounding the **arm `A`** (`22/63`, `25/63`), landing at the tripod point. -/
def armPairA {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₁ : LandsN hN b2a y)
    (h₂ : LandsN hN b2b y) : CoPair hN where
  toRawPair := ⟨b2a, b2b, y⟩
  lands_a := h₁
  lands_b := h₂

/-- The pair of rays bounding the **arm `B`** (`25/63`, `37/63`). -/
def armPairB {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₂ : LandsN hN b2b y)
    (h₃ : LandsN hN b2c y) : CoPair hN where
  toRawPair := ⟨b2b, b2c, y⟩
  lands_a := h₂
  lands_b := h₃

/-- The pair of rays bounding the **arm `C`** (`37/63`, `85/63`). -/
def armPairC {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₃ : LandsN hN b2c y)
    (h₁ : LandsN hN (b2a + 1) y) : CoPair hN where
  toRawPair := ⟨b2c, b2a + 1, y⟩
  lands_a := h₃
  lands_b := h₁

/-- The **arm `A`** of the tripod: the side of the pair `(22/63, 25/63)` through its own arc. -/
def armA {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₁ : LandsN hN b2a y)
    (h₂ : LandsN hN b2b y) : Set ℂ :=
  pairSide (armPairA hN y h₁ h₂)

/-- The **arm `B`** of the tripod: the side of the pair `(25/63, 37/63)` through its own arc. -/
def armB {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₂ : LandsN hN b2b y)
    (h₃ : LandsN hN b2c y) : Set ℂ :=
  pairSide (armPairB hN y h₂ h₃)

/-- The **arm `C`** of the tripod: the side of the pair `(37/63, 85/63)` through its own arc. -/
def armC {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) (h₃ : LandsN hN b2c y)
    (h₁ : LandsN hN (b2a + 1) y) : Set ℂ :=
  pairSide (armPairC hN y h₃ h₁)

/-- **The `α`-pair** at the parabolic point `z₁`: the two rays of the root portrait
`371/1023` and `404/1023`, landing at `z₁`. -/
def alphaPair {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z₁ : ℂ) (h₁ : LandsN hN alpha1 z₁)
    (h₂ : LandsN hN alpha2 z₁) : CoPair hN where
  toRawPair := ⟨alpha1, alpha2, z₁⟩
  lands_a := h₁
  lands_b := h₂

/-! ## `F c` is the tenth iterate of `T_c` -/

theorem iterate_two_eq_comp (f : ℂ → ℂ) : f^[2] = f ∘ f := by
  funext z
  simp [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply']

theorem Tsq_eq_comp (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  rw [iterate_two_eq_comp]
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow]

/-- `F c = (Tsq c)^[5]` is the tenth iterate of the antiholomorphic quadratic `T_c`. -/
theorem F_eq_tantibar (c : ℂ) : F c = (Tantibar c)^[10] := by
  rw [F, Tsq_eq_comp, ← Function.iterate_mul, show (2 : ℕ) * 5 = 10 from rfl]

/-! ## The Fatou-coordinate input of `ELRig` -/

/-- The **Leau–Fatou flower** consumed by ELRig.  It *is* the contract's
`Work.FatouCoord.ParabolicFlower` (`Submission/Work/FatouCoord/Flower.lean`), i.e. §4 of
`NOTES_LEAD_mandelbar_EL_F_contracts.md`: the wide attracting petal `Pa`, the antiholomorphic
attracting coordinate `φa`, the entire inverse repelling coordinate `Ψ`, the functional equations
`Ψ (w+1) = F (Ψ w)`, `Ψ (conj w + 1/2) = g (Ψ w)`, the smallness of `Ψ` at the far repelling end,
its injectivity on a far-left half-plane, the ends `Ψ_ends` in the petal, and the covering `cover`.
The name is kept here so that the statements of this area read `Work.EL.ParabolicFlower …`; the
definition is the contract's, so `equatorLeak` applies to the flower that FatouCoord hands over. -/
abbrev FlowerData (F g : ℂ → ℂ) (z₀ : ℂ) := Work.FatouCoord.ParabolicFlower F g z₀

/-- The flower, under the name used by the contract's §4. -/
abbrev ParabolicFlower (F g : ℂ → ℂ) (z₀ : ℂ) := Work.FatouCoord.ParabolicFlower F g z₀

/-- The (identity) projection used by the statements of this area: `fl = fl`. -/
def toFlowerData {F g : ℂ → ℂ} {z₀ : ℂ} (fl : FlowerData F g z₀) : FlowerData F g z₀ := fl

/-- **Local biholomorphy of `Ψ` at a real point**: `Ψ` has a holomorphic two-sided local inverse
on a ball around `x`.  This is *not* a field of the flower: at a point `x` with `Ψ x` precritical
it can fail.  The rigidity argument needs it only at the two points `x*` and `x* + 1` with
`Ψ x* = b₂`, where it is *derived* from `b₂ ∉` the critical orbit of `0`
(`Work.EL.exists_localInverseAt_of_notPostcrit`). -/
def LocalInverseAt {F g : ℂ → ℂ} {z₀ : ℂ} (fl : FlowerData F g z₀) (x : ℝ) : Prop :=
  ∃ δ > 0, ∃ τ : ℂ → ℂ,
    AnalyticOnNhd ℂ τ (Metric.ball (fl.Ψ (x : ℂ)) δ) ∧
    (∀ w ∈ Metric.ball (x : ℂ) δ, τ (fl.Ψ w) = w) ∧
    (∀ z ∈ Metric.ball (fl.Ψ (x : ℂ)) δ, fl.Ψ (τ z) = z)

/-! ## The equator of the repelling coordinate -/

/-- The **equator** `E = Ψ '' ℝ` of the repelling coordinate `Ψ` of the parabolic point `z₀`: the
set of points of Ecalle height `0`, in the parametrization by the whole real line. -/
def equator {F g : ℂ → ℂ} {z₀ : ℂ} (fl : FlowerData F g z₀) : Set ℂ :=
  Set.range (fun x : ℝ => fl.Ψ (x : ℂ))

theorem mem_equator {F g : ℂ → ℂ} {z₀ : ℂ} {fl : FlowerData F g z₀} {z : ℂ} :
    z ∈ equator fl ↔ ∃ x : ℝ, fl.Ψ (x : ℂ) = z :=
  Iff.rfl

/-! ## The two-sidedness of a co-landing pair -/

/-- **Two-sidedness of a co-landing pair**: the complement of the pair curve is the disjoint
union of its far side (`pairSide`, the side through the arc `(a, b)`) and its near side
(`pairSideNear`, the side through the complementary arc `(b, a + 1)`), and both are open and
preconnected.  This is (T6) of `NOTES_LEAD_mandelbar_EL_F_contracts.md` §2, the input that
`ELTop` supplies.  (The complement of a pair curve on the sphere has exactly two components,
because the curve completed by `∞` is a Jordan curve.) -/
structure PairSides {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (P : CoPair hN) : Prop where
  /-- the far side is open. -/
  isOpen_far : IsOpen (pairSide P)
  /-- the near side is open. -/
  isOpen_near : IsOpen (pairSideNear P)
  /-- the two sides are disjoint. -/
  disjoint : Disjoint (pairSide P) (pairSideNear P)
  /-- together they cover the complement of the pair curve. -/
  union_eq : pairSide P ∪ pairSideNear P = (pairCurve P)ᶜ
  /-- the far side is preconnected. -/
  preconnected_far : IsPreconnected (pairSide P)
  /-- the near side is preconnected. -/
  preconnected_near : IsPreconnected (pairSideNear P)
  /-- the frontier of the far side is the pair curve. -/
  frontier_far : frontier (pairSide P) = pairCurve P
  /-- the frontier of the near side is the pair curve. -/
  frontier_near : frontier (pairSideNear P) = pairCurve P
  /-- (T3, angle-side) the ray of an angle in the far arc of `P` lies in the far side. -/
  paramRay_far : ∀ θ : ℝ, InArc θ P.a P.b → paramRay hN θ ⊆ pairSide P
  /-- (T3, angle-side) the ray of an angle in the complementary arc lies in the near side. -/
  paramRay_near : ∀ θ : ℝ, InArc θ P.b (P.a + 1) → paramRay hN θ ⊆ pairSideNear P

/-! ## The three arms of the tripod -/

/-- **The arms of the tripod at `b₂`**: the three sides of the three pairs bounding the arms
are pairwise disjoint, open, preconnected, and together with the tripod curve they cover the
plane.  This is (T8) of §2 (`ELTop`), with the co-landing of the three rays at `b₂`. -/
structure TripodSides {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (y : ℂ) : Prop where
  /-- the ray of angle `22/63` lands at the tripod point. -/
  lands_a : LandsN hN b2a y
  /-- the ray of angle `25/63` lands at the tripod point. -/
  lands_b : LandsN hN b2b y
  /-- the ray of angle `37/63` lands at the tripod point. -/
  lands_c : LandsN hN b2c y
  /-- the ray of angle `85/63` (the same ray as `22/63`) lands at the tripod point. -/
  lands_a' : LandsN hN (b2a + 1) y
  /-- the arm `A` is open. -/
  isOpen_A : IsOpen (armA hN y lands_a lands_b)
  /-- the arm `B` is open. -/
  isOpen_B : IsOpen (armB hN y lands_b lands_c)
  /-- the arm `C` is open. -/
  isOpen_C : IsOpen (armC hN y lands_c lands_a')
  /-- the three arms are pairwise disjoint. -/
  disjoint_AB : Disjoint (armA hN y lands_a lands_b) (armB hN y lands_b lands_c)
  disjoint_AC : Disjoint (armA hN y lands_a lands_b) (armC hN y lands_c lands_a')
  disjoint_BC : Disjoint (armB hN y lands_b lands_c) (armC hN y lands_c lands_a')
  /-- the arms cover the complement of the tripod curve. -/
  union_eq : armA hN y lands_a lands_b ∪ (armB hN y lands_b lands_c ∪
      armC hN y lands_c lands_a') = (tripodCurve hN y)ᶜ
  /-- the two-sidedness of the pair bounding the arm `A` (needed for the separation lemma). -/
  sides_A : PairSides hN (armPairA hN y lands_a lands_b)
  /-- the two-sidedness of the pair bounding the arm `B`. -/
  sides_B : PairSides hN (armPairB hN y lands_b lands_c)
  /-- the two-sidedness of the pair bounding the arm `C`. -/
  sides_C : PairSides hN (armPairC hN y lands_c lands_a')
  /-- the arms are preconnected. -/
  preconnected_A : IsPreconnected (armA hN y lands_a lands_b)
  preconnected_B : IsPreconnected (armB hN y lands_b lands_c)
  preconnected_C : IsPreconnected (armC hN y lands_c lands_a')

end Work.EL
