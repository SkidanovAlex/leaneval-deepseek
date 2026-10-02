/-
# SeedCertRay — the rational box layer of the ray-chain certificate

Vocabulary of the certified ray chain of `Submission/Work/SeedCertRay/` (area SeedCertRay of
the mandelbar seed; see `Submission/Work/NOTES_LEAD_mandelbar_noncusp.md` §2.3–§2.6):

* `Work.SeedCertRay.Box` : a closed axis-parallel rectangle in the plane with rational
  corners.  Every piece of certificate data of the chain is a box.
* `Box.mem`, `Box.toSet` : membership and the underlying closed set.
* `Box.neg`, `Box.center`, `Box.rad` : the reflection `z ↦ -z`, the centre, and the rational
  bound `rad B` for the distance of a point of `B` to its centre.
* `Work.SeedCertRay.SqrtCover` : the preimage cover condition (D1) of the chain, per box:
  the two-valued preimage of `Bq` under `T_c u = conj u ^ 2 + c`, with `c` running over the
  parameter box `X`, is contained in `B' ∪ -B'`.
* `Work.SeedCertRay.SepSelf`, `SepPair` : the two radial separation conditions (D2) of the
  chain: `B ∩ -B = ∅` and `B ∩ -B' = ∅`.
* `Work.SeedCertRay.seg` : the ray piece `rp θ '' Icc r₁ r₂` of the external ray at angle `θ`
  between the levels `r₁ ≤ r₂` (vocabulary `Work.EL.rayPt`).
* `Work.SeedCertRay.Petal` : the repelling petal `Re (-1/(A (z - z₁))) < -R` of the parabolic
  point, the landing region of the tail argument.
-/
import Mathlib
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.SeedCertRay

open Classical Set Function Filter
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. Boxes -/

/-- A closed axis-parallel rectangle in the plane, with rational corners. -/
structure Box where
  xl : ℚ
  xh : ℚ
  yl : ℚ
  yh : ℚ

namespace Box

/-- Membership in a box. -/
def mem (B : Box) (z : ℂ) : Prop :=
  (B.xl : ℝ) ≤ z.re ∧ z.re ≤ (B.xh : ℝ) ∧ (B.yl : ℝ) ≤ z.im ∧ z.im ≤ (B.yh : ℝ)

/-- The closed set underlying a box. -/
def toSet (B : Box) : Set ℂ := {z | B.mem z}

@[simp] theorem mem_toSet {B : Box} {z : ℂ} : z ∈ B.toSet ↔ B.mem z := Iff.rfl

/-- The reflection of a box. -/
def neg (B : Box) : Box := ⟨-B.xh, -B.xl, -B.yh, -B.yl⟩

@[simp] theorem neg_xl (B : Box) : B.neg.xl = -B.xh := rfl
@[simp] theorem neg_xh (B : Box) : B.neg.xh = -B.xl := rfl
@[simp] theorem neg_yl (B : Box) : B.neg.yl = -B.yh := rfl
@[simp] theorem neg_yh (B : Box) : B.neg.yh = -B.yl := rfl

theorem mem_neg {B : Box} {z : ℂ} : B.neg.mem z ↔ B.mem (-z) := by
  simp only [mem, neg_xl, neg_xh, neg_yl, neg_yh, Complex.neg_re, Complex.neg_im,
    Rat.cast_neg]
  constructor <;> intro h
  · exact ⟨by linarith [h.2.1], by linarith [h.1], by linarith [h.2.2.2], by linarith [h.2.2.1]⟩
  · exact ⟨by linarith [h.2.1], by linarith [h.1], by linarith [h.2.2.2], by linarith [h.2.2.1]⟩

theorem neg_toSet (B : Box) : B.neg.toSet = -B.toSet := by
  ext z
  rw [mem_toSet, Set.mem_neg, mem_neg]
  exact mem_toSet.symm

/-- The rational centre of a box, as a complex number. -/
def center (B : Box) : ℂ := (((B.xl + B.xh) / 2 : ℚ) : ℂ) + ((B.yl + B.yh) / 2 : ℚ) * Complex.I

/-- A rational upper bound for the distance from any point of the box to its centre. -/
def rad (B : Box) : ℚ := (B.xh - B.xl) + (B.yh - B.yl)

end Box

/-- The box with rational half-width `ρ` around the point `conj (w0re + i w0im)`.  This is the
shape of the boxes produced by a square-root step, and the reason the certificate data of a step
is just `(w0re, w0im, s, R, ρ)`. -/
def boxOf (w0re w0im ρ : ℚ) : Box :=
  ⟨w0re - ρ, w0re + ρ, -w0im - ρ, -w0im + ρ⟩

@[simp] theorem boxOf_xl (a b ρ : ℚ) : (boxOf a b ρ).xl = a - ρ := rfl
@[simp] theorem boxOf_xh (a b ρ : ℚ) : (boxOf a b ρ).xh = a + ρ := rfl
@[simp] theorem boxOf_yl (a b ρ : ℚ) : (boxOf a b ρ).yl = -b - ρ := rfl
@[simp] theorem boxOf_yh (a b ρ : ℚ) : (boxOf a b ρ).yh = -b + ρ := rfl

/-! ## 2. The preimage cover (D1) and the radial separations (D2) -/

/-- **Condition (D1) of the ray chain.**  For every `q` in the box `Bq` and every parameter
`c` in the parameter box `X`, every preimage `u` of `q` under `T_c` lies in `B'` or in `-B'`.
This is the localised form of "the preimage of the covering is covered". -/
def SqrtCover (Bq X B' : Box) : Prop :=
  ∀ q c u : ℂ, Bq.mem q → X.mem c → Tantibar c u = q → B'.mem u ∨ B'.mem (-u)

/-- **Radial separation of a box from its own reflection**: `B ∩ -B = ∅`. -/
def SepSelf (B : Box) : Prop := Disjoint B.toSet (-B.toSet)

/-- **Radial separation of two boxes**: `B ∩ -B' = ∅`. -/
def SepPair (B B' : Box) : Prop := Disjoint B.toSet (-B'.toSet)

/-! ## 3. Ray pieces -/

/-- The piece of the external ray of angle `θ` between the levels `r₁` and `r₂`: the image of
`Icc r₁ r₂` under the level parametrisation `t ↦ rp θ t` of the ray.  For `1 < r₁ ≤ r₂` this
is a compact, connected piece of the ray `R_c(θ)` (vocabulary `Work.EL.rayPt`). -/
def seg {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) (r₁ r₂ : ℝ) : Set ℂ :=
  Work.EL.rayPt hN θ '' Set.Icc r₁ r₂

theorem seg_def {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ r₁ r₂ : ℝ) :
    seg hN θ r₁ r₂ = Work.EL.rayPt hN θ '' Set.Icc r₁ r₂ := rfl

/-! ## 4. The repelling petal -/

/-- The Fatou coordinate `w = -1/(A (z - z₁))` of the petal. -/
def fatou (z₁ A : ℂ) (z : ℂ) : ℂ := -(A * (z - z₁))⁻¹

/-- The **repelling petal** at the parabolic point `z₁` with multiplier model `A` (the
quadratic coefficient `F''(z₁)/2` of the first return map `F`): the set of points whose Fatou
coordinate `w = -1/(A (z - z₁))` has real part below `-R`.  This is the region into which the
tail of the ray is certified to enter (`Q_R` of the design note). -/
def Petal (z₁ A : ℂ) (R : ℝ) : Set ℂ := {z : ℂ | z ≠ z₁ ∧ (fatou z₁ A z).re < -R}

@[simp] theorem mem_Petal_iff {z₁ A : ℂ} {R : ℝ} {z : ℂ} :
    z ∈ Petal z₁ A R ↔ z ≠ z₁ ∧ (fatou z₁ A z).re < -R := Iff.rfl

end Work.SeedCertRay
