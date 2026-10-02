/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the mod-1 two-ray portrait at the seed

This area proves the local ray portrait of the seed parabolic point `z₁` from the *simple*
flower, and restates `FSeed`'s input as `NonCuspRootLimit`.  Design:
`Submission/Work/NOTES_LEAD_mandelbar_seed.md` §4 (all of it) and §5.1.

This file fixes the vocabulary: the cited clause `NonCuspRootLimit`, the angle set
`LandAngles`, the integer angle model of `ℤ/1023` used by the finite certificate, and the
`RayTailLift`/tail-order vocabulary in which the order lemmas (L, O, M, GF) are phrased.
-/
import Submission.Work.ELRig.All
import Submission.Work.FSeed.Inputs
import Submission.Work.ELPull.Defs
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

set_option maxHeartbeats 2000000

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The one cited clause of the seed** (`NOTES_LEAD_mandelbar_seed.md` §0.5, §3.1): a parameter
`c` of the tricorn which is a *limit point* of the parameter ray `R(α₁)` but not on it, at which
the two root rays land at a common point `z₁` which is a **simple** parabolic point of the second
return map `F c = (T_c)^[10]`.

Sources: MNS 1404.5031 L. 5.6 + L. 4.4(2) for the co-landing at every limit point of `R(α₁)`,
and IM 1406.3428 Thm 1.1 + MNS L. 2.9 for a limit point that is not a cusp.  This is the same
statement as `Work.SeedExist.NonCuspRootLimit` (the SeedExist area, §3.1 of the design note); it
is repeated here so that the SeedSimple2 area is self-contained. -/
def NonCuspRootLimit : Prop :=
  ∃ c z₁ : ℂ, c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) ∧
    c ∉ Work.ParamRays.paramRay Work.EL.alpha1 ∧
    Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧ Work.Landing.landsAt c Work.EL.alpha2 z₁ ∧
    iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0

/-- The angles `α₁`, `α₂` of `Work.EL`, as `Work.FSeed`'s angles. -/
theorem fseed_alpha1 : Work.FSeed.α₁ = Work.EL.alpha1 := by
  norm_num [Work.FSeed.α₁, Work.EL.alpha1]

theorem fseed_alpha2 : Work.FSeed.α₂ = Work.EL.alpha2 := by
  norm_num [Work.FSeed.α₂, Work.EL.alpha2]

/-- **The set of angles landing at `z`**, taken in the representative interval `[0,1)`.

`LandAngles hN z` is the set denoted `A` in §4.2 of the design note. -/
def LandAngles {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z : ℂ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Ico 0 1 ∧ Work.EL.LandsN hN θ z}

theorem mem_LandAngles {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z : ℂ} {θ : ℝ} :
    θ ∈ LandAngles hN z ↔ θ ∈ Set.Ico 0 1 ∧ Work.EL.LandsN hN θ z := Iff.rfl

/-- **The four angles of the portrait problem are pairwise distinct mod `1`** (the hypothesis of
the unlinked lemma `U`, §4.2). -/
def PairwiseDistinct4 (a b a' b' : ℝ) : Prop :=
  Int.fract a ≠ Int.fract b ∧ Int.fract a ≠ Int.fract a' ∧ Int.fract a ≠ Int.fract b' ∧
  Int.fract b ≠ Int.fract a' ∧ Int.fract b ≠ Int.fract b' ∧ Int.fract a' ≠ Int.fract b'

/-! ## The angle dynamics of the portrait problem -/

/-- The angle map of the second return map `g = (T_c)^[5]`: `θ ↦ T^[5] θ = -32 θ mod 1`. -/
abbrev GAngle (θ : ℝ) : ℝ := (Work.EL.T^[5]) θ

/-- The angle map of `F c = (T_c)^[10]`: `θ ↦ 1024 θ mod 1`. -/
abbrev FAngle (θ : ℝ) : ℝ := (Work.EL.T^[10]) θ

/-- `θ` is fixed by `g = (T_c)^[5]`. -/
def IsGFixed (θ : ℝ) : Prop := GAngle θ = θ

/-! ## Tails in the repelling coordinate: the vocabulary of §4.2 (items L, O, M, GF) -/

/-- The far-left half plane (the "strip") of the repelling coordinate `w` of the flower. -/
def strip (R : ℝ) : Set ℂ := {w : ℂ | w.re < -R}

/-- The "top end" of the strip `strip R` at height `Y`. -/
def topPoint (R Y : ℝ) : ℂ := ⟨-R - 1, Y⟩

/-- **The order of two tails in the strip**: the tail `Γ'` is *above* the tail `Γ` if (the top
end is off `Γ` and) `Γ'` meets the component of `(strip R) ∖ Γ` containing the top end.  Since
`Γ'` is preconnected and disjoint from `Γ`, meeting that component means being contained in it,
so this is the "top side" of the curve `Γ` in the sense of §4.2, item O. -/
def TailAbove (Γ Γ' : Set ℂ) (R Y : ℝ) : Prop :=
  topPoint R Y ∉ Γ ∧ ∃ w ∈ Γ', w ∈ connectedComponentIn ((strip R) \ Γ) (topPoint R Y)

/-- The tail `Γ''` lies *between* the tails `Γ` (below) and `Γ'` (above). -/
def TailBetween (Γ Γ'' Γ' : Set ℂ) (R Y : ℝ) : Prop :=
  TailAbove Γ Γ'' R Y ∧ TailAbove Γ'' Γ' R Y

/-- **The tail lift of the ray of angle `θ` in the repelling coordinate of the flower**: the
generalisation of `Work.ELRig.RayCylLift` from the two root rays to an arbitrary ray landing at
`z₁` (§4.2, item L).  `γ` parametrises the `Ψ`-preimages of the ray `R(θ)`; the level `τ s` of
the ray point is strictly increasing in `s`; `htailId` is the generalised `TailId`. -/
structure RayTailLift {c : ℂ} (d : Work.EL.RootParabolic c) (Ψ : ℂ → ℂ) (θ : ℝ) where
  /-- the tail curve. -/
  γ : ℝ → ℂ
  /-- the level of the ray point at parameter `s`. -/
  τ : ℝ → ℝ
  /-- the half-plane level of the tail identity. -/
  R : ℝ
  /-- the level parametrisation is strictly increasing. -/
  hτmono : StrictMono τ
  /-- all levels are `> 1`. -/
  hτ1 : ∀ s : ℝ, 1 < τ s
  /-- `Ψ` of the tail is the ray point of angle `θ` at the level `τ s`. -/
  hΨ : ∀ s : ℝ, Ψ (γ s) = Work.EL.rayPt d.hN θ (τ s)
  /-- the tail is continuous. -/
  cont : Continuous γ
  /-- the tail is injective. -/
  hinj : Function.Injective γ
  /-- the tail leaves the strip at the left end. -/
  hleft : Tendsto (fun s : ℝ => (γ s).re) atBot atBot
  /-- the tail is bounded in the imaginary direction. -/
  hbound : ∃ Y : ℝ, ∀ s : ℝ, |(γ s).im| ≤ Y
  /-- **the generalised `TailId`**: in the half plane `{Re < -R}` the `Ψ`-preimages of the ray
  `R(θ)` are exactly the points of the tail. -/
  htailId : ∀ w : ℂ, w.re < -R → Ψ w ∈ Work.EL.paramRay d.hN θ → w ∈ Set.range γ

/-! ## The integer angle model `ℤ/1023`

The angles `j/1023` (`0 ≤ j < 1023`) are the fixed points of the angle map `θ ↦ 1024 θ` of `F`,
and `377 = α₁`, `404 = α₂` among them.  All finite certificates of this area are checked in that
model, with the bridge lemmas in `Angle.lean`. -/

/-- The angle `j = 371` of `α₁` in the `/1023` model. -/
def α₁N : ℕ := 371

/-- The angle `j = 404` of `α₂`. -/
def α₂N : ℕ := 404

/-- The four angles `j/1023` that survive the finite certificate of §4.2. -/
def survivors : Finset ℕ := {371, 372, 403, 404}

/-- The angle map `T θ = -2θ mod 1` on `ℤ/1023`: `TN j` is the representative in `[0,1023)` of
`-2j mod 1023`. -/
def TN (j : ℕ) : ℕ := (1023 - (2 * j) % 1023) % 1023

/-- The second-return angle map `g = T^5` on `ℤ/1023`. -/
def gN (j : ℕ) : ℕ := (TN^[5]) j

/-- The angle map of `F = T^10` on `ℤ/1023`; it is the identity on `[0,1023)`. -/
def FN (j : ℕ) : ℕ := (TN^[10]) j

end Work.SeedSimple2

end
