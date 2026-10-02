/-
# EL nest, part 0: the vocabulary of the two shrinking nests

Area `Submission/Work/ELNest/` of the mandelbar project (EL part 3 of
`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6): the two shrinking nests, at the parabolic point
`z₁` (items N0=N1, N1, N2) and at the branch point `b₂` (items N3, N4, N5).

This file fixes the vocabulary of the area.  It is built on the shared vocabulary `Work.EL`
declared by the area `ELTop` (`Submission/Work/ELTop/Defs.lean`): the filled Julia set `K c`,
the dynamical Böttcher data `DynB c φ`, the potential `pot hN`, the rays `paramRay`/`rayPt`,
the co-landing pairs `CoPair hN` with their two sides `pairSide`/`pairSideNear`, the ray
polygons `polyCurve`/`polyRegion`, the tripod at `b₂`, and the input bundle `RootParabolic c`.

What is added here:

* `F c = (Tsq c)^[5] = f_c^{10}` with its antiholomorphic square root `G c = (Tantibar c)^[5]`
  (kept under the names used by `Work.ELRig`, which imports this module for `F_eq_tantibar`);
* `F6 c = (Tsq c)^[3] = f_c^6`, the map whose inverse branch is the `b₂`-nest;
* the exact rational angle data of the certificate `mb_EL_cert.py`:
  `bAng n`, `bAng' n` (the `z₁`-nest), `Qlev`, `Dlev` (the levels), `armA1 … armC2` (the level-`n`
  arm pairs), `φ`, and the `contract` normalisation used in the certificate script;
* `FlowerData c z₀`, the Leau–Fatou flower of the parabolic point `z₀` of `F c` with square root
  `G c` (the structure of `NOTES_LEAD_mandelbar_EL_F_contracts.md` §4, written in the
  specialised form used by the nest arguments), together with its conversion to
  `Work.FatouCoord.ParabolicFlower (F c) (G c) z₀`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## The tenth iterate and its square root -/

/-- `F c = (Tsq c)^[5] = (T_c)^{10}`: holomorphic, of degree `1024`. -/
def F (c : ℂ) : ℂ → ℂ := (Work.Landing.Tsq c)^[5]

/-- `G c = (Tantibar c)^[5]`: the antiholomorphic square root of `F c`, `G c ∘ G c = F c`. -/
def G (c : ℂ) : ℂ → ℂ := (Tantibar c)^[5]

/-- `F6 c = (Tsq c)^[3] = (T_c)^6`: holomorphic, of degree `64`. -/
def F6 (c : ℂ) : ℂ → ℂ := (Work.Landing.Tsq c)^[3]

theorem F_eq (c z : ℂ) : F c z = (Work.Landing.Tsq c)^[5] z := rfl

/-- The second iterate of a function is its square. -/
theorem iterate_two_eq_comp (f : ℂ → ℂ) : f^[2] = f ∘ f := by
  funext z
  simp [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply']

/-- `Tsq c = (T_c)²` as a function. -/
theorem Tsq_eq_comp (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  rw [iterate_two_eq_comp]
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow]

theorem F_eq_tantibar (c : ℂ) : F c = (Tantibar c)^[10] := by
  rw [F, Tsq_eq_comp, ← Function.iterate_mul, show (2 : ℕ) * 5 = 10 from rfl]

theorem F6_eq_tantibar (c : ℂ) : F6 c = (Tantibar c)^[6] := by
  rw [F6, Tsq_eq_comp, ← Function.iterate_mul, show (2 : ℕ) * 3 = 6 from rfl]

theorem G_comp_G (c : ℂ) : G c ∘ G c = F c := by
  rw [F_eq_tantibar, G, ← iterate_two_eq_comp, ← Function.iterate_mul,
    show (5 : ℕ) * 2 = 10 from rfl]

/-- `Tsq c` is continuous. -/
theorem continuous_tsq (c : ℂ) : Continuous (Work.Landing.Tsq c) := by
  rw [show Work.Landing.Tsq c = fun z => (z ^ 2 + star c) ^ 2 + c from rfl]
  continuity

theorem continuous_F (c : ℂ) : Continuous (F c) := by
  rw [F]; exact (continuous_tsq c).iterate 5

theorem continuous_F6 (c : ℂ) : Continuous (F6 c) := by
  rw [F6]; exact (continuous_tsq c).iterate 3

/-- `Tantibar c` is continuous. -/
theorem continuous_tantibar (c : ℂ) : Continuous (Tantibar c) := by
  rw [show Tantibar c = fun z => star z ^ 2 + c from rfl]
  continuity

/-! ## The angle data of the certificate -/

/-- Folding a real number into `(-1/2, 1/2]` (up to the endpoint convention), as used in the
certificate `lead_mb/mb_EL_cert.py`. -/
def centred (x : ℝ) : ℝ := Int.fract (x + 1 / 2) - 1 / 2

/-- The `N`-fold contraction of the angle `t` toward the angle `fix`, in the normalisation of
`lead_mb/mb_EL_cert.py`. -/
def contract (t fix : ℝ) (N : ℕ) : ℝ := Int.fract (fix + centred (t - fix) / (N : ℝ))

/-- First root angle `α₁ = 371/1023`. -/
def alpha1 : ℝ := 371 / 1023

/-- Second root angle `α₂ = 404/1023`. -/
def alpha2 : ℝ := 404 / 1023

/-- The angle `β₀ = 379859/1047552` of the level-0 pair of the `z₁`-nest. -/
def beta0 : ℝ := 379859 / 1047552

/-- The angle `β₀' = 414113/1047552` of the level-0 pair of the `z₁`-nest. -/
def beta0' : ℝ := 414113 / 1047552

/-- The angle `βₙ = α₁ − (α₁ − β₀)/1024ⁿ` of the level-`n` pair of the `z₁`-nest (the angle
near `α₁`). -/
def bAng (n : ℕ) : ℝ := alpha1 - (alpha1 - beta0) / (1024 : ℝ) ^ n

/-- The angle `βₙ' = α₂ + (β₀' − α₂)/1024ⁿ` of the level-`n` pair of the `z₁`-nest (the angle
near `α₂`). -/
def bAng' (n : ℕ) : ℝ := alpha2 + (beta0' - alpha2) / (1024 : ℝ) ^ n

/-- The level `L ^ (1/1024ⁿ)` of the `n`-th region of the `z₁`-nest. -/
def Qlev (L : ℝ) (n : ℕ) : ℝ := L ^ ((1 : ℝ) / (1024 : ℝ) ^ n)

/-- The level `L ^ (1/64ⁿ)` of the `n`-th region of the `b₂`-nest. -/
def Dlev (L : ℝ) (n : ℕ) : ℝ := L ^ ((1 : ℝ) / (64 : ℝ) ^ n)

/-- First angle of the level-`n` arm-`A` pair (arm `(22/63, 25/63)`). -/
def armA1 (n : ℕ) : ℝ := contract alpha1 (22 / 63) (64 ^ n)

/-- Second angle of the level-`n` arm-`A` pair. -/
def armA2 (n : ℕ) : ℝ := contract alpha2 (25 / 63) (64 ^ n)

/-- First angle of the level-`n` arm-`B` pair (arm `(25/63, 37/63)`). -/
def armB1 (n : ℕ) : ℝ := contract (461 / 1023) (25 / 63) (64 ^ n)

/-- Second angle of the level-`n` arm-`B` pair. -/
def armB2 (n : ℕ) : ℝ := contract (593 / 1023) (37 / 63) (64 ^ n)

/-- First angle of the level-`n` arm-`C` pair (arm `(37/63, 22/63 + 1)`). -/
def armC1 (n : ℕ) : ℝ := contract (821 / 1023) (37 / 63) (64 ^ n)

/-- Second angle of the level-`n` arm-`C` pair. -/
def armC2 (n : ℕ) : ℝ := contract (1349 / 1023) (22 / 63) (64 ^ n)

/-! ## The Leau--Fatou flower at the parabolic point -/

/-- **The Leau–Fatou flower** of the simple parabolic fixed point `z₀` of `F c`, with the
antiholomorphic square root `G c`, in the normalisation of Hubbard–Schleicher Lemma 2.3.
This is `Work.FatouCoord.ParabolicFlower (F c) (G c) z₀` (contract §4) written out in the
specialised form in which the nest arguments use it: a structure *field* whose type mentions
`Work.FatouCoord.ParabolicFlower (F c) (G c) z₀` (with the two functions as arguments) makes the
elaborator's `isDefEq` blow up as soon as the structure is unpacked, so the two maps are
specialised here.  The conversion from the generic flower of `FatouCoord` is
`Work.ELNest.FlowerData.ofFatouCoord` (`Flower.lean`); it drops `Ψ_diff` and the antiholomorphy
of the chart, which the nest arguments do not use. -/
structure FlowerData (c : ℂ) (z₀ : ℂ) where
  /-- the (wide) attracting petal. -/
  Pa : Set ℂ
  /-- the attracting Fatou coordinate on `Pa`. -/
  φa : ℂ → ℂ
  /-- the inverse repelling coordinate, entire. -/
  Ψ : ℂ → ℂ
  isOpen_Pa : IsOpen Pa
  isPreconnected_Pa : IsPreconnected Pa
  z₀_not_mem : z₀ ∉ Pa
  mapsTo_Pa : Set.MapsTo (F c) Pa Pa
  tendsto_Pa : ∀ z ∈ Pa, Tendsto (fun n => (F c)^[n] z) atTop (nhds z₀)
  enters_Pa : ∀ z, Tendsto (fun n => (F c)^[n] z) atTop (nhds z₀) → (∀ n, (F c)^[n] z ≠ z₀) →
    ∃ n, (F c)^[n] z ∈ Pa
  φa_fatou : ∀ z ∈ Pa, φa (G c z) = star (φa z) + 1 / 2
  φa_inj : Set.InjOn φa Pa
  Ψ_shift : ∀ w, Ψ (w + 1) = F c (Ψ w)
  Ψ_anti : ∀ w, Ψ (star w + 1 / 2) = G c (Ψ w)
  Ψ_small : ∀ ε > 0, ∃ R, ∀ w : ℂ, w.re < -R → Ψ w ≠ z₀ ∧ ‖Ψ w - z₀‖ < ε
  Ψ_inj : ∃ R₀, Set.InjOn Ψ {w | w.re < -R₀}
  Ψ_ends : ∃ R₀, ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → Ψ w ∈ Pa
  cover : ∀ R, ∃ r > 0, ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
    z ∈ Pa ∨ ∃ w, w.re < -R ∧ Ψ w = z

/-- The flower of the half-line `H_R = {Re w < -R}`. -/
def Hhalf (R : ℝ) : Set ℂ := {w : ℂ | w.re < -R}

theorem mem_Hhalf {R : ℝ} {w : ℂ} : w ∈ Hhalf R ↔ w.re < -R := Iff.rfl

end Work.ELNest
