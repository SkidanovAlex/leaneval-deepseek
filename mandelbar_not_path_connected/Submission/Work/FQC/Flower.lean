/-
# `Work.FQC.Flower` — the flower of a root-parabolic parameter, and the critical height

The hypotheses of `Work.FatouCoord.Flower.exists_parabolicFlower` at `F c = (Tantibar c)^[10]`,
`g = (Tantibar c)^[5]` and `z₁` are exactly the fields of a root-parabolic parameter, so every
`d : Work.EL.RootParabolic c` carries a Leau–Fatou flower.  This file provides

* `Work.FQC.flowerOf`, `Work.FQC.EcalleData.canonical` and `Work.FQC.critHeight`;
* `Work.FQC.tapPoint`, the first critical-orbit point inside the petal;
* `Work.FQC.SimpleTransfer` and `Work.FQC.EcalleInput`, the explicit inputs of the height-shift
  theorem (the petal structure, MNS's phase normalisation, the petal-direction input for the
  transferred parabolic point, and the uniqueness of the height).
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FatouCoord.Flower.exists_parabolicFlower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The iterates `Tsq` and `F = T_c^[10]`

`F c = (Tsq c)^[5] = (Tantibar c)^[10]`, and the explicit polynomial model of `(Tantibar c)^[2]`
is `TsqP c z = (z^2 + c̄)^2 + c`.  Working with `TsqP` (rather than with `Work.Landing.Tsq`)
keeps the definitional equalities cheap. -/

/-- The explicit polynomial `z ↦ (z^2 + c̄)^2 + c` of the holomorphic second iterate. -/
def TsqP (c : ℂ) : ℂ → ℂ := fun z => (z ^ 2 + star c) ^ 2 + c

theorem differentiable_TsqP (c : ℂ) : Differentiable ℂ (TsqP c) := by
  unfold TsqP
  fun_prop

theorem tantibar_two (c : ℂ) : (Tantibar c)^[2] = TsqP c := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  funext z
  rw [Function.comp_apply, Work.Landing.Tantibar_apply, Work.Landing.Tantibar_apply]
  simp only [star_add, star_pow, star_star]
  rfl

theorem F_eq_poly (c : ℂ) : F c = (TsqP c)^[5] := by
  rw [Work.EL.F, Tsq_eq_iterate, ← tantibar_two c]

theorem differentiable_F (c : ℂ) : Differentiable ℂ (F c) := by
  rw [F_eq_poly c]
  exact (differentiable_TsqP c).iterate 5

theorem iterate_four_eq (c : ℂ) : (Tantibar c)^[4] = (TsqP c)^[2] := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, Function.iterate_mul, tantibar_two]

theorem iterate_five_eq (c : ℂ) : (Tantibar c)^[5] = (Tantibar c) ∘ (TsqP c)^[2] := by
  rw [show (5 : ℕ) = 1 + 4 by norm_num, Function.iterate_add, Function.iterate_one,
    iterate_four_eq]

theorem star_comp_g_eq (c : ℂ) :
    (fun w : ℂ => star ((Tantibar c)^[5] w)) =
      (fun w : ℂ => w ^ 2 + star c) ∘ (TsqP c)^[2] := by
  rw [iterate_five_eq c]
  funext w
  simp only [Function.comp_apply]
  rw [Work.Landing.Tantibar_apply]
  simp only [star_add, star_pow, star_star]

theorem differentiableAt_star_comp_g (c : ℂ) :
    ∀ z : ℂ, DifferentiableAt ℂ (fun w => star ((Tantibar c)^[5] w)) z := by
  have hpoly : Differentiable ℂ (fun w : ℂ => w ^ 2 + star c) := by fun_prop
  have hT : Differentiable ℂ ((TsqP c)^[2]) := (differentiable_TsqP c).iterate 2
  rw [star_comp_g_eq c]
  exact fun z => hpoly.differentiableAt.comp z hT.differentiableAt

theorem g_comp_g (c : ℂ) : ((Tantibar c)^[5]) ∘ ((Tantibar c)^[5]) = F c := by
  funext z
  rw [Function.comp_apply, ← Function.iterate_add_apply, F_eq_iterate]

theorem F_fix (c : ℂ) (d : RootParabolic c) : F c d.z₁ = d.z₁ := by
  rw [F_eq_iterate, show (10 : ℕ) = 5 + 5 by norm_num, Function.iterate_add_apply,
    d.per_half, d.per_half]

theorem deriv_F_eq_one (c : ℂ) (d : RootParabolic c) : deriv (F c) d.z₁ = 1 := by
  rw [Work.EL.F]
  exact d.mult

/-! ## 2. The flower, the canonical Écalle data and the critical height -/

/-- The Leau–Fatou flower of `F c` at `d.z₁`. -/
noncomputable def flowerOf {c : ℂ} (d : RootParabolic c) :
    Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁ :=
  Classical.choice (Work.FatouCoord.Flower.exists_parabolicFlower (F c) ((Tantibar c)^[5]) d.z₁
    (differentiable_F c) (differentiableAt_star_comp_g c) (g_comp_g c) (F_fix c d)
    (deriv_F_eq_one c d) d.simple d.per_half)

/-- The canonical Écalle data of a root-parabolic parameter. -/
noncomputable def EcalleData.canonical {c : ℂ} (d : RootParabolic c) : EcalleData d :=
  EcalleData.ofFlower d (flowerOf d)

/-- The **critical Écalle height** of a root-parabolic parameter: the imaginary part of the
Fatou coordinate at the first critical-orbit point inside the petal. -/
noncomputable def critHeight {c : ℂ} (d : RootParabolic c) : ℝ :=
  critHeightAt d (EcalleData.canonical d)

/-- The first critical-orbit point inside the petal: where the critical height is read off. -/
noncomputable def tapPoint {c : ℂ} (d : RootParabolic c) (E : EcalleData d) : ℂ :=
  (F c)^[nEnter E] c

theorem tapPoint_mem {c : ℂ} (d : RootParabolic c) (E : EcalleData d) :
    tapPoint d E ∈ E.Pa := nEnter_spec E

theorem critHeightAt_eq_im {c : ℂ} (d : RootParabolic c) (E : EcalleData d) :
    critHeightAt d E = (E.φa (tapPoint d E)).im := rfl

/-! ## 3. The inputs of the height-shift theorem -/

/-- The first critical-orbit point inside the petal, computed directly from the flower (without
passing through `EcalleData`). -/
noncomputable def phasePoint {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) : ℂ :=
  (F c)^[Nat.find (fl.enters_Pa c d.crit.1 d.crit.2)] c

/-- **The petal-direction input at a fixed `t`.**  For every conjugacy `θ` produced by the
deformation (i.e. `θ = principal (muQC d fl t)`) with `θ ∘ T_c = T_{c₂} ∘ θ`, the transported
parabolic point `θ z₁` of `T_{c₂}` is again *simple*.

This is the one genuinely local input: it follows from the fact that the number of attracting
petals of a parabolic germ (one for a simple parabolic point, `> 1` for a multiple one) is
invariant under a topological conjugacy, together with the transported petal structure; the local
theory of multiple parabolic points is not in the library. -/
def SimpleTransfer {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) (P : Set ℂ)
    (t : ℝ) : Prop :=
  ∀ c₂ : ℂ, ∀ θ : ℂ ≃ₜ ℂ,
    (θ : ℂ → ℂ) = Work.MRMT.Found.principal (muQC d fl P t) →
    (∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) →
    iteratedDeriv 2 (F c₂) (θ d.z₁) ≠ 0

end Work.FQC

end
