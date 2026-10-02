/-
# The root arc: the flower exists, and the critical Écalle height

Area `Submission/Work/Final/`.  This module proves that the **root-arc data** `Work.Final.RootArc`
is not an extra hypothesis: every `Work.EL.RootParabolic c` (the output of the `FSeed`/`FQC`/`FBif`
side) carries a Leau–Fatou flower of its characteristic parabolic point, by the delivered
existence theorem `Work.FatouCoord.Flower.exists_parabolicFlower` of the `FatouCoord` area.

The only new ingredient is the differentiability of the *antiholomorphic* square root: the flower
asks for `Differentiable ℂ (fun z => star (g z))` where `g = (T_c)^5`, i.e. for
`differentiable_star_Tantibar_five` below; this is the classical fact that an odd iterate of an
antiholomorphic map, composed with the complex conjugation, is holomorphic.

## Main results

* `Work.Final.differentiable_Tsq`, `Work.Final.differentiable_star_Tantibar_five` — the
  differentiability inputs;
* `Work.Final.exists_flower` — the flower exists at every root-parabolic parameter;
* `Work.Final.exists_rootArc`, `Work.Final.ofRootParabolic` — the root-arc data exists;
* `Work.Final.RootArc.critHeight_eq` — the critical height is the imaginary part of the attracting
  Fatou coordinate of the transited critical value.
-/
import Submission.Work.Final.Defs
import Submission.Work.FinalFix.Shift
import Submission.Work.FatouCoord.Flower.exists_parabolicFlower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The differentiability of the flower's data -/

/-- The holomorphic second return map `Tsq c = (T_c)^2` is differentiable. -/
theorem differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  have h : Work.Landing.Tsq c = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c := rfl
  rw [h]
  fun_prop

/-- `(T_c)^5` is the composite of `T_c` with the *holomorphic* iterate `(Tsq c)^[2]` of
`Tsq c = (T_c)^2`. -/
theorem Tantibar_iterate_five (c : ℂ) :
    (Tantibar c)^[5] = (Tantibar c) ∘ (Work.Landing.Tsq c)^[2] := by
  have h4 : (Tantibar c)^[4] = (Work.Landing.Tsq c)^[2] := by
    have h : (Tantibar c)^[4] = ((Tantibar c)^[2])^[2] := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul (Tantibar c) 2 2]
    rw [h, ← Work.EL.Tsq_eq_comp]
  rw [show (5 : ℕ) = 1 + 4 from rfl, Function.iterate_add (Tantibar c) 1 4,
    Function.iterate_one (Tantibar c), h4]

/-- **`star ∘ (T_c)^5` is holomorphic**, explicitly.  This is the differentiability requirement of
the flower `Work.FatouCoord.ParabolicFlower F g z₀` for `F = (T_c)^{10}` and `g = (T_c)^5`: the odd
iterate of the antiholomorphic map composed with the conjugation is a polynomial in `z`. -/
theorem star_Tantibar_iterate_five (c z : ℂ) :
    star ((Tantibar c)^[5] z) = ((Work.Landing.Tsq c)^[2] z) ^ 2 + star c := by
  rw [Tantibar_iterate_five, Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar]
  simp

theorem differentiable_star_Tantibar_five (c : ℂ) :
    Differentiable ℂ (fun z => star ((Tantibar c)^[5] z)) := by
  have hfun : (fun z : ℂ => star ((Tantibar c)^[5] z)) =
      fun z : ℂ => ((Work.Landing.Tsq c)^[2] z) ^ 2 + star c :=
    funext (star_Tantibar_iterate_five c)
  rw [hfun]
  exact (((differentiable_Tsq c).iterate 2).pow 2).add_const (star c)

/-! ## The flower at a root-parabolic parameter -/

/-- `(T_c)^5` is an antiholomorphic square root of the second return map `F c = (T_c)^{10}`. -/
theorem Tantibar_five_comp_self (c : ℂ) :
    ((Tantibar c)^[5]) ∘ ((Tantibar c)^[5]) = Work.EL.F c := by
  have hcomp : ∀ g : ℂ → ℂ, g ∘ g = g^[2] := by
    intro g
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add g 1 1, Function.iterate_one g]
  rw [hcomp ((Tantibar c)^[5]), Work.EL.F_eq_tantibar,
    show (10 : ℕ) = 5 * 2 from rfl, Function.iterate_mul (Tantibar c) 5 2]

theorem Tantibar_five_fix {c z₁ : ℂ} (h : (Tantibar c)^[5] z₁ = z₁) :
    Work.EL.F c z₁ = z₁ := by
  rw [Work.EL.F_eq_tantibar, show (10 : ℕ) = 5 + 5 from rfl,
    Function.iterate_add_apply (Tantibar c) 5 5 z₁, h, h]

/-- The second return map `F c = (T_c)^{10}` is differentiable (it is the fifth iterate of the
holomorphic `Tsq c`). -/
theorem differentiable_F (c : ℂ) : Differentiable ℂ (Work.EL.F c) := by
  have h : Work.EL.F c = (Work.Landing.Tsq c)^[5] := rfl
  rw [h]
  exact (differentiable_Tsq c).iterate 5

/-- **The flower of a root-parabolic parameter exists** (the `FatouCoord` area's
`exists_parabolicFlower`, applied to `F = (T_c)^{10}`, `g = (T_c)^5`).  Every input is either a
field of `Work.EL.RootParabolic` or one of the differentiability lemmas above; in particular the
flower is *not* an extra hypothesis of the root-arc data. -/
theorem exists_flower {c : ℂ} (d : Work.EL.RootParabolic c) :
    Nonempty (Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :=
  Work.FatouCoord.Flower.exists_parabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁
    (differentiable_F c)
    (differentiable_star_Tantibar_five c)
    (Tantibar_five_comp_self c)
    (Tantibar_five_fix d.per_half)
    d.mult
    d.simple
    d.per_half

/-- **The root-arc data exists** at every root-parabolic parameter. -/
theorem exists_rootArc {c : ℂ} (d : Work.EL.RootParabolic c) : Nonempty (RootArc c) :=
  (exists_flower d).map fun fl => ⟨d, fl⟩

/-- The root-arc data at a given root-parabolic parameter, with the flower chosen by choice. -/
noncomputable def ofRootParabolic {c : ℂ} (d : Work.EL.RootParabolic c) : RootArc c :=
  ⟨d, Classical.choice (exists_flower d)⟩

@[simp] theorem ofRootParabolic_d {c : ℂ} (d : Work.EL.RootParabolic c) :
    (ofRootParabolic d).d = d := rfl

/-! ## API of the critical height

`RootArc.critHeight` follows the normalisation of `NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.1:
the imaginary part of the attracting Fatou coordinate of the critical orbit *at the first time it
enters the petal* (`nEnter`).  Because the Fatou coordinate translates by the **real** shift
`z ↦ z + 1` along the dynamics (`φa ∘ F = φa + 1` on `Pa`), the Écalle height `Im φa` is invariant
under `F`, so the value does not depend on which time (past the entry) one taps the orbit:
`RootArc.critHeight_eq_ecalleHeightAt`.  This is exactly the design's critical Écalle height
`(trans c).im` of `NOTES_LEAD_mandelbar_arc_top.md` §2.3.

**The interface hypothesis: `φa_shift` (FatouCoordFix §3.1).**  The Fatou equation for the
*second* return map, `φa (F c z) = φa z + 1` on `Pa` with `F c = (T_c)^{10}`, is **not** derivable
from `mapsTo_Pa` alone: the field `φa_fatou.1.comp_self` squares the antiholomorphic relation
`φa ∘ g = conj ∘ φa + 1/2` and therefore needs `g = (T_c)^5` to preserve the petal, which is
*false* in general for the constructed flower (`NOTES_LEAD_mandelbar_residuals.md` §3.1: the wide
petal is symmetric about the equator but `g_W W = conj W + conj b + O(1/‖W‖)` with `Re b = 1/2`
and `Im b` arbitrary).  The equation *is* true for the construction (`φa` is the honest attracting
coordinate there), and it is exactly the field `φa_shift` that `FatouCoordFix` exports and that
`Work.FQC.PetalInput` already carries

```lean
φa_shift : ∀ z ∈ fl.Pa, fl.φa ((F c) z) = fl.φa z + 1
```

(Definitionally the same statement as `Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5])
fl`, so a `PetalInput` supplies `phi_comp`/`ecalleHeightAt_eq`/`critHeight_eq_ecalleHeightAt`
directly.)  The lemmas below therefore take `φa_shift` as their hypothesis.  The old hypothesis
`Set.MapsTo ((Tantibar c)^[5]) Pa Pa` is *not* needed anywhere; where it does hold,
`Work.FinalFix.HasPhiShift.of_comp_self` recovers `φa_shift` from it.  Nothing in the final
assembly depends on either: `critHeight` is only ever *evaluated* at the fixed tap time `nEnter`.
-/

namespace RootArc

variable {c : ℂ} (A : RootArc c)

/-- The critical height is the imaginary part of the attracting Fatou coordinate of the transited
critical value, at the first time it enters the petal (the normalisation of the F contract). -/
theorem critHeight_eq : A.critHeight = (A.fl.φa ((Work.EL.F c)^[A.nEnter] c)).im := rfl

/-- The Fatou relation `φa ∘ F = φa + 1` of the second return map `F c = (T_c)^{10}` on the
attracting petal (Hubbard–Schleicher Lemma 2.3, squared), under the interface hypothesis that the
antiholomorphic square root preserves the petal. -/
theorem phi_comp (hshift : Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) A.fl)
    {z : ℂ} (hz : z ∈ A.fl.Pa) : A.fl.φa (Work.EL.F c z) = A.fl.φa z + 1 :=
  hshift z hz

theorem phi_iterate (hshift : Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) A.fl)
    {z : ℂ} (hz : z ∈ A.fl.Pa) (k : ℕ) : A.fl.φa ((Work.EL.F c)^[k] z) = A.fl.φa z + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      A.phi_comp hshift (Work.FatouCoord.mapsTo_iterate_of_mapsTo A.fl.mapsTo_Pa k hz), ih]
    push_cast; ring

/-- **The Écalle height** of the `n`-th iterate of the critical value: `Im φa (F^n c)`.  This is
the transverse (height) coordinate of the point in the Écalle cylinder of the petal; the phase is
`Re φa` modulo `1`. -/
def ecalleHeightAt (n : ℕ) : ℝ := (A.fl.φa ((Work.EL.F c)^[n] c)).im

/-- **The Écalle height is invariant under the dynamics**: as soon as the orbit has entered the
petal, every later tap of the critical orbit gives the same height.  (Requires the interface
hypothesis of `phi_comp`.) -/
theorem ecalleHeightAt_eq
    (hshift : Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) A.fl)
    {n m : ℕ} (hnm : n ≤ m) (hmem : (Work.EL.F c)^[n] c ∈ A.fl.Pa) :
    A.ecalleHeightAt n = A.ecalleHeightAt m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hiter : (Work.EL.F c)^[n + k] c = (Work.EL.F c)^[k] ((Work.EL.F c)^[n] c) := by
    rw [Nat.add_comm n k, Function.iterate_add_apply]
  have hfat : A.fl.φa ((Work.EL.F c)^[k] ((Work.EL.F c)^[n] c))
      = A.fl.φa ((Work.EL.F c)^[n] c) + (k : ℂ) := A.phi_iterate hshift hmem k
  have hk : (A.fl.φa ((Work.EL.F c)^[n] c) + (k : ℂ)).im
      = (A.fl.φa ((Work.EL.F c)^[n] c)).im := by
    rw [Complex.add_im, Complex.natCast_im, add_zero]
  simp only [ecalleHeightAt, hiter, hfat, hk]

/-- **The critical height does not depend on the tap time**: for every `n` past the entry time of
the critical orbit into the petal, `critHeight` is the Écalle height of `F^n c`. -/
theorem critHeight_eq_ecalleHeightAt
    (hshift : Work.FinalFix.HasPhiShift (Work.EL.F c) ((Tantibar c)^[5]) A.fl)
    {n : ℕ} (hn : A.nEnter ≤ n) : A.critHeight = A.ecalleHeightAt n := by
  rw [critHeight_eq]
  exact A.ecalleHeightAt_eq hshift hn A.nEnter_spec

end RootArc

end Work.Final
