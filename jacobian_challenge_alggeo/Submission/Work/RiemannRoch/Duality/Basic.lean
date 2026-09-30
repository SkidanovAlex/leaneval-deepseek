/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR, layer 5: linear algebra of Weil differentials

This file collects the elementary linear-algebra of the space `Ω = Omega C` of Weil
differentials (Serre, *Algebraic Groups and Class Fields*, II §8):

* `smulWLin C ω` — the `k`-linear map `f ↦ f ω`, making `Ω` a module over `K = K(C)`
  (the `K`-module structure itself is `smulW` of `Differentials.lean`);
* `smulW_ne_zero` — a nonzero differential stays nonzero under multiplication by `0 ≠ f ∈ K`;
* `IsDivW C ω W` — `W` is the *maximal* divisor with `ω ∈ WD C W`, i.e. the divisor of `ω`;
* `divW C ω` — that divisor, when it exists, with its universal property
  (`mem_WD_divW`, `le_divW`, `divW_spec`).

The existence of `divW` for `ω ≠ 0` in `Ω` (`exists_isDivW`), its behaviour under
multiplication (`smulW_divW`), and the resulting duality `i D = l (W - D)` for
`W = divW ω` (`isCanonical_divW`) are proved in the files of `RiemannRoch/Duality/`.
-/
import Submission.Work.RiemannRoch.Differentials
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.CurveBasics.Linear.finiteDimensional_L
import Submission.Work.RiemannRoch.RR.smulW_mem_WD
import Submission.Work.RiemannRoch.RR.smulW_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The Riemann–Roch space `L D` is finite dimensional: registered as an instance so that
`finrank`-computations about `L` do not need to carry it around. -/
instance finiteDimensional_L (C : Curve k) (D : C.Div) : FiniteDimensional k ↥(C.L D) :=
  Work.CurveBasics.Linear.finiteDimensional_L C D

/-! ## Linearity of multiplication by a function -/

theorem mulAdele_add (C : Curve k) (f g : C.functionField) (a : Adeles C) :
    mulAdele C (f + g) a = mulAdele C f a + mulAdele C g a := by
  ext Q
  simp only [mulAdele_apply, Submodule.coe_add, Pi.add_apply, add_mul]

theorem mulAdele_smul (C : Curve k) (c : k) (f : C.functionField) (a : Adeles C) :
    mulAdele C (c • f) a = c • mulAdele C f a := by
  ext Q
  simp only [mulAdele_apply, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc]

/-- `f ↦ f ω` is additive. -/
theorem smulW_add (C : Curve k) (f g : C.functionField) (ω : WeilDifferential C) :
    smulW C (f + g) ω = smulW C f ω + smulW C g ω := by
  ext a
  simp only [smulW_apply, LinearMap.add_apply, mulAdele_add, map_add]

/-- `f ↦ f ω` is `k`-linear. -/
theorem smulW_smul_k (C : Curve k) (c : k) (f : C.functionField) (ω : WeilDifferential C) :
    smulW C (c • f) ω = c • smulW C f ω := by
  ext a
  simp only [smulW_apply, LinearMap.smul_apply, mulAdele_smul, map_smul]

theorem smulW_zero_left (C : Curve k) (ω : WeilDifferential C) :
    smulW C (0 : C.functionField) ω = 0 := by
  have h : (0 : C.functionField) = (0 : k) • (0 : C.functionField) := by simp
  rw [h, smulW_smul_k, zero_smul]

theorem smulW_zero_right (C : Curve k) (f : C.functionField) :
    smulW C f (0 : WeilDifferential C) = 0 := by
  ext a; simp [smulW_apply]

/-- The `k`-linear map `f ↦ f ω`: the `K`-module structure of the space of Weil
differentials, as a `k`-linear map. -/
def smulWLin (C : Curve k) (ω : WeilDifferential C) :
    C.functionField →ₗ[k] WeilDifferential C where
  toFun := fun f => smulW C f ω
  map_add' := fun f g => smulW_add C f g ω
  map_smul' := fun c f => smulW_smul_k C c f ω

@[simp]
theorem smulWLin_apply (C : Curve k) (ω : WeilDifferential C) (f : C.functionField) :
    smulWLin C ω f = smulW C f ω := rfl

theorem smulW_sum (C : Curve k) {ι : Type*} (s : Finset ι) (f : ι → C.functionField)
    (ω : WeilDifferential C) :
    smulW C (∑ i ∈ s, f i) ω = ∑ i ∈ s, smulW C (f i) ω := by
  rw [← smulWLin_apply, map_sum]
  simp

/-- Multiplying a nonzero differential by `0 ≠ f ∈ K` keeps it nonzero. -/
theorem smulW_ne_zero (C : Curve k) {f : C.functionField} (hf : f ≠ 0)
    {ω : WeilDifferential C} (hω : ω ≠ 0) : smulW C f ω ≠ 0 :=
  fun h => hω ((RR.smulW_eq_zero_iff C hf ω).mp h)

/-! ## The divisor of a Weil differential -/

/-- `IsDivW C ω W` says that `W` is the largest divisor with `ω ∈ WD C W`, i.e. that `W` is
the divisor of the Weil differential `ω`.  Such a `W` exists exactly for the nonzero elements
of `Ω` (`exists_isDivW`). -/
def IsDivW (C : Curve k) (ω : WeilDifferential C) (W : C.Div) : Prop :=
  ω ∈ WD C W ∧ ∀ E : C.Div, ω ∈ WD C E → E ≤ W

theorem isDivW_unique {C : Curve k} {ω : WeilDifferential C} {W W' : C.Div}
    (h : IsDivW C ω W) (h' : IsDivW C ω W') : W = W' :=
  le_antisymm (h'.2 W h.1) (h.2 W' h'.1)

/-- The divisor of a Weil differential: the largest `D` with `ω ∈ WD C D`, when it exists
(and `0` otherwise). -/
noncomputable def divW (C : Curve k) (ω : WeilDifferential C) : C.Div :=
  if h : ∃ W : C.Div, IsDivW C ω W then Classical.choose h else 0

theorem divW_spec (C : Curve k) {ω : WeilDifferential C} (h : ∃ W : C.Div, IsDivW C ω W) :
    IsDivW C ω (divW C ω) := by
  have h' : divW C ω = Classical.choose h := dite_eq_left h
  rw [h']
  exact Classical.choose_spec h

theorem mem_WD_divW (C : Curve k) {ω : WeilDifferential C} (h : ∃ W : C.Div, IsDivW C ω W) :
    ω ∈ WD C (divW C ω) :=
  (divW_spec C h).1

theorem le_divW (C : Curve k) {ω : WeilDifferential C} (h : ∃ W : C.Div, IsDivW C ω W)
    {E : C.Div} (hE : ω ∈ WD C E) : E ≤ divW C ω :=
  (divW_spec C h).2 E hE

/-- A divisor `W` with the universal property of `divW` *is* `divW`, when the latter exists. -/
theorem divW_eq_of_isDivW (C : Curve k) {ω : WeilDifferential C} {W : C.Div}
    (h : ∃ W' : C.Div, IsDivW C ω W') (hW : IsDivW C ω W) : divW C ω = W :=
  isDivW_unique (divW_spec C h) hW

end

end Curve

end Work.RiemannRoch
