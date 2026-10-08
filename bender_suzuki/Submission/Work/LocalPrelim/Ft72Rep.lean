/-
Feit--Thompson odd order theorem: the `𝔽_p[X]`-module `O_p(X)/Φ(O_p(X))`.

This file provides the plumbing for the proof of Feit--Thompson Lemma 7.2 condition (3)
(`Work.LocalPrelim.ft7_2_cond3`): for a normal subgroup `F ⊴ X` the conjugation action of `X`
on the *Frattini quotient* `↥F ⧸ Φ(↥F)` is a representation of `X` over `ZMod p`.

* `Work.LocalPrelim.frattiniQuotConjAut` : the automorphism of `↥F ⧸ Φ(↥F)` induced by
  conjugation by `x : X`;
* `Work.LocalPrelim.frattiniQuotConj` : the same, as a monoid hom `X →* MulAut (↥F ⧸ Φ(↥F))`;
* `Work.LocalPrelim.frattiniQuotRep` : the conjugation representation of `X` on the `ZMod p`-space
  `Additive (↥F ⧸ Φ(↥F))`.
-/
import Mathlib
import Submission.Work.PGroup.All
import Submission.Work.Coprime.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement IsMulCommutative

namespace Work.LocalPrelim

variable {X : Type*} [Group X]

/-- An abelian *quotient* group of exponent dividing `p` carries the canonical `ZMod p`-module
structure.  (Companion of `Work.PStable.instModuleAdditiveSubgroup` for quotient groups.) -/
instance instModuleAdditiveQuotient {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    [IsMulCommutative (H ⧸ N)] {p : ℕ} [Fact (∀ x : H ⧸ N, x ^ p = 1)] :
    Module (ZMod p) (Additive (H ⧸ N)) :=
  AddCommGroup.zmodModule (fun x => (Fact.out : ∀ y : H ⧸ N, y ^ p = 1) x)

/-- The automorphism of the Frattini quotient `↥F ⧸ Φ(↥F)` of a normal subgroup `F ⊴ X`
induced by conjugation by `x : X`. -/
noncomputable def frattiniQuotConjAut (F : Subgroup X) [F.Normal] (x : X) :
    MulAut (↥F ⧸ frattini ↥F) :=
  QuotientGroup.congr (frattini ↥F) (frattini ↥F) (MulAut.conjNormal x)
    (Work.PGroup.frattini_map_mulEquiv (MulAut.conjNormal x))

@[simp] lemma frattiniQuotConjAut_mk (F : Subgroup X) [F.Normal] (x : X) (y : ↥F) :
    frattiniQuotConjAut F x ↑y = ↑((MulAut.conjNormal x) y) :=
  QuotientGroup.congr_mk _ _ _ _ _

/-- The conjugation action of `X` on the Frattini quotient `↥F ⧸ Φ(↥F)` of a normal subgroup
`F ⊴ X`, as a monoid hom. -/
noncomputable def frattiniQuotConj (F : Subgroup X) [F.Normal] :
    X →* MulAut (↥F ⧸ frattini ↥F) where
  toFun := frattiniQuotConjAut F
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y => rw [frattiniQuotConjAut_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' := by
    intro a b
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [frattiniQuotConjAut_mk]
      conv_rhs => rw [MulAut.mul_apply]
      rw [frattiniQuotConjAut_mk, frattiniQuotConjAut_mk]
      rw [map_mul, MulAut.mul_apply]

@[simp] lemma frattiniQuotConj_apply_mk (F : Subgroup X) [F.Normal] (x : X) (y : ↥F) :
    frattiniQuotConj F x ↑y = ↑((MulAut.conjNormal x) y) :=
  frattiniQuotConjAut_mk F x y

lemma frattiniQuotConjAut_eq (F : Subgroup X) [F.Normal] (x : X) :
    frattiniQuotConjAut F x = frattiniQuotConj F x := rfl

/-- The linear automorphism of `Additive (↥F ⧸ Φ(↥F))` induced by conjugation by `x : X`. -/
noncomputable def frattiniQuotLinAut (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)] (x : X) :
    Additive (↥F ⧸ frattini ↥F) ≃ₗ[ZMod p] Additive (↥F ⧸ frattini ↥F) :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive (frattiniQuotConj F x))
    (fun c v => ZMod.map_smul _ c v)

@[simp] lemma frattiniQuotLinAut_apply (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    (x : X) (v : Additive (↥F ⧸ frattini ↥F)) :
    frattiniQuotLinAut p F x v =
      Additive.ofMul (frattiniQuotConj F x (Additive.toMul v)) := rfl

/-- The conjugation representation of `X` over `ZMod p` on the Frattini quotient
`↥F ⧸ Φ(↥F)` of a normal subgroup `F ⊴ X`, when that quotient is elementary abelian of
exponent `p`. -/
noncomputable def frattiniQuotRep (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)] :
    X →* Module.End (ZMod p) (Additive (↥F ⧸ frattini ↥F)) where
  toFun x := (frattiniQuotLinAut p F x).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearEquiv.coe_toLinearMap, Module.End.one_apply]
    rw [frattiniQuotLinAut_apply]
    simp
  map_mul' := by
    intro a b
    refine LinearMap.ext fun v => ?_
    simp only [LinearEquiv.coe_toLinearMap, Module.End.mul_apply]
    rw [frattiniQuotLinAut_apply, frattiniQuotLinAut_apply, frattiniQuotLinAut_apply]
    simp

@[simp] lemma frattiniQuotRep_apply (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    (x : X) (v : Additive (↥F ⧸ frattini ↥F)) :
    frattiniQuotRep p F x v = frattiniQuotLinAut p F x v := rfl

@[simp] lemma frattiniQuotRep_apply_ofMul (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    (x : X) (y : ↥F) :
    frattiniQuotRep p F x (Additive.ofMul (↑y)) =
      Additive.ofMul (↑((MulAut.conjNormal x) y)) := by
  rw [frattiniQuotRep_apply, frattiniQuotLinAut_apply]
  rfl

/-- If conjugation by `x` is the identity on `↥F ⧸ Φ(↥F)`, then `x` acts as the identity linear
map on the associated `ZMod p`-space. -/
lemma frattiniQuotRep_eq_one_of_frattiniQuotConj_eq_one (p : ℕ) (F : Subgroup X) [F.Normal]
    [IsMulCommutative (↥F ⧸ frattini ↥F)] [Fact (∀ x : ↥F ⧸ frattini ↥F, x ^ p = 1)]
    {x : X} (h : frattiniQuotConj F x = 1) : frattiniQuotRep p F x = 1 := by
  have h2 : frattiniQuotLinAut p F x = 1 := by
    ext v
    rw [frattiniQuotLinAut_apply, h, MulAut.one_apply]
    simp
  rw [show frattiniQuotRep p F x = (frattiniQuotLinAut p F x).toLinearMap from rfl, h2]
  rfl

end Work.LocalPrelim
