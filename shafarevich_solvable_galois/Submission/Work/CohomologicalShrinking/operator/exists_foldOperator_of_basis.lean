/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The folding operator from a basis

Schmidt–Wingberg's shrinking lemma (arXiv:math/9809211, Section 2, proof of Proposition 6)
needs, for `a : Fin r → 𝔽_p` with `a k₀ = 1`, a *surjective* `G`-operator homomorphism

`ψ : F(r·n) ⟶ F(n)`,  `x_{(k,j),g} ↦ x_{(j,g)}^{a_k}`

of free `G`-operator groups, whose induced map `ψ̄ : F(r·n)/F(r·n)² → F(n)/F(n)²` realises the
folding map `φ_a : (F(n)/F(n)²)^r → F(n)/F(n)²` (`Work.Shrinking.foldMap`), `x ↦ ∑_k a_k • x_k`,
under the canonical identification `e : (F(n)/F(n)²)^r ≅ F(r·n)/F(r·n)²` of the two sides.

`Work.CohomologicalShrinking.operator.exists_foldOperator` produces one such `e` (namely
`foldEquiv`) together with `ψ`.  The present file proves the *basis form* of the statement:
whenever a linear equivalence `e` is given which is described on the standard basis vectors
`Pi.single k (genMk p G n (j,g))` by `e (Pi.single k (genMk p G n (j,g)))
= genMk p G (r·n) (finProdFinEquiv (k,j), g)`, the *same* `ψ` realises the fold with respect to
*that* `e`.  This is what makes the shrinking step independent of the particular isomorphism `e`
chosen: any two such `e` agree on a spanning set, hence are equal.

## Main results

* `Work.CohomologicalShrinking.operator.FoldOperatorOfBasis.psi` : the homomorphism `ψ` whose
  value on the free generator `x_{(k,j),g}` is `x_{(j,g)}^{a_k}`.
* `Work.CohomologicalShrinking.operator.FoldOperatorOfBasis.psi_surj`,
  `...psi_smul` : it is onto (`k₀` with `a k₀ = 1` provides the generators) and `G`-equivariant.
* `Work.CohomologicalShrinking.operator.FoldOperatorOfBasis.quotMapLin_genMk` : `ψ̄` on the class
  of a free generator.
* `Work.CohomologicalShrinking.operator.exists_foldOperator_of_basis` : the target.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.operator

set_option maxHeartbeats 1000000

set_option linter.style.haveILetI false

open Work.CohomologicalShrinking

/-! The auxiliary material is confined to its own namespace so that the file can be imported
together with the other files of the chapter without name clashes. -/
namespace FoldOperatorOfBasis

/-! ## The induced map on `F(d)/F(d)²` -/

section QuotMap

variable {p : ℕ}

/-- The homomorphism `P_n → Q_n` between the `n`-th terms of the descending `p`-central series
induced by a surjective homomorphism `ψ : P →* Q`. -/
noncomputable def pCentralSubtypeMap (p : ℕ) {P Q : Type*} [Group P] [Group Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ) (n : ℕ) :
    ↥(Work.Shrinking.pCentralSeries p P n) →* ↥(Work.Shrinking.pCentralSeries p Q n) where
  toFun x := ⟨ψ (x : P), by
    rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ n]
    exact Subgroup.mem_map_of_mem ψ x.2⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' x y := Subtype.ext (map_mul ψ (x : P) (y : P))

/-- `pCentralMapMul` sends the class of `x` to the class of `ψ x`. -/
theorem pCentralMapMul_mk (p : ℕ) {P Q : Type*} [Group P] [Group Q]
    (ψ : P →* Q) (hψ : Function.Surjective ψ) (n : ℕ)
    (x : ↥(Work.Shrinking.pCentralSeries p P n)) :
    pCentralMapMul p ψ hψ n (QuotientGroup.mk' _ x)
      = QuotientGroup.mk' _ (pCentralSubtypeMap p ψ hψ n x) := by
  rw [pCentralMapMul, QuotientGroup.map_mk']
  rfl

/-- The induced map `F(m)/F(m)² → F(n)/F(n)²` of a surjective operator homomorphism, computed
on the class of a free generator. -/
theorem quotMapLin_genMk (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) (x : Fin m × G) :
    quotMapLin p G ψ hψ (genMk p G m x)
      = modsquare.squareQuotientClass p G n (ψ (FreeGroup.of x)) := by
  change Additive.ofMul (pCentralMapMul p ψ hψ 0
    (QuotientGroup.mk' _ (⟨FreeGroup.of x, Subgroup.mem_top _⟩ :
      ↥(Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) 0))))
    = modsquare.squareQuotientClass p G n (ψ (FreeGroup.of x))
  rw [pCentralMapMul_mk, modsquare.squareQuotientClass]
  try rfl

end QuotMap

/-! ## The class of a power in `F(d)/F(d)²` -/

section Pow

/-- The class of a power of a word is the corresponding multiple of the class. -/
theorem squareQuotientClass_pow (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (w : Work.Shrinking.freeOperatorGroup G d) (c : ℕ) :
    modsquare.squareQuotientClass p G d (w ^ c)
      = c • modsquare.squareQuotientClass p G d w := by
  induction c with
  | zero => rw [pow_zero, modsquare.squareQuotientClass_one, zero_smul]
  | succ k ih => rw [pow_succ, modsquare.squareQuotientClass_mul, ih, succ_nsmul]

/-- The class of a power of a free generator, as a scalar multiple of `genMk`. -/
theorem squareQuotientClass_of_pow (p : ℕ) (G : Type*) [Group G] (d : ℕ) (y : Fin d × G)
    (m : ℕ) :
    modsquare.squareQuotientClass p G d (FreeGroup.of y ^ m)
      = (m : ZMod p) • genMk p G d y := by
  rw [squareQuotientClass_pow, modsquare.squareQuotientClass_of, Nat.cast_smul_eq_nsmul]

end Pow

/-! ## Two linear maps agreeing on the `genMk`-coordinates are equal -/

section Ext

/-- A linear map out of `F(d)/F(d)²` which vanishes on all the classes `genMk p G d y` of the
free generators is zero.  This is the spanning statement for the identification
`F(d)/F(d)² ≅ (Fin d × G → 𝔽_p)`: every element is a linear combination of the `genMk`. -/
theorem linearMap_eq_zero_of_genMk (p : ℕ) (G : Type*) [Group G] [Fintype G] (d : ℕ)
    {N : Type*} [AddCommGroup N] [Module (ZMod p) N]
    (f : squareQuotient p G d →ₗ[ZMod p] N)
    (h : ∀ y : Fin d × G, f (genMk p G d y) = 0) : f = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [← modsquare.funToSquareQuotient_squareQuotientToFun p G d x]
  show f (∑ y, squareQuotientToFun p G d x y • genMk p G d y) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [map_smul, h y, smul_zero]

/-- A linear endomorphism of `Fin r → F(n)/F(n)²` which vanishes on the vectors
`Pi.single k (genMk p G n y)` is zero. -/
theorem linearMap_eq_zero_of_single_genMk (p : ℕ) (G : Type*) [Group G] [Fintype G] (r n : ℕ)
    (D : (Fin r → squareQuotient p G n) →ₗ[ZMod p] squareQuotient p G n)
    (h : ∀ (k : Fin r) (y : Fin n × G), D (Pi.single k (genMk p G n y)) = 0) : D = 0 := by
  have hcomp : ∀ k : Fin r,
      D.comp (LinearMap.single (ZMod p) (fun _ : Fin r => squareQuotient p G n) k) = 0 := by
    intro k
    apply linearMap_eq_zero_of_genMk p G n
    intro y
    rw [LinearMap.comp_apply, LinearMap.single_apply]
    exact h k y
  refine LinearMap.ext fun z => ?_
  rw [show z = ∑ k, Pi.single k (z k) from (Finset.univ_sum_single z).symm, map_sum,
    LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hh : (D.comp (LinearMap.single (ZMod p) (fun _ : Fin r => squareQuotient p G n) k))
      (z k) = 0 := by rw [hcomp k]; rfl
  simpa only [LinearMap.comp_apply, LinearMap.single_apply] using hh

/-- Two linear endomorphisms of `Fin r → F(n)/F(n)²` which agree on the vectors
`Pi.single k (genMk p G n y)` are equal. -/
theorem linearMap_ext_of_single_genMk (p : ℕ) (G : Type*) [Group G] [Fintype G] (r n : ℕ)
    (L L' : (Fin r → squareQuotient p G n) →ₗ[ZMod p] squareQuotient p G n)
    (h : ∀ (k : Fin r) (y : Fin n × G),
      L (Pi.single k (genMk p G n y)) = L' (Pi.single k (genMk p G n y))) : L = L' := by
  rw [← sub_eq_zero]
  apply linearMap_eq_zero_of_single_genMk p G r n
  intro k y
  rw [LinearMap.sub_apply, h k y, sub_self]

end Ext

/-! ## The folding operator homomorphism `ψ` -/

section Psi

/-- The map on generators defining the folding operator homomorphism
`F(r·n) → F(n)`: the generator `x_{(k,j),g}` (with `finProdFinEquiv (k,j)` its `Fin (r·n)`
index) is sent to `x_{(j,g)}^{a_k}`. -/
noncomputable def psiGen (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) :
    Fin (r * n) × G → Work.Shrinking.freeOperatorGroup G n :=
  fun x => FreeGroup.of ((finProdFinEquiv.symm x.1).2, x.2)
    ^ (a (finProdFinEquiv.symm x.1).1).val

/-- The folding operator homomorphism `ψ : F(r·n) →* F(n)`. -/
noncomputable def psi (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) :
    Work.Shrinking.freeOperatorGroup G (r * n) →* Work.Shrinking.freeOperatorGroup G n :=
  FreeGroup.lift (psiGen p G r n a)

/-- The value of `ψ` on a free generator. -/
theorem psi_of (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p)
    (x : Fin (r * n) × G) : psi p G r n a (FreeGroup.of x) = psiGen p G r n a x :=
  FreeGroup.lift_apply_of

/-- The value of `ψ` on the generator indexed by `(finProdFinEquiv (k,j), g)`. -/
theorem psi_of_finProd (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p)
    (k : Fin r) (j : Fin n) (g : G) :
    psi p G r n a (FreeGroup.of (finProdFinEquiv (k, j), g))
      = FreeGroup.of (j, g) ^ (a k).val := by
  rw [psi_of, psiGen, Equiv.symm_apply_apply]

/-- `ψ` is `G`-equivariant. -/
theorem psi_smul (p : ℕ) (G : Type*) [Group G] (r n : ℕ) (a : Fin r → ZMod p) (g : G)
    (y : Work.Shrinking.freeOperatorGroup G (r * n)) :
    psi p G r n a (g • y) = g • psi p G r n a y := by
  have key : ∀ x : Fin (r * n) × G,
      psi p G r n a (g • FreeGroup.of x) = g • psi p G r n a (FreeGroup.of x) := by
    intro x
    rw [Work.Shrinking.smul_freeOperator_of, psi_of, psi_of]
    simp only [psiGen]
    rw [smul_pow', Work.Shrinking.smul_freeOperator_of]
  induction y using FreeGroup.induction_on with
  | one => simp
  | of x => exact key x
  | inv_of x ih =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ih ⊢
      simp only [map_inv, ih]
  | mul x y ihx ihy =>
      simp only [Work.Shrinking.smul_freeOperatorGroup_eq] at ihx ihy ⊢
      simp only [map_mul, ihx, ihy]

/-- `ψ` is surjective: the hypothesis `a k₀ = 1` makes it the identity on the generators
`x_{(k₀,j),g}`, and those generate `F(n)`. -/
theorem psi_surj (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (r n : ℕ) {k₀ : Fin r}
    (a : Fin r → ZMod p) (ha : a k₀ = 1) : Function.Surjective (psi p G r n a) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [psi, ← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
  apply le_antisymm le_top
  rw [← FreeGroup.closure_range_of (Fin n × G)]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, rfl⟩
  refine ⟨((finProdFinEquiv (k₀, x.1) : Fin (r * n)), x.2), ?_⟩
  rw [psiGen, Equiv.symm_apply_apply, ha, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp,
    pow_one]

end Psi

end FoldOperatorOfBasis

open FoldOperatorOfBasis

/-- **The folding operator, from the basis description of `e`.**  If the linear equivalence
`e : (F(n)/F(n)²)^r ≅ F(r·n)/F(r·n)²` sends the standard basis vector
`Pi.single k (genMk p G n (j,g))` to `genMk p G (r·n) (finProdFinEquiv (k,j), g)`, then the
operator homomorphism `ψ : F(r·n) → F(n)`, `x_{(k,j),g} ↦ x_{(j,g)}^{a_k}`, is surjective,
`G`-equivariant and satisfies `ψ̄ ∘ e = φ_a`. -/
theorem exists_foldOperator_of_basis (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (r n : ℕ) {k₀ : Fin r} (a : Fin r → ZMod p) (ha : a k₀ = 1)
    (e : (Fin r → Work.CohomologicalShrinking.squareQuotient p G n) ≃ₗ[ZMod p]
          Work.CohomologicalShrinking.squareQuotient p G (r * n))
    (he : ∀ (k : Fin r) (j : Fin n) (g : G),
        e (Pi.single k (Work.CohomologicalShrinking.genMk p G n (j, g)))
          = Work.CohomologicalShrinking.genMk p G (r * n) (finProdFinEquiv (k, j), g)) :
    ∃ (ψ : Work.Shrinking.freeOperatorGroup G (r * n) →* Work.Shrinking.freeOperatorGroup G n)
      (hψ : Function.Surjective ψ),
      (∀ (g : G) (y : Work.Shrinking.freeOperatorGroup G (r * n)), ψ (g • y) = g • ψ y) ∧
      (Work.CohomologicalShrinking.quotMapLin p G ψ hψ).comp e.toLinearMap
        = Work.Shrinking.foldMap (M := Work.CohomologicalShrinking.squareQuotient p G n) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨psi p G r n a, psi_surj p G r n a ha, psi_smul p G r n a, ?_⟩
  apply linearMap_ext_of_single_genMk p G r n
  intro k y
  obtain ⟨j, g⟩ := y
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, he k j g, quotMapLin_genMk,
    psi_of_finProd, squareQuotientClass_of_pow, ZMod.natCast_zmod_val (a k),
    Work.Shrinking.foldMap_apply_single]

end Work.CohomologicalShrinking.operator
