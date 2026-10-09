/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `G`-equivariance of the identification `F(d)/F(d)² ≅ 𝔽_p[G]^d`

This file proves that the canonical `𝔽_p`-linear isomorphism
`squareQuotientToFun : F(d)/F(d)^2 →ₗ[ZMod p] (Fin d × G → ZMod p)` of
`Submission.Work.CohomologicalShrinking.ModSquare` is `G`-equivariant, where the action on
the quotient is the one descended from the free `G`-operator structure of `F(d)` and the
action on `Fin d × G → ZMod p` is the left regular representation
`(h • f) (i,g) = f (i, h⁻¹ * g)`.

The proof is a direct computation:

* On the level of the free group `F(d) = FreeGroup (Fin d × G)`, the homomorphism
  `freeToFun` is `G`-equivariant; both sides are monoid homomorphisms out of a free group,
  and they agree on the free generators because `g • Pi.single x 1 = Pi.single (x.1, g * x.2) 1`.
* Passing to the quotient `F(d)/F(d)^2` is legitimate because the `G`-action on the quotient
  sends the class of `x` to the class of `subAut g x`, whose underlying element is `g • x`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.ModSquare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking.modsquare

open Work.Shrinking

universe u

/-! ## The action on the coordinate functions -/

/-- The left regular action on `Fin d × G → 𝔽_p` sends the coordinate function at `x` to the
coordinate function at `(x.1, g * x.2)`. -/
theorem smul_pi_single (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G) (x : Fin d × G) :
    (g • Pi.single x (1 : ZMod p) : Fin d × G → ZMod p) = Pi.single (x.1, g * x.2) 1 := by
  funext y
  rw [smul_prodFun_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : y = (x.1, g * x.2)
  · subst h; simp
  · have h' : ¬ ((y.1, g⁻¹ * y.2) = x) := by
      intro hc
      apply h
      rw [Prod.ext_iff]
      exact ⟨by simpa using congrArg Prod.fst hc,
        inv_mul_eq_iff_eq_mul.mp (by simpa using congrArg Prod.snd hc)⟩
    simp [h, h']

/-! ## Equivariance of `freeToFun` on the free `G`-operator group -/

/-- The homomorphism `freeToFun : F(d) →* Multiplicative (Fin d × G → 𝔽_p)` is
`G`-equivariant: the two sides are monoid homomorphisms out of the free group `F(d)` which
agree on the free generators. -/
theorem freeToFun_toAdd_smul (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (y : freeOperatorGroup G d) :
    Multiplicative.toAdd (freeToFun p G d (g • y)) =
      g • Multiplicative.toAdd (freeToFun p G d y) := by
  induction y using FreeGroup.induction_on with
  | one => simp
  | of x =>
      rw [smul_freeOperator_of, freeToFun_of, freeToFun_of, toAdd_ofAdd, toAdd_ofAdd]
      exact (smul_pi_single p G d g x).symm
  | inv_of x ih =>
      simp only [smul_inv', map_inv, toAdd_inv, ih, smul_neg]
  | mul a b iha ihb =>
      simp only [smul_mul', map_mul, toAdd_mul, iha, ihb, smul_add]

/-! ## Equivariance of the descended action on the quotient -/

/-- On the subquotient `P_n/P_{n+1}` of the descending `p`-central series, the class of `x`
acted on by `g` is the class of `subAut g x`. -/
theorem pCentralQuotient_smul_mk {G P : Type*} [Group G] [Group P] [MulDistribMulAction G P]
    (p n : ℕ) (g : G) (x : ↥(pCentralSeries p P n)) :
    g • (QuotientGroup.mk x : pCentralQuotient p P n)
      = QuotientGroup.mk (subAut (pCentralSeries p P n) g
          (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) n) x) := by
  rw [show g • (QuotientGroup.mk x : pCentralQuotient p P n)
        = quotAut (pCentralSeries p P n) (pCentralSeries p P (n + 1)) g
            (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) n)
            (map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) (n + 1))
            (QuotientGroup.mk'
              ((pCentralSeries p P (n+1)).subgroupOf (pCentralSeries p P n)) x)
        from rfl]
  rw [quotAut_mk]
  rfl

/-- The canonical map `quotHom : F(d)/F(d)^2 →* Multiplicative (Fin d × G → 𝔽_p)` is
`G`-equivariant, in the form that involves `Multiplicative.toAdd` on the target. -/
theorem quotHom_toAdd_smul (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (y : pCentralQuotient p (freeOperatorGroup G d) 0) :
    Multiplicative.toAdd (quotHom p G d (g • y)) =
      g • Multiplicative.toAdd (quotHom p G d y) := by
  classical
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective
    ((pCentralSeries p (freeOperatorGroup G d) 1).subgroupOf
      (pCentralSeries p (freeOperatorGroup G d) 0)) y
  have hquot : ∀ z : ↥(pCentralSeries p (freeOperatorGroup G d) 0),
      quotHom p G d (QuotientGroup.mk z) = freeToFun p G d z := by
    intro z
    rfl
  rw [QuotientGroup.mk'_apply, pCentralQuotient_smul_mk p 0 g y0]
  rw [hquot, hquot]
  have hsub : ((subAut (pCentralSeries p (freeOperatorGroup G d) 0) g
        (map_pCentralSeries_eq p
          (MulDistribMulAction.toMulAut G (freeOperatorGroup G d) g) 0) y0 :
        freeOperatorGroup G d)) = g • (y0 : freeOperatorGroup G d) := by
    rw [subAut_coe]; rfl
  rw [hsub, freeToFun_toAdd_smul]

/-! ## The target: `G`-equivariance of `squareQuotientToFun` -/

theorem squareQuotientToFun_smul (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (x : squareQuotient p G d) :
    squareQuotientToFun p G d (g • x) = g • squareQuotientToFun p G d x := by
  show Multiplicative.toAdd (quotHom p G d (Additive.toMul (g • x))) =
    g • Multiplicative.toAdd (quotHom p G d (Additive.toMul x))
  rw [show Additive.toMul (g • x) = g • Additive.toMul x from rfl]
  exact quotHom_toAdd_smul p G d g (Additive.toMul x)

end Work.CohomologicalShrinking.modsquare
