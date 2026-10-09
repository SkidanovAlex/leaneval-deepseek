import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.HassePrinciple.localUnits_h2_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level norm-valuation formula (ported to `Work.SSGRoute.SSG`)

This is a port of `Submission/Work/SSGRoute/E7cOmega/levelNorm_valuation.lean` (which does not
compile: line 63 has the arguments of `Finset.sum_apply` in the wrong order and the closing
computation at line 93 leaves a `∏_const` goal), with both errors fixed and the proof otherwise
verbatim.  Statement unchanged.

For a finite place `q'` of a number field `L` that is Galois over `k`, and `b ∈ L_{q'}ˣ`, the
valuation of the group-theoretic norm `∏_{σ ∈ Γ_{q'}} σ·b` (where `Γ_{q'} =
MulAction.stabilizer (L ≃ₐ[k] L) q'` is the decomposition group, and `Rep.norm` is the sum
`∑_σ ρ(σ)` of the action) is the `|Γ_{q'}|`-th power of `v b`:

`v (N b) = (v b) ^ |Γ_{q'}|`.

The proof is the one recorded in the docstring of
`Work.SSGRoute.E7cOmega.isUnramifiedExt_extLoc_of_kills_unramified`: rewrite `Rep.norm` as the sum
`∑_σ ρ(σ)`, evaluate the action via `localUnitsEquiv`, convert the sum of `Additive.ofMul` into the
product of units, and use the Galois invariance of the local valuation
`NK.HassePrinciple.localUnitsEquiv_valued` on every factor.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory Representation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute.SSG

theorem levelNorm_valuation (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'))]
    (b : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
    Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
        (Γ₀ := WithZero (Multiplicative ℤ))
        ((Additive.toMul
          ((Rep.norm (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q'))).hom
            (Additive.ofMul b)) : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
          NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')) =
      (Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
        (Γ₀ := WithZero (Multiplicative ℤ))
        ((b : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
          NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
        ^ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q')) := by
  -- ## Step 1: `Rep.norm` evaluated at `ofMul b` is the sum of the conjugates.
  have hsum :
      (Rep.norm (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofFinite q'))).hom (Additive.ofMul b)
        = ∑ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
            Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
              (NK.GlobalCFT.Place.ofFinite q') σ b) := by
    rw [Rep.norm_apply (A := NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofFinite q')) (x := Additive.ofMul b), Representation.norm]
    have hstep : (∑ g : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
          (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q')).ρ g)
            (Additive.ofMul b)
        = ∑ g : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
            (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q')).ρ g
              (Additive.ofMul b) :=
      map_sum (LinearMap.applyₗ (Additive.ofMul b))
        (fun g : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') =>
          (NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q')).ρ g)
        Finset.univ
    rw [hstep]
    exact Finset.sum_congr rfl (fun σ _ => rfl)
  -- ## Step 2: convert the sum of `ofMul`s into the product of the conjugates.
  have hprod :
      (Additive.toMul ((Rep.norm (NK.HassePrinciple.localUnitsRep k L
          (NK.GlobalCFT.Place.ofFinite q'))).hom (Additive.ofMul b))
        : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ)
        = ∏ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
            NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
              (NK.GlobalCFT.Place.ofFinite q') σ b := by
    rw [hsum, toMul_sum]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    exact toMul_ofMul _
  -- ## Step 3: the valuation of the product, factor by factor.
  have hval :
      Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
          (Γ₀ := WithZero (Multiplicative ℤ))
          (((∏ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
              NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
                (NK.GlobalCFT.Place.ofFinite q') σ b)
            : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ)
            : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')) =
        (Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
          (Γ₀ := WithZero (Multiplicative ℤ))
          ((b : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
            NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
          ^ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q')) := by
    rw [Units.coe_prod, map_prod]
    rw [show (∏ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
              Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
                (Γ₀ := WithZero (Multiplicative ℤ))
                ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
                  (NK.GlobalCFT.Place.ofFinite q') σ b
                  : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
                  NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
          = ∏ σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q'),
              Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
                (Γ₀ := WithZero (Multiplicative ℤ))
                ((b : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
                  NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')) from
        Finset.prod_congr rfl (fun σ _ =>
          NK.HassePrinciple.localUnitsEquiv_valued (K := k) q' σ b)]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  -- ## Assembly.
  rw [← hval]
  exact congrArg
    (fun u : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ =>
      Valued.v (R := NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))
        (Γ₀ := WithZero (Multiplicative ℤ))
        (u : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
    hprod

end Work.SSGRoute.SSG
