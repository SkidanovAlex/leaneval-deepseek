import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Multiplicativity of `ideleOfIdeal`

The idèle attached to an ideal `I` is the idèle whose local exponent at a prime `𝔮` is the
multiplicity of `𝔮` in the factorisation of `I`, with the archimedean components equal to `1`
(see `NK.HeckeL.ideleOfIdeal`).  This file shows that this construction is multiplicative in
`I`, i.e. `ideleOfIdeal K (I * J) = ideleOfIdeal K I * ideleOfIdeal K J` for nonzero `I, J`.

The proof is bookkeeping: `ideleOfFun` is multiplicative in its exponent function, and the
`𝔮`-adic exponent of a product of ideals is the sum of the exponents
(`FractionalIdeal.count_mul`).
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open NK.GlobalCFT (Idele IdeleClassGroup)

namespace NK.HeckeL.Basic

-- Bookkeeping lemmas about `IdeleClassGroup.ideleOfFun`.  They are isolated in their own
-- namespace so that they cannot clash with anything else under `NK.HeckeL.Basic`.
namespace IdeleFun

/-- The value of `ideleOfFun` at a finite place: the prescribed power of a local uniformiser. -/
theorem apply_ofFinite {K : Type*} [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) → ℤ) (hf : ∀ᶠ q in Filter.cofinite, f q = 0)
    (q : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup.ideleOfFun K f hf (NK.GlobalCFT.Place.ofFinite q) =
      IdeleClassGroup.unifUnit K q ^ f q := rfl

/-- `ideleOfFun` only depends on the exponent function, not on the proof of the restricted
product condition. -/
theorem congr {K : Type*} [Field K] [NumberField K]
    {f g : HeightOneSpectrum (𝓞 K) → ℤ}
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hg : ∀ᶠ q in Filter.cofinite, g q = 0)
    (h : f = g) :
    IdeleClassGroup.ideleOfFun K f hf = IdeleClassGroup.ideleOfFun K g hg := by
  subst h
  exact Subtype.ext rfl

/-- `ideleOfFun` is multiplicative in the exponent function: the exponents add. -/
theorem mul {K : Type*} [Field K] [NumberField K]
    (f g : HeightOneSpectrum (𝓞 K) → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) (hg : ∀ᶠ q in Filter.cofinite, g q = 0)
    (hfg : ∀ᶠ q in Filter.cofinite, (f + g) q = 0) :
    IdeleClassGroup.ideleOfFun K f hf * IdeleClassGroup.ideleOfFun K g hg =
      IdeleClassGroup.ideleOfFun K (f + g) hfg := by
  ext v
  match v with
  | Sum.inl w =>
      rw [Idele.mul_apply]
      rw [show IdeleClassGroup.ideleOfFun K f hf (Sum.inl w) = 1 from rfl,
        show IdeleClassGroup.ideleOfFun K g hg (Sum.inl w) = 1 from rfl,
        show IdeleClassGroup.ideleOfFun K (f + g) hfg (Sum.inl w) = 1 from rfl]
      simp
  | Sum.inr q =>
      rw [Idele.mul_apply]
      rw [apply_ofFinite, apply_ofFinite, apply_ofFinite]
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Pi.add_apply, zpow_add]

end IdeleFun

theorem ideleOfIdeal_mul {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    NK.HeckeL.ideleOfIdeal K (I * J) =
      NK.HeckeL.ideleOfIdeal K I * NK.HeckeL.ideleOfIdeal K J := by
  have hI' : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  have hJ' : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  -- The `𝔮`-adic exponents of a product are the sums of the exponents.
  have key : (fun q => FractionalIdeal.count K q (((I * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))
      = (fun q => FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K))
        + (fun q => FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K)) := by
    funext q
    rw [Pi.add_apply, FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K q hI' hJ']
  have hsum : ∀ᶠ q in Filter.cofinite,
      ((fun q => FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K))
        + (fun q => FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K))) q = 0 :=
    ((FractionalIdeal.finite_factors (K := K) (I := (I : FractionalIdeal (𝓞 K)⁰ K))).and
      (FractionalIdeal.finite_factors (K := K) (I := (J : FractionalIdeal (𝓞 K)⁰ K)))).mono
      (fun q hq => by simp [Pi.add_apply, hq.1, hq.2])
  rw [NK.HeckeL.ideleOfIdeal, NK.HeckeL.ideleOfIdeal, NK.HeckeL.ideleOfIdeal]
  trans IdeleClassGroup.ideleOfFun K
      ((fun q => FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K))
        + (fun q => FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K))) hsum
  · exact IdeleFun.congr _ _ key
  · exact (IdeleFun.mul _ _ _ _ hsum).symm

end NK.HeckeL.Basic
