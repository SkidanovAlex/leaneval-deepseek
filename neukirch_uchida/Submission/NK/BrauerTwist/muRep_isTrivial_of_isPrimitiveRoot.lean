import Mathlib
import Submission.NK.BrauerTwist.Basic

namespace NK.BrauerTwist

universe u

/-- If `K` contains a primitive `p`-th root of unity `ζ`, then *every* `K`-algebra automorphism of
`K'` fixes every `p`-th root of unity of `K'`: such a root is a power of the image of `ζ`
(`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), and the image of `ζ` is fixed because `ζ ∈ K`.

This is the pointwise form of `muLevel_eq_top_of_isPrimitiveRoot`, with the quantifier over `σ`
ranging over the *whole* Galois group and not only over the fixing subgroup of a level. -/
private lemma smul_rootsOfUnity_eq_self {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (σ : Gal(K'/K)) (x : rootsOfUnity p K') : σ • x = x := by
  have hζ' : IsPrimitiveRoot (algebraMap K K' ζ) p :=
    hζ.map_of_injective (algebraMap K K').injective
  have hxpow : (x : (K')ˣ) ^ p = 1 := (mem_rootsOfUnity p (x : (K')ˣ)).mp x.2
  have hzpow : (((x : (K')ˣ) : K')) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxpow, Units.val_one]
  obtain ⟨i, -, hpow⟩ := hζ'.eq_pow_of_pow_eq_one hzpow
  apply Subtype.ext
  apply Units.ext
  show (((σ • x : rootsOfUnity p K') : (K')ˣ) : K') = ((x : (K')ˣ) : K')
  rw [show (((σ • x : rootsOfUnity p K') : (K')ˣ) : K')
      = (σ : Gal(K'/K)) • (((x : (K')ˣ) : K')) from rfl]
  rw [← hpow]
  change (↑σ : K' ≃ₐ[K] K') ((algebraMap K K') ζ ^ i) = (algebraMap K K') ζ ^ i
  rw [map_pow, AlgEquiv.commutes]

/-- **The cyclotomic twist is trivial when `K ∋ μ_p`.**

If `K` contains a primitive `p`-th root of unity, then `Gal(K'/K)` acts trivially on the `p`-th
roots of unity of `K'` (`smul_rootsOfUnity_eq_self`), hence also on the level module `μ_p(L)` and
therefore on the quotient group `Gal(K'/K) ⧸ Gal(K'/L) = Gal(L/K)` through which the level
representation `muRep p L` factors: the cyclotomic character `Gal(L/K) → (Z/p)ˣ` is trivial.

Equivalently: in Kummer theory the twist by `μ_p` is invisible whenever the ground field already
contains `μ_p`, so `H^n(Gal(L/K), μ_p(L)) = H^n(Gal(L/K), Z/p)` for such `K`. -/
theorem muRep_isTrivial_of_isPrimitiveRoot {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {p : ℕ} [NeZero p] (L : FiniteGaloisIntermediateField K K')
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    (NK.BrauerTwist.muRep (K := K) (K' := K') p L).IsTrivial := by
  obtain ⟨ζ, hζ⟩ := hζ
  -- The action of the whole Galois group on `μ_p(L)` is trivial.
  have hfix : ∀ (σ : Gal(K'/K)) (y : ↥(muLevel p L)), σ • y = y := by
    intro σ y
    apply Subtype.ext
    exact smul_rootsOfUnity_eq_self hζ σ (y : rootsOfUnity p K')
  -- Hence so is the action of the quotient `Gal(K'/K) ⧸ Gal(K'/L)`, which is computed on lifts.
  have hquot : ∀ (g : Gal(K'/K) ⧸ L.fixingSubgroup) (y : ↥(muLevel p L)), g • y = y := by
    intro g y
    induction g using QuotientGroup.induction_on with
    | H g₀ =>
      rw [show (QuotientGroup.mk g₀) • y = g₀ • y from rfl]
      exact hfix g₀ y
  -- `muRep p L` is the representation on `Additive ↥(μ_p(L))` attached to that action.
  have hrep : Representation.IsTrivial
      (Representation.ofDistribMulAction CoeffInt (Gal(K'/K) ⧸ L.fixingSubgroup)
        (Additive ↥(muLevel p L))) := by
    refine ⟨fun g => LinearMap.ext fun (x : Additive ↥(muLevel p L)) => ?_⟩
    rw [Representation.ofDistribMulAction_apply_apply]
    show g • x = x
    apply Additive.toMul.injective
    show g • Additive.toMul x = Additive.toMul x
    exact hquot g (Additive.toMul x)
  exact hrep

end NK.BrauerTwist
