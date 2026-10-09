import Mathlib
import Submission.NK.BrauerTwist.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.BrauerTwist

universe u

/-- `ζ ↦ algebraMap K K' ζ` preserves primitivity of roots of unity. -/
private lemma isPrimitiveRoot_algebraMap {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {p : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (algebraMap K K' ζ) p :=
  hζ.map_of_injective (algebraMap K K').injective

/-- The `p`-th roots of unity of `K'` are fixed by every `K`-algebra automorphism sending the
primitive root `ζ` to itself; here that automorphism is a `K`-algebra map and `ζ ∈ K`, so the
fixed points of any subgroup of `Gal(K'/K)` contain all of `μ_p(K')` as soon as `K ∋ μ_p`. -/
private lemma smul_eq_self_of_isPrimitiveRoot {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {L : FiniteGaloisIntermediateField K K'}
    (σ : ↥L.fixingSubgroup) (x : rootsOfUnity p K') : σ • x = x := by
  have hζ' := isPrimitiveRoot_algebraMap (K' := K') hζ
  have hxpow : (x : (K')ˣ) ^ p = 1 := (mem_rootsOfUnity p (x : (K')ˣ)).mp x.2
  have hzpow : (((x : (K')ˣ) : K')) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxpow, Units.val_one]
  obtain ⟨i, -, hpow⟩ := hζ'.eq_pow_of_pow_eq_one hzpow
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.smul_def]
  show ((((σ : Gal(K'/K)) • x : rootsOfUnity p K') : (K')ˣ) : K') = ((x : (K')ˣ) : K')
  rw [show ((((σ : Gal(K'/K)) • x : rootsOfUnity p K') : (K')ˣ) : K')
      = (σ : Gal(K'/K)) • (((x : (K')ˣ) : K')) from rfl]
  rw [← hpow]
  change (↑σ : K' ≃ₐ[K] K') ((algebraMap K K') ζ ^ i) = (algebraMap K K') ζ ^ i
  rw [map_pow, AlgEquiv.commutes]

/-- **The level module at a level `L` containing the `p`-th roots of unity is everything.**

If `K` contains a primitive `p`-th root of unity (so `K ∋ μ_p` and hence `L ∋ μ_p` for the
intermediate field `L`), then every `p`-th root of unity in `K'` is a power of the image of that
primitive root, hence lies in `K` — in particular it is fixed by the whole of `Gal(K'/L)`. -/
theorem muLevel_eq_top_of_isPrimitiveRoot {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {p : ℕ} [NeZero p] (L : FiniteGaloisIntermediateField K K')
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    NK.BrauerTwist.muLevel (K := K) (K' := K') p L = ⊤ := by
  obtain ⟨ζ, hζ⟩ := hζ
  rw [Subgroup.eq_top_iff']
  intro x
  rw [mem_muLevel]
  intro σ
  exact smul_eq_self_of_isPrimitiveRoot hζ σ x

end NK.BrauerTwist
