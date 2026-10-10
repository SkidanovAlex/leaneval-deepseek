import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# NodeS37: a Kummer class killing the inertia at a place has even order there

For a finite Galois level `K | k` of number fields, a unit `b ∈ Kˣ`, a finite place `B` of `k`
(with `𝔭` the prime of `K` below it) and a primitive `2`-nd root of unity `ζ ∈ K`: if the Kummer
cochain `χ_b` of `b` (in its `ZMod 2`-valued node form `ZSplit.nodeKummerCocharZMod`) vanishes on
the whole inertia subgroup of `B` inside `G_K`, then `b` has **even** `𝔭`-adic order:

  `Even (count_𝔭 (b))`.

Equivalently: a class of *odd* order at `𝔭` is ramified at `B`, so some inertia element sees it.

## Proof

Contrapose.  `¬ Even (count_𝔭 b)` is `Odd (count_𝔭 b)`, so `b` is not a local square at `𝔭`; the
arithmetic lemma `ZDataTwo.not_exists_sq_val_of_odd_count` upgrades this to the statement that the
`B`-valuation of `b` is not the square of the `B`-valuation of any element of `Kˣ`.  The Kummer
dichotomy `ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness` (the `p = 2` arithmetic core of
clause (D) of the node, valid also in the wild case `B | 2`) then produces an inertia element
`σ ∈ K.fixingSubgroup` with `Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ ≠ 0`.  The two `2`-adic
node cochains agree on `K.fixingSubgroup` (they are the Kummer index of `b` computed at two
different chosen square roots, `kummerIdx_congr`), which contradicts the hypothesis `hkill`.
-/

namespace Work.SSGRoute.NodeS37

open scoped Classical

/-- At `p = 2` the `ZMod 2`-valued node cochain `ZSplit.nodeKummerCocharZMod` agrees, on
`K.fixingSubgroup`, with `Work.SSGRoute.nodeKummerCochar`: both are the Kummer index of `b`
evaluated at a chosen square root of `b`, and the Kummer index is independent of that choice
(`Work.SSGRoute.kummerIdx_congr`). -/
theorem nodeKummerCocharZMod_two_eq_nodeKummerCochar {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} {ζ : Ω} {hζK : ζ ∈ K} {hζ : IsPrimitiveRoot ζ 2} {b : (↥K)ˣ}
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ =
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ := by
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hσ,
    Work.SSGRoute.nodeKummerCochar, Work.SSGRoute.kummerCochar_apply K _ _ b hσ,
    Work.SSGRoute.kummerChar_apply, Work.SSGRoute.kummerCharZMod_apply]
  exact (Work.SSGRoute.kummerIdx_congr 2 _ b (Work.SSGRoute.kummerSqrt_pow b)
    (Work.SSGRoute.kummerSqrtUnitZMod_pow 2 b) _).symm

theorem evenCountOfKillsInertia {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0) :
    Even (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
  by_contra hne
  -- an odd order at `𝔭` means `b` is not a local square there
  have hodd : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (b : ↥K))) := Int.not_even_iff_odd.mp hne
  -- `B` is a finite place over the number field `↥K` (its pullback is not the whole ring)
  have hA : B.comap (algebraMap ↥K Ω) ≠ ⊤ := NK.Reconstruct.comap_level_ne_top hB K
  -- consequently the `B`-valuation of `b` is not a square in `Kˣ`
  have hnsq := Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count ↥K Ω B hA 𝔭 h𝔭 b hodd
  -- so some inertia element sees `b` as a non-square, i.e. has non-vanishing Kummer cochain
  obtain ⟨σ, hσmem, hσI, hσne⟩ :=
    Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness k Ω K ζ hζ hζK b B hB hnsq
  -- in the `ZMod 2` node form this contradicts `hkill`
  exact hσne (by
    rw [← nodeKummerCocharZMod_two_eq_nodeKummerCochar hσmem]
    exact hkill σ hσmem hσI)

end Work.SSGRoute.NodeS37
