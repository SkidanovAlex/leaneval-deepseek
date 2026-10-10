import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.SSGRoute.shafarevich_z_data_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia criterion of the Kummer cochain, in both directions

For a finite place `A` of `Ω` whose residue characteristic is not `2` (`¬ A.valuation (2 : Ω) < 1`)
and `b ∈ Kˣ`, the two halves of the classical criterion are:

* `Work.SSGRoute.kummerCochar_eq_zero_of_isInertia_of_even_valuation` (proved): if the
  `A`-valuation of `b` is the square of the `A`-valuation of an element of `Kˣ` — i.e. `b` is a unit
  times a square at `A`, which for `A ∤ 2` is the classical "`v_A(b)` even" — then the Kummer cochain
  of `b` kills the inertia of `A`;
* `Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq` (proved): conversely, if the
  `A`-valuation of `b` is *not* such a square, then the Kummer cochain of `b` is non-zero somewhere
  in the inertia of `A`.

This module consolidates the two into the criterion in the form the assembly needs:

* `kills_inertia_iff_even_valuation` — the equivalence, at the level `Gal(Ω/↥K)`;
* `exists_val_sq_of_kills_inertia` — its arithmetic form at the level `G_K = K.fixingSubgroup`, i.e.
  the form in which clause (5) of the node (`z` kills the inertia outside `cs(S)` at the places not
  split in `Λ`) yields clause (B) of `Work.SSGRoute.ZDataTwo.ArithCore` (the even valuation of `b`
  at those places);
* `exists_decomp_ne_zero_of_not_localPowClass` — the *trigger* form: if `b` is not a local
  `2`-power at the prime below `A`, then the cochain of `b` is non-zero somewhere in the whole local
  group `decomp k A ⊓ G_K` (not only in its inertia); this is the converse of the local Kummer
  dictionary `Work.SSGRoute.kummerCochar_eq_zero_iff_localPowClass` and is what certifies that the
  trigger of clause (6) of the node fires at the places the construction does not touch.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

/-- **The inertia criterion, in both directions** (at the level `Gal(Ω/↥K)`): for a finite place `A`
with `A ∤ 2`, the Kummer cochain of `b ∈ Kˣ` kills the inertia of `A` if and only if the
`A`-valuation of `b` is the square of the `A`-valuation of some element of `Kˣ`. -/
theorem kills_inertia_iff_even_valuation (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1) :
    (∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) ↔
      ∃ d : (↥K)ˣ, A.valuation (algebraMap ↥K Ω (b : ↥K)) =
        A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2 := by
  refine ⟨fun h0 => ?_, fun hd => ?_⟩
  · by_contra hodd
    obtain ⟨σ, hσK, hσI, hne⟩ :=
      kummerCochar_ne_zero_of_val_not_sq k Ω K ζ hζ hζK b A hA h2 hodd
    exact hne (h0 σ hσK hσI)
  · obtain ⟨d, hd⟩ := hd
    intro σ hσK hσI
    refine Work.SSGRoute.kummerCochar_eq_zero_of_isInertia_of_even_valuation k Ω K ζ hζ hζK
      A hA h2 b d hd σ hσK ?_
    exact (Work.SSGRoute.isInertia_baseChange (k := k) (Ω := Ω) K A σ hσK).mpr hσI

/-- **The arithmetic form of the criterion** (at the level `G_K`): if the Kummer cochain of `b`
kills the inertia of the finite place `A` (with `A ∤ 2`), then the `A`-valuation of `b` is the square
of the `A`-valuation of an element of `Kˣ`.  This is the form in which clause (5) of the node yields
clause (B) of `ArithCore`. -/
theorem exists_val_sq_of_kills_inertia (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (h0 : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) :
    ∃ d : (↥K)ˣ, A.valuation (algebraMap ↥K Ω (b : ↥K)) =
      A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2 :=
  (kills_inertia_iff_even_valuation k Ω K ζ hζ hζK b A hA h2).mp h0

/-- **The trigger form of the local Kummer dictionary**: if `b` is not a local `2`-power at the
prime `𝔭` of `K` below the finite place `A`, then the Kummer cochain of `b` is non-zero somewhere in
the local group `decomp k A ⊓ K.fixingSubgroup` of `A`. -/
theorem exists_decomp_ne_zero_of_not_localPowClass (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h : ¬ NK.UchidaKummer.localPowClass ↥K 2 𝔭 b = 1) :
    ∃ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine h ((Work.SSGRoute.kummerCochar_eq_zero_iff_localPowClass (K := K) ⟨ζ, hζK⟩
    (isPrimitiveRoot_subtype_of_mem hζK hζ) b A hA 𝔭 h𝔭).mp ?_)
  intro σ hσ
  exact hcon σ hσ

end Work.SSGRoute.ZDataTwo
