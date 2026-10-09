import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.TotallyPositive
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness
import Submission.Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The crossed two-place reciprocity at `p = 2`: the hypothesis set of the target is inconsistent

**Finding (machine-checked below).**  The target `Work.SSGRoute.H9.crossed_two_place_p2` is
*vacuous*: its hypotheses `hoddB` (odd `𝔭`-adic valuation of `b`), `h𝔭B` (`B` lies over `𝔭`),
`hLb` (`L` contains the Kummer level `k(√b)`) and `hunrL` (`L/k` is unramified at `B`) cannot hold
simultaneously, and the same is true of the `c`-sided quadruple (`hoddBc`, `h𝔮Bc`, `hLc`,
`hunrL.2`).

The mechanism is `isRamifiedIn_of_odd_count` below, a genuine (and reusable) arithmetic statement
resting on the two proved companions `Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count` (the
converse-shaped companion of `Work.SSGRoute.ZDataTwo.odd_log_of_not_sq_val`) and
`Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness` (the inertia criterion with
its superfluous tameness hypothesis deleted — needed at `p = 2`):

> if `b ∈ Kˣ` has odd `𝔭`-adic valuation and `L ⊇ k(√b)`, then `L/k` is **ramified** at every place
> `B` of `Ω` over `𝔭`, i.e. `SSGRoute.IsRamifiedIn k L B` holds.

The reason is that odd valuation forces the quadratic Kummer extension `K(√b)/K` to be ramified at
`𝔭` (with even ramification index, `Work.SSGRoute.ZDataTwo.two_dvd_ramificationIdx_of_odd_valuation`
— no tameness needed at `p = 2`), so the inertia of `B` contains an element that moves `√b` (and
hence does not fix `L ⊇ k(√b)`); this produces an element of `IsRamifiedIn k L B` directly.

The two halves of the finding are named `crossed_two_place_p2_hypotheses_unsatisfiable` (the
`b`-side: `hoddB`, `h𝔭B`, `hLb` and `hunrL.1` are inconsistent) and
`crossed_two_place_p2_hypotheses_unsatisfiable_c` (the `c`-side, with `hoddBc`, `h𝔮Bc`, `hLc` and
`hunrL.2`), so the defect is visible from the environment of this module.

Consequently the target's function value `nodeKummerCochar K ζ hζK hζ b σ` is never restricted by
the intended "`σ` is a Frobenius at the unramified level `L`" datum in a satisfiable way: any datum
satisfying `hLb` and `hunrL.1` already satisfies `hoddB`'s negation, and symmetrically on the `c`
side.  The target is therefore proved below by contradiction (`False.elim`), and the two-place
reciprocity has to be *re-stated* (e.g. with the Frobenius datum pinned modulo the Kummer level
kernel — see the restatement recommendation in `NOTE_two_place_reciprocity_odd_vacuous.md`, which
records the same defect for the odd-`p` twin — rather than through an `L` that contains the Kummer
levels and is unramified at the marked places, an impossible combination).
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute

/-- **The Kummer cochain of `b` vanishes at the automorphisms fixing a level containing `k(√b)`.**

If `σ ∈ G_K` lies in the fixing subgroup of a level `L ⊇ k(√b)` (where `√b = kummerSqrtVal b` is the
chosen square root of `b` in `Ω`), then the Kummer cochain of `b` vanishes at `σ`.  This is the
sense in which the Kummer level `k(√b)` pins the cochain: together with `IsFrobAtPrime` it makes the
value of `χ_b` at a Frobenius element of a level unramified at the place well defined. -/
lemma nodeKummerCochar_eq_zero_of_mem_fixingSubgroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ)
    (L : IntermediateField k Ω)
    (hLb : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b} ≤ L)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) (hσL : σ ∈ L.fixingSubgroup) :
    nodeKummerCochar K ζ hζK hζ b σ = 0 := by
  rw [Work.SSGRoute.nodeKummerCochar, Work.SSGRoute.kummerCochar_apply K ⟨ζ, hζK⟩ _ b hσ,
    Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt]
  have hroot : σ (Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b) =
      Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b :=
    (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσL _
      (hLb (IntermediateField.mem_adjoin_simple_self k _))
  have hcoe : ⇑(((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω ≃ₐ[↥K] Ω)) = ⇑σ := by
    ext x; rfl
  rw [hcoe]
  simpa only [Work.SSGRoute.kummerSqrt, Units.val_mk0] using hroot

/-- **Odd `𝔭`-adic valuation forces ramification of the Kummer level at the places over `𝔭`.**

Let `b ∈ Kˣ` have odd `𝔭`-adic valuation and let `B` be a finite place of `Ω` whose restriction to
`K` is the valuation ring at `𝔭`.  Then for every level `L` containing the Kummer level `k(√b)`, the
extension `L/k` is ramified at `B`: `SSGRoute.IsRamifiedIn k L B`.

Proof: the odd valuation makes the `A.valuation` of `b` a non-square
(`Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count`, the converse-shaped companion of
`Work.SSGRoute.ZDataTwo.odd_log_of_not_sq_val`), so by the inertia criterion
(`Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness`, whose tameness hypothesis is
superfluous) some inertia element `σ₀ ∈ G_K` of `B` sees `b` as a non-square, i.e. moves the chosen
square root `√b`.  Since `L ⊇ k(√b)`, such a `σ₀` is not in `L.fixingSubgroup`; it is therefore a
witness for `IsRamifiedIn k L B`. -/
theorem isRamifiedIn_of_odd_count (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭B : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hodd : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))))
    (L : IntermediateField k Ω)
    (hLb : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b} ≤ L) :
    SSGRoute.IsRamifiedIn k L B := by
  -- the odd `𝔭`-adic valuation of `b` in the value-group form used by the inertia criterion
  have hodd' : ¬ ∃ d : (↥K)ˣ,
      B.valuation (algebraMap ↥K Ω (b : ↥K)) =
        (B.valuation (algebraMap ↥K Ω (d : ↥K))) ^ 2 :=
    Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count ↥K Ω B
      (NK.Reconstruct.comap_level_ne_top hB K) 𝔭 h𝔭B b hodd
  -- an inertia element of `B` at which the Kummer cochain of `b` does not vanish
  obtain ⟨σ₀, hσ₀K, hσ₀I, hσ₀ne⟩ :
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup ∧ IsInertia k B σ ∧
        nodeKummerCochar K ζ hζK hζ b σ ≠ 0 :=
    Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness k Ω K ζ hζ hζK b B hB hodd'
  -- it is not in the fixing subgroup of `L ⊇ k(√b)`: that would kill the Kummer cochain
  exact ⟨σ₀, hσ₀I, fun hfix =>
    hσ₀ne (nodeKummerCochar_eq_zero_of_mem_fixingSubgroup k Ω K ζ hζ hζK b L hLb hσ₀K hfix)⟩

/-- **The hypothesis set of `crossed_two_place_p2` is inconsistent.**

The four hypotheses `hodd` (odd `𝔭`-adic valuation of `b`), `h𝔭B` (`B` lies over `𝔭`), `hLb` (`L`
contains the Kummer level `k(√b)`) and `hunr` (`L/k` is unramified at `B`) cannot hold at once, by
`isRamifiedIn_of_odd_count`.  The same statement with `b` replaced by `c`, `𝔭` by `𝔮` and `B` by
`Bc` refutes the `c`-sided quadruple of the target.  This is the precise defect of the target
statement: both marked places are the places at which the corresponding Kummer extension
*ramifies* (odd valuation!), so no level `L` containing the Kummer levels can be unramified
there. -/
theorem crossed_two_place_p2_hypotheses_unsatisfiable (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭B : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hoddB : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))))
    (L : IntermediateField k Ω)
    (hLb : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b} ≤ L)
    (hunr : ¬ SSGRoute.IsRamifiedIn k L B) : False :=
  hunr (isRamifiedIn_of_odd_count k Ω K ζ hζ hζK b B hB 𝔭 h𝔭B hoddB L hLb)

/-- **The `c`-sided half of the defect**: the hypotheses `hoddBc` (odd `𝔮`-adic valuation of `c`),
`h𝔮Bc` (`Bc` lies over `𝔮`), `hLc` (`L` contains the Kummer level `k(√c)`) and `hunr` (`L/k` is
unramified at `Bc`) cannot hold at once.  This is
`crossed_two_place_p2_hypotheses_unsatisfiable` with `(b, B, 𝔭)` replaced by `(c, Bc, 𝔮)`. -/
theorem crossed_two_place_p2_hypotheses_unsatisfiable_c (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (c : (↥K)ˣ) (Bc : ValuationSubring Ω) (hBc : SSGRoute.IsFinPlace k Bc)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮Bc : Bc.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
    (hoddBc : Odd (FractionalIdeal.count ↥K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (c : ↥K))))
    (L : IntermediateField k Ω)
    (hLc : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) c} ≤ L)
    (hunr : ¬ SSGRoute.IsRamifiedIn k L Bc) : False :=
  hunr (isRamifiedIn_of_odd_count k Ω K ζ hζ hζK c Bc hBc 𝔮 h𝔮Bc hoddBc L hLc)

/-- **The crossed two-place reciprocity at `p = 2`** (the `p = 2` analogue of the odd-`p`
`Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity`, which is proved there only for `p ≠ 2`).

Let `b, c ∈ Kˣ`. Suppose `b` has odd `𝔭`-adic valuation and is a unit at `𝔮`, `c` has odd `𝔮`-adic
valuation and is a unit at `𝔭` (`𝔭 ≠ 𝔮` primes of `K`, with places `B`, `Bc` of `Ω` above them), and
suppose the local pairings of `b` and `c` are *trivial* at every other place — here expressed as:
at every finite place `B'` outside the `k`-classes of `B` and `Bc`, one of the two Kummer cochains
vanishes on the whole local group of `B'` (the local-triviality condition), and at every real place
of `K` at least one of `b, c` is not negative.

If `σ` is an element of the local group of `Bc` lifting a Frobenius at the `k`-prime `𝔮k` below
`Bc`, and `τ` is an element of the local group of `B` lifting a Frobenius at the `k`-prime `𝔭k`
below `B`, at a common finite Galois level `L` containing both Kummer levels `k(√b)`, `k(√c)`
(so that `σ`, resp. `τ` are pinned modulo the kernel of the two cochains), then

  `χ_b(σ) = χ_c(τ)`.

This is the global product formula for the Hilbert symbol at `p = 2`
(`Work.HilbertSymbolGeneral.hilbertReciprocityTwo`) together with the two local computations:
`(b,c)_{Bc} = χ_b(Frob_{Bc})` (because `c` has odd valuation at `Bc`, the relevant extension is
ramified there) and `(b,c)_B = χ_c(Frob_B)`, so that the product formula collapses to the two
marked places.  The symmetry `(b,c) = (c,b)` of the Hilbert symbol — a `p = 2` phenomenon — is what
makes the collapse possible here. -/
theorem crossed_two_place_p2 (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (b c : (↥K)ˣ)
    (B Bc : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) (hBc : SSGRoute.IsFinPlace k Bc)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭B : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮Bc : Bc.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
    (hne : 𝔭 ≠ 𝔮)
    (hoddB : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))))
    (hoddBc : Odd (FractionalIdeal.count ↥K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (c : ↥K))))
    (hunrBc_b : FractionalIdeal.count ↥K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (b : ↥K)) = 0)
    (hunrB_c : FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (c : ↥K)) = 0)
    (hvanish : ∀ (B' : ValuationSubring Ω), SSGRoute.IsFinPlace k B' →
      (∀ ρ : Ω ≃ₐ[k] Ω, ρ • B ≠ B') → (∀ ρ : Ω ≃ₐ[k] Ω, ρ • Bc ≠ B') →
      (∀ u ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ b u = 0) ∨
      (∀ u ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ c u = 0))
    (hvanish_inf : (∀ w : NumberField.InfinitePlace ↥K, w.IsReal →
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w b) ∨
      (∀ w : NumberField.InfinitePlace ↥K, w.IsReal →
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w c))
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L B ∧ ¬ SSGRoute.IsRamifiedIn k L Bc)
    (hLb : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b} ≤ L)
    (hLc : IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) c} ≤ L)
    (𝔭k : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭kB : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭k)
    (𝔮k : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔮kBc : Bc.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔮k)
    (σ τ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ SSGRoute.decomp k Bc ⊓ K.fixingSubgroup)
    (hσf : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔮k (SSGRoute.res k L σ))
    (hτ : τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup)
    (hτf : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭k (SSGRoute.res k L τ)) :
    nodeKummerCochar K ζ hζK hζ b σ = nodeKummerCochar K ζ hζK hζ c τ := by
  -- the hypotheses `hoddB`, `h𝔭B`, `hLb` and `hunrL.1` are inconsistent: `L ⊇ k(√b)` is ramified
  -- at `B` as soon as `b` has odd `𝔭`-adic valuation, so the statement is vacuous
  exact (hunrL.1 (isRamifiedIn_of_odd_count k Ω K ζ hζ hζK b B hB 𝔭 h𝔭B hoddB L hLb)).elim

end Work.SSGRoute.H9
