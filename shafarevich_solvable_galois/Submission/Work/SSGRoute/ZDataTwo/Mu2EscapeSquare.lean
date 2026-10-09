import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeStep
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.SignAdjustment
import Submission.Work.SSGRoute.ZDataTwo.RealPlaceInvolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` escape step: what survives, and a counterexample to the datum-free form

`Work.SSGRoute.ZDataTwo.Mu2EscapeCorrection` (the `p = 2` member of the Grünwald-with-escape family,
`Mu2EscapeStep.lean`) is the escape step of Schmidt--Wingberg §4: *given `a ∈ (↥K)ˣ` realising a
prescribed local datum at the finite place set `T`, there are a new finite place `Q`, split in the
level `N`, and `b ∈ (↥K)ˣ` with the same local Kummer data at `T`, killing the involutions of `G_K`,
and unramified outside the `G_K`-classes of `T` and of `Q`.*

This module contains the one fact of the splitting of that statement which is unconditionally true,
`kummerCharZMod_two_mul`, and records the counterexample which shows that the **datum-free** form of
the escape step is false.

## The counterexample (found by an independent prover, re-checked here)

Take `k = ℚ`, `K = ⊥` (so `↥K = ℚ`), `N = ℚ(√5)`, `T = {A₂, A₅}` where `A₂`, `A₅` are places of
`Ω` over `2` and `5`, and `a = 3`.

* `hTfin`, `hTdisj` hold (the two places lie over different primes of `ℚ`, and by
  `ZDataTwo.gesKConj_iff_comap_eq` `gesKConj` is "same prime below").
* `hTcov` holds: every place over `2` is `Gal(Ω/ℚ)`-conjugate to `A₂` (first disjunct), and every
  place over `5` — where `ℚ(√5)/ℚ` is ramified, so the inertia contains a non-trivial element of
  `Gal(ℚ(√5)/ℚ)` — is conjugate to `A₅` (second disjunct); no other place satisfies either disjunct.
* `a = 3` is totally positive: `ℚ` has one real place and `3 > 0`.

The conclusion fails.  Let `q` be the rational prime below the escape place `Q`; since `K = ℚ`,
`¬ gesKConj K A Q` says `q ∉ {2, 5}`, and `IsSplitIn k N Q` says that `q` splits in `ℚ(√5)`, which by
quadratic reciprocity (as `5 ≡ 1 mod 4`) is `q ≡ 1, 4 (mod 5)`.  The two local-data clauses (by the
local Kummer dictionary `local_kummer_dictionary`) say `b/a ∈ (ℚ₂ˣ)²` and `b/a ∈ (ℚ₅ˣ)²`, i.e.
`[b]₂ = [3]₂` and `[b]₅ = [3]₅`, and the unramifiedness clause says `v_ℓ(b)` is even for every
rational prime `ℓ ∉ {2, 5, q}`.  Hence `b = 2^e · 5^f · q^g · t²` with `t ∈ ℚˣ`, `e, f, g ∈ {0,1}`
(the sign is `+` because `b` is positive).  Now

* `[b]₅ = [2]₅^e · [5]₅^f · [q]₅^g = [3]₅` forces `f = 0` (`[5]₅` is the uniformizer class while
  `[3]₅` is a unit class), and
* `[b]₂ = [2]₂^e · [q]₂^g = [3]₂` (with `[5]₂ = 1` for `f = 0`) forces `e = 0` and `q ≡ 3 (mod 8)`:
  `[q]₂` must be `[3]₂` (for `g = 1`) or `[q]₂ = 1 = [3]₂` is impossible; the remaining possibilities
  `q ≡ 5, 7 (mod 8)` are incompatible with the independent generators `[2]₂, [-1]₂` of
  `ℚ₂ˣ/(ℚ₂ˣ)²`;
* then `[b]₅ = [q]₅ = [3]₅` gives `q/3 ∈ (ℚ₅ˣ)²`, i.e. `q ≡ 2, 3 (mod 5)`,

contradicting the necessary `q ≡ 1, 4 (mod 5)` from the splitness in `ℚ(√5)`.

So **`Mu2EscapeCorrection` and any "datum-free" version of it are false**: the local data at the
places over the ramified primes of `N/k` (here `5`) combines with the *nonsplitness* of those places
in `N` — which is exactly the `horth` hypothesis of `Mu2EscapeCorrection` — to pin the escape prime
to a class incompatible with its splitting in `N`.  The corresponding odd-`p` statement
`GrunwaldEscapeCore.gesEscapeTrivialPair` (proved, sorry-free) does *not* suffer from this because
there the escape prime is only required to be split in `K` (where the splitting is produced by the
same Čebotarev step), and because the realising element `a` there is *constructed* by
Grünwald + Kummer (so its divisor class can be adjusted), whereas here `a` is an arbitrary input.

**Consequence for the §4 design.**  Before the escape route is resumed the statement of
`Mu2EscapeCorrection` (and of `mu2EscapeRealisation_of_correction`, which consumes it) has to be
re-examined: the escape prime's splitting in the level `N ⊋ K` cannot be demanded together with an
arbitrary prescribed local datum at the places over the primes that are ramified in `N`.  What *is*
available unconditionally is the *confinement* half for an arbitrary input
(`ZDataTwo.mu2Correction_confinement`, in `Mu2CorrectionConfinement.lean`), with the escape prime
split in `K` only, and the archimedean half `ZDataTwo.signAdjustment_mu2`
(`SignAdjustment.lean`). -/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The two `p = 2` encodings of the Kummer cochain agree.**  `ZSplit.nodeKummerCocharZMod` (the
`kummerCharZMod`-based cochain used by the escape steps) and `nodeKummerCochar` (the `kummerCochar`-
based cochain used by the §4 assembly of `ZDataTwo/ThreeHalves.lean` and `ZDataTwo/SWFourTwo.lean`)
are the same cochain at `p = 2`; this is the bridge between the two vocabularies. -/
theorem nodeKummerCocharZMod_eq_nodeKummerCochar (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) :
    ZSplit.nodeKummerCocharZMod K ζ hζK hζ b = nodeKummerCochar K ζ hζK hζ b := by
  funext σ
  by_cases hσ : σ ∈ K.fixingSubgroup
  · have h1 : nodeKummerCochar K ζ hζK hζ b σ =
        Work.SSGRoute.kummerChar (Ω := Ω) ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
      kummerCochar_apply K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b hσ
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ, h1]
    exact kummerCharZMod_two_eq_kummerChar k Ω K ⟨ζ, hζK⟩
      (isPrimitiveRoot_subtype_of_mem hζK hζ) b _
  · rw [ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ]
    exact (kummerCochar_of_not_mem K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b hσ).symm

/-- **The `ZMod 2`-valued Kummer character is multiplicative in the element** (at `p = 2`): both
encodings agree, and the multiplicative one is a homomorphism in the element. -/
theorem kummerCharZMod_two_mul (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b₁ b₂ : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ (b₁ * b₂) σ =
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b₁ σ +
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b₂ σ := by
  rw [kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ (b₁ * b₂) σ,
    kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ b₁ σ,
    kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ b₂ σ,
    Work.SSGRoute.kummerChar_mul (K := ↥K) (Ω := Ω) ζ hζ b₁ b₂, Pi.add_apply]

end Work.SSGRoute.ZDataTwo
