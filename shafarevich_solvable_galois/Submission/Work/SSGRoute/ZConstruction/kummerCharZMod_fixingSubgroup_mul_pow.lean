import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer character on the level-`K` local groups: multiplicativity and `p`-th powers

`Work.SSGRoute.kummerCharZMod` is the *global* Kummer character of `β ∈ Kˣ` (`K` an intermediate
field of `Ω/k` with `ζ_p ∈ K`), a `ZMod p`-valued function on `Gal(Ω/K) = K.fixingSubgroup`.

This file records the two elementary properties which make it a *homomorphism* on the level-`K`
local groups, and hence the first ingredient of the level-`K` local Kummer dictionary
`H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup) ≅ K_𝔭ˣ/(K_𝔭ˣ)^p`:

* it is *multiplicative* in `β` (additive, in the `ZMod p`-valued encoding): the Kummer ratio of
  `ββ'` at the product of the chosen root is the product of the ratios, and the Kummer index is
  independent of the chosen `p`-th root (`kummerIdx_congr`, `kummerIdx_mul`);
* it *vanishes on `p`-th powers*: `β = γ^p` gives a root differing from `γ` by a `p`-th root of
  unity lying in `K`, hence fixed by every `σ ∈ Gal(Ω/K)` (`kummerIdx_eq_zero_of_mem_pow`).

The vanishing statement in the other direction — the character of `β` kills the decomposition group
of `A` if and only if `β` is a local `p`-th power at the prime below `A` — is the *local Kummer
dictionary* `Work.SSGRoute.local_kummer_dictionary`, which is proved.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

/-- **The Kummer character is additive in `β` on `K.fixingSubgroup` and kills `p`-th powers.** -/
theorem kummerCharZMod_fixingSubgroup_mul_pow
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) :
    (∀ (β β' : Kˣ) (g : ↥K.fixingSubgroup),
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (β * β')
          ((IntermediateField.fixingSubgroupEquiv K) g) =
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β
            ((IntermediateField.fixingSubgroupEquiv K) g) +
          kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β'
            ((IntermediateField.fixingSubgroupEquiv K) g)) ∧
    (∀ (β : Kˣ) (g : ↥K.fixingSubgroup),
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (β ^ p)
        ((IntermediateField.fixingSubgroupEquiv K) g) = 0) := by
  constructor
  · intro β β' g
    set σ : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) g with hσdef
    have hcd : (kummerSqrtUnitZMod (Ω := Ω) p β * kummerSqrtUnitZMod (Ω := Ω) p β') ^ p =
        Units.map (algebraMap ↥K Ω) (β * β') := by
      rw [mul_pow, kummerSqrtUnitZMod_pow, kummerSqrtUnitZMod_pow, ← map_mul]
    rw [kummerCharZMod_apply,
      kummerIdx_congr p hζ (β * β')
        (kummerSqrtUnitZMod_pow (Ω := Ω) p (β * β')) hcd σ,
      kummerIdx_mul p hζ β β'
        (kummerSqrtUnitZMod (Ω := Ω) p β) (kummerSqrtUnitZMod (Ω := Ω) p β')
        (kummerSqrtUnitZMod_pow (Ω := Ω) p β) (kummerSqrtUnitZMod_pow (Ω := Ω) p β') hcd σ,
      ← kummerCharZMod_apply, ← kummerCharZMod_apply]
  · intro β g
    rw [kummerCharZMod_apply]
    exact kummerIdx_eq_zero_of_mem_pow p hζ (β ^ p) β rfl
      (kummerSqrtUnitZMod (Ω := Ω) p (β ^ p))
      (kummerSqrtUnitZMod_pow (Ω := Ω) p (β ^ p))
      ((IntermediateField.fixingSubgroupEquiv K) g)

end Work.SSGRoute.ZConstruction
