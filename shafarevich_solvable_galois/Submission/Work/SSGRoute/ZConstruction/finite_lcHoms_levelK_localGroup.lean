import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the level-`K` local `lcHoms`

`natCard_lcHoms_levelK_localGroup` gives the *cardinality* equality
`Nat.card ↥(lcHoms p ↥(decomp (k := ↥K) A)) = Nat.card (κˣ ⧸ (κˣ)^p)`, and a `Nat.card` equality
alone does not give finiteness (both sides could be `0`).  But the right-hand side is a finite local
class group (`Work.SSGRoute.finite_powClass_localField`), so its `Nat.card` is nonzero, hence so is
the left-hand count, hence `↥(lcHoms p ↥(decomp (k := ↥K) A))` is finite.

This finiteness is the hypothesis the injective-implies-bijective squeeze for `localKummerHom`
consumes (with the same cardinality equality), giving the level-`K` local Kummer isomorphism
`κˣ ⧸ (κˣ)^p ≃* ↥(lcHoms p ↥(decomp (k := ↥K) A))`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The level-`K` local `lcHoms` is finite.** -/
theorem finite_lcHoms_levelK_localGroup (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (hA' : SSGRoute.IsFinPlace ↥K A) :
    Finite ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := by
  -- the completion's `p`-power class group is finite
  haveI hfin : Finite
      (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        ((powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range)) :=
    Work.SSGRoute.finite_powClass_localField _ p Fact.out
  -- hence the count on the left is nonzero
  have hcard := natCard_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω) (K := K) A hA hAK hA'
  have hne : Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) ≠ 0 := by
    rw [hcard]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  -- a nonzero `Nat.card` is finite
  rw [← not_infinite_iff_finite]
  intro hinf
  exact hne (Nat.card_eq_zero.mpr (Or.inr hinf))

end Work.SSGRoute.ZConstruction
