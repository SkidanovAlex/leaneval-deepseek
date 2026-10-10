import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.HRec.archLevelAux
import Submission.Work.SSGRoute.ZDataTwo.mu2KummerFirstElement
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin--Schreier dictionary at an intermediate level: involutions are real places

`Work.SSGRoute.HRec.realPlaceOfInvolution_isReal` and
`Work.SSGRoute.ZDataTwo.exists_realPlace_of_involution` give the Artin--Schreier dictionary for a
*base field* `k` and an algebraic closure `Ω`: every non-trivial involution `c` of `Ω ≃ₐ[k] Ω` is the
conjugation at a real place `w` of `k`, with `χ_c(a) = 0 ⟺ a` is not negative at `w`.

The archimedean side of the `p = 2` escape construction needs the same dictionary at an intermediate
level `K` with `k ≤ K ≤ Ω`: an involution `c ∈ Gal(Ω/K)` inside the fixing subgroup `K.fixingSubgroup`
of `Gal(Ω/k)` has to be matched with a real place of `↥K`.  That is the statement proved here:

`Work.SSGRoute.ZDataTwo.realPlace_involution_kummerChar_iff`

— for every involutive `c ∈ K.fixingSubgroup` with `c ≠ 1` there is a *real* infinite place `w` of
`↥K` such that, for every `b ∈ (↥K)ˣ`, the `ZMod 2`-valued Kummer character of `b` at (the image of)
`c` vanishes exactly when `b` is not negative at `w`.

The proof is plumbing, not new mathematics: transport `c` along the monoid isomorphism
`IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* (Ω ≃ₐ[↥K] Ω)` (which preserves
squares, hence involutions, and injectivity, hence `≠ 1`), apply the existing dictionary with the
base field `↥K` (the required `IsAlgClosure ↥K Ω` instance is `⟨IsAlgClosure.isAlgClosed k,
inferInstance⟩`, as elsewhere in this workspace), and identify the two `ZMod 2`-valued Kummer
characters `kummerCharZMod 2` and `kummerChar` through `Work.SSGRoute.kummerIdx_congr` (both are
`kummerIdx` evaluated at a square root of `b`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The `ZMod 2`-valued Kummer character is the multiplicative one.**  At `p = 2` the two
encodings `kummerCharZMod` and `kummerChar` of "`σ √b / √b`" agree, because `Work.SSGRoute.kummerIdx`
depends on the chosen root only through its defining relation `γ ^ 2 = b`. -/
theorem kummerCharZMod_two_eq_kummerChar (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b σ =
      Work.SSGRoute.kummerChar (K := ↥K) (Ω := Ω) ζ hζ b σ := by
  rw [Work.SSGRoute.kummerCharZMod_apply, Work.SSGRoute.kummerChar_apply]
  exact Work.SSGRoute.kummerIdx_congr 2 hζ b
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 b) (Work.SSGRoute.kummerSqrt_pow (Ω := Ω) b) σ

/-- **The Artin--Schreier dictionary at the intermediate level `K`.**  Every non-trivial involution
of `Gal(Ω/K)` — i.e. every `c ∈ K.fixingSubgroup` with `c ^ 2 = 1` and `c ≠ 1` — is the conjugation
at a real place `w` of `↥K`, and the `ZMod 2`-valued Kummer character of `b ∈ (↥K)ˣ` at `c` vanishes
exactly when `b` is not negative at `w`. -/
theorem realPlace_involution_kummerChar_iff (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ w : NumberField.InfinitePlace ↥K, w.IsReal ∧
      ∀ b : (↥K)ˣ,
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
          ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩) = 0 ↔
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w b := by
  classical
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- the involution, viewed in `Gal(Ω/↥K)`
  set c' : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ with hc'def
  have hc'2 : c' ^ 2 = 1 := by
    rw [hc'def, ← map_pow]
    have h2 : (⟨c, hc⟩ : K.fixingSubgroup) ^ 2 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc2
    rw [h2, map_one]
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    have h1 : (⟨c, hc⟩ : K.fixingSubgroup) = 1 := by
      apply (IntermediateField.fixingSubgroupEquiv K).injective
      rw [hc'def] at h
      simpa using h
    exact congrArg Subtype.val h1
  -- the existing dictionary, with the base field `↥K`
  obtain ⟨w, hwreal, hw⟩ := Work.SSGRoute.HRec.realPlaceOfInvolution_isReal
    (k := ↥K) (Ω := Ω) ζ hζ c' hc'2 hc'1
  refine ⟨w, hwreal, fun b => ?_⟩
  rw [kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ b ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩)]
  exact hw b

end Work.SSGRoute.ZDataTwo
