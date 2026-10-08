import Mathlib
import Submission.Work.BG.ThmABCCharDefs

namespace Work.BG

/-- Auxiliary: a sum over all irreducible characters equals the (set-restricted) `finsum`
over the support set `𝒮(χ)`, when the summand vanishes off that set.

The point is that `𝒮(χ) = C16.bset C f χ` consists of *class functions* (it is a `Set` in the
class-function space), whereas the left-hand side sums over the finite index type of irreducible
characters.  The two are related by the (injective) coercion
`IrreducibleCharacter H → ClassFunction H ℂ`:  every class function lying in `𝒮(χ)` is an
irreducible character, hence is the image of an index. -/
theorem s02_sum_irr_eq_finsum_bset {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (F : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → ℂ)
    (hF : ∀ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
      (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) ∉
        Work.GW2.C16.bset C f χ → F (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) = 0) :
    (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        F (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)) =
      ∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, F ν := by
  classical
  -- Turn the set-restricted `finsum` into a plain `finsum` of the indicator function.
  rw [finsum_mem_def]
  -- The coercion `Irr → ClassFunction` is injective, so summing over its image is the same as
  -- summing over the index type.
  have hinj : Set.InjOn
      (fun ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))
      ↑(Finset.univ : Finset (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)) :=
    fun a _ b _ h => OddOrder.RepresentationTheory.IrreducibleCharacter.ext h
  -- The indicator is supported inside the image of the coercion: any class function on which it
  -- does not vanish lies in `𝒮(χ)`, hence is an irreducible character.
  have hsupp : Function.support ((Work.GW2.C16.bset C f χ).indicator F) ⊆
      ↑(Finset.univ.image (fun ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hmem : ν ∈ Work.GW2.C16.bset C f χ := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hν
      exact hν rfl
    exact Finset.mem_image.mpr
      ⟨⟨ν, hmem.1⟩, Finset.mem_univ _, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  -- Now both sides are sums over the index type; they agree termwise because `F` vanishes off
  -- `𝒮(χ)` (this is exactly `hF`).
  refine Finset.sum_congr rfl ?_
  intro ν _
  by_cases h : (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) ∈
      Work.GW2.C16.bset C f χ
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, hF ν h]

end Work.BG
