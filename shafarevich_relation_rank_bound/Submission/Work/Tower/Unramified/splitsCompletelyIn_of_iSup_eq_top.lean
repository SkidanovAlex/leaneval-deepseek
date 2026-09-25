import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_sup
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

/-!
# Complete splitting ascends to a finite supremum of intermediate fields

If `𝔭 ≠ ⊥` is a prime of `𝓞 F` which splits completely in each of finitely many intermediate
fields `E i ⊆ L`, then it splits completely in the compositum `⨆ i, E i`, hence — when the
supremum is everything — in `L` itself.

The compositum step is `Work.Tower.Unramified.SplitsCompletelyIn_sup` (ascending complete
splitting from two fields to their compositum), iterated over the finite index set.  Passing
from the equality `⨆ i, E i = ⊤` to `L` uses that `SplitsCompletelyIn` is invariant under
`F`-algebra isomorphisms (`Work.Tower.Unramified.splitsCompletelyIn_of_algEquiv`, which is the
descent lemma `Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom` applied to the inverse
isomorphism) together with `IntermediateField.topEquiv : ↥(⊤ : IntermediateField F L) ≃ₐ[F] L`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-- Complete splitting is invariant under `F`-algebra isomorphisms: if `↥𝔭` splits completely in
`L'/F` and `L' ≃ₐ[F] L`, then it splits completely in `L/F`. -/
theorem splitsCompletelyIn_of_algEquiv {F L L' : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    [FiniteDimensional F L] [FiniteDimensional F L']
    {𝔭 : Ideal (NumberField.RingOfIntegers F)} (e : L' ≃ₐ[F] L)
    (h : Work.Tower.SplitsCompletelyIn F L' 𝔭) : Work.Tower.SplitsCompletelyIn F L 𝔭 :=
  Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭 (e.symm : L →ₐ[F] L') h

/-- **Complete splitting ascends to a finite supremum**, auxiliary induction step: for a fixed
index `i₀`, the supremum of any finite family containing `E i₀` again has `𝔭` splitting
completely. -/
theorem splitsCompletelyIn_finset_sup_insert {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {ι : Type} [Fintype ι]
    (E : ι → IntermediateField F L) [∀ i, FiniteDimensional F (E i)]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h : ∀ i, Work.Tower.SplitsCompletelyIn F ↥(E i) 𝔭) (i₀ : ι) :
    ∀ s : Finset ι, Work.Tower.SplitsCompletelyIn F ↥((insert i₀ s).sup E) 𝔭 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.insert_empty, Finset.sup_singleton]
      exact h i₀
  | insert a s _ ih =>
      rw [Finset.insert_comm i₀ a s, Finset.sup_insert]
      exact Work.Tower.Unramified.SplitsCompletelyIn_sup.mpr ⟨h a, ih⟩

/-- **Complete splitting ascends to a finite supremum of intermediate fields.** -/
theorem splitsCompletelyIn_iSup {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {ι : Type} [Fintype ι] [Nonempty ι]
    (E : ι → IntermediateField F L) [∀ i, FiniteDimensional F (E i)]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h : ∀ i, Work.Tower.SplitsCompletelyIn F ↥(E i) 𝔭) :
    Work.Tower.SplitsCompletelyIn F ↥(⨆ i, E i) 𝔭 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [← Finset.sup_univ_eq_iSup, ← Finset.insert_erase (Finset.mem_univ i₀)]
  exact splitsCompletelyIn_finset_sup_insert E h i₀ (Finset.univ.erase i₀)

theorem splitsCompletelyIn_of_iSup_eq_top {F L : Type} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {ι : Type} [Fintype ι] [Nonempty ι]
    (E : ι → IntermediateField F L) [∀ i, FiniteDimensional F (E i)]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hsup : ⨆ i, E i = ⊤) (h : ∀ i, Work.Tower.SplitsCompletelyIn F ↥(E i) 𝔭) :
    Work.Tower.SplitsCompletelyIn F L 𝔭 := by
  have hK : Work.Tower.SplitsCompletelyIn F ↥(⨆ i, E i) 𝔭 := splitsCompletelyIn_iSup E h
  have htop : Work.Tower.SplitsCompletelyIn F ↥(⊤ : IntermediateField F L) 𝔭 := hsup ▸ hK
  exact splitsCompletelyIn_of_algEquiv IntermediateField.topEquiv htop

end Work.Tower.Unramified
