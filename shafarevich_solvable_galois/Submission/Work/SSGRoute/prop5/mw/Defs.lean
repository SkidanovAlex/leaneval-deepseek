import Mathlib.Algebra.Lie.OfAssociative
import Submission.Work.SSGRoute.prop5.nestedLieDefs
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.mw

/-- The free associative `ℤ`-algebra `FreeAssoc X`, regarded as a Lie ring through the
commutator. -/
instance instLieRingFreeAssoc (X : Type*) : LieRing (FreeAssoc X) := LieRing.ofAssociativeRing

/-- The `ℤ`-span of the values of `ψ` on the **Hall trees of size `n`**. -/
def VspanSize {X : Type*} [LinearOrder X] {M : Type*} [LieRing M]
    (ψ : Magma X → M) (n : ℕ) : Submodule ℤ M :=
  Submodule.span ℤ
    (Set.range (fun h : {h : Magma X // IsHall h ∧ Magma.size h = n} => ψ h.1))

/-- The bracket monomial of `nestedLieDefs` is the commutator evaluation of `witt.Vocab`. -/
theorem brkMon_eq_monBrk (X : Type*) (c : Magma X) : brkMon X c = monBrk X c := by
  induction c with
  | gen x => simp [brkMon_gen, monBrk_gen, wordEl]
  | mul a b iha ihb => rw [brkMon_mul, monBrk_mul, iha, ihb]

/-- The swap inequality for the foliages of a Hall tree. -/
theorem hswap_hall {X : Type*} [LinearOrder X] {a b : Magma X}
    (h : IsHall (Magma.mul a b)) :
    Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a :=
  swap_hall_of_crux (fun _ _ hh => witt.hall_foliage_lt_right hh) h

/-- **Leading term of the bracketed monomial of a Hall tree.**  The foliage of a Hall tree `c` is
the lexicographically smallest word occurring in `monBrk c`, and it occurs with coefficient `1`. -/
theorem hlead_monBrk {X : Type*} [LinearOrder X] (c : Magma X) (hc : IsHall c) :
    coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
      ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0 :=
  witt.leading_term_coeff hc (fun _ _ hab => hswap_hall hab)


/-- An element of the graded Hall span is a finite `ℤ`-linear combination of the values `ψ h` on
Hall trees `h` of size `j`. -/
theorem exists_finsupp_of_mem_VspanSize {X : Type*} [LinearOrder X] {M : Type*} [LieRing M]
    (ψ : Magma X → M) (j : ℕ) {x : M} (hx : x ∈ VspanSize ψ j) :
    ∃ d : {h : Magma X // IsHall h ∧ Magma.size h = j} →₀ ℤ,
      x = ∑ h ∈ d.support, d h • ψ h.1 := by
  rw [VspanSize] at hx
  rw [← Finsupp.range_linearCombination (ℤ)
    (v := fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => ψ h.1)] at hx
  obtain ⟨d, hd⟩ := hx
  refine ⟨d, ?_⟩
  rw [← hd, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset d (Finset.Subset.refl _) (fun h r => r • ψ h.1) (by simp)]

end Work.SSGRoute.prop5.mw
