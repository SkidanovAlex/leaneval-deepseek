import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Fin

open scoped BigOperators

/-- If two strictly increasing real-valued tuples `γ` and `β` of lengths `N`
and `M` have mutually disjoint value sets, and `α` is a strictly increasing
tuple of length `N + M` whose values are all among the values of `γ` and `β`,
then the sum of `α`'s entries equals the sum of `γ`'s entries plus the sum of
`β`'s entries. -/
theorem sorted_union_sum_eq {N M : ℕ} (γ : Fin N → ℝ) (β : Fin M → ℝ)
    (α : Fin (N + M) → ℝ)
    (hγmono : ∀ ⦃i j : Fin N⦄, i.val < j.val → γ i < γ j)
    (hβmono : ∀ ⦃i j : Fin M⦄, i.val < j.val → β i < β j)
    (hdisj : ∀ (i : Fin N) (j : Fin M), γ i ≠ β j)
    (hαmono : ∀ ⦃i j : Fin (N + M)⦄, i.val < j.val → α i < α j)
    (hcover : ∀ i : Fin (N + M),
      (∃ k : Fin N, α i = γ k) ∨ (∃ l : Fin M, α i = β l)) :
    (∑ i : Fin (N + M), α i) = (∑ k : Fin N, γ k) + (∑ l : Fin M, β l) := by
  classical
  -- Strictly increasing real-valued maps are injective.
  have hγinj : Function.Injective γ := StrictMono.injective (f := γ) hγmono
  have hβinj : Function.Injective β := StrictMono.injective (f := β) hβmono
  have hαinj : Function.Injective α := StrictMono.injective (f := α) hαmono
  -- Value sets of γ, β, α.
  let Sγ : Finset ℝ := Finset.univ.image γ
  let Sβ : Finset ℝ := Finset.univ.image β
  let Sα : Finset ℝ := Finset.univ.image α
  -- The value sets of γ and β are disjoint.
  have hdisjS : Disjoint Sγ Sβ := by
    rw [Finset.disjoint_left]
    intro x hxγ hxβ
    rcases (Finset.mem_image.mp hxγ) with ⟨i, hi, hix⟩
    rcases (Finset.mem_image.mp hxβ) with ⟨j, hj, hjx⟩
    exact hdisj i j (hix.trans hjx.symm)
  -- Their sizes are N, M, N + M respectively.
  have hcardSγ : Sγ.card = N := by
    simpa [Sγ] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin N))) (f := γ) hγinj)
  have hcardSβ : Sβ.card = M := by
    simpa [Sβ] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin M))) (f := β) hβinj)
  have hcardSα : Sα.card = N + M := by
    simpa [Sα] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin (N + M)))) (f := α) hαinj)
  have hcardUnion : (Sγ ∪ Sβ).card = N + M := by
    rw [Finset.card_union_of_disjoint hdisjS, hcardSγ, hcardSβ]
  -- Every value of α lies in Sγ or Sβ.
  have hsub : Sα ⊆ Sγ ∪ Sβ := by
    intro x hx
    rcases (Finset.mem_image.mp hx) with ⟨i, hi, hix⟩
    rw [Finset.mem_union]
    rcases hcover i with ⟨k, hk⟩ | ⟨l, hl⟩
    · left
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm.trans hix⟩
    · right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, hl.symm.trans hix⟩
  -- Same cardinality makes this an equality of value sets.
  have hEq : Sα = Sγ ∪ Sβ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardUnion, hcardSα])
  -- Sums over a tuple equal sums over its value set (tuple is injective).
  have hsum_alpha : (∑ i : Fin (N + M), α i) = ∑ x ∈ Sα, x := by
    symm
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hαinj hab
  have hsum_gamma : (∑ k : Fin N, γ k) = ∑ x ∈ Sγ, x := by
    symm
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hγinj hab
  have hsum_beta : (∑ l : Fin M, β l) = ∑ x ∈ Sβ, x := by
    symm
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hβinj hab
  rw [hsum_alpha, hEq, Finset.sum_union hdisjS]
  rw [← hsum_gamma, ← hsum_beta]

end Commons.Combinatorics.Fin