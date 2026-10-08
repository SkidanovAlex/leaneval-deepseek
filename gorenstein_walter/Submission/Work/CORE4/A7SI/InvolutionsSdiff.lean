import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CountFibre

/-!
# Counting the involutions outside a subgroup, by right cosets

Let `G` be a finite group and `M ≤ G`.  Suppose that for every involution `y ∉ M` the set

`{x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ M}`

of involutions lying in the right coset `M·y` has at most `21` elements.  Then the total number of
involutions of `G` that do not lie in `M` is at most `21 · [G : M]`.

The proof is the fibre decomposition of `{x : orderOf x = 2, x ∉ M}` along the map
`x ↦ (x⁻¹) M` from `G` to the coset space `G ⧸ M`: since the classes of `G ⧸ M` are the *left*
cosets, its fibres are exactly the *right* cosets `M·y⁻¹`, and the fibre over the class of `y⁻¹`
is contained in the set counted by the hypothesis.  Each fibre therefore has at most `21` elements
(and `0` if it meets no involution outside `M`), and there are `[G : M]` classes.
-/

namespace Work.CORE4.A7SI

theorem InvolutionsSdiff {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (h : ∀ y : G, orderOf y = 2 → y ∉ M →
        {x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ M}.ncard ≤ 21) :
    {x : G | orderOf x = 2 ∧ x ∉ M}.ncard ≤ 21 * M.index := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
  -- The involution predicate, and the coset map `x ↦ (x⁻¹) M`.
  let p : G → Prop := fun x => orderOf x = 2 ∧ x ∉ M
  let f : G → G ⧸ M := fun x => QuotientGroup.mk (s := M) x⁻¹
  -- Every fibre is bounded by `21`: it is contained in the set of the hypothesis.
  have key : ∀ c : G ⧸ M, ({x : G | p x ∧ f x = c} : Set G).ncard ≤ 21 := by
    intro c
    by_cases hc : ∃ y : G, orderOf y = 2 ∧ y ∉ M ∧ f y = c
    · obtain ⟨y, hy2, hyM, hyc⟩ := hc
      have hsub : {x : G | p x ∧ f x = c} ⊆ {x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ M} := by
        intro x hx
        obtain ⟨⟨hx2, hxM⟩, hxc⟩ := hx
        refine ⟨hx2, ?_⟩
        have h1 : f x = f y := by rw [hxc, hyc]
        have := QuotientGroup.eq.mp h1
        simpa [f] using this
      exact le_trans (Set.ncard_le_ncard hsub) (h y hy2 hyM)
    · push Not at hc
      have hempty : {x : G | p x ∧ f x = c} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro x hx
        exact hc x hx.1.1 hx.1.2 hx.2
      rw [hempty, Set.ncard_empty]
      norm_num
  -- Decompose the target set into the fibres of `f` and sum the bounds.
  change ({x : G | p x} : Set G).ncard ≤ 21 * M.index
  rw [Work.CORE4.ncard_eq_sum_ncard_fiber f p]
  calc ∑ c : G ⧸ M, ({x : G | p x ∧ f x = c} : Set G).ncard
      ≤ ∑ _c : G ⧸ M, (21 : ℕ) := Finset.sum_le_sum (fun c _ => key c)
    _ = 21 * M.index := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
          ← Subgroup.index_eq_card, Nat.mul_comm]

end Work.CORE4.A7SI
