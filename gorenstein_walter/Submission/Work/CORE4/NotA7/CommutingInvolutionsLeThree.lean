import Mathlib
import Submission.Work.AUTA7.A7.EvenInvolutionCycleType
import Submission.Work.CORE4.A7FGB.involution_support_mem
import Submission.Work.CORE4.NotA7.InvolSupportEqCompl

namespace Work.CORE4.NotA7

/-!
# At most three commuting involutions for a `3`-element support in `A₇`

Let `x ∈ A₇` have support of cardinality `3` (so `x` is a `3`-cycle) and suppose every
involution of the centralizer `C_{A₇}(x)` fixes the support of `x` pointwise.  Then `C_{A₇}(x)`
contains at most three involutions.

Indeed, writing `T` for the complement of the support of `x` (a four-element set), the
hypothesis forces every such involution `y` to fix the support of `x` pointwise, so that
`support y ⊆ T`; since `y` is an even non-identity involution, `support y` has cardinality `4`
(`Work.AUTA7.A7.EvenInvolutionCycleType`), hence `support y = T`
(`Work.CORE4.NotA7.InvolSupportEqCompl`).  The set of non-identity involutions of `A₇` with
support exactly `T` has at most three elements — an involution on the four-element support `T`
is determined by the image of one of its points, which lies in the three-element set
`T \ {a}` — which is `Work.CORE4.A7FGB.card_involutions_support_le_three`.
-/

open scoped Classical

theorem CommutingInvolutionsLeThree {x : alternatingGroup (Fin 7)}
    (hsupp : (x : Equiv.Perm (Fin 7)).support.card = 3)
    (hfix : ∀ y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))),
        orderOf y = 2 → ∀ a ∈ (x : Equiv.Perm (Fin 7)).support, (y : Equiv.Perm (Fin 7)) a = a) :
    Nat.card {y : alternatingGroup (Fin 7) //
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))) ∧ orderOf y = 2} ≤ 3 := by
  classical
  -- `T` is the complement of the support of `x`, a four-element set.
  set T : Finset (Fin 7) := Finset.univ \ (x : Equiv.Perm (Fin 7)).support with hT
  have hTcard : T.card = 4 := by
    rw [hT, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hsupp]
  -- Turn the `Nat.card` of the subtype into the cardinality of a `Finset` filter.
  have hNat : Nat.card {y : alternatingGroup (Fin 7) //
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))) ∧ orderOf y = 2} =
      (Finset.univ.filter (fun y : alternatingGroup (Fin 7) =>
        y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))) ∧
          orderOf y = 2)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hNat]
  -- Reduce to the standard count of involutions with support `T`.
  refine le_trans (Finset.card_le_card ?_)
    (Work.CORE4.A7FGB.card_involutions_support_le_three T hTcard)
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  obtain ⟨-, hyC, hy2⟩ := hy
  have hy2' : y * y = 1 := by
    have h : y ^ 2 = 1 := by simpa [hy2] using pow_orderOf_eq_one y
    rwa [pow_two] at h
  have hy1 : y ≠ 1 := by
    intro hc
    have h1 : orderOf y = 1 := by rw [hc, orderOf_one]
    omega
  refine ⟨Finset.mem_univ _, hy2', hy1, ?_⟩
  rw [hT]
  exact InvolSupportEqCompl hsupp (hfix y hyC hy2) hy2

end Work.CORE4.NotA7
