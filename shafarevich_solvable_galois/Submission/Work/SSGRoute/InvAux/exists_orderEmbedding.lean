import Mathlib
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.exists_nat_ge_of_aeval_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed field of an involution of `ℚ̄` embeds in `ℝ` as an ordered field

Let `c : ℚ̄ ≃+* ℚ̄` be a non-trivial involutive ring automorphism of an algebraic closure of `ℚ`,
with fixed field `F = ℚ̄^c ⊆ ℚ̄`.  The norm set `normSet c = {m * c m | m ≠ 0}` endows `F` with the
order whose positive cone is `cone x = (x = 0 ∨ x ∈ normSet c)` (see `InvAux.lean`).

The purpose of this file is to produce an *ordered ring embedding* of `F` into `ℝ` whose positivity
cone is exactly `cone`.

The point is that every element of `ℚ̄` is algebraic over `ℚ`, hence bounded by a natural number
inside the ordered field `F` (Cauchy's root bound); this says precisely that the order of `F` is
Archimedean.  For an Archimedean linearly ordered field `Mathlib` provides a monotone ring
homomorphism to `ℝ` (`Real.nonemptyOrderRingHom`).  Such a homomorphism is injective because its
domain is a field, and then it is strictly monotone, which pins down the cone.

The only ingredient not present in `Mathlib` is Cauchy's root bound, supplied by the file
`InvAux/exists_nat_ge_of_aeval_eq_zero.lean`.
-/

namespace Work.SSGRoute
namespace InvAux

open TwoTorsion

/-- Every element of `ℚ̄` is algebraic over `ℚ`, and this is inherited by the fixed field. -/
lemma exists_aeval_eq_zero_fixSub {c : SSGRoute.QBar ≃+* SSGRoute.QBar} (x : ↥(fixSub c)) :
    ∃ p : Polynomial ℚ, p ≠ 0 ∧ (Polynomial.aeval x) p = 0 := by
  haveI hΩ : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  have hy : IsAlgebraic ℚ ((x : ↥(fixSub c)) : SSGRoute.QBar) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact hy.of_ringHom_of_comp_eq (RingEquiv.refl ℚ) (Subfield.subtype (fixSub c))
    (EquivLike.surjective _) (Subfield.subtype_injective _) (Subsingleton.elim _ _)

/-- `cone x` says that `x` is non-negative for the order of the fixed field. -/
lemma zero_le_iff_cone {c : SSGRoute.QBar ≃+* SSGRoute.QBar} [Fact (c * c = 1)] [Fact (c ≠ 1)]
    (x : ↥(fixSub c)) : (0 : ↥(fixSub c)) ≤ x ↔ cone x := by
  show cone (x - 0) ↔ cone x
  rw [sub_zero]

/-- The order coming from the norm set of an involution of `ℚ̄` is Archimedean: every element of the
fixed field is dominated by a natural number, because it is algebraic over `ℚ`. -/
theorem instArchimedean_fixSub {c : SSGRoute.QBar ≃+* SSGRoute.QBar} [Fact (c * c = 1)]
    [Fact (c ≠ 1)] : Archimedean ↥(fixSub c) := by
  rw [archimedean_iff_nat_le]
  intro x
  obtain ⟨p, hp, hp0⟩ := exists_aeval_eq_zero_fixSub x
  exact exists_nat_ge_of_aeval_eq_zero hp hp0

theorem exists_orderEmbedding {c : SSGRoute.QBar ≃+* SSGRoute.QBar} [Fact (c * c = 1)] [Fact (c ≠ 1)] :
    ∃ ι : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ,
      Function.Injective ι ∧ ∀ x, 0 ≤ ι x ↔ Work.SSGRoute.InvAux.cone x := by
  haveI hArch : Archimedean ↥(fixSub c) := instArchimedean_fixSub
  -- An Archimedean linearly ordered field has a monotone ring homomorphism to `ℝ`.
  obtain ⟨ι⟩ := (inferInstance : Nonempty (↥(fixSub c) →+*o ℝ))
  have hinj : Function.Injective ι := RingHom.injective (ι : ↥(fixSub c) →+* ℝ)
  -- an injective monotone map is strictly monotone
  have hmono : StrictMono ι := ι.monotone'.strictMono_of_injective hinj
  refine ⟨ι, hinj, ?_⟩
  intro x
  constructor
  · intro h
    by_contra hc
    have hx0 : x < 0 := lt_of_not_ge fun hle => hc ((zero_le_iff_cone x).mp hle)
    have h1 := hmono hx0
    rw [map_zero] at h1
    exact (not_le_of_gt h1) h
  · intro hcone
    calc (0 : ℝ) = ι 0 := (map_zero ι).symm
      _ ≤ ι x := ι.monotone' ((zero_le_iff_cone x).mpr hcone)

end InvAux
end Work.SSGRoute
