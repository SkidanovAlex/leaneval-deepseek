import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.SSGRoute.InvAux.exists_orderEmbedding
import Submission.Work.SSGRoute.InvAux.irreducible_natDegree_le_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed field of an involution of an algebraic closure of `ℚ` embeds in `ℝ`

Let `Ω` be an algebraically closed field of characteristic zero which is algebraic over `ℚ`
(e.g. an algebraic closure of `ℚ`), and let `c : Ω ≃+* Ω` be a non-trivial involutive ring
automorphism with fixed field `F = Ω^c`.  The norm set `normSet c = {m * c m | m ≠ 0}` endows
`F` with the structure of a linearly ordered field whose positive cone is
`cone x ↔ x = 0 ∨ x ∈ normSet c` (see `InvAux.lean`).

We show that `F` admits an *ordered ring embedding* into `ℝ` whose positivity cone is exactly
`cone`, i.e. an injective map `ρ : F →+*o ℝ` with `0 ≤ ρ x ↔ cone x`.  This is the general
form of `Work.SSGRoute.InvAux.exists_orderEmbedding`, which treats the special case
`Ω = ℚ̄`.

The argument is unchanged from the special case.  Every element of `Ω` is algebraic over `ℚ`,
hence so is every element of the fixed field; by Cauchy's root bound an algebraic element of a
linearly ordered field is dominated by a natural number, so the order of `F` is Archimedean.
For an Archimedean linearly ordered field Mathlib provides a monotone ring homomorphism to `ℝ`
(`Real.nonemptyOrderRingHom`); it is injective because `F` is a field, hence strictly monotone,
which pins down the positivity cone.
-/

namespace Work.SSGRoute.ZDataTwo

open Work.SSGRoute.InvAux

/-- Every element of the fixed field of an involutive ring automorphism of a field algebraic
over `ℚ` is a root of a non-zero polynomial over `ℚ`. -/
lemma exists_aeval_eq_zero_fixSub_of_isAlgebraic {Ω : Type*} [Field Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} (x : ↥(fixSub c)) :
    ∃ p : Polynomial ℚ, p ≠ 0 ∧ (Polynomial.aeval x) p = 0 := by
  have hy : IsAlgebraic ℚ ((x : ↥(fixSub c)) : Ω) := Algebra.IsAlgebraic.isAlgebraic _
  exact hy.of_ringHom_of_comp_eq (RingEquiv.refl ℚ) (Subfield.subtype (fixSub c))
    (EquivLike.surjective _) (Subfield.subtype_injective _) (Subsingleton.elim _ _)

/-- The order of the fixed field of a non-trivial involution of an algebraically closed field of
characteristic zero which is algebraic over `ℚ` is Archimedean: every element is dominated by a
natural number, because it is algebraic over `ℚ`. -/
theorem instArchimedean_fixSub_of_isAlgebraic {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)] :
    Archimedean ↥(fixSub c) := by
  rw [archimedean_iff_nat_le]
  intro x
  obtain ⟨p, hp, hp0⟩ := exists_aeval_eq_zero_fixSub_of_isAlgebraic (Ω := Ω) (c := c) x
  exact exists_nat_ge_of_aeval_eq_zero hp hp0

/-- `cone x` says that `x` is non-negative for the order of the fixed field. -/
lemma zero_le_iff_cone_fixSub {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)] (x : ↥(fixSub c)) :
    (0 : ↥(fixSub c)) ≤ x ↔ cone x := by
  show cone (x - 0) ↔ cone x
  rw [sub_zero]

theorem exists_orderEmbedding_fixSub {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)] :
    ∃ ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ,
      Function.Injective ρ ∧ ∀ x, 0 ≤ ρ x ↔ Work.SSGRoute.InvAux.cone x := by
  have hArch : Archimedean ↥(fixSub c) := instArchimedean_fixSub_of_isAlgebraic
  -- An Archimedean linearly ordered field has a monotone ring homomorphism to `ℝ`.
  obtain ⟨ι⟩ := (@Real.nonemptyOrderRingHom ↥(fixSub c) _ _ _ hArch)
  have hinj : Function.Injective ι := RingHom.injective (ι : ↥(fixSub c) →+* ℝ)
  -- an injective monotone map is strictly monotone
  have hmono : StrictMono ι := ι.monotone'.strictMono_of_injective hinj
  refine ⟨ι, hinj, fun x => ?_⟩
  constructor
  · intro h
    by_contra hc
    have hx0 : x < 0 := lt_of_not_ge fun hle => hc ((zero_le_iff_cone_fixSub x).mp hle)
    have h1 := hmono hx0
    rw [map_zero] at h1
    exact (not_le_of_gt h1) h
  · intro hcone
    calc (0 : ℝ) = ι 0 := (map_zero ι).symm
      _ ≤ ι x := ι.monotone' ((zero_le_iff_cone_fixSub x).mpr hcone)

end Work.SSGRoute.ZDataTwo
