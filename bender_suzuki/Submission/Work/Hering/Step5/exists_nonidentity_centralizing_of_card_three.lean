import Mathlib
import Submission.Work.Hering.Step5.exists_nontrivial_fixed_point_of_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step 5 of the Hering area: a `C₃` acting on a group of order `8` has a nontrivial fixed point

Let `U ≤ G` be a subgroup of order `8` and `X ≤ N_G(U)` a subgroup of order `3`.  Then `X` acts by
conjugation on `U`; we must exhibit `u ∈ U`, `u ≠ 1`, centralized by all of `X`.

The mathematics is a counting argument.  Since `|X| = 3` is prime and coprime to `|U| = 8`, for
the conjugation action of `X` on the finite set `U` the number of fixed points satisfies
`|U| ≡ |C_U(X)| (mod 3)` (a general fact for `p`-groups acting on finite sets,
`IsPGroup.card_modEq_card_fixedPoints`).  Because `|U| = 8 ≡ 2 (mod 3)` and the identity is always
fixed, there are at least two fixed points, hence a nontrivial one.

This is packaged as the already-proved counting lemma
`exists_nontrivial_fixed_point_of_coprime`, which needs a `MulDistribMulAction ↥X ↥U`.  That action
is the conjugation action of `N_G(U)` on `U` (the Mathlib instance on `Subgroup.normalizer`),
pulled back along `X ≤ N_G(U)`; the local lemma `key` records what it computes to.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Hering.Step5

theorem exists_nonidentity_centralizing_of_card_three {G : Type*} [Group G] [Finite G]
    {U X : Subgroup G} (hX : X ≤ Subgroup.normalizer (U : Set G)) (hXcard : Nat.card X = 3)
    (hUcard : Nat.card U = 8) :
    ∃ u : G, u ∈ U ∧ u ≠ 1 ∧ ∀ x ∈ X, x * u = u * x := by
  haveI : Finite ↥X := Finite.of_injective (Subtype.val : ↥X → G) Subtype.val_injective
  haveI : Finite ↥U := Finite.of_injective (Subtype.val : ↥U → G) Subtype.val_injective
  -- The conjugation action of `X` on `U`, obtained from the action of `N_G(U)` on `U`.
  letI : MulDistribMulAction ↥X ↥U :=
    MulDistribMulAction.compHom ↥U (U.normalizerMonoidHom.comp (Subgroup.inclusion hX))
  -- What the action computes to: `a • v` is conjugation of `v` by `a`.
  have key : ∀ (a : ↥X) (v : ↥U),
      ((a • v : ↥U) : G) = (a : G) * (v : G) * (a : G)⁻¹ := by
    intro a v
    simp only [MulAction.compHom_smul_def, MonoidHom.comp_apply, MulAut.smul_def,
      Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
      MulDistribMulAction.toMulEquiv_apply]
    rfl
  -- The counting lemma produces a nontrivial fixed point of the action.
  obtain ⟨u, hu1, hufix⟩ :=
    exists_nontrivial_fixed_point_of_coprime (A := ↥X) (U := ↥U) 3 Nat.prime_three
      hXcard (by rw [hUcard]; norm_num) (by rw [hUcard]; norm_num)
      (by rw [hUcard]; norm_num)
  refine ⟨(u : G), u.2, ⟨?_, ?_⟩⟩
  · intro h1
    exact hu1 (Subtype.ext h1)
  · intro x hx
    have h := hufix ⟨x, hx⟩
    have h2 : x * (u : G) * x⁻¹ = (u : G) := by
      rw [← key ⟨x, hx⟩ u, h]
    calc x * (u : G) = x * (u : G) * x⁻¹ * x := by group
      _ = (u : G) * x := by rw [h2]

end Work.Hering.Step5
